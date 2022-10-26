//! Deduces supplementary parameter attributes from MIR.
//!
//! Deduced parameter attributes are those that can only be soundly determined by examining the
//! body of the function instead of just the signature. These can be useful for optimization
//! purposes on a best-effort basis. We compute them here and store them into the crate metadata so
//! dependent crates can use them.

use rustc_hir::def_id::DefId;
use rustc_index::bit_set::BitSet;
use rustc_middle::mir::visit::{NonMutatingUseContext, PlaceContext, Visitor};
use rustc_middle::mir::{Body, Local, Location, Operand, Terminator, TerminatorKind, RETURN_PLACE};
use rustc_middle::ty::{self, DeducedParamAttrs, ParamEnv, Ty, TyCtxt};
use rustc_session::config::OptLevel;
use rustc_span::DUMMY_SP;

/// A visitor that determines which arguments have been mutated. We can't use the mutability field
/// on LocalDecl for this because it has no meaning post-optimization.
struct DeduceReadOnly {
    /// Each bit is indexed by argument number, starting at zero (so 0 corresponds to local decl
    /// 1). The bit is true if the argument may have been mutated or false if we know it hasn't
    /// been up to the point we're at.
    mutable_args: BitSet<usize>,
}

impl DeduceReadOnly {
    /// Returns a new DeduceReadOnly instance.
    fn new(arg_count: usize) -> Self {
        Self { mutable_args: BitSet::new_empty(arg_count) }
    }
}

impl<'tcx> Visitor<'tcx> for DeduceReadOnly {
    fn visit_local(&mut self, local: Local, mut context: PlaceContext, _: Location) {
        // We're only interested in arguments.
        if local == RETURN_PLACE || local.index() > self.mutable_args.domain_size() {
            return;
        }

        // Replace place contexts that are moves with copies. This is safe in all cases except
        // function argument position, which we already handled in `visit_terminator()` by using the
        // ArgumentChecker. See the comment in that method for more details.
        //
        // In the future, we might want to move this out into a separate pass, but for now let's
        // just do it on the fly because that's faster.
        if matches!(context, PlaceContext::NonMutatingUse(NonMutatingUseContext::Move)) {
            context = PlaceContext::NonMutatingUse(NonMutatingUseContext::Copy);
        }

        match context {
            PlaceContext::MutatingUse(..)
            | PlaceContext::NonMutatingUse(NonMutatingUseContext::Move) => {
                // This is a mutation, so mark it as such.
                self.mutable_args.insert(local.index() - 1);
            }
            PlaceContext::NonMutatingUse(..) | PlaceContext::NonUse(..) => {
                // Not mutating, so it's fine.
            }
        }
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        // OK, this is subtle. Suppose that we're trying to deduce whether `x` in `f` is read-only
        // and we have the following:
        //
        //     fn f(x: BigStruct) { g(x) }
        //     fn g(mut y: BigStruct) { y.foo = 1 }
        //
        // If, at the generated MIR level, `f` turned into something like:
        //
        //      fn f(_1: BigStruct) -> () {
        //          let mut _0: ();
        //          bb0: {
        //              _0 = g(move _1) -> bb1;
        //          }
        //          ...
        //      }
        //
        // then it would be incorrect to mark `x` (i.e. `_1`) as `readonly`, because `g`'s write to
        // its copy of the indirect parameter would actually be a write directly to the pointer that
        // `f` passes. Note that function arguments are the only situation in which this problem can
        // arise: every other use of `move` in MIR doesn't actually write to the value it moves
        // from.
        //
        // Anyway, right now this situation doesn't actually arise in practice. Instead, the MIR for
        // that function looks like this:
        //
        //      fn f(_1: BigStruct) -> () {
        //          let mut _0: ();
        //          let mut _2: BigStruct;
        //          bb0: {
        //              _2 = move _1;
        //              _0 = g(move _2) -> bb1;
        //          }
        //          ...
        //      }
        //
        // Because of that extra move that MIR construction inserts, `x` (i.e. `_1`) can *in
        // practice* safely be marked `readonly`.
        //
        // To handle the possibility that other optimizations (for example, destination propagation)
        // might someday generate MIR like the first example above, we panic upon seeing an argument
        // to *our* function that is directly moved into *another* function as an argument. Having
        // eliminated that problematic case, we can safely treat moves as copies in this analysis.
        //
        // In the future, if MIR optimizations cause arguments of a caller to be directly moved into
        // the argument of a callee, we can just add that argument to `mutated_args` instead of
        // panicking.
        //
        // Note that, because the problematic MIR is never actually generated, we can't add a test
        // case for this.

        if let TerminatorKind::Call { ref args, .. } = terminator.kind {
            for arg in args {
                if let Operand::Move(_) = *arg {
                    // ArgumentChecker panics if a direct move of an argument from a caller to a
                    // callee was detected.
                    //
                    // If, in the future, MIR optimizations cause arguments to be moved directly
                    // from callers to callees, change the panic to instead add the argument in
                    // question to `mutating_uses`.
                    ArgumentChecker::new(self.mutable_args.domain_size())
                        .visit_operand(arg, location)
                }
            }
        };

        self.super_terminator(terminator, location);
    }
}

/// A visitor that simply panics if a direct move of an argument from a caller to a callee was
/// detected.
struct ArgumentChecker {
    /// The number of arguments to the calling function.
    arg_count: usize,
}

impl ArgumentChecker {
    /// Creates a new ArgumentChecker.
    fn new(arg_count: usize) -> Self {
        Self { arg_count }
    }
}

impl<'tcx> Visitor<'tcx> for ArgumentChecker {
    fn visit_local(&mut self, local: Local, context: PlaceContext, _: Location) {
        // Check to make sure that, if this local is an argument, we didn't move directly from it.
        if matches!(context, PlaceContext::NonMutatingUse(NonMutatingUseContext::Move))
            && local != RETURN_PLACE
            && local.index() <= self.arg_count
        {
            // If, in the future, MIR optimizations cause arguments to be moved directly from
            // callers to callees, change this panic to instead add the argument in question to
            // `mutating_uses`.
            panic!("Detected a direct move from a caller's argument to a callee's argument!")
        }
    }
}

/// Returns true if values of a given type will never be passed indirectly, regardless of ABI.
fn type_will_always_be_passed_directly<'tcx>(ty: Ty<'tcx>) -> bool {
    matches!(
        ty.kind(),
        ty::Bool
            | ty::Char
            | ty::Float(..)
            | ty::Int(..)
            | ty::RawPtr(..)
            | ty::Ref(..)
            | ty::Slice(..)
            | ty::Uint(..)
    )
}

/// Returns the deduced parameter attributes for a function.
///
/// Deduced parameter attributes are those that can only be soundly determined by examining the
/// body of the function instead of just the signature. These can be useful for optimization
/// purposes on a best-effort basis. We compute them here and store them into the crate metadata so
/// dependent crates can use them.
pub fn deduced_param_attrs<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> &'tcx [DeducedParamAttrs] {
    // This computation is unfortunately rather expensive, so don't do it unless we're optimizing.
    // Also skip it in incremental mode.
    if tcx.sess.opts.optimize == OptLevel::No || tcx.sess.opts.incremental.is_some() {
        return &[];
    }

    // If the Freeze language item isn't present, then don't bother.
    if tcx.lang_items().freeze_trait().is_none() {
        return &[];
    }

    // Codegen won't use this information for anything if all the function parameters are passed
    // directly. Detect that and bail, for compilation speed.
    let fn_ty = tcx.type_of(def_id);
    if matches!(fn_ty.kind(), ty::FnDef(..)) {
        if fn_ty
            .fn_sig(tcx)
            .inputs()
            .skip_binder()
            .iter()
            .cloned()
            .all(type_will_always_be_passed_directly)
        {
            return &[];
        }
    }

    // Don't deduce any attributes for functions that have no MIR.
    if !tcx.is_mir_available(def_id) {
        return &[];
    }

    // Deduced attributes for other crates should be read from the metadata instead of via this
    // function.
    debug_assert!(def_id.is_local());

    // Grab the optimized MIR. Analyze it to determine which arguments have been mutated.
    let body: &Body<'tcx> = tcx.optimized_mir(def_id);
    let mut deduce_read_only = DeduceReadOnly::new(body.arg_count);
    deduce_read_only.visit_body(body);

    // Set the `readonly` attribute for every argument that we concluded is immutable and that
    // contains no UnsafeCells.
    //
    // FIXME: This is overly conservative around generic parameters: `is_freeze()` will always
    // return false for them. For a description of alternatives that could do a better job here,
    // see [1].
    //
    // [1]: https://github.com/rust-lang/rust/pull/103172#discussion_r999139997
    let mut deduced_param_attrs = tcx.arena.alloc_from_iter(
        body.local_decls.iter().skip(1).take(body.arg_count).enumerate().map(
            |(arg_index, local_decl)| DeducedParamAttrs {
                read_only: !deduce_read_only.mutable_args.contains(arg_index)
                    && local_decl.ty.is_freeze(tcx.at(DUMMY_SP), ParamEnv::reveal_all()),
            },
        ),
    );

    // Trailing parameters past the size of the `deduced_param_attrs` array are assumed to have the
    // default set of attributes, so we don't have to store them explicitly. Pop them off to save a
    // few bytes in metadata.
    while deduced_param_attrs.last() == Some(&DeducedParamAttrs::default()) {
        let last_index = deduced_param_attrs.len() - 1;
        deduced_param_attrs = &mut deduced_param_attrs[0..last_index];
    }

    deduced_param_attrs
}