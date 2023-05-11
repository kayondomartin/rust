use rustc_middle::mir;
use rustc_middle::mir::NonDivergingIntrinsic;
use rustc_middle::ty;
use rustc_target::abi::Align;

use super::FunctionCx;
use super::LocalRef;
use crate::traits::BuilderMethods;
use crate::traits::*;

impl<'a, 'tcx, Bx: BuilderMethods<'a, 'tcx>> FunctionCx<'a, 'tcx, Bx> {
    #[instrument(level = "debug", skip(self, bx))]
    pub fn codegen_statement(&mut self, mut bx: Bx, statement: &mir::Statement<'tcx>) -> Bx {
        self.set_debug_loc(&mut bx, statement.source_info);
        match statement.kind {
            mir::StatementKind::Assign(box (ref place, ref rvalue)) => {
                if let Some(index) = place.as_local() {
                    match self.locals[index] {
                        LocalRef::Place(cg_dest) => self.codegen_rvalue(bx, cg_dest, rvalue),
                        LocalRef::UnsizedPlace(cg_indirect_dest) => {
                            self.codegen_rvalue_unsized(bx, cg_indirect_dest, rvalue)
                        }
                        LocalRef::Operand(None) => {
                            let (mut bx, operand) = self.codegen_rvalue_operand(bx, rvalue);
                            self.locals[index] = LocalRef::Operand(Some(operand));
                            self.debug_introduce_local(&mut bx, index);
                            bx
                        }
                        LocalRef::Operand(Some(op)) => {
                            if !op.layout.is_zst() {
                                span_bug!(
                                    statement.source_info.span,
                                    "operand {:?} already assigned",
                                    rvalue
                                );
                            }

                            // If the type is zero-sized, it's already been set here,
                            // but we still need to make sure we codegen the operand
                            self.codegen_rvalue_operand(bx, rvalue).0
                        }
                    }
                } else {
                    let cg_dest = self.codegen_place(&mut bx, place.as_ref());
                    self.codegen_rvalue(bx, cg_dest, rvalue)
                }
            }
            mir::StatementKind::SetDiscriminant { box ref place, variant_index } => {
                self.codegen_place(&mut bx, place.as_ref())
                    .codegen_set_discr(&mut bx, variant_index);
                bx
            }
            mir::StatementKind::Deinit(..) => {
                // For now, don't codegen this to anything. In the future it may be worth
                // experimenting with what kind of information we can emit to LLVM without hurting
                // perf here
                bx
            }
            mir::StatementKind::StorageLive(local) => {
                if let LocalRef::Place(cg_place) = self.locals[local] {
                    cg_place.storage_live(&mut bx);
                } else if let LocalRef::UnsizedPlace(cg_indirect_place) = self.locals[local] {
                    cg_indirect_place.storage_live(&mut bx);
                }
                bx
            }
            mir::StatementKind::StorageDead(local) => {
                if let LocalRef::Place(cg_place) = self.locals[local] {
                    cg_place.storage_dead(&mut bx);
                } else if let LocalRef::UnsizedPlace(cg_indirect_place) = self.locals[local] {
                    cg_indirect_place.storage_dead(&mut bx);
                }
                bx
            }
            mir::StatementKind::Coverage(box ref coverage) => {
                self.codegen_coverage(&mut bx, coverage.clone(), statement.source_info.scope);
                bx
            }
            mir::StatementKind::Intrinsic(box NonDivergingIntrinsic::Assume(ref op)) => {
                let op_val = self.codegen_operand(&mut bx, op);
                bx.assume(op_val.immediate());
                bx
            }
            mir::StatementKind::Intrinsic(box NonDivergingIntrinsic::CopyNonOverlapping(
                mir::CopyNonOverlapping { ref count, ref src, ref dst },
            )) => {
                let dst_val = self.codegen_operand(&mut bx, dst);
                let src_val = self.codegen_operand(&mut bx, src);
                let count = self.codegen_operand(&mut bx, count).immediate();
                let pointee_layout = dst_val
                    .layout
                    .pointee_info_at(&bx, rustc_target::abi::Size::ZERO)
                    .expect("Expected pointer");
                let bytes = bx.mul(count, bx.const_usize(pointee_layout.size.bytes()));

                let align = pointee_layout.align;
                let dst = dst_val.immediate();
                let src = src_val.immediate();
                bx.memcpy(dst, align, src, align, bytes, crate::MemFlags::empty());

                //RustMeta: copy smart pointers
                if let ty::RawPtr(i) = dst_val.layout.ty.kind() {
                    if bx.tcx().contains_special_ty(i.ty){
                        let dst_segment_ptr_int = bx.ptrtoint(dst, bx.type_i64()); //TODO: need to consider cases where the dst & src may be from different
                        let src_segment_ptr_int = bx.ptrtoint(src, bx.type_i64());
                        let dst_segment = bx.and(dst_segment_ptr_int, bx.const_u64(0xFFFFFFFFFE000000));
                        let dst_offset = bx.and(dst_segment_ptr_int, bx.const_u64(0x1FFFFFF));
                        let src_offset = bx.and(src_segment_ptr_int, bx.const_u64(0x1FFFFFF));
                        let dst_segment_ptr = bx.inttoptr(dst_segment, bx.type_ptr_to(bx.type_i64()));
                        let safe_house_ptr = bx.load(bx.type_i64(), dst_segment_ptr, Align::from_bits(64).expect("align"));
                        let safe_dst = bx.or(safe_house_ptr, dst_offset);
                        let safe_src = bx.or(safe_house_ptr, src_offset);
                        let safe_src_ptr = bx.inttoptr(safe_src, bx.type_ptr_to(bx.type_i64()));
                        let safe_dst_ptr = bx.inttoptr(safe_dst, bx.type_ptr_to(bx.type_i64()));
                        bx.memcpy(safe_dst_ptr, align, safe_src_ptr, align, bytes, crate::MemFlags::empty());
                    }
                }
                bx
            }
            mir::StatementKind::FakeRead(..)
            | mir::StatementKind::Retag { .. }
            | mir::StatementKind::AscribeUserType(..)
            | mir::StatementKind::Nop => bx,
        }
    }
}
