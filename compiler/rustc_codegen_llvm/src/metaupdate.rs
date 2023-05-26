use rustc_codegen_ssa::traits::BuilderMethods;
use rustc_codegen_ssa::traits::ConstMethods;
use rustc_codegen_ssa::traits::DerivedTypeMethods;
use rustc_codegen_ssa::traits::BaseTypeMethods;
use rustc_codegen_ssa::common::IntPredicate;
use rustc_target::abi::Align;
use crate::builder::Builder;
use crate::value::Value;
use crate::llvm;


pub(super) fn get_smart_pointer_shadow(
    bx: &mut Builder<'_, 'll, 'tcx>,
    val: &'ll Value
) -> &'ll Value {
    // if bx.project_smart_pointer_field(val) {

    // }

    let stack_mask: u64 = !(0x7FFFFF);
    let segment_mask: u64 = 0xFFFFFFFFFE000000;
    let lower_addr_offset: u64 = !segment_mask;

    let stack_shadow_bb = bx.append_sibling_block("shadow.maybe_stack");
    let heap_shadow_bb = bx.append_sibling_block("shadow.maybe_heap");
    let end = bx.append_sibling_block("shadow_block");

    let stack_mask_val = bx.const_u64(stack_mask);
    let segment_mask_val = bx.const_u64(segment_mask);
    let lower_addr_mask_val = bx.const_u64(lower_addr_offset);

    let addr_to_int = bx.ptrtoint(val, bx.type_i64());
    let addr_masked = bx.and(addr_to_int, stack_mask_val);
    let stack_ptr = unsafe {llvm::LLVMReadStackPtr(bx.llbb(), bx.llfn()) };
    let masked_stack_ptr = bx.and(stack_ptr, stack_mask_val);
    let xored = bx.xor(masked_stack_ptr, addr_masked);
    let icmp = bx.icmp(IntPredicate::IntEQ, xored, bx.const_u64(0));
    bx.cond_br(icmp, stack_shadow_bb, heap_shadow_bb);

    bx.switch_to_block(stack_shadow_bb); //TODO: load the shadow stack here
    let dummy_mask = bx.and(val, bx.const_u64(u64::MAX));
    let stack_shadow = bx.inttoptr(dummy_mask, bx.type_i8p());
    //TODO: remember to mask the address at the end
    bx.br(end);

    bx.switch_to_block(heap_shadow_bb);
    let segment_ptr_int_sub = bx.sub(addr_to_int, bx.const_u64(1));
    let segment_ptr_int = bx.and(segment_ptr_int_sub, segment_mask_val);
    let segment_ptr = bx.inttoptr(segment_ptr_int, bx.type_ptr_to(bx.type_i8p()));
    let heap_shadow = bx.load(bx.type_i8p(), segment_ptr, Align::from_bits(64).expect("align"));
    bx.br(end);

    bx.switch_to_block(end);
    let address = bx.phi(bx.type_i8p(), &[heap_shadow, stack_shadow], &[heap_shadow_bb, stack_shadow_bb]);
    address //TODO: bit cast to orig type, cache, we don't want to do this over and over again for the same object.
}
