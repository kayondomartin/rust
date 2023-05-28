use rustc_codegen_ssa::traits::BuilderMethods;
use rustc_codegen_ssa::traits::ConstMethods;
use rustc_codegen_ssa::traits::DerivedTypeMethods;
use rustc_codegen_ssa::traits::BaseTypeMethods;
//use rustc_codegen_ssa::common::IntPredicate;
use rustc_codegen_ssa::MemFlags;
//use rustc_data_structures::fx::FxHashMap;
use rustc_middle::ty::layout::HasTyCtxt;
use rustc_target::abi::Align;
use crate::builder::Builder;
use crate::value::Value;
//use crate::llvm;
use rustc_middle::ty::Ty;


pub(super) fn get_smart_pointer_shadow<'ll>(
    bx: &mut Builder<'_, 'll, '_>,
    val: &'ll Value
) -> &'ll Value {

    let addr_to_int = bx.ptrtoint(val, bx.type_i64());
    let addr_masked = bx.and(addr_to_int, bx.const_u64(u64::MAX)); 
    //mask this for soon comming dummy load from llvm pass. we need to maintain the performance overhead
    // putting the volatile load here may affect optimizations such as DCE before reaching LLVm pass.
    let addr = bx.inttoptr(dummy_mask, bx.type_ptr_to(bx.type_i8p()));
    bx.mark_field_projection(addr, 0); //mark this for further optimizatoin in LLVM pass.
    addr

    /*let dbg_loc = unsafe {llvm::LLVMGetCurrentDebugLocation2(bx.llbuilder)};

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
    //unsafe { llvm::LLVMSetCurrentDebugLocation2(bx.llbuilder, dbg_loc); }
    let dummy_mask = bx.and(addr_to_int, bx.const_u64(u64::MAX));
    let stack_shadow = bx.inttoptr(dummy_mask, bx.type_i8p());
    //TODO: remember to mask the address at the end
    bx.br(end);

    bx.switch_to_block(heap_shadow_bb);
    //unsafe{ llvm::LLVMSetCurrentDebugLocation2(bx.llbuilder, dbg_loc); }
    let segment_ptr_int_sub = bx.sub(addr_to_int, bx.const_u64(1));
    let segment_ptr_int = bx.and(segment_ptr_int_sub, segment_mask_val);
    let segment_ptr = bx.inttoptr(segment_ptr_int, bx.type_ptr_to(bx.type_i64()));
    let heap_shadow_ptr = bx.load(bx.type_i64(), segment_ptr, Align::from_bits(64).expect("align"));
    let addr_offset_mask = bx.and(addr_to_int, lower_addr_mask_val);
    let heap_shadow_int = bx.or(heap_shadow_ptr, addr_offset_mask);
    let mut heap_shadow = bx.inttoptr(heap_shadow_int, bx.type_i8p());
    //dummy store, need to meaure actual heap & performance overhead.
    bx.store(bx.const_int(bx.type_i8(), 1), heap_shadow, Align::from_bits(8).expect("align"));
    heap_shadow = bx.and(addr_to_int, bx.const_u64(u64::MAX));
    heap_shadow = bx.inttoptr(heap_shadow, bx.type_i8p());
    bx.br(end);

    bx.switch_to_block(end);
    unsafe { llvm::LLVMSetCurrentDebugLocation2(bx.llbuilder, dbg_loc); }
    let address = bx.phi(bx.type_i8p(), &[heap_shadow, stack_shadow], &[heap_shadow_bb, stack_shadow_bb]);
    //SHADOW_MAP.insert(val, address);

    address //TODO: bit cast to orig type, cache, we don't want to do this over and over again for the same object.
    let bitcast = bx.ptrtoint(val, bx.type_i64());
    let mask = bx.and(bitcast, bx.const_u64(u64::MAX));
    let ptr = bx.inttoptr(mask, bx.type_i8p());
    bx.mark_field_projection(ptr, 0);
    ptr*/
}


pub(super) fn copy_smart_pointers<'ll, 'tcx>(
    src: &'ll Value,
    src_ty: Ty<'tcx>,
    dst: &'ll Value,
    dst_ty: Ty<'tcx>,
    bx: &mut Builder<'_, 'll, 'tcx>,
    align: Align,
    flags: MemFlags
){
    if bx.tcx().contains_special_ty(src_ty) && bx.tcx().contains_special_ty(dst_ty) {
        let src_shadow = get_smart_pointer_shadow(bx, src);
        let dst_shadow = get_smart_pointer_shadow(bx, dst);
        bx.memcpy(dst_shadow, align, src_shadow, align, bx.const_i32(1), flags);
    } else if bx.tcx().contains_special_ty(src_ty) {
        let src_shadow = get_smart_pointer_shadow(bx, src);
        bx.memcpy(dst, align, src_shadow, align, bx.const_i32(1), flags);
    } else if bx.tcx().contains_special_ty(dst_ty) {
        let dst_shadow = get_smart_pointer_shadow(bx, dst);
        bx.memcpy(dst_shadow, align, src, align, bx.const_i32(1), flags);
    }
}