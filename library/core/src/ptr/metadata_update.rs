/// This trait is intended for implementation by smart pointers
/// Each smart pointer whose metadata wishes to be protected should implement this trait, and define
/// a synchronization method.

/// MetaUpdate trait. The trait to be implemented by smartpointers.
/// We were using Drop + Deref with the assumption that all smart
/// pointers implement the Deref and Drop trait. But it turns out not all
/// smart pointers implement Deref and Drop. Forexam Mutex
#[unstable(feature = "metadata_update", issue = "none")]
#[allow(drop_bounds)]
pub trait MetaUpdate{
    /// synchronize the update metadata with the allocator.
    fn synchronize(&self) -> bool;
}

/// enable write access on the metadata memory region
/// is static because we will be setting access rights for the whole region
/// this actually depending on the method we choose for protection.
/// it makes more sense if we opt for MPK protection for example.
/// other methods like guard pages don't require this message.
pub fn enable_metadata_update(){}

/// disable metadata write access
/// implementation condition is same as that of enable_metadata_update
/// only makes sense depending on the method chosen for protection
pub fn disable_metadata_update(){}
