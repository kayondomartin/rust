I have to add a field to GlobalCtxt... but how do I init/modify a field of GlobalCtxt?

Let's look at how they're implemented

ex: selection_cache
-> SelectionContext has a field infcx, whose type is InferCtxt, which has a field tcx
-> a function directly accesses the tcx
-> the function is `insert_candidate_cache`
  -> what's shocking is that `.insert` works on `&self`, not `&mut self`
-> the function is called by `candidate_from_obligation` (only one callsite)
-> `candidate_from_obligation` is called by `select_from_obligation` and `evaluate_stack`
-> ... they go to `evaluate_root_obligation` ... which finally arrives at `evaluate_obligation`, which is a query

okay... a query modifies TyCtxt, ... but is that safe? How do I modify the context safely?

`lower_to_hir` is a provider of query: `hir_crate`
`hir_crate` is used a lot: many other queries that are related to hirs call hir_crate, ...

def_id_to_node_id of ResolverAstLowering

query `resolver_for_lowering` returns a resolver, but it's unavailable after `lower_to_hir`

GlobalCtxt has the table: LocalDefId -> NodeId
-> the table must be initialized inside `lower_to_hir`

query: DefId -> NodeId
(HirId -> OwnerId -> DefId is always available, without queries)

---

change plan: I have to update `def_id_to_node_id` of `GlobalCtxt` via `&TyCtxt`