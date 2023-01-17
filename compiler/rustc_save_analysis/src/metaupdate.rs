use rustc_data_structures::fx::FxHashSet;
use rustc_hir as hir;
use std::{path::Path, io::Write};
use serde::{Serialize, Deserialize};
use rustc_middle::ty::{TyCtxt, List, ParamEnv};
use hir::{intravisit::Visitor, def_id::DefId, Expr, ExprKind};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_trait_selection::infer::InferCtxtExt;

#[derive(Default)]
pub struct SpecialTypes{
    types: FxHashSet<hir::HirId>,
    fields: FxHashSet<hir::HirId>
}

pub struct DumpVisitor<'tcx>{
    tcx: TyCtxt<'tcx>,
    special_types: SpecialTypes,
    trait_id: Option<DefId>
}

#[derive(Deserialize, Serialize, Debug)]
pub struct MetaUpdateHirId{
    local_id: u32,
    def_index: usize
}

impl MetaUpdateHirId{
    fn new(hir_id: hir::HirId) -> Self{
        Self{
            local_id: hir_id.local_id.as_u32(),
            def_index: hir_id.owner.def_id.local_def_index.as_usize()
        }
    }
    
    /*fn to_hir_id(&self) -> hir::HirId{
        hir::HirId {
            owner: hir::OwnerId{
                def_id: LocalDefId::new(self.def_index)
            },
            local_id: hir::ItemLocalId::from(self.local_id)
        }
    }*/
}

impl SpecialTypes {
    fn types(&self) -> Vec<MetaUpdateHirId> {
        self.types.iter().map(|id| MetaUpdateHirId::new(*id)).collect()
    }
    
    fn fields(&self) -> Vec<MetaUpdateHirId> {
        self.fields.iter().map(|id| MetaUpdateHirId::new(*id)).collect()
    }
}

impl<'tcx> DumpVisitor<'tcx> {
    // TODO: ensure the file name matches crate && file path matches current crate's root path
    fn save(&self){
        if !Path::new("target/metaupdate").exists() {
            std::fs::create_dir_all("target/metaupdate").expect("Failed to create `metaupdate` directory");
        }
        
        let file_path = Path::new("target/metaupdate").join("special_types.json");
        
        if !file_path.exists() {
            let _ = std::fs::File::create(&file_path).expect("Failed to create special_types.json file");
        }
        
        #[derive(Serialize, Deserialize, Debug)]
        struct JsonObject {
            types: Vec<MetaUpdateHirId>,
            fields: Vec<MetaUpdateHirId>,
        }
        
        let object = JsonObject {
            types: self.special_types.types(),
            fields: self.special_types.fields()
        };
        
        let val = serde_json::to_string(&object).unwrap();
        let mut file = std::fs::File::open(&file_path).unwrap();
        let _ = file.write_all(val.as_bytes());
    }
    
    pub fn new(tcx: TyCtxt<'tcx>) -> Self{
        let mut this = Self{
            tcx,
            special_types: SpecialTypes::default(),
            trait_id: None
        };
        
        for trait_id in tcx.all_traits(){
            if tcx.item_name(trait_id).as_str() == "MetaUpdate" {
                this.trait_id = Some(trait_id);
                break;
            }
        }
        
        this
    }
    
    pub fn dump_metaupdate_special_types(&mut self){
        self.tcx.hir().visit_all_item_likes_in_crate(self);
        self.save();
    }
}

impl<'tcx> Visitor<'tcx> for DumpVisitor<'tcx>{
    type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;
    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }
    
    fn visit_expr(&mut self, expr: &'tcx Expr<'_>){
        if self.trait_id.is_none() { return; }
        
        let tc = self.tcx.typeck(expr.hir_id.owner.def_id);
        let ictxt = self.tcx.infer_ctxt().build();
        match expr.kind {
            ExprKind::Struct(_, fields, _) => {  
                for field in fields {
                    if let Some(ty) = tc.node_type_opt(field.expr.hir_id) {
                        if ictxt.type_implements_trait(self.trait_id.unwrap(), ty, List::empty(), ParamEnv::empty()).may_apply(){
                            self.special_types.fields.insert(field.expr.hir_id);
                        }
                    }
                }
            },
            ExprKind::Assign(ref lhs, ref rhs,  _) => {
                if let ExprKind::Field(..) = lhs.kind{
                    if let Some(ty) = tc.node_type_opt(rhs.hir_id) {
                        if ictxt.type_implements_trait(self.trait_id.unwrap(), ty, List::empty(), ParamEnv::empty()).may_apply(){
                            self.special_types.fields.insert(rhs.hir_id);
                        }
                    }
                }
            },
            _ => {}
        }
        hir::intravisit::walk_expr(self, expr);
    }
}