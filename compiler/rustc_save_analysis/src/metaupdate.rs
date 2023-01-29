use rustc_data_structures::fx::{FxHashSet, FxHashMap};
use rustc_hir as hir;
use std::{path::Path, io::{Write, Read}, fs::{OpenOptions, File}};
use serde::{Serialize, Deserialize};
use rustc_middle::ty::{TyCtxt, List, ParamEnv, TyKind};
use hir::{intravisit::Visitor, def_id::{DefId, LocalDefId}, Expr, ExprKind, OwnerId, FieldDef};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_trait_selection::infer::InferCtxtExt;
use rustc_index::vec::Idx;

#[derive(Default)]
pub struct SpecialTypes{
    pub types: FxHashSet<hir::HirId>,
    pub fields: FxHashSet<hir::HirId>,
}

impl Clone for SpecialTypes{
    fn clone(&self) -> Self {
        SpecialTypes { types: self.types.clone(), fields: self.fields.clone() }
    }
}

pub struct DumpVisitor<'tcx>{
    pub tcx: TyCtxt<'tcx>,
    pub special_types: FxHashSet<hir::HirId>,
    pub special_fields: FxHashSet<hir::HirId>,
    pub special_generics: FxHashSet<hir::HirId>,
    pub special_generic_impls: FxHashSet<hir::HirId>,
    pub special_field_map: FxHashMap<OwnerId, Vec<u32>>,
    pub trait_id: Option<DefId>
}

#[derive(Deserialize, Serialize, Debug)]
pub struct MetaUpdateHirId{
    local_id: u32,
    def_index: usize
}

#[derive(Serialize, Deserialize, Debug)]
struct JsonObject {
    types: Vec<MetaUpdateHirId>,
    fields: Vec<MetaUpdateHirId>,
}

impl MetaUpdateHirId{
    pub fn new(hir_id: hir::HirId) -> Self{
        Self{
            local_id: hir_id.local_id.as_u32(),
            def_index: hir_id.owner.def_id.local_def_index.as_usize()
        }
    }
    
    pub fn to_hir_id(&self) -> hir::HirId{
        hir::HirId {
            owner: hir::OwnerId{
                def_id: LocalDefId::new(self.def_index)
            },
            local_id: hir::ItemLocalId::from(self.local_id)
        }
    }
}

impl SpecialTypes {
    pub fn types(&self) -> Vec<MetaUpdateHirId> {
        self.types.iter().map(|id| MetaUpdateHirId::new(*id)).collect()
    }
    
    pub fn fields(&self) -> Vec<MetaUpdateHirId> {
        self.fields.iter().map(|id| MetaUpdateHirId::new(*id)).collect()
    }
}

impl<'tcx> DumpVisitor<'tcx> {
    
    fn special_fields(&self) -> Vec<MetaUpdateHirId>{
        let mut collected = vec![];
        for (owner, locals) in self.special_field_map.iter() {
            let mut locals = locals.clone();
            locals.sort();
            for id in locals{
                collected.push(MetaUpdateHirId{local_id: id, def_index: owner.def_id.local_def_index.as_usize()});
            }
        }
        collected
    }
    // TODO: ensure the file name matches crate && file path matches current crate's root path
    // TODO: safely handle errors concerning file writing, creation and openning.
    fn save(&self){
        if !Path::new("target/metaupdate").exists() {
            std::fs::create_dir_all("target/metaupdate").expect("Failed to create `metaupdate` directory");
        }
        
        let file_path = Path::new("target/metaupdate").join("special_types.json");
        
        let object = JsonObject {
            types: self.special_types.iter().map(|id| MetaUpdateHirId::new(*id)).collect(),
            fields: self.special_fields()
        };
        
        let val = serde_json::to_string(&object).unwrap();
        let mut file = OpenOptions::new()
                                .write(true)
                                .create(true)
                                .truncate(true)
                                .open(file_path)
                                .unwrap();
        file.write_all(val.as_bytes()).expect("Unable to save metaupdate results");
    }
    
    pub fn new(tcx: TyCtxt<'tcx>) -> Self{
        let mut this = Self{
            tcx,
            special_types: FxHashSet::default(),
            special_fields: FxHashSet::default(),
            special_field_map: FxHashMap::default(),
            trait_id: None
        };
        
        for trait_id in tcx.all_traits(){
            if tcx.item_name(trait_id).as_str() == "MetaUpdate" {
                this.trait_id = Some(trait_id);
                tcx.all_impls(trait_id).for_each(|impl_id|{
                    if let Some(trait_ref) = tcx.impl_trait_ref(impl_id) {
                        if let TyKind::Adt(adt,_ ) = trait_ref.self_ty().kind {
                            let def_id = adt.0.did.expect_local();
                            let hir_id = tcx.hir().local_def_id_to_hir_id(def_id);
                            this.special_types.insert(hir_id);
                        }
                    }
                });
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
    
    fn visit_field_def(&mut self, field_def: &'tcx hir::FieldDef<'_>) {
        if self.tcx.is_special_ty(self.tcx.type_of(self.tcx.hir().local_def_id(field_def.hir_id).to_def_id())){
            self.special_fields.insert(field_def.hir_id);
        }
        hir::intravisit::walk_field_def(self, field_def);
    }
    
    fn visit_expr(&mut self, expr: &'tcx Expr<'_>){
        if self.trait_id.is_none() { return; }
        
        match expr.kind {
            ExprKind::Struct(_, fields, _) => {  
                let tc = self.tcx.typeck(expr.hir_id.owner.def_id);
                let ictxt = self.tcx.infer_ctxt().build();
                for field in fields {
                    if let Some(ty) = tc.node_type_opt(field.expr.hir_id) {
                        if ictxt.type_implements_trait(self.trait_id.unwrap(), ty, List::empty(), ParamEnv::empty()).may_apply() || self.tcx.is_special_ty(ty) {
                            if let Some(vec) = self.special_field_map.get_mut(&field.hir_id.owner){
                                vec.push(field.hir_id.local_id.as_u32());
                            }else{
                                self.special_field_map.insert(field.hir_id.owner, vec![field.hir_id.local_id.as_u32()]);
                            }
                        }
                    }
                }
            },
            ExprKind::Assign(ref lhs, ref rhs,  _) => {
                let tc = self.tcx.typeck(expr.hir_id.owner.def_id);
                let ictxt = self.tcx.infer_ctxt().build();
                if let ExprKind::Field(..) = lhs.kind{
                    if let Some(ty) = tc.node_type_opt(rhs.hir_id) {
                        if ictxt.type_implements_trait(self.trait_id.unwrap(), ty, List::empty(), ParamEnv::empty()).may_apply() || self.tcx.is_special_ty(ty){
                            if let Some(vec) = self.special_field_map.get_mut(&rhs.hir_id.owner){
                                vec.push(rhs.hir_id.local_id.as_u32());
                            }else{
                                self.special_field_map.insert(rhs.hir_id.owner, vec![rhs.hir_id.local_id.as_u32()]);
                            }
                        }
                    }
                }
            },
            _ => {}
        }
        hir::intravisit::walk_expr(self, expr);
    }
}

pub fn load_metaupdate_analysis() -> SpecialTypes{
    if !Path::new("target/metaupdate").exists() {
        panic!("No metaupdate folder for loading analysis results!");
    }
    
    let file_path = Path::new("target/metaupdate").join("special_types.json");
    let mut buffer = String::new();
    let mut file = File::open(file_path).expect("No metaupdate file for loading analysis results");
    let _ = file.read_to_string(&mut buffer).expect("Unable to read metaupdate file");
    let json_object: JsonObject = serde_json::from_str(& buffer).expect("Unable to parse metaupdate file to json");
    
    let mut special_types = SpecialTypes::default();
    special_types.types = json_object.types.iter().map(|id| id.to_hir_id()).collect();
    special_types.fields = json_object.fields.iter().map(|id| id.to_hir_id()).collect();
    special_types
}