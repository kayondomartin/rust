use rustc_data_structures::fx::{FxHashSet, FxHashMap};
use rustc_hir as hir;
use rustc_span::def_id;
use std::{path::Path, io::{Write, Read}, fs::{OpenOptions, File}, collections::hash_map::Entry};
use serde::{Serialize, Deserialize};
use rustc_middle::{ty::{TyCtxt, List, ParamEnv, self}};
use hir::{intravisit::Visitor, def_id::{DefId, LocalDefId, LOCAL_CRATE}, Expr, ExprKind, Node};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_trait_selection::infer::InferCtxtExt;
use rustc_index::vec::Idx;


#[derive(Default)]
pub struct SpecialTypes{
    pub fields: FxHashSet<hir::HirId>,
    pub field_exprs: FxHashMap<hir::OwnerId, FxHashSet<u32>>,
    pub unbox_exprs: FxHashMap<hir::OwnerId, FxHashSet<u32>>
}

impl Clone for SpecialTypes{
    fn clone(&self) -> Self {
        SpecialTypes { fields: self.fields.clone(), field_exprs: self.field_exprs.clone(), unbox_exprs: self.unbox_exprs.clone() }
    }
}


enum FieldExprAction {
    NeedsBox,
    DontTouch
}

pub struct ExternStructField {
    field_hir_id: hir::HirId,    //struct Field HirId
    needs_boxed: bool,   // if this field should be boxed
    used_exprs: FxHashMap<String, FxHashMap<hir::OwnerId, FxHashMap<u32, Option<FieldExprAction>>>>
}

pub struct DumpVisitor<'tcx>{
    pub tcx: TyCtxt<'tcx>,
    pub used_field_exprs: FxHashMap<String, FxHashMap<String, FxHashMap<LocalDefId, FxHashMap<String, FxHashSet<hir::HirId>>>>>, // field_def expressions in a given crate
    pub need_box_exprs: FxHashMap<String, FxHashSet<hir::HirId>>,
    pub unbox_except_exprs: FxHashMap<String, FxHashSet<hir::HirId>>,
    pub field_defs: FxHashMap<String, FxHashMap<LocalDefId, FxHashMap<String, bool>>>,
    pub trait_id: Option<DefId>
}

#[derive(Deserialize, Serialize, Debug, Clone, Copy)]
pub struct MetaUpdateHirId{
    local_id: u32,
    def_index: usize
}

#[derive(Deserialize, Serialize, Debug)]
pub struct JsonExternStructField {
    field_owner: usize,
    field_local_idx: u32,
    should_box: bool,
    uses: FxHashMap<String, FxHashMap<usize, FxHashMap<u32, u8>>>, // 0: no action needed, 1: should box, 2: Don't touch
}

impl ExternStructField {
    fn to_json_serializable(&self) -> JsonExternStructField {
        JsonExternStructField {
            field_owner: self.field_hir_id.owner.def_id.local_def_index.as_usize(),
            field_local_idx: self.field_hir_id.local_id.as_u32(),
            should_box: self.needs_boxed,
            uses: self.used_exprs.iter().map(|(crate_name, uses_map)|{
                (crate_name.clone(), uses_map.iter().map(|(owner, locals)|{
                    (owner.def_id.local_def_index.as_usize(), locals.iter().map(|(i, actions)| {
                        (*i, match actions {
                                Some(action) => {
                                    match action {
                                        FieldExprAction::NeedsBox => {1},
                                        FieldExprAction::DontTouch => {2}
                                    }
                                },
                                _ => 0})
                    }).collect())
                }).collect())
            }).collect(),
        }
    }
}

impl JsonExternStructField {
    fn to_extern_struct_field(&self) -> ExternStructField {
        ExternStructField {
            field_hir_id: hir::HirId {owner: hir::OwnerId{def_id: LocalDefId::new(self.field_owner)}, local_id: hir::ItemLocalId::from(self.field_local_idx)},
            needs_boxed: self.should_box,
            used_exprs: self.uses.iter().map(|(crate_name, hir_ids)|{
                (crate_name.clone(), hir_ids.iter().map(|(local_index, offsets)|{
                    (hir::OwnerId {
                        def_id: LocalDefId::new(*local_index),
                    }, offsets.iter().map(|(i, j)|{
                        (*i, match j {
                            1 => Some(FieldExprAction::NeedsBox),
                            2 => Some(FieldExprAction::DontTouch),
                            _ => None
                        })
                    }).collect())
                }).collect())
            }).collect(),
        }
    }
}

#[derive(Serialize, Deserialize, Debug)]
struct JsonObject {
    used_field_exprs: FxHashMap<String, FxHashMap<String, FxHashMap<usize, FxHashMap<String, Vec<MetaUpdateHirId>>>>>,
    need_box_exprs: FxHashMap<String, Vec<MetaUpdateHirId>>,
    unbox_except_exprs: FxHashMap<String, Vec<MetaUpdateHirId>>,
    field_defs: FxHashMap<String, FxHashMap<usize, FxHashMap<String, bool>>>
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
    pub fn fields(&self) -> Vec<MetaUpdateHirId> {
        self.fields.iter().map(|id| MetaUpdateHirId::new(*id)).collect()
    }
   /*
    pub fn field_exprs(&self) -> Vec<MetaUpdateHirId> {
        self.field_exprs.iter().map(|id| MetaUpdateHirId::new(*id)).collect()
    }*/
}


impl<'tcx> DumpVisitor<'tcx> {

    fn data_to_json(&self) -> JsonObject {
        let object = JsonObject {
            used_field_exprs: self.used_field_exprs.iter().map(|(local_krate, uses)|{
                (local_krate.clone(), uses.iter().map(|(krate, struct_def)|{
                    (krate.clone(), struct_def.iter().map(|(def_id, fields)|{
                        (def_id.as_usize(), fields.iter().map(|(field, use_hir_ids)|{
                            (field.clone(), use_hir_ids.iter().map(|id| MetaUpdateHirId::new(*id)).collect())
                        }).collect())
                    }).collect())
                }).collect())
            }).collect(),
            need_box_exprs: self.need_box_exprs.iter().map(|(krate, ids)|{
                (krate.clone(), ids.iter().map(|id|MetaUpdateHirId::new(*id)).collect())
            }).collect(),
            unbox_except_exprs: self.unbox_except_exprs.iter().map(|(krate, ids)|{
                (krate.clone(), ids.iter().map(|(id)| MetaUpdateHirId::new(*id)).collect())
            }).collect(),
            field_defs: self.field_defs.iter().map(|(krate, structs)|{
                (krate.clone(), structs.iter().map(|(struct_id, field_uses)|{
                    (struct_id.as_usize(), field_uses.iter().map(|(field, should_box)|{
                        (field.clone(), *should_box)
                    }).collect())
                }).collect())
            }).collect()
        };
        object
    }

    fn load_data_from_json_object(&mut self, object: &JsonObject) {
        self.need_box_exprs = object.need_box_exprs.iter().map(|(krate, ids)|{
            (krate.clone(), ids.iter().map(|id|id.to_hir_id()).collect())
        }).collect();
        self.unbox_except_exprs = object.unbox_except_exprs.iter().map(|(krate, ids)|{
            (krate.clone(), ids.iter().map(|id|id.to_hir_id()).collect())
        }).collect();
        self.field_defs = object.field_defs.iter().map(|(krate, structs)|{
            (krate.clone(), structs.iter().map(|(struct_def_id, fields)|{
                (LocalDefId::new(*def_id), fields.iter().map(|(field_ident, should_box)|{
                    (field_ident.clone(), *should_box)
                }).collect())
            }).collect())
        }).collect();
        self.used_field_exprs  = object.used_field_exprs.iter().map(|(krate, uses)|{
            (krate.clone(), uses.iter().map(|(def_krate, structs)|{
                (def_krate.clone(), structs.iter().map(|(def_id, fields_uses)|{
                    (LocalDefId::new(*def_id), fields_uses.iter().map(|(field_name, use_ids)|{
                        (field_name.clone(), use_ids.iter().map(|(id)|id.to_hir_id()))
                    }).collect())
                }).collect())
            }).collect())
        }).collect();
    }

    fn save(&self){
        if !Path::new("/tmp/metaupdate").exists() {
            std::fs::create_dir_all("/tmp/metaupdate").expect("Failed to create `metaupdate` directory");
        }

        let file_path = Path::new("/tmp/metaupdate").join("special_types.json");

        let object = self.data_to_json();

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
            need_box_exprs: FxHashMap::default(),
            unbox_except_exprs: FxHashMap::default(),
            used_field_exprs: FxHashMap::default(),
            field_defs: FxHashMap::default(),
            trait_id: None
        };

        if Path::new("/tmp/metaupdate").exists() {
            let file_path = Path::new("/tmp/metaupdate").join("special_types.json");
            let mut buffer = String::new();
            match File::open(file_path) {
                Ok(mut file) => {
                    let _ = file.read_to_string(&mut buffer).expect("Unable to read metaupdate file");
                    let json_object: JsonObject = serde_json::from_str(& buffer).expect("Unable to parse metaupdate file to json");
                    this.load_from_json_object(&json_object);
                }
                _ => {}
            }
        }

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

    pub fn mark_require_unbox_def(&mut self, adt_def: DefId,  field_hir: hir::HirId, field_ident: String, unboxable: bool){
        let krate_name = self.tcx.crate_name(adt_def.krate).to_string();
        let local_krate_name = self.tcx.crate_name(LOCAL_CRATE).to_string();
        let struct_def_id = LocalDefId{local_def_index: adt_def.index};
        if let Some(struct_map) = self.field_defs.get_mut(&krate_name){
            if let Some(fields) = struct_map.get_mut(&LocalDefId{local_def_index: adt_def.index}) {
               match fields.entry(&field_ident) {
                    Entry::Occupied(_) => {
                        self.used_field_exprs.entry(&local_krate_name)
                                            .or_insert(FxHashMap::default()).entry(&krate_name)
                                            .or_insert(FxHashMap::default()).entry(&struct_def_id)
                                            .or_insert(FxHashMap::default()).entry(&field_indent)
                                            .or_insert(FxHashSet::default()).insert(field_hir);
                        if !unboxable {
                            self.unbox_except_exprs.entry(&local_krate_name)
                                .or_insert(FxHashSet::default()).insert(field_hir);
                        }
                    },

                    Entry::Vacant(_) => {}
               }
            }
        }
    }

    pub fn add_box_require_def_use(&mut self, adt_def: DefId, field_hir: hir::HirId, field_ident: String, is_special: bool){
        let krate_name = self.tcx.crate_name(adt_def.krate).to_string();
        let local_krate_name = self.tcx.crate_name(LOCAL_CRATE).to_string();
        let struct_def_id = LocalDefId {local_def_index: adt_def.index};
        if let Some(struct_map) = self.field_defs.get_mut(&krate_name){
            if let Some(fields) = struct_map.get_mut(&struct_def_id) {
                if let Some(field) = fields.get_mut(&field_ident) {
                    if !field && is_special{
                        *field = true;
                    }

                    self.used_field_exprs.entry(&local_krate_name)
                    .or_insert_with(||{
                        FxHashMap::default()
                    }).entry(&krate_name)
                    .or_insert_with(FxHashMap::default()).entry(&struct_def_id)
                    .or_insert_with(FxHashMap::default()).entry(&field_ident).or_insert(FxHashSe
                    ::default()).insert(field_hir);

                    self.need_box_exprs.entry(&local_krate_name)
                    .or_insert_with(||{
                        FxHashSet::default()
                    }).insert(field_hir);
                }
            }
        }
    }


    pub fn add_field_def(&mut self, field_def: &'tcx hir::FieldDef<'_>) -> bool{
        let parent_def_id = self.tcx.hir().get_parent_item(field_def.hir_id).def_id;
        if let Some(struct_map) = self.field_defs.get_mut(&self.tcx.crate_name(LOCAL_CRATE).to_string()){
            if let Some(fields) = struct_map.get_mut(&parent_def_id) {
                let is_special = self.tcx.is_special_ty(self.tcx.type_of(self.tcx.hir().local_def_id(field_def.hir_id).to_def_id()));
                if let Some(field_rec) = fields.get_mut(&field_def.ident.to_string()) {
                    if !field_rec && is_special {
                        *field_rec = true
                    }
                }else{
                    fields.insert(field_def.ident.to_string(), is_special);
                }
                return true;
            }else{
                struct_map.insert(parent_def_id, FxHashMap::default());
                return false;
            }
        }else{
            self.field_defs.insert(self.tcx.crate_name(LOCAL_CRATE).to_string(), FxHashMap::default());
            return false;
        }
    }
}

impl<'tcx> Visitor<'tcx> for DumpVisitor<'tcx>{
    type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;
    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_field_def(&mut self, field_def: &'tcx hir::FieldDef<'_>) {
        while !self.add_field_def(field_def){
            self.add_field_def(field_def);
        }
        hir::intravisit::walk_field_def(self, field_def);
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'_>){
        if self.trait_id.is_none() { return; }
        match expr.kind {
            ExprKind::Struct(_, fields, _) => {
                let tc = self.tcx.typeck(expr.hir_id.owner.def_id);
                let ictxt = self.tcx.infer_ctxt().build();
                if let Some(parent_ty) = tc.node_type_opt(expr.hir_id){
                    if !self.tcx.is_special_ty(parent_ty) {
                        if let ty::Adt(adt, _) = parent_ty.kind(){
                            for (_, field) in fields.iter().enumerate() {
                                if let Some(ty) = tc.node_type_opt(field.expr.hir_id){
                                    let is_special = ictxt.type_implements_trait(self.trait_id.unwrap(), ty, List::empty(), ParamEnv::reveal_all()).may_apply() || self.tcx.is_special_ty(ty);
                                    self.add_box_require_def_use(adt.0.did, field.hir_id, field.ident.to_string(), is_special);
                                }
                            }
                        }
                    }
                }
            },
            ExprKind::Assign(ref lhs, ref rhs,  _) => {
                let tc = self.tcx.typeck(expr.hir_id.owner.def_id);
                let ictxt = self.tcx.infer_ctxt().build();
                if let ExprKind::Field(ref sub_expr, ident) = lhs.kind{
                    if let Some(ty) = tc.node_type_opt(rhs.hir_id) {
                        let is_special = ictxt.type_implements_trait(self.trait_id.unwrap(), ty, List::empty(), ParamEnv::empty()).may_apply() || self.tcx.is_special_ty(ty);
                        if let Some(parent_ty) = tc.node_type_opt(sub_expr.hir_id){
                            if !self.tcx.is_special_ty(parent_ty) {
                                if let ty::Adt(adt, _) = parent_ty.kind() {
                                    self.add_box_require_def_use(adt.0.did, lhs.hir_id, ident.to_string(), is_special);
                                }
                            }
                        }
                    }
                }
            }, //OPTION 2: just load everything
            ExprKind::Field(ref field, ident) => {
                let tc  = self.tcx.typeck(expr.hir_id.owner.def_id);
                let _ictxt = self.tcx.infer_ctxt().build();
                if let Some(parent_ty) = tc.node_type_opt(field.hir_id) {
                    if let ty::Adt(adt, _) = parent_ty.kind() {
                        let parent_expr_id = self.tcx.hir().get_parent_node(expr.hir_id);
                        let parent_expr_node = self.tcx.hir().get(parent_expr_id);
                        let mut unboxable = true;

                        if !self.tcx.is_special_ty(parent_ty) {
                            match parent_expr_node {
                                Node::Expr(parent_expr) => {
                                    match parent_expr.kind {
                                        ExprKind::Assign(_, _, _ ) |
                                        ExprKind::Struct(_, _, _) => {unboxable = false;},
                                        _ => {}
                                    }
                                },
                                _ => {}
                            }
                        }

                        self.mark_require_unbox_def(adt.0.did, expr.hir_id, ident.to_string(), unboxable);
                    }
                }
            },

            _ => {}
        }
        hir::intravisit::walk_expr(self, expr);
    }
}

pub fn load_metaupdate_analysis(crate_name: &str) -> SpecialTypes{
    if !Path::new("/tmp/metaupdate").exists() {
        panic!("No metaupdate folder for loading analysis results!");
    }

    let file_path = Path::new("/tmp/metaupdate").join("special_types.json");
    let mut buffer = String::new();
    let mut file = File::open(file_path).expect("No metaupdate file for loading analysis results");
    let _ = file.read_to_string(&mut buffer).expect("Unable to read metaupdate file");
    let json_object: JsonObject = serde_json::from_str(& buffer).expect("Unable to parse metaupdate file to json");

    let mut special_types = SpecialTypes::default();
    let mut should_box = json_object.field_defs.clone();
    for (_, structs) in should_box.iter_mut(){
        structs.retain(|_, usage|{
            usage.retain(|fname, should_box| *should_box);
            !usage.is_empty()
        })
    }
    let mut used_exprs = json_object.used_field_exprs.clone().get_mut(&String::from(crate_name)).unwrap_or_default();
    let mut expr_per_owner = used_exprs.iter().map(|(krate, structs)|{
        (krate.clone(), structs.iter().map(|(def_id, uses){
            (*def_id, uses.iter().map(|(field_name, hir_ids)|{
                let mut hir_id_map = FxHashMap::default();
                for id in hir_ids.iter() {
                    hir_id_map.entry(id.def_index).or_insert(Vec::new()).push(id.local_id);
                }
                (field_name.clone(), hir_ids.iter().map(|id|))
            }))
        }))
    }).collect();

    special_types

}
