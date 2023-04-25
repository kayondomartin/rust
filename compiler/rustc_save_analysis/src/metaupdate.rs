use rustc_data_structures::fx::{FxHashSet, FxHashMap};
use rustc_hir as hir;
use std::{path::Path, io::{Write, Read}, fs::{OpenOptions, File}};
use serde::{Serialize, Deserialize};
use rustc_middle::ty::{TyCtxt, List, ParamEnv, self};
use hir::{intravisit::Visitor, def_id::{DefId, LocalDefId, LOCAL_CRATE}, Expr, ExprKind, Node};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_trait_selection::infer::InferCtxtExt;
use rustc_index::vec::Idx;


#[derive(Default)]
pub struct SpecialTypes{
    pub fields: FxHashSet<hir::HirId>,
    pub field_exprs: FxHashMap<hir::OwnerId, FxHashSet<u32>>,
}

impl Clone for SpecialTypes{
    fn clone(&self) -> Self {
        SpecialTypes { fields: self.fields.clone(), field_exprs: self.field_exprs.clone() }
    }
}

pub struct ExternStructField {
    field_hir_id: hir::HirId,    //struct Field HirId
    needs_boxed: bool,   // if this field should be boxed
    used_exprs: FxHashMap<String, FxHashMap<hir::OwnerId, FxHashSet<u32>>>
}

pub struct DumpVisitor<'tcx>{
    pub tcx: TyCtxt<'tcx>,
    pub struct_field_records: FxHashMap<String, FxHashMap<LocalDefId, FxHashMap<String, ExternStructField>>>, //LocalDefId: struct DefId,
    pub trait_id: Option<DefId>
}

#[derive(Deserialize, Serialize, Debug)]
pub struct MetaUpdateHirId{
    local_id: u32,
    def_index: usize
}

#[derive(Deserialize, Serialize, Debug)]
pub struct JsonExternStructField {
    field_owner: usize,
    field_local_idx: u32,
    should_box: bool,
    uses: FxHashMap<String, FxHashMap<usize, FxHashSet<u32>>>
}

impl ExternStructField {
    fn to_json_serializable(&self) -> JsonExternStructField {
        JsonExternStructField {
            field_owner: self.field_hir_id.owner.def_id.local_def_index.as_usize(),
            field_local_idx: self.field_hir_id.local_id.as_u32(),
            should_box: self.needs_boxed,
            uses: self.used_exprs.iter().map(|(crate_name, uses_map)|{
                (crate_name.clone(), uses_map.iter().map(|(owner, locals)|{
                    (owner.def_id.local_def_index.as_usize(), locals.iter().map(|i|*i).collect())
                }).collect())
            }).collect()
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
                    }, offsets.iter().map(|i|*i).collect())
                }).collect())
            }).collect()
        }
    }
}

#[derive(Serialize, Deserialize, Debug)]
struct JsonObject {
    data: FxHashMap<String, FxHashMap<usize, FxHashMap<String, JsonExternStructField>>> /*{
        [Crate: {
            CrateNum: u32
            structs: [
                {   struct_def_idx: u32,
                    fields: [
                        {   field_ident: String,
                            field_owner: u32,
                            field_local_idx: u32,
                            should_box: bool,
                            uses: [
                            {
                                crate: u32,
                                users: [{
                                    owner: u32,
                                    locals: [local_idx: u32]
                                }]
                            },]
                        },
                    ]
                },
            ]
            }
        ]*/
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

    /*fn special_field_exprs(&self) -> Vec<MetaUpdateHirId>{
        let mut collected = vec![];
        for (owner, locals) in self.special_field_expr_map.iter() {
            for id in locals{
                collected.push(MetaUpdateHirId{local_id: *id, def_index: owner.def_id.local_def_index.as_usize()});
            }
        }
        collected
    }*/
    // TODO: ensure the file name matches crate && file path matches current crate's root path
    // TODO: safely handle errors concerning file writing, creation and openning.
    fn save(&self){
        if !Path::new("/tmp/metaupdate").exists() {
            std::fs::create_dir_all("/tmp/metaupdate").expect("Failed to create `metaupdate` directory");
        }

        let file_path = Path::new("/tmp/metaupdate").join("special_types.json");

        let object = JsonObject {
            data: self.struct_field_records.iter().map(|(crate_name, structs)|{
                (crate_name.clone(), structs.iter().map(|(did, fields)|{
                    (did.local_def_index.as_usize(), fields.iter().map(|(ident, uses)|{
                        (String::from(ident.as_str()), uses.to_json_serializable())
                    }).collect())
                }).collect())
            }).collect(),
        };

        let val = serde_json::to_string(&object).unwrap();
        let mut file = OpenOptions::new()
                                .write(true)
                                .create(true)
                                .truncate(true)
                                .open(file_path)
                                .unwrap();
        println!("Crate: {}", self.tcx.crate_name(LOCAL_CRATE).to_string());
        file.write_all(val.as_bytes()).expect("Unable to save metaupdate results");
    }

    pub fn new(tcx: TyCtxt<'tcx>) -> Self{
        let mut this = Self{
            tcx,
            struct_field_records: FxHashMap::default(),
            trait_id: None
        };

        if Path::new("/tmp/metaupdate").exists() {
            println!("Current Directory: {}, metaupdate exists: {}", std::env::current_dir().unwrap().to_str().unwrap(), Path::new("/tmp/metaupdate").exists());
            let file_path = Path::new("/tmp/metaupdate").join("special_types.json");
            let mut buffer = String::new();
            match File::open(file_path) {
                Ok(mut file) => {
                    let _ = file.read_to_string(&mut buffer).expect("Unable to read metaupdate file");
                    let json_object: JsonObject = serde_json::from_str(& buffer).expect("Unable to parse metaupdate file to json");
                    this.struct_field_records = json_object.data.iter().map(|(krate_name, structs_map)|{
                        (krate_name.clone(),structs_map.iter().map(|(def_idx, fields)|{
                            (LocalDefId::new(*def_idx), fields.iter().map(|(s, jsf)|{
                                (s.clone(), jsf.to_extern_struct_field())
                            }).collect())
                        }).collect())
                    }).collect()
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

    pub fn add_field_def_use(&mut self, adt_def: DefId, field_hir: hir::HirId, field_ident: String, is_special: bool){
        let krate_name = self.tcx.crate_name(adt_def.krate).to_string();
        if let Some(struct_map) = self.struct_field_records.get_mut(&krate_name){
            if let Some(fields) = struct_map.get_mut(&LocalDefId{local_def_index: adt_def.index}) {
                if let Some(field) = fields.get_mut(&field_ident) {
                    if !field.needs_boxed && is_special{
                        field.needs_boxed = true;
                    }
                    if let Some(uses) = field.used_exprs.get_mut(&self.tcx.crate_name(LOCAL_CRATE).to_string()) {
                        if let Some(exprs) = uses.get_mut(&field_hir.owner){
                            exprs.insert(field_hir.local_id.as_u32());
                        }else{
                            let mut locals = FxHashSet::default();
                            locals.insert(field_hir.local_id.as_u32());
                            uses.insert(field_hir.owner, locals);
                        }
                    }else{
                        let mut uses = FxHashMap::default();
                        let mut locals = FxHashSet::default();
                        locals.insert(field_hir.local_id.as_u32());
                        uses.insert(field_hir.owner, locals);
                        field.used_exprs.insert(self.tcx.crate_name(LOCAL_CRATE).to_string(), uses);
                    }
                }
            }
        }
    }


    pub fn add_field_def(&mut self, field_def: &'tcx hir::FieldDef<'_>) -> bool{
        let parent_def_id = self.tcx.hir().get_parent_item(field_def.hir_id).def_id;
        if let Some(struct_map) = self.struct_field_records.get_mut(&self.tcx.crate_name(LOCAL_CRATE).to_string()){
            if let Some(fields) = struct_map.get_mut(&parent_def_id) {
                let is_special = self.tcx.is_special_ty(self.tcx.type_of(self.tcx.hir().local_def_id(field_def.hir_id).to_def_id()));
                if let Some(field_rec) = fields.get_mut(&field_def.ident.to_string()) {
                    if !field_rec.needs_boxed && is_special {
                        field_rec.needs_boxed = true
                    }
                }else{
                    fields.insert(field_def.ident.to_string(), ExternStructField {
                        field_hir_id: field_def.hir_id,
                        needs_boxed: is_special,
                        used_exprs: FxHashMap::default()
                    });
                }
                return true;
            }else{
                struct_map.insert(parent_def_id, FxHashMap::default());
                return false;
            }
        }else{
            self.struct_field_records.insert(self.tcx.crate_name(LOCAL_CRATE).to_string(), FxHashMap::default());
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
        let tc = self.tcx.typeck(expr.hir_id.owner.def_id);
        let ictxt = self.tcx.infer_ctxt().build();

        match expr.kind {
            ExprKind::Struct(_, fields, _) => {
                if let Some(parent_ty) = tc.node_type_opt(expr.hir_id){
                    if !self.tcx.is_special_ty(parent_ty) {
                        if let ty::Adt(adt, _) = parent_ty.kind(){
                            for (_, field) in fields.iter().enumerate() {
                                if let Some(ty) = tc.node_type_opt(field.expr.hir_id){
                                    let is_special = ictxt.type_implements_trait(self.trait_id.unwrap(), ty, List::empty(), ParamEnv::reveal_all()).may_apply() || self.tcx.is_special_ty(ty);
                                    self.add_field_def_use(adt.0.did, field.hir_id, field.ident.to_string(), is_special);
                                }
                            }
                        }
                    }
                }
            },
            ExprKind::Assign(ref lhs, ref rhs,  _) => {
                if let ExprKind::Field(ref sub_expr, ident) = lhs.kind{
                    if let Some(ty) = tc.node_type_opt(rhs.hir_id) {
                        let is_special = ictxt.type_implements_trait(self.trait_id.unwrap(), ty, List::empty(), ParamEnv::empty()).may_apply() || self.tcx.is_special_ty(ty);
                        if let Some(parent_ty) = tc.node_type_opt(sub_expr.hir_id){
                            if !self.tcx.is_special_ty(parent_ty) {
                                if let ty::Adt(adt, _) = parent_ty.kind() {
                                    self.add_field_def_use(adt.0.did, rhs.hir_id, ident.to_string(), is_special);
                                }
                            }
                        }
                    }
                }
            },
            _ => {
                if let ExprKind::Field(ref sub_expr, ident) = expr.kind {
                    let parent_id = self.tcx.hir().get_parent_node(expr.hir_id);
                    if let Some(parent_node) = self.tcx.hir().find(parent_id) {
                        match parent_node {
                            Node::Expr(ref parent_expr) => {
                                match parent_expr.kind {
                                    ExprKind::Struct(_,_,_) =>{}, //Don't care, we're handling this above
                                    ExprKind::Assign(ref lhs, ref rhs ) => {
                                        if *rhs == expr {
                                            //TODO: check if lhs is a field too, if not, add rhs to required deref's
                                        }//Don't care about RHS, we're handling it about anyway.
                                    },
                                    _ => {
                                        //TODO: add expr to those that require deref
                                    }
                                }
                            },
                            _ => {}
                        }
                    }
                }
            }
        }
        hir::intravisit::walk_expr(self, expr);
    }
}

pub fn load_metaupdate_analysis(crate_name: &str) -> SpecialTypes{
    if !Path::new("/tmp/metaupdate").exists() {
        panic!("No metaupdate folder for loading analysis results!");
    }

    println!("Crate name from load analysis: {}", crate_name);

    let file_path = Path::new("/tmp/metaupdate").join("special_types.json");
    let mut buffer = String::new();
    let mut file = File::open(file_path).expect("No metaupdate file for loading analysis results");
    let _ = file.read_to_string(&mut buffer).expect("Unable to read metaupdate file");
    let json_object: JsonObject = serde_json::from_str(& buffer).expect("Unable to parse metaupdate file to json");

    let mut special_types = SpecialTypes::default();
    if let Some(data) = json_object.data.get(&String::from(crate_name)) {
        println!("Crate name: {}", crate_name);
        for (_index, fields) in data.iter() {
            for (_field_name, field) in fields.iter(){
                if field.should_box {
                    let extern_struct_field = field.to_extern_struct_field();
                    special_types.fields.insert(extern_struct_field.field_hir_id);
                    if let Some(field_exprs) = extern_struct_field.used_exprs.get(&String::from(crate_name)) {
                            special_types.field_exprs.extend(field_exprs.into_iter().map(|(owner, locals)|{
                                (*owner, locals.clone())
                            }));
                    }
                }
            }
        }
    }
    for f in &special_types.field_exprs {
        println!("Owner: {}\nIDs:\n", f.0.def_id.local_def_index.as_usize());
        for id in f.1 {
            print!("{}, ", *id);
        }
        println!("");
    }
    /*special_types.fields = json_object.fields.iter().map(|id| id.to_hir_id()).collect();
    let mut fields_exprs: FxHashMap<hir::OwnerId, FxHashSet<u32>> = FxHashMap::default();
    for id in json_object.field_exprs {
        let hir_id = id.to_hir_id();
        if let Some(set) = fields_exprs.get_mut(&hir_id.owner){
            set.insert(hir_id.local_id.as_u32());
        }else{
            let mut set = FxHashSet::default();
            set.insert(hir_id.local_id.as_u32());
            fields_exprs.insert(hir_id.owner, set);
        }
    }
    special_types.field_exprs = fields_exprs.clone();*/
    special_types
}
