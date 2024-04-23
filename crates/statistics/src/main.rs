use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::PathBuf;
use std::cell::RefCell;
use std::error::Error;
use std::ops::Deref;
use std::rc::Rc;
use std::sync::{Arc, Mutex, MutexGuard};
use ide::{Analysis, StructureNode, StructureNodeKind, SymbolKind};
use clap::{
    Command, arg, value_parser
};
use regex::Regex;
use syntax::TextSize;
use toml::Table;


enum RustType {
    Struct,
    Function,
    Field,
    Static,
    Impl,
}

struct Context {
    path: PathBuf,
    raw: Vec<StructureNode>,
    structs: BTreeMap<usize, Arc<Mutex<RustStruct>>>,
    functions: BTreeMap<usize, Arc<RustFunction>>,
    statics: BTreeMap<usize, Arc<RustStatic>>,
    impls: BTreeMap<usize, Arc<RustImpl>>,
    orphan_fields: BTreeMap<usize, Arc<RustField>>,
}

impl Context {
    fn new(path: &PathBuf) -> Self {
        Context {
            path: path.clone(),
            raw: Vec::new(),
            structs: BTreeMap::new(),
            functions: BTreeMap::new(),
            statics: BTreeMap::new(),
            impls: BTreeMap::new(),
            orphan_fields: BTreeMap::new(),
        }
    }

    fn load(&mut self, nodes: Vec<StructureNode>) {
        self.raw = nodes;
    }

    fn reset(&mut self) {
        self.raw.clear();
        self.structs.clear();
        self.functions.clear();
        self.statics.clear();
        self.impls.clear();
        self.orphan_fields.clear();
    }

    fn insert(&mut self, index: usize, node: &StructureNode) {
        match node.kind {
            StructureNodeKind::SymbolKind(kind) => match kind {
                SymbolKind::Struct => {
                    self.structs.insert(index, Arc::new(Mutex::new(
                        <RustStruct as FromContext<StructureNode>>::from(node, self))));
                }
                SymbolKind::Trait => {
                    self.structs.insert(index, Arc::new(Mutex::new(
                        <RustStruct as FromContext<StructureNode>>::from(node, self))));
                }
                SymbolKind::Function => {
                    let f = Arc::new(
                        <RustFunction as FromContext<StructureNode>>::from(node, self));
                    self.functions.insert(index, f);
                }
                SymbolKind::Method => {
                    let f = Arc::new(
                        <RustFunction as FromContext<StructureNode>>::from(node, self));
                    if let Some(st) = f.deref().structure.clone() {
                        st.lock().as_mut().unwrap().functions.push(f.clone());
                    }
                    self.functions.insert(index, f);
                }
                SymbolKind::Field => {
                    let field = Arc::new(
                        <RustField as FromContext<StructureNode>>::from(node, self));
                    if let Some(st) = field.deref().structure.clone() {
                        st.lock().as_mut().unwrap().fields.push(field);
                    } else {
                        self.orphan_fields.insert(index, field);
                    }
                }
                SymbolKind::Static => {
                    self.statics.insert(index, Arc::new(
                        <RustStatic as FromContext<StructureNode>>::from(node, self)));
                }
                SymbolKind::Impl => {
                    self.impls.insert(index, Arc::new(
                        <RustImpl as FromContext<StructureNode>>::from(node, self)));
                }
                _ => {}
            }
            _ => {}
        }
    }

    fn parse_pass(&mut self, filter: &BTreeSet<SymbolKind>) {
        let mut nodes: Vec<(usize, StructureNode)> = Vec::new();
        for (i, node) in self.raw.iter().enumerate() {
            let kind = match &node.kind {
                StructureNodeKind::SymbolKind(k) => k,
                _ => continue,
            };
            if filter.contains(kind) {
                nodes.push((i, node.clone()));
            }
        }

        for (i, node) in nodes {
            log::trace!("Node: {:?}", node);
            self.insert(i, &node);
        }
    }

    fn parse(&mut self) {
        let passes = vec![
            BTreeSet::from([SymbolKind::Struct, SymbolKind::Trait]),
            BTreeSet::from([SymbolKind::Impl]),
            BTreeSet::from([SymbolKind::Field, SymbolKind::Function, SymbolKind::Method]),
            BTreeSet::from([SymbolKind::Static]),
        ];
        for (i, pass) in passes.iter().enumerate() {
            self.parse_pass(pass);
            log::trace!("\n\n\nPass {}\n{}", i, self.format());
        }
    }

    fn format_static(&self) -> String {
        let mut out = String::new();
        let path = self.path.to_str().unwrap();
        for (i, (_, s)) in self.statics.iter().enumerate() {
            out.push_str(&format!("{: <16} | {: <4} | {: <16} | {: <80}\n", path, i, s.node.name, s.def));
        }
        out
    }

    fn format_structs(&self) -> String {
        let mut out = String::new();
        let path = self.path.to_str().unwrap();
        for (i, (_, s)) in self.structs.iter().enumerate() {
            let st = s.lock().unwrap();
            out.push_str(&format!("{: <16} |  {: <4} {: <16}{{}}\n", path, i, st.node.name));
            for f in st.fields.iter() {
                out.push_str(&format!("  - {: <16}: {: <80}\n", f.node.name, f.def));
            }
        }
        out
    }

    fn format_functions(&self) -> String {
        let mut out = String::new();
        let path = self.path.to_str().unwrap();
        for (i, (_, f)) in self.functions.iter().enumerate() {
            let tokens = format!("{:?}", f.tokens);
            out.push_str(&format!("{: <16} | {: <4} | {: >6} | ", path, i, tokens));
            if let Some(st) = f.structure.clone() {
                out.push_str(&format!("{: <16}::", st.lock().unwrap().node.name));
            }
            out.push_str(&format!("{: <16} | {}", f.node.name, f.signature));
            if let Some(t) = f.impl_trait.clone() {
                out.push_str(&format!(" | impl {}", t));
            }
            out.push_str("\n");
        }
        out
    }

    fn format(&self) -> String {
        let mut out = String::new();
        out.push_str("== Static Variables ==\n");
        out.push_str(&self.format_static());
        out.push_str("==\n");

        out.push_str("== Structs ==\n");
        out.push_str(&self.format_structs());
        out.push_str("==\n");

        out.push_str("== Functions ==\n");
        out.push_str(&self.format_functions());
        out.push_str("==\n");
        out
    }
}

fn format_contexts(contexts: &Vec<Arc<Context>>) -> String {
    let mut out = String::new();
    out.push_str("== Static Variables ==\n");
    for ctx in contexts {
        out.push_str(&ctx.format_static());
    }
    out.push_str("==\n");

    out.push_str("== Structs ==\n");
    for ctx in contexts {
        out.push_str(&ctx.format_structs());
    }
    out.push_str("==\n");

    out.push_str("== Functions ==\n");
    for ctx in contexts {
        out.push_str(&ctx.format_functions());
    }
    out.push_str("==\n");
    out
}

struct RustCodeNode {
    pub(crate) name: String,
    pub(crate) ty: RustType,
}

struct RustField {
    pub(crate) node: RustCodeNode,
    pub(crate) def: String,
    pub(crate) structure: Option<Arc<Mutex<RustStruct>>>,
}

struct RustFunction {
    pub(crate) node: RustCodeNode,
    pub(crate) structure: Option<Arc<Mutex<RustStruct>>>,
    pub(crate) impl_trait: Option<String>,
    pub(crate) signature: String,
    pub(crate) tokens: TextSize,
}

struct RustStruct {
    pub(crate) node: RustCodeNode,
    pub(crate) fields: Vec<Arc<RustField>>,
    pub(crate) functions: Vec<Arc<RustFunction>>,
}

struct RustStatic {
    pub(crate) node: RustCodeNode,
    pub(crate) def: String,
}

struct RustImpl {
    pub(crate) node: RustCodeNode,
    pub(crate) target: Arc<Mutex<RustStruct>>,
    pub(crate) traits: Option<Arc<String>>,
}

impl RustCodeNode {
    fn from(node: &StructureNode) -> Self {
        let kind = match node.kind {
            StructureNodeKind::SymbolKind(k) => k,
            _ => panic!("Unknown node kind: {:?}", node.kind),
        };
        let ty = match kind {
            SymbolKind::Struct | SymbolKind::Trait => RustType::Struct,
            SymbolKind::Function | SymbolKind::Method => RustType::Function,
            SymbolKind::Field => RustType::Field,
            SymbolKind::Static => RustType::Static,
            SymbolKind::Impl => RustType::Impl,
            _ => panic!("Unknown symbol kind: {:?}", node.kind),
        };
        RustCodeNode {
            name: node.label.clone(),
            ty,
        }
    }
}

trait FromContext<T> {
    fn from(node: &T, ctx: &Context) -> Self;
}

impl FromContext<StructureNode> for RustField {
    fn from(node: &StructureNode, ctx: &Context) -> Self {
        let mut e = RustField {
            node: RustCodeNode::from(node),
            def: node.detail.as_ref().unwrap().clone(),
            structure: None,
        };
        if let Some(parent) = node.parent {
            let st = ctx.structs.get(&parent).unwrap();
            e.structure = Some(st.clone());
        }
        e
    }
}

impl FromContext<StructureNode> for RustFunction {
    fn from(node: &StructureNode, ctx: &Context) -> Self {
        let mut f = RustFunction {
            node: RustCodeNode::from(node),
            structure: None,
            impl_trait: None,
            signature: node.detail.as_ref().unwrap().clone(),
            tokens: node.node_range.len().clone()
        };
        if let Some(parent) = node.parent {
            if let Some(implementation) = ctx.impls.get(&parent) {
                f.structure = Some(implementation.target.clone());
                f.impl_trait = match &implementation.traits {
                    Some(t) => Some(t.as_ref().to_string()),
                    None => None,
                };
            } else if let Some(st) = ctx.structs.get(&parent) {
                f.structure = Some(st.clone());
            }
        }
        f
    }
}

impl FromContext<StructureNode> for RustImpl {
    fn from(node: &StructureNode, ctx: &Context) -> Self {
        let impl_signature = node.label.as_ref();
        let re = Regex::new(
            r"impl(?:\s+(?P<trait>[^\s]+)\s+for)?\s+(?P<target>[^\s<]+)(?:<[^>]+>)?\s*\{?"
        ).unwrap();
        let captures = re.captures(&impl_signature).unwrap();
        let target = captures["target"].to_string();
        let traits: Option<Arc<String>> = match captures.name("trait") {
            Some(t) => Some(Arc::new(t.as_str().to_string())),
            None => None,
        };

        let st = ctx.structs.iter().find(
            |(_, s)| s.lock().unwrap().node.name == target);

        let st = match st {
            Some((_, s)) => s.clone(),
            None => {
                let o = Arc::new(Mutex::new(RustStruct {
                    node: RustCodeNode {
                        name: target.clone(),
                        ty: RustType::Struct,
                    },
                    fields: Vec::new(),
                    functions: Vec::new(),
                }));
                o
            },
        };


        RustImpl {
            node: RustCodeNode::from(node),
            target: st.clone(),
            traits: traits,
        }
    }
}

impl FromContext<StructureNode> for RustStruct {
    fn from(node: &StructureNode, ctx: &Context) -> Self {
        RustStruct {
            node: RustCodeNode::from(node),
            fields: Vec::new(),
            functions: Vec::new(),
        }
    }
}

impl FromContext<StructureNode> for RustStatic {
    fn from(node: &StructureNode, _ctx: &Context) -> Self {
        RustStatic {
            node: RustCodeNode::from(node),
            def: node.detail.as_ref().unwrap_or(&"UNDEFINED".to_string()).clone(),
        }
    }
}

fn parse(path: &PathBuf) -> Arc<Context> {
    let mut ctx = Context::new(path);
    let code = fs::read_to_string(path).unwrap_or_else(|e| {
        log::error!("Error reading file: {:?} ({})", path, e);
        "".to_string()
    });
    let (analysis, file_id) = Analysis::from_single_file(code);
    let structure = analysis.file_structure(file_id).unwrap();

    ctx.load(structure);
    ctx.parse();
    Arc::new(ctx)
}

fn main() {
    env_logger::init();
    let cmd = Command::new("statistics")
        .bin_name("statistics")
        .about("Prints statistics about the codebase")
        .args(&[
            arg!(--"verbose" "Enable verbose output")
                .global(true),
            arg!(--"rs" <PATH> "Path to analyze")
                .value_parser(value_parser!(
                    PathBuf
                )),
            arg!(--"toml" <TOML> "Path to the configuration file")
                .value_parser(value_parser!(
                    PathBuf
                )),
        ]);
    let matches = cmd.get_matches();
    if matches.get_flag("verbose") {
        env_logger::builder().filter_level(log::LevelFilter::Trace).init();
    }

    if let Some(path) = matches.get_one::<PathBuf>("rs") {
        // single file mode
        let ctx = parse(path);
        let statistics = ctx.format();
        println!("{}", statistics);
    }

    if let Some(toml) = matches.get_one::<PathBuf>("toml") {
        // multi file mode
        let content = fs::read_to_string(toml);
        let config = match content {
            Ok(c) => toml::from_str::<Table>(&c),
            Err(e) => {
                log::error!("Error parsing TOML: {:?}", e);
                return;
            }
        };

        if let Err(e) = config {
            log::error!("Error parsing TOML: {:?}", e);
            return;
        }

        let tbl = config.unwrap();
        let src = tbl.get("sources");
        if src.is_none() {
            log::error!("No sources found in TOML");
            return;
        }

        let sources = src.unwrap().as_array().unwrap();
        let mut contexts: Vec<Arc<Context>> = Vec::new();
        for source in sources {
            let path = PathBuf::from(source.as_str().unwrap().trim());
            log::trace!("Parsing: {:?}", path);
            let ctx = parse(&path);
            contexts.push(ctx);
        }

        let statistics = format_contexts(&contexts);
        println!("{}", statistics);
    }
}
