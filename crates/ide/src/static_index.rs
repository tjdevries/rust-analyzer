//! This module provides `StaticIndex` which is used for powering
//! read-only code brow scheme: todo!(), identifier: todo!(), unique: todo!(), kind: todo!()  scheme: todo!(), identifier: todo!(), unique: todo!(), kind: todo!() sers and emitting LSIF

use std::collections::HashMap;

use hir::Semantics;
use hir::{db::HirDatabase, Crate, Module};
use ide_db::base_db::{FileId, FileRange, SourceDatabaseExt};
use ide_db::defs::Definition;
use ide_db::RootDatabase;
use lsp_types::{self, Moniker};
use rustc_hash::FxHashSet;
use syntax::{AstNode, SyntaxKind::*, T};
use syntax::{SyntaxToken, TextRange};

use crate::display::TryToNav;
use crate::hover::hover_for_definition;
use crate::{
    Analysis, Fold, HoverConfig, HoverDocFormat, HoverResult, InlayHint, InlayHintsConfig,
};

/// A static representation of fully analyzed source code.
///
/// The intended use-case is powering read-only code browsers and emitting LSIF
#[derive(Debug)]
pub struct StaticIndex<'a> {
    pub files: Vec<StaticIndexedFile>,
    pub tokens: TokenStore,
    analysis: &'a Analysis,
    db: &'a RootDatabase,
    def_map: HashMap<Definition, TokenId>,

    // TODO: Do impl instead
    pub moniker_map: HashMap<Definition, Moniker>,
}

#[derive(Debug)]
pub struct ReferenceData {
    pub range: FileRange,
    pub is_definition: bool,
}

#[derive(Debug)]
pub struct TokenStaticData {
    pub hover: Option<HoverResult>,
    pub definition: Option<FileRange>,
    pub references: Vec<ReferenceData>,
    pub moniker: Option<Moniker>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TokenId(usize);

impl TokenId {
    pub fn raw(self) -> usize {
        self.0
    }
}

#[derive(Default, Debug)]
pub struct TokenStore(Vec<TokenStaticData>);

impl TokenStore {
    pub fn insert(&mut self, data: TokenStaticData) -> TokenId {
        let id = TokenId(self.0.len());
        self.0.push(data);
        id
    }

    pub fn get_mut(&mut self, id: TokenId) -> Option<&mut TokenStaticData> {
        self.0.get_mut(id.0)
    }

    pub fn get(&self, id: TokenId) -> Option<&TokenStaticData> {
        self.0.get(id.0)
    }

    pub fn iter(self) -> impl Iterator<Item = (TokenId, TokenStaticData)> {
        self.0.into_iter().enumerate().map(|(i, x)| (TokenId(i), x))
    }
}

#[derive(Debug)]
pub struct StaticIndexedFile {
    pub file_id: FileId,
    pub folds: Vec<Fold>,
    pub inlay_hints: Vec<InlayHint>,
    pub tokens: Vec<(TextRange, TokenId)>,
}

fn all_modules(db: &dyn HirDatabase) -> Vec<Module> {
    let mut worklist: Vec<_> =
        Crate::all(db).into_iter().map(|krate| krate.root_module(db)).collect();
    let mut modules = Vec::new();

    while let Some(module) = worklist.pop() {
        modules.push(module);
        worklist.extend(module.children(db));
    }

    modules
}

impl StaticIndex<'_> {
    fn add_file(&mut self, file_id: FileId) {
        let folds = self.analysis.folding_ranges(file_id).unwrap();
        let inlay_hints = self
            .analysis
            .inlay_hints(
                &InlayHintsConfig {
                    type_hints: true,
                    parameter_hints: true,
                    chaining_hints: true,
                    max_length: Some(25),
                },
                file_id,
            )
            .unwrap();
        // hovers
        let sema = hir::Semantics::new(self.db);
        let tokens_or_nodes = sema.parse(file_id).syntax().clone();
        let tokens = tokens_or_nodes.descendants_with_tokens().filter_map(|x| match x {
            syntax::NodeOrToken::Node(_) => None,
            syntax::NodeOrToken::Token(x) => Some(x),
        });
        let hover_config =
            HoverConfig { links_in_hover: true, documentation: Some(HoverDocFormat::Markdown) };
        let tokens = tokens.filter(|token| match token.kind() {
            IDENT | INT_NUMBER | LIFETIME_IDENT | T![self] | T![super] | T![crate] => true,
            _ => false,
        });
        let mut result = StaticIndexedFile { file_id, inlay_hints, folds, tokens: vec![] };
        for token in tokens {
            let range = token.text_range();
            let node = token.parent().unwrap();
            let def = match get_definition(&sema, token.clone()) {
                Some(x) => x,
                None => continue,
            };
            let id = if let Some(x) = self.def_map.get(&def) {
                *x
            } else {
                self.add_moniker(&def);

                let x = self.tokens.insert(TokenStaticData {
                    hover: hover_for_definition(&sema, file_id, def, &node, &hover_config),
                    definition: def
                        .try_to_nav(self.db)
                        .map(|x| FileRange { file_id: x.file_id, range: x.focus_or_full_range() }),
                    references: vec![],
                    moniker: match self.moniker_map.get(&def) {
                        Some(moniker) => Some(moniker.clone()),
                        None => None,
                    },
                });
                self.def_map.insert(def, x);
                x
            };
            let token = self.tokens.get_mut(id).unwrap();
            token.references.push(ReferenceData {
                range: FileRange { range, file_id },
                is_definition: match def.try_to_nav(self.db) {
                    Some(x) => x.file_id == file_id && x.focus_or_full_range() == range,
                    None => false,
                },
            });
            result.tokens.push((range, id));
        }
        self.files.push(result);
    }

    pub fn add_moniker(&mut self, def: &Definition) {
        if let Some(vis) = def.visibility(self.db) {
            if matches!(vis, hir::Visibility::Public) {
                match def.module(self.db) {
                    Some(module) => {
                        let krate = module.krate().display_name(self.db).unwrap();
                        if krate.to_string() == "core" {
                            return;
                        }

                        let module_name = match module.name(self.db) {
                            Some(module_name) => module_name.to_string(),
                            None => return,
                        };

                        let name = def.name(self.db).unwrap().to_string();
                        let id = format!("{}:{}:{}", krate, module_name, name);
                        let moniker = lsp_types::Moniker {
                            scheme: "rust-analyzer".to_string(),
                            identifier: id,
                            unique: lsp_types::UniquenessLevel::Scheme,
                            kind: Some(lsp_types::MonikerKind::Export),
                        };
                        // eprintln!("VISIBLE: {:?}", moniker);

                        self.moniker_map.insert(*def, moniker);
                    }
                    None => {}
                }
            }
        }
    }
    pub fn compute<'a>(analysis: &'a Analysis) -> StaticIndex<'a> {
        let db = &*analysis.db;
        let work = all_modules(db).into_iter().filter(|module| {
            let file_id = module.definition_source(db).file_id.original_file(db);
            let source_root = db.file_source_root(file_id);
            let source_root = db.source_root(source_root);
            !source_root.is_library
        });
        let mut this = StaticIndex {
            files: vec![],
            tokens: Default::default(),
            analysis,
            db,
            def_map: Default::default(),
            moniker_map: Default::default(),
        };
        let mut visited_files = FxHashSet::default();
        for module in work {
            let file_id = module.definition_source(db).file_id.original_file(db);
            if visited_files.contains(&file_id) {
                continue;
            }
            this.add_file(file_id);
            // mark the file
            visited_files.insert(file_id);
        }
        this
    }
}

fn get_definition(sema: &Semantics<RootDatabase>, token: SyntaxToken) -> Option<Definition> {
    for token in sema.descend_into_macros(token) {
        let def = Definition::from_token(&sema, &token);
        if let [x] = def.as_slice() {
            return Some(*x);
        } else {
            continue;
        };
    }
    None
}

#[cfg(test)]
mod tests {
    use crate::{fixture, StaticIndex};
    use ide_db::base_db::FileRange;
    use std::collections::HashSet;

    fn check_all_ranges(ra_fixture: &str) {
        let (analysis, ranges) = fixture::annotations_without_marker(ra_fixture);
        let s = StaticIndex::compute(&analysis);
        let mut range_set: HashSet<_> = ranges.iter().map(|x| x.0).collect();
        for f in s.files {
            for (range, _) in f.tokens {
                let x = FileRange { file_id: f.file_id, range };
                if !range_set.contains(&x) {
                    panic!("additional range {:?}", x);
                }
                range_set.remove(&x);
            }
        }
        if !range_set.is_empty() {
            panic!("unfound ranges {:?}", range_set);
        }
    }

    fn check_definitions(ra_fixture: &str) {
        let (analysis, ranges) = fixture::annotations_without_marker(ra_fixture);
        let s = StaticIndex::compute(&analysis);
        let mut range_set: HashSet<_> = ranges.iter().map(|x| x.0).collect();
        for (_, t) in s.tokens.iter() {
            if let Some(x) = t.definition {
                if !range_set.contains(&x) {
                    panic!("additional definition {:?}", x);
                }
                range_set.remove(&x);
            }
        }
        if !range_set.is_empty() {
            panic!("unfound definitions {:?}", range_set);
        }
    }

    #[test]
    fn struct_and_enum() {
        check_all_ranges(
            r#"
struct Foo;
     //^^^
enum E { X(Foo) }
   //^   ^ ^^^
"#,
        );
        check_definitions(
            r#"
struct Foo;
     //^^^
enum E { X(Foo) }
   //^   ^
"#,
        );
    }

    #[test]
    fn derives() {
        check_all_ranges(
            r#"
#[rustc_builtin_macro]
pub macro Copy {}
        //^^^^
#[rustc_builtin_macro]
pub macro derive {}
        //^^^^^^
#[derive(Copy)]
//^^^^^^ ^^^^
struct Hello(i32);
     //^^^^^ ^^^
"#,
        );
    }
}
