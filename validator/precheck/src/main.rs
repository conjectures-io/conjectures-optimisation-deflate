use syn::{
    spanned::Spanned,
    visit::{self, Visit},
};

#[derive(Default)]
struct Check {
    errors: Vec<serde_json::Value>,
}
impl Check {
    fn reject<T: Spanned>(&mut self, node: &T, message: &str) {
        self.errors
            .push(serde_json::json!({"line": node.span().start().line, "message": message}));
    }
}
impl<'ast> Visit<'ast> for Check {
    fn visit_attribute(&mut self, node: &'ast syn::Attribute) {
        let path = node.path();
        let allowed = if path.is_ident("doc") {
            matches!(&node.meta, syn::Meta::NameValue(v) if matches!(&v.value,
                syn::Expr::Lit(l) if matches!(l.lit, syn::Lit::Str(_))))
        } else if path.is_ident("inline") {
            matches!(&node.meta, syn::Meta::Path(_))
                || node
                    .parse_args::<syn::Ident>()
                    .is_ok_and(|x| x == "always" || x == "never")
        } else if path.is_ident("cold") {
            matches!(&node.meta, syn::Meta::Path(_))
        } else if path.is_ident("allow") {
            node.parse_args::<syn::Ident>()
                .is_ok_and(|x| x == "dead_code" || x == "unused_variables")
        } else {
            false
        };
        if !allowed {
            self.reject(node, "unsupported attribute: conditional compilation and extraction/linker overrides are forbidden; write the selected implementation directly");
        }
    }
    fn visit_macro(&mut self, node: &'ast syn::Macro) {
        self.reject(node, "unsupported macro: expand pure macros into ordinary Rust; no I/O, embedded data or conditional compilation");
    }
    fn visit_item_mod(&mut self, node: &'ast syn::ItemMod) {
        self.reject(
            node,
            "the submission is one crate root: external modules are unsupported",
        );
    }
    fn visit_item_foreign_mod(&mut self, node: &'ast syn::ItemForeignMod) {
        self.reject(node, "no foreign code");
    }
    fn visit_item_extern_crate(&mut self, node: &'ast syn::ItemExternCrate) {
        self.reject(node, "no external crates");
    }
    fn visit_expr_unsafe(&mut self, node: &'ast syn::ExprUnsafe) {
        self.reject(node, "`unsafe` is outside the translated subset");
    }
    fn visit_signature(&mut self, node: &'ast syn::Signature) {
        if node.unsafety.is_some() || node.abi.is_some() || node.asyncness.is_some() {
            self.reject(node, "unsafe, foreign and async functions are unsupported");
        }
        visit::visit_signature(self, node);
    }
    fn visit_item_static(&mut self, node: &'ast syn::ItemStatic) {
        self.reject(
            node,
            "statics are unsupported: use constants or local state",
        );
    }
    fn visit_item_impl(&mut self, node: &'ast syn::ItemImpl) {
        if node.unsafety.is_some() {
            self.reject(node, "unsafe impl is forbidden");
        }
        if let Some((_, path, _)) = &node.trait_ {
            // Charon's Aeneas preset omits precise drops. Aliased Drop is caught by IR too.
            if path.segments.last().is_some_and(|s| s.ident == "Drop") {
                self.reject(
                    node,
                    "custom destructors require precise drop analysis and are unsupported",
                );
            }
        }
        visit::visit_item_impl(self, node);
    }
    fn visit_item_trait(&mut self, node: &'ast syn::ItemTrait) {
        if node.unsafety.is_some() {
            self.reject(node, "unsafe trait is forbidden");
        }
        visit::visit_item_trait(self, node);
    }
    fn visit_expr_for_loop(&mut self, node: &'ast syn::ExprForLoop) {
        self.reject(
            node,
            "Iterator loops are unsupported by extraction; use indices",
        );
    }
    fn visit_label(&mut self, node: &'ast syn::Label) {
        self.reject(node, "labelled loops are unsupported by Aeneas");
    }
    fn visit_use_tree(&mut self, node: &'ast syn::UseTree) {
        if let syn::UseTree::Path(path) = node {
            if path.ident == "crate" {
                self.reject(node, "the slot is compiled as its own crate root");
            }
        }
        visit::visit_use_tree(self, node);
    }
    fn visit_path(&mut self, node: &'ast syn::Path) {
        let parts: Vec<String> = node
            .segments
            .iter()
            .map(|s| s.ident.to_string().trim_start_matches("r#").to_owned())
            .collect();
        if parts.first().is_some_and(|s| s == "crate") {
            self.reject(node, "the slot is compiled as its own crate root");
        }
        if parts.first().is_some_and(|s| s == "std")
            && parts.get(1).is_some_and(|s| {
                [
                    "fs", "net", "process", "thread", "env", "io", "time", "sync",
                ]
                .contains(&s.as_str())
            })
        {
            self.reject(
                node,
                "no I/O, processes, threads, environment, clocks or shared state",
            );
        }
        visit::visit_path(self, node);
    }
}
fn main() {
    let result = std::env::args()
        .nth(1)
        .ok_or("expected a Rust source path".to_owned())
        .and_then(|path| std::fs::read_to_string(path).map_err(|e| e.to_string()))
        .and_then(|source| syn::parse_file(&source).map_err(|e| e.to_string()));
    let mut check = Check::default();
    match result {
        Ok(file) => check.visit_file(&file),
        Err(error) => check
            .errors
            .push(serde_json::json!({"line": 0, "message": error})),
    }
    println!("{}", serde_json::json!({"diagnostics": check.errors}));
    if !check.errors.is_empty() {
        std::process::exit(1);
    }
}
