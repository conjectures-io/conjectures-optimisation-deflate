# Charon JSON is a versioned external schema. Runtime checks below validate
# capability-bearing nodes; dynamic payload types deliberately stay at this boundary.
# pyright: reportAny=false, reportExplicitAny=false, reportUnknownVariableType=false, reportUnknownArgumentType=false
"""Capability policy for the pinned Charon 0.1.245 LLBC output.

Input is produced by our compiler, never accepted from a miner. This is a closed
operation policy: unsupported pure operations need a reviewed model, not a bypass.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

# Reviewed scalar operations and slice length have no callback or host capability.
NUMERIC = {
    "wrapping_add",
    "wrapping_sub",
    "wrapping_mul",
    "wrapping_div",
    "wrapping_rem",
    "wrapping_shl",
    "wrapping_shr",
    "wrapping_neg",
    "wrapping_abs",
    "checked_add",
    "checked_sub",
    "checked_mul",
    "checked_div",
    "checked_rem",
    "checked_shl",
    "checked_shr",
    "saturating_add",
    "saturating_sub",
    "saturating_mul",
    "rotate_left",
    "rotate_right",
    "count_ones",
    "count_zeros",
    "leading_zeros",
    "trailing_zeros",
    "swap_bytes",
    "reverse_bits",
    "to_le",
    "to_be",
    "from_le",
    "from_be",
}
EXTERNAL = {"core::slice::{impl}::len"} | {f"core::num::{{impl}}::{name}" for name in NUMERIC}
# Vec indexing uses sealed standard-library traits. Its destructor only frees
# owned storage: custom Drop/allocator implementations are not admitted below.
EXTERNAL.update(
    {
        f"alloc::vec::{{impl}}::{name}"
        for name in (
            "new",
            "with_capacity",
            "push",
            "len",
            "index",
            "index_mut",
            "deref",
            "deref_mut",
        )
    }
    | {
        f"core::slice::index::{{impl}}::{name}"
        for name in (
            "get",
            "get_mut",
            "get_unchecked",
            "get_unchecked_mut",
            "index",
            "index_mut",
        )
    }
)
DROP_MODELS = {"alloc::vec::Vec::{impl}::drop_glue", "alloc::alloc::Global::{impl}::drop_glue"}
EXTERNAL.update(DROP_MODELS)
EXTERNAL_TRAITS = {
    "core::marker::Destruct",
    "core::slice::index::SliceIndex",
    "core::ops::index::Index",
    "core::ops::index::IndexMut",
    "core::ops::deref::Deref",
    "core::ops::deref::DerefMut",
}
EXTERNAL_IMPLS = {
    "alloc::vec::Vec::{impl}",
    "alloc::alloc::Global::{impl}",
    "alloc::vec::{impl}",
    "core::slice::index::{impl}",
}
EXTERNAL_TYPES = {
    "alloc::vec::Vec",
    "alloc::alloc::Global",
    "core::option::Option",
    "core::result::Result",
    "core::cmp::Ordering",
    "core::num::error::TryFromIntError",
    "core::array::TryFromSliceError",
}
STATEMENTS = {
    "Assign",
    "SetDiscriminant",
    "StorageLive",
    "StorageDead",
    "Deinit",
    "Nop",
    "Assert",
    "Call",
    "Abort",
    "Return",
    "Break",
    "Continue",
    "Switch",
    "Loop",
    "UnwindResume",
    "Error",
    "Borrowck",
    "PlaceMention",
    "Drop",
}


class Unsupported(ValueError):
    """The resolved program is outside the reviewed capability subset."""


def name_of(parts: list[dict[str, Any]]) -> str:
    out: list[str] = []
    for part in parts:
        if set(part) == {"Ident"}:
            out.append(str(part["Ident"][0]))
        elif set(part) == {"Impl"}:
            out.append("{impl}")
        else:
            raise Unsupported("unknown resolved name component")
    return "::".join(out)


def check(path: Path) -> list[str]:
    try:
        data = json.loads(path.read_text())
        if data["charon_version"] != "0.1.245" or data["has_errors"] is not False:
            raise Unsupported("wrong Charon version or incomplete extraction")
        crate = data["translated"]
        if crate["crate_name"] != "slot":
            raise Unsupported("unexpected crate identity")
        options = crate["options"]
        if (
            options["preset"] != "Aeneas"
            or options["translate_all_methods"] is not True
            or any(
                options[x]
                for x in (
                    "exclude",
                    "opaque",
                    "start_from",
                    "start_from_if_exists",
                    "start_from_attribute",
                    "start_from_pub",
                    "skip_borrowck",
                    "no_typecheck",
                )
            )
        ):
            raise Unsupported("unreviewed extraction configuration")
        # The compiler owns this IR. Resolve its shared nodes before checking
        # generic dispatch; never infer a target from source spelling.
        shared: dict[int, Any] = {}

        def collect(value: Any) -> None:
            if isinstance(value, list):
                for entry in value:
                    collect(entry)
            elif isinstance(value, dict):
                if "HashConsedValue" in value:
                    index, node = value["HashConsedValue"]
                    if index in shared:
                        raise Unsupported("duplicate shared IR node")
                    shared[index] = node
                for entry in value.values():
                    collect(entry)

        collect(crate)

        def unshare(value: Any) -> Any:
            if set(value) == {"HashConsedValue"}:
                return value["HashConsedValue"][1]
            if set(value) == {"Deduplicated"}:
                return shared[value["Deduplicated"]]
            raise Unsupported("unknown shared IR reference")

        traits: dict[int, str] = {}
        local_traits: dict[int, Any] = {}
        implementations: dict[int, Any] = {}
        for trait in crate["trait_decls"]:
            if trait is None:
                continue
            name = name_of(trait["item_meta"]["name"])
            if trait["item_meta"]["is_local"]:
                if not name.startswith("slot::") or trait["item_meta"]["opacity"] != "Transparent":
                    raise Unsupported(f"uninspectable local trait: {name}")
                local_traits[trait["def_id"]] = trait
            elif name not in EXTERNAL_TRAITS:
                raise Unsupported(f"unreviewed trait/destructor: {name}")
            traits[trait["def_id"]] = name
        for implementation in crate["trait_impls"]:
            if implementation is None:
                continue
            meta = implementation["item_meta"]
            name = name_of(meta["name"])
            trait = traits.get(implementation["impl_trait"]["id"])
            generated_drop = (
                trait == "core::marker::Destruct" and implementation["src"] == "Destruct"
            )
            local_dispatch = implementation["impl_trait"]["id"] in local_traits
            if (
                not trait
                or (meta["is_local"] and not (generated_drop or local_dispatch))
                or (not meta["is_local"] and name not in EXTERNAL_IMPLS)
            ):
                raise Unsupported(f"unreviewed trait implementation: {name}")
            if meta["is_local"] and meta["opacity"] != "Transparent":
                raise Unsupported(f"uninspectable local implementation: {name}")
            implementations[implementation["def_id"]] = implementation
        functions: set[int] = set()
        external: list[str] = []
        drop_functions: set[int] = set()
        for key in ("fun_decls", "type_decls", "global_decls"):
            for item in crate[key]:
                if item is None:
                    continue
                meta = item["item_meta"]
                name = name_of(meta["name"])
                local = meta["is_local"]
                if local:
                    if not name.startswith("slot::") or meta["opacity"] != "Transparent":
                        raise Unsupported(f"uninspectable local item: {name}")
                elif not (
                    (key == "fun_decls" and name in EXTERNAL)
                    or (key == "type_decls" and name in EXTERNAL_TYPES)
                ):
                    raise Unsupported(f"unapproved external operation/model: {name}")
                elif key == "fun_decls":
                    external.append(name)
                if key == "fun_decls":
                    functions.add(item["def_id"])
                    if name in DROP_MODELS or (local and item["src"] == "DropGlue"):
                        drop_functions.add(item["def_id"])
                    if local and (
                        not isinstance(item["body"], dict) or set(item["body"]) != {"Structured"}
                    ):
                        raise Unsupported(f"missing function body: {name}")
                if key == "global_decls" and item["global_kind"] not in ("NamedConst", "AnonConst"):
                    raise Unsupported(f"global state: {name}")

        # All provided methods are extracted, including unused defaults. Abstract
        # signatures have no body; every concrete dictionary entry must have one.
        for trait in local_traits.values():
            for method in trait["methods"]:
                method = method["skip_binder"]
                signature = method["signature"]
                if signature["is_unsafe"] or signature["abi"] != "Rust":
                    raise Unsupported("unsafe/foreign trait method")
                default = method["default"]
                if default is not None and default["id"] not in functions:
                    raise Unsupported("trait default has no inspected body")
        for implementation in implementations.values():
            trait_id = implementation["impl_trait"]["id"]
            if trait_id in local_traits:
                if len(implementation["methods"]) != len(local_traits[trait_id]["methods"]):
                    raise Unsupported("incomplete trait method dictionary")
                for method in implementation["methods"]:
                    if method["skip_binder"]["id"] not in functions:
                        raise Unsupported("trait implementation has no inspected body")

        def trait_reference(value: Any) -> int:
            reference = unshare(value)
            trait_id = reference["trait_decl_ref"]["skip_binder"]["id"]
            if trait_id not in traits:
                raise Unsupported("trait reference has no inspected declaration")
            kind = reference["kind"]
            if isinstance(kind, dict) and set(kind) == {"TraitImpl"}:
                implementation = implementations[kind["TraitImpl"]["id"]]
                if implementation["impl_trait"]["id"] != trait_id:
                    raise Unsupported("trait implementation identity mismatch")
            elif isinstance(kind, dict) and set(kind) == {"Clause"}:
                # Rust type checking supplies this generic dictionary; every
                # concrete implementation in this closed crate is checked above.
                if set(kind["Clause"]) not in ({"Free"}, {"Bound"}):
                    raise Unsupported("unknown generic trait clause")
            elif isinstance(kind, dict) and set(kind) == {"BuiltinOrAuto"}:
                builtin = kind["BuiltinOrAuto"]
                if not (
                    traits[trait_id] == "core::marker::Destruct"
                    and builtin["builtin_data"] == "UntrackedDestruct"
                    and not builtin["parent_trait_refs"]
                    and not builtin["types"]
                    and builtin["vtable"] is None
                ):
                    raise Unsupported("unreviewed builtin trait dictionary")
            elif isinstance(kind, dict) and set(kind) == {"ParentClause"}:
                parent, clause = kind["ParentClause"]
                parent_id = trait_reference(parent)
                if parent_id not in local_traits:
                    raise Unsupported("unreviewed inherited trait")
                clauses = local_traits[parent_id]["implied_clauses"]
                if not any(
                    item["clause_id"] == clause and item["trait_"]["skip_binder"]["id"] == trait_id
                    for item in clauses
                ):
                    raise Unsupported("inherited trait identity mismatch")
            elif kind != "SelfId":
                raise Unsupported("unresolved trait dictionary")
            return trait_id

        def walk(value: Any) -> None:
            if isinstance(value, list):
                for entry in value:
                    walk(entry)
            elif isinstance(value, dict):
                if "trait_refs" in value:
                    for reference in value["trait_refs"]:
                        trait_reference(reference)
                # Statements have an id, span and kind; all effects must be known.
                if {"id", "span", "kind", "comments_before"} <= value.keys():
                    kind = value["kind"]
                    if isinstance(kind, dict) and len(kind) != 1:
                        raise Unsupported("malformed statement variant")
                    variant = kind if isinstance(kind, str) else next(iter(kind))
                    if variant == "Drop" and isinstance(kind, dict):
                        target = kind["Drop"]["fn_ptr"]["kind"]
                        if set(target) == {"Trait"}:
                            reference, method = target["Trait"]
                            # All concrete types in this closed crate have been
                            # checked: user Drop and foreign resource types are
                            # rejected, so generic drop can only release storage.
                            if (
                                traits[trait_reference(reference)] != "core::marker::Destruct"
                                or method != 0
                            ):
                                raise Unsupported("unreviewed generic drop behavior")
                        elif (
                            set(target) != {"Fun"}
                            or set(target["Fun"]) != {"Regular"}
                            or target["Fun"]["Regular"] not in drop_functions
                        ):
                            raise Unsupported("unreviewed drop behavior")
                    if variant == "Assign" and isinstance(kind, dict):
                        rvalue = kind["Assign"][1]
                        if (
                            not isinstance(rvalue, dict)
                            or len(rvalue) != 1
                            or next(iter(rvalue))
                            not in {
                                "Use",
                                "Ref",
                                "BinaryOp",
                                "UnaryOp",
                                "NullaryOp",
                                "Discriminant",
                                "Aggregate",
                                "Len",
                                "Repeat",
                            }
                        ):
                            raise Unsupported("unreviewed rvalue")
                    if variant not in STATEMENTS or variant == "Error":
                        raise Unsupported(f"unsupported statement: {variant}")
                if "func" in value:
                    function = value["func"]
                    if set(function) != {"Regular"}:
                        raise Unsupported("unresolved indirect call")
                    target = function["Regular"]["kind"]
                    if set(target) == {"Trait"}:
                        reference, method = target["Trait"]
                        trait_id = trait_reference(reference)
                        if trait_id not in local_traits or not (
                            isinstance(method, int)
                            and 0 <= method < len(local_traits[trait_id]["methods"])
                        ):
                            raise Unsupported("unreviewed trait call")
                        # Nested generic arguments are still visited below.
                        target = None
                    elif set(target) == {"Fun"}:
                        target = target["Fun"]
                    else:
                        raise Unsupported("unknown call target")
                    if target is None:
                        pass
                    elif set(target) == {"Regular"}:
                        if target["Regular"] not in functions:
                            raise Unsupported("call has no inspected declaration")
                    elif set(target) == {"Builtin"}:
                        builtin = target["Builtin"]
                        if builtin not in (
                            "ArrayRepeat",
                            "ArrayToSliceShared",
                            "ArrayToSliceMut",
                        ) and not (isinstance(builtin, dict) and set(builtin) == {"Index"}):
                            raise Unsupported(f"unreviewed builtin: {builtin}")
                    else:
                        raise Unsupported("unknown call target")
                for key, entry in value.items():
                    if key not in ("source_text", "contents", "comments", "comments_before"):
                        walk(entry)

        walk(crate)
        return sorted(set(external))
    except (
        KeyError,
        TypeError,
        IndexError,
        AttributeError,
        StopIteration,
        json.JSONDecodeError,
    ) as exc:
        raise Unsupported(f"malformed or unsupported LLBC: {exc}") from exc
