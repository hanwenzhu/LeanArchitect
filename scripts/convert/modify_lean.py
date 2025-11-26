"""Utilities for adding @[blueprint] attributes to Lean source files."""

from pathlib import Path
import re
from typing import Generator, Optional, Literal

from loguru import logger

from common import Node, NodeWithPos, Position, DeclarationRange, DeclarationLocation, make_docstring, _quote


def split_declaration(source: str, pos: Position, end_pos: Position):
    """Split a Lean file into pre, declaration, and post parts."""
    lines = source.splitlines(keepends=True)

    # -1 because Lean Position is 1-indexed
    start = sum(len(lines[i]) for i in range(pos.line - 1)) + pos.column
    end = sum(len(lines[i]) for i in range(end_pos.line - 1)) + end_pos.column

    pre = source[:start]
    decl = source[start:end]
    post = source[end:]

    return pre, decl, post


warned_to_additive = False

def insert_attributes(decl: str, new_attr: str) -> str:
    """Inserts attribute to the declaration.

    Note: This function assumes that the declaration is written in a "parseable" style,
    and corner cases would be fixed manually.
    """

    if decl.startswith("to_additive"):
        global warned_to_additive
        if not warned_to_additive:
            warned_to_additive = True
            logger.warning(
                "Encountered additive declaration(s) generated from @[to_additive]. You may decide to:\n"
                "- (Current) Add both to the same node in the blueprint by `@[to_additive (attr := blueprint)]`\n"
                "- Add only the additive declaration in the blueprint by `attribute [blueprint] additive_name`\n"
                "- Add only the multiplicative declaration in the blueprint by `@[to_additive, blueprint]`"
            )
        decl = decl.removeprefix("to_additive").strip()
        match = re.search(r"\(attr\s*:=\s*(.*?)\)", decl, flags=re.DOTALL)
        if match:
            attrs = match.group(1) + ", " + new_attr
            decl = decl.replace(match.group(0), "", 1)
        else:
            attrs = new_attr
        if decl:
            return f"to_additive (attr := {attrs}) {decl}"
        else:
            return f"to_additive (attr := {attrs})"

    # open ... in, omit ... in, include ... in, etc (assuming one-line, ending in newline, no interfering comments, etc)
    match = re.search(r"^(?:[a-zA-Z_]+.*? in\n)+", decl)
    if match:
        command_modifiers = match.group(0)
        decl = decl.removeprefix(match.group(0))
    else:
        command_modifiers = ""

    match = re.search(r"^\s*/--.*?-/\s*", decl, flags=re.DOTALL)
    if match:
        docstring = match.group(0)
        decl = decl.removeprefix(match.group(0))
    else:
        docstring = ""

    match = re.search(r"^\s*@\[(.*?)\]\s*", decl, flags=re.DOTALL)
    if match:
        attrs = match.group(1) + ", " + new_attr
        decl = decl.removeprefix(match.group(0))
    else:
        attrs = new_attr

    return f"{command_modifiers}{docstring}@[{attrs}]\n{decl}"


def modify_source(
    node: Node, file: Path, location: DeclarationLocation, add_uses: bool,
    docstring_indent: int, docstring_style: Literal["hanging", "compact"],
    prepend: Optional[list[str]] = None
):
    """Modify a Lean source file to add @[blueprint] attribute and docstring to the node."""
    source = file.read_text()
    pre, decl, post = split_declaration(source, location.range.pos, location.range.end_pos)
    # If there needs to be raw `uses` added, or there is `sorry`, then the inferred dependencies are incomplete, so `uses` is needed
    add_uses = add_uses or (node.proof is None and "sorry" in decl)
    add_proof_uses = add_uses or (node.proof is not None and "sorry" in decl)
    attr = node.to_lean_attribute(
        add_uses=add_uses, add_proof_uses=add_proof_uses,
        docstring_indent=docstring_indent, docstring_style=docstring_style
    )
    decl = insert_attributes(decl, attr)

    if prepend is not None:
        # Special cases:
        # pre = "...@[", decl = "to_additive..."
        if pre.endswith("@[") and decl.startswith("to_additive"):
            pre = pre.removesuffix("@[")
            decl = "@[" + decl
        # pre = "...(open|variable|...) ... in"
        match = re.search(r"\n((?:[a-zA-Z_]+.*? in\n)+)$", pre)
        if match:
            pre = pre.removesuffix(match.group(1))
            decl = match.group(1) + decl
        # Add prepend to between pre and decl
        decl = "".join(p + "\n\n" for p in prepend) + decl

    file.write_text(pre + decl + post)


def add_lean_architect_import(file: Path):
    """Adds `import Architect` before the first import in the file."""
    source = file.read_text()
    lines = source.splitlines(keepends=True)
    first_import_index = 0
    for i, line in enumerate(lines):
        if line.startswith("import ") or line.startswith("public import "):
            first_import_index = i
            break
    lines = lines[:first_import_index] + ["import Architect\n"] + lines[first_import_index:]
    source = "".join(lines)
    file.write_text(source)


def topological_sort(nodes: list[NodeWithPos]) -> list[NodeWithPos]:
    name_to_node: dict[str, NodeWithPos] = {node.name: node for node in nodes}

    visited: set[str] = set()
    result: list[NodeWithPos] = []

    def visit(name: str):
        if name in visited:
            return
        visited.add(name)

        node = name_to_node[name]
        for other in nodes:
            if other.latex_label in node.uses:
                visit(other.name)
        result.append(node)

    for node in nodes:
        visit(node.name)

    return result


def write_blueprint_attributes(
    nodes: list[NodeWithPos], modules: list[str], root_file: str,
    convert_informal: bool, convert_upstream: bool,
    add_uses: bool, docstring_indent: int, docstring_style: Literal["hanging", "compact"]
) -> list[NodeWithPos]:

    def is_upstream(node: NodeWithPos) -> bool:
        return node.location is not None and not any(node.location.module.split(".")[0] == module for module in modules)
    def is_informal(node: NodeWithPos) -> bool:
        return node.location is None

    # Sort nodes by reverse position, so that we can modify later declarations first
    nodes_location_order = sorted(
        nodes,
        key=lambda n:
            (n.location.module, n.location.range.pos.line) if n.location is not None else ("", 0),
        reverse=True
    )
    nodes_topological_order = topological_sort(nodes)

    # For upstream nodes and informal-only nodes, they are rendered as `attribute [blueprint] node_name` and
    # `theorem node_name : (sorry_using [uses] : Prop) := by sorry_using [uses]` respectively,
    # and prepended to normal nodes that directly depend on them.
    # If no such normal node exists, the upstream node is added to the root file.
    def upstream_or_informal_to_lean(node: NodeWithPos) -> str:
        if node.location is not None:
            return f"attribute [{node.to_lean_attribute(add_uses=False, add_proof_uses=False, docstring_indent=docstring_indent, docstring_style=docstring_style)}]\n  {node.name}"
        elif convert_informal:
            lean = ""
            lean += f"@[{node.to_lean_attribute(add_uses=False, add_proof_text=False, add_proof_uses=False, docstring_indent=docstring_indent, docstring_style=docstring_style)}]\n"
            if node.proof is None:
                lean += f"def {node.name} : (sorry : Type) :=\n"
                lean += f"  sorry_using [{', '.join(_quote(use) for use in node.statement.uses)}]"
            else:
                lean += f"theorem {node.name} : (sorry_using [{', '.join(_quote(use) for use in node.proof.uses)}] : Prop) := by\n"
                if node.proof.text.strip():
                    lean += f"  {make_docstring(node.proof.text, indent=2, start_column=len("  "))}\n"
                lean += f"  sorry_using [{', '.join(_quote(use) for use in node.statement.uses)}]"
            return lean
        else:
            logger.warning(
                f"Could not find the location of {node.name}. Please add the following manually:\n"
                f"attribute [{node.to_lean_attribute(add_uses=False, add_proof_uses=False, docstring_indent=docstring_indent, docstring_style=docstring_style)}]\n  {node.name}"
            )
            return ""

    # Mapping from node to nodes that should be prepended to it.
    prepends: dict[str, list[NodeWithPos]] = {n.name: [] for n in nodes}
    # The extra Lean source to be inserted into the root file,
    # containing (1) upstream nodes and (2) informal-only nodes,
    # whose positions cannot be determined.
    extra_nodes: list[NodeWithPos] = []

    # Prepend every upstream or informal node to the first node that uses it
    for node in nodes_topological_order:
        if (convert_upstream and is_upstream(node)) or (convert_informal and is_informal(node)):
            for other in nodes_topological_order:
                # Prepend to node that uses the upstream/informal node and is formalized without `sorry`
                # The reason for the latter is that, if the upstream node is inserted where it is not
                # used, the module containing the upstream node might not be imported, causing "unknown constant" errors
                if node.latex_label in other.uses and other.lean_ok:
                    prepends[other.name].append(node)
                    break
            else:
                extra_nodes.append(node)

    # All nodes that should be prepended to the given node.
    def all_prepends(node: NodeWithPos) -> Generator[NodeWithPos, None, None]:
        if node.name in prepends:
            for n in prepends[node.name]:
                yield from all_prepends(n)
                yield n

    # Main loop for adding @[blueprint] attributes to nodes
    modified_files: set[str] = set()
    modified_nodes: list[NodeWithPos] = []

    for node in nodes_location_order:
        if is_upstream(node) or is_informal(node):
            continue
        assert node.has_lean and node.file is not None and node.location is not None
        prepend_nodes = list(all_prepends(node))
        modify_source(
            node, Path(node.file), node.location, add_uses=add_uses,
            docstring_indent=docstring_indent, docstring_style=docstring_style,
            prepend=list(upstream_or_informal_to_lean(n) for n in prepend_nodes)
        )
        modified_files.add(node.file)
        modified_nodes.append(node)
        modified_nodes.extend(prepend_nodes)

    # Write extra nodes to the root file
    if extra_nodes:
        extra_nodes_lean = [upstream_or_informal_to_lean(n) for n in extra_nodes]
        extra_nodes_file = Path(root_file)
        logger.warning(
            f"Outputting some nodes to\n  {extra_nodes_file}\n" +
            "You may want to move them to appropriate locations."
        )
        if extra_nodes_file.exists():
            existing = extra_nodes_file.read_text()
        else:
            existing = ""
        extra_nodes_file.write_text(
            existing + "\n\n" +
            "\n\n".join(lean for lean in extra_nodes_lean) + "\n"
        )

        modified_files.add(root_file)
        modified_nodes.extend(extra_nodes)

    for file in modified_files:
        add_lean_architect_import(Path(file))

    # This should not be possible in the code above, assuming `nodes` has unique names
    assert len(set(n.name for n in modified_nodes)) == len(modified_nodes), "Duplicate nodes in modified_nodes"

    return modified_nodes
