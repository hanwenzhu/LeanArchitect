import uuid
from pathlib import Path
import re
from dataclasses import dataclass
from typing import Optional

from loguru import logger
from pydantic import BaseModel

from common import Node, NodePart, _quote


def read_latex_file(file: Path) -> str:
    """Read the LaTeX file at `file`, recursively resolving and inlining any `\\input{...}` commands."""
    root_dir = file.parent
    def _read(file: Path, seen: set[Path]) -> str:
        if file in seen:
            logger.warning(f"Circular \\input detected for file: {file}")
            return ""
        seen.add(file)
        text = file.read_text()
        def replace_input(match):
            input_path = match.group(1).strip()
            if not input_path.endswith(".tex"):
                input_path += ".tex"
            input_file : Path = root_dir / input_path
            if not input_file.exists():
                logger.warning(f"\\input file not found: {input_file}")
                return ""
            return _read(input_file, seen)
        text = re.sub(r"\\input\s*\{([^\}]*)\}", replace_input, text)
        return text
    return _read(file, set())


def find_and_remove_command(command: str, source: str) -> tuple[bool, str]:
    match = re.search(r"\\" + command + r"\b", source)
    source = re.sub(r"\\" + command + r"\b", "", source)
    return match is not None, source


def find_and_remove_command_arguments(command: str, source: str, sub_count: int = 0) -> tuple[list[str], str]:
    matches = re.findall(r"\\" + command + r"\s*\{([^\}]*)\}", source)
    values = [item.strip() for m in matches for item in m.split(",")]
    source = re.sub(r"\\" + command + r"\s*\{[^\}]*\}", "", source, count=sub_count)
    return values, source


def find_and_remove_command_argument(command: str, source: str) -> tuple[Optional[str], str]:
    args, source = find_and_remove_command_arguments(command, source, sub_count=1)
    if len(args) > 1:
        logger.warning(f"Multiple \\{command} arguments found: {', '.join(args)}; only using the first one.")
    return args[0] if args else None, source


@dataclass
class SourceInfo:
    label: Optional[str]
    uses: list[str]
    alsoIn: list[str]
    proves: Optional[str]
    leanok: bool
    notready: bool
    mathlibok: bool
    lean: Optional[list[str]]
    discussion: Optional[int]


def strip_empty_lines(text: str) -> str:
    text = re.sub(r"^(?:[ \t]*\r?\n)+", "", text)
    text = re.sub(r"(?:\r?\n[ \t]*)+$", "", text)
    return text


def parse_and_remove_blueprint_commands(source: str) -> tuple[SourceInfo, str]:
    """Parse and remove custom commands (\\label, plastexdepgraph, leanblueprint commands)."""
    # \label
    # We only look for \label in the outermost environment because inner environments may have their own labels.
    def remove_environments(source: str) -> str:
        # TODO: this is only approximate, e.g. it does not handle nested same environments correctly
        return re.sub(r"\\begin\s*\{(.*?)\}.*?\\end\s*\{\1\}", r"", source, flags=re.DOTALL)
    label, _ = find_and_remove_command_argument("label", remove_environments(source))
    source = source.replace(f"\\label{{{label}}}", "")  # remove \label from source manually
    # plastexdepgraph commands
    uses, source = find_and_remove_command_arguments("uses", source)
    alsoIn, source = find_and_remove_command_arguments("alsoIn", source)
    proves, source = find_and_remove_command_argument("proves", source)
    # leanblueprint commands
    leanok, source = find_and_remove_command("leanok", source)
    notready, source = find_and_remove_command("notready", source)
    mathlibok, source = find_and_remove_command("mathlibok", source)
    lean, source = find_and_remove_command_arguments("lean", source)
    discussion, source = find_and_remove_command_argument("discussion", source)
    source = strip_empty_lines(source)
    return SourceInfo(
        label=label,
        uses=uses,
        alsoIn=alsoIn,
        proves=proves,
        leanok=leanok,
        notready=notready,
        mathlibok=mathlibok,
        lean=lean,
        discussion=try_int(discussion)
    ), source


def try_int(s: Optional[str]) -> Optional[int]:
    if s is None:
        return None
    try:
        return int(s)
    except ValueError:
        return None


warned_verb = False
def process_source(source: str) -> tuple[SourceInfo, str]:
    source_info, source = parse_and_remove_blueprint_commands(source)
    global warned_verb
    if "\\verb" in source and not warned_verb:
        warned_verb = True
        logger.warning("Converting \\verb to \\Verb which is friendlier to macros.")
    source = source.replace("\\verb", "\\Verb")
    return source_info, source


class LatexSource(BaseModel):
    """The source codes of a node in the original LaTeX blueprint."""
    statements: list[str] = []
    proofs: list[str] = []


# NB: this is not used if --convert_informal is not set
def generate_new_lean_name(visited_names: set[str], base: Optional[str]) -> str:
    """Generate a unique Lean identifier."""
    if base is None:
        base = f"node_{uuid.uuid4().hex}"
    else:
        base = base.split(":")[-1].replace("-", "_").replace(" ", "_")
        if base and base[0].isdigit():
            base = "_" + base
    if base not in visited_names:
        return base
    return generate_new_lean_name(visited_names, f"{base}_{uuid.uuid4().hex}")


def parse_nodes(source: str, convert_informal: bool) -> tuple[list[Node], dict[str, LatexSource]]:
    """Parse the nodes in the LaTeX source."""
    match = re.search(r"\\usepackage\s*\[[^\]]*\bthms\s*=\s*([^,\]\}]*)", source)
    if match:
        depgraph_thm_types = match.group(1).strip().split("+")
    else:
        depgraph_thm_types = "definition+lemma+proposition+theorem+corollary".split("+")

    ENV_PATTERN = re.compile(
        r"\\begin\s*\{(" + "|".join(depgraph_thm_types + ["proof"]) + r")\}\s*(?:\[(.*?)\])?(.*?)\\end\s*\{\1\}",
        re.DOTALL
    )

    # Maps matches[i] to nodes
    match_idx_to_label: dict[int, Optional[str]] = {}

    # Parsed nodes
    nodes: list[Node] = []
    seen_lean_names: set[str] = set()
    seen_latex_labels: set[str] = set()

    # Maps LaTeX label to a canonical label, if two nodes have different \label but the same \lean
    label_alias: dict[str, str] = {}

    # Raw sources (statements, proofs) of each name, for modifying LaTeX later
    label_to_source: dict[str, LatexSource] = {}

    # Parse all theorem and definition statements
    for i, match in enumerate(ENV_PATTERN.finditer(source)):
        env, title, content = match.groups()

        if env not in depgraph_thm_types:
            continue
        # Skip if match is commented out
        if "%" in source[:match.span()[0]].split("\n")[-1].strip():
            continue

        source_info, node_source = process_source(content)

        label = source_info.label
        match_idx_to_label[i] = label
        if label is None:
            logger.warning(f"Ignoring node without \\label: {match.group(0)[:30]}...")
            continue
        if label in seen_latex_labels:
            logger.warning(f"Merging nodes with \\label{{{label}}} which occur in blueprint multiple times")
        seen_latex_labels.add(label)
        label_to_source.setdefault(label, LatexSource()).statements.append(match.group(0))

        if source_info.lean is not None:
            names = source_info.lean
        elif not convert_informal:
            # Ignore proof node in first pass
            continue
        else:
            names = [generate_new_lean_name(seen_lean_names, label)]

        for name in names:
            if name in seen_lean_names:
                for seen in nodes:
                    if seen.name == name:
                        logger.warning(f"Merging {seen.latex_label} and {label} which both have \\lean{{{name}}}")
                        seen.statement.uses |= set(source_info.uses)
                        label_alias[label] = seen.latex_label
                        label_to_source[seen.latex_label].statements.extend(label_to_source[label].statements)
                continue
            seen_lean_names.add(name)
            statement = NodePart(
                lean_ok=source_info.leanok,
                text=node_source,
                uses=set(source_info.uses),
                latex_env=env
            )
            node = Node(
                name=name,
                latex_label=label,
                statement=statement,
                proof=None,  # to be added in the next loop
                title=title,
                not_ready=source_info.notready,
                discussion=source_info.discussion,
            )
            nodes.append(node)

    label_to_nodes: dict[str, list[Node]] = {}
    for node in nodes:
        label_to_nodes.setdefault(node.latex_label, []).append(node)

    # Parse all proof statements
    for i, match in enumerate(ENV_PATTERN.finditer(source)):
        env, title, content = match.groups()

        if env != "proof":
            continue
        # Skip if match is commented out
        if "%" in source[:match.span()[0]].split("\n")[-1].strip():
            continue

        source_info, node_source = process_source(content)
        proves = source_info.proves
        if proves is not None:  # manually specified \proves in plastexdepgraph
            proved_label = proves
        else:
            if i - 1 in match_idx_to_label:
                proved_label = match_idx_to_label[i - 1]
                if proved_label is None:
                    continue
            else:
                logger.warning(f"Cannot determine the statement proved by: {node_source}")
                continue
        if proved_label in label_alias:
            proved_label = label_alias[proved_label]

        label_to_source[proved_label].proofs.append(match.group(0))

        if proved_label in label_to_nodes:
            for proved in label_to_nodes[proved_label]:
                if proved.proof is not None:
                    logger.warning(f"Proof of {proved_label} occurs in blueprint multiple times; merging.")
                    proved.proof.uses |= set(source_info.uses)
                    continue
                proved.proof = NodePart(
                    lean_ok=source_info.leanok,
                    text=node_source,
                    uses=set(source_info.uses),
                    latex_env=env
                )

    # Clear self-loops
    for node in nodes:
        node.statement.uses.discard(node.latex_label)
        if node.proof is not None:
            node.proof.uses.discard(node.latex_label)

    # Duplicate names should have been merged above
    assert len(set(n.name for n in nodes)) == len(nodes), "Duplicate Lean names in nodes found"

    return nodes, label_to_source


def get_bibliography_files(source: str) -> list[Path]:
    """Get the bibliography from the document."""
    bibs, _ = find_and_remove_command_arguments("bibliography", source)
    bibs = [Path(bib + ".bib") for bib in bibs]
    return bibs
