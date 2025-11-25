import subprocess
import re
import json
import sys
from typing import Optional, Literal

from loguru import logger

from pydantic import BaseModel, ConfigDict
from pydantic.alias_generators import to_camel


def _quote(s: str) -> str:
    """Quotes a string in double quotes."""
    return json.dumps(s, ensure_ascii=False)


class BaseSchema(BaseModel):
    """A Pydantic base model with camelCase aliases."""
    model_config = ConfigDict(
        alias_generator=to_camel,
        populate_by_name=True,
    )

# These classes are ported from Architect/Basic.lean

class NodePart(BaseSchema):
    lean_ok: bool
    text: str
    uses: set[str]
    latex_env: str


class Node(BaseSchema):
    name: str  # Lean identifier (unique)
    latex_label: str
    statement: NodePart
    proof: Optional[NodePart]
    not_ready: bool
    discussion: Optional[int]
    title: Optional[str]

    @property
    def uses(self) -> set[str]:
        return self.statement.uses | (self.proof.uses if self.proof is not None else set())

    @property
    def lean_ok(self) -> bool:
        return self.statement.lean_ok and (self.proof is None or self.proof.lean_ok)

    def to_lean_attribute(
        self,
        add_statement_text: bool = True, add_uses: bool = True,
        add_proof_text: bool = True, add_proof_uses: bool = True,
        docstring_indent: int = 2, docstring_style: Literal["hanging", "compact"] = "hanging"
    ) -> str:
        configs = []
        # See Architect/Attribute.lean for the options
        configs.append(_quote(self.latex_label))
        if self.title:
            configs.append(f"(title := {_quote(self.title)})")
        if add_statement_text and self.statement.text.strip():
            configs.append(f"(statement := {make_docstring(self.statement.text, indent=docstring_indent, style=docstring_style, start_column=len("  (statement := "))})")
        if add_uses and self.statement.uses:
            configs.append(f"(uses := [{_wrap_list([_quote(use) for use in self.statement.uses], indent=4, start_column=len('  (uses := ['))}])")
        if self.proof is not None:
            if add_proof_text and self.proof.text.strip():
                configs.append(f"(proof := {make_docstring(self.proof.text, indent=docstring_indent, style=docstring_style, start_column=len("  (proof := "))})")
            if add_proof_uses and self.proof.uses:
                configs.append(f"(proofUses := [{_wrap_list([_quote(use) for use in self.proof.uses], indent=4, start_column=len('  (proofUses := ['))}])")
        if self.not_ready:
            configs.append("(notReady := true)")
        if self.discussion:
            configs.append(f"(discussion := {self.discussion})")
        if self.proof is None and self.statement.latex_env != "definition" or self.proof is not None and self.statement.latex_env != "theorem":
            configs.append(f"(latexEnv := {_quote(self.statement.latex_env)})")
        config = "".join(f"\n  {config}" for config in configs)
        return f"blueprint{config}"

class Position(BaseSchema):
    line: int
    column: int

class DeclarationRange(BaseSchema):
    pos: Position
    end_pos: Position

class DeclarationLocation(BaseSchema):
    module: str
    range: DeclarationRange

class NodeWithPos(Node):
    has_lean: bool
    location: Optional[DeclarationLocation]
    file: Optional[str]


LEAN_MAX_COLUMNS = 100

def _indent(lines: list[str], indent: int) -> list[str]:
    if not lines:
        return []
    common_indent = min(len(line) - len(line.lstrip()) for line in lines if line.strip())
    dedented = [line[common_indent:] for line in lines]
    return [f"{' ' * indent}{line}" for line in dedented]

def _wrap(line: str, indent: Optional[int], start_column: int, indent_first_line: bool = True, latex_mode: bool = True) -> list[str]:
    """Wrap a single line of text to a list of indented lines.
    If indent is not provided, infer from the number of leading spaces.
    Respects LaTeX comments if latex_mode is True.
    """
    if indent is None:
        indent = len(line) - len(line.lstrip())
    is_comment = False
    words = line.lstrip().split(" ")
    if not words:
        return [""]
    res = []
    cur = (" " * indent if indent_first_line else "") + words[0]
    for word in words[1:]:
        if (start_column if not res else 0) + len(cur) + 1 + len(word) > LEAN_MAX_COLUMNS:
            res.append(cur)
            # If unescaped % is in the current line, then switch to is_comment
            if latex_mode and re.search(r"[^\\]%", cur):
                is_comment = True
            if is_comment:
                cur = " " * indent + "% " + word
            else:
                cur = " " * indent + word
        else:
            cur += " " + word
    res.append(cur)
    return res

def _wrap_list(items: list[str], indent: int, start_column: int) -> str:
    text = ", ".join(items)
    return "\n".join(_wrap(text, indent, start_column, latex_mode=False)).strip()

def make_docstring(text: str, indent: int = 0, style: Literal["hanging", "compact"] = "hanging", start_column: int = 0) -> str:
    # If fits in one line, then use /-- {text} -/
    if "\n" not in text.strip() and start_column + len(f"/-- {text.strip()} -/") <= LEAN_MAX_COLUMNS:
        return f"/-- {text.strip()} -/"

    # Remove common indentation
    lines = [line.rstrip() for line in text.splitlines()]
    lines = _indent(lines, indent)
    if style == "hanging":
        lines = [subline for line in lines for subline in _wrap(line, None, 0)]
    else:
        lines[-1] += " -/"
        lines = [
            subline
            for i, line in enumerate(lines)
            for subline in (_wrap(line, None, start_column + len("/-- "), indent_first_line=False) if i == 0 else _wrap(line, None, 0))
        ]
    text = "\n".join(lines)
    if style == "hanging":
        return f"/--\n{text}\n{' ' * indent}-/"
    else:
        return f"/-- {text}"
