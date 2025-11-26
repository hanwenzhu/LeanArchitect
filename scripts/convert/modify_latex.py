import re
from pathlib import Path

from loguru import logger

from parse_latex import LatexSource
from common import Node, NodeWithPos

def write_latex_source(
    nodes_with_pos: list[NodeWithPos],
    label_to_raw_source: dict[str, LatexSource],
    blueprint_root: Path,
    libraries: list[str]
):
    for node in nodes_with_pos:
        for file in blueprint_root.glob("**/*.tex"):
            file_content = file.read_text()
            # TODO: str.replace is not accurate, because multiple nodes can have the same proof string.
            # We should record the start/end positions and file names of the latex source instead.
            source = label_to_raw_source[node.latex_label]
            for s in source.statements:
                file_content = file_content.replace(s, f"\\inputleannode{{{node.latex_label}}}")
            for s in source.proofs:
                file_content = file_content.replace(s, "")
            file.write_text(file_content)

    # Add import to macros file
    macros_files_common = [
        blueprint_root / "macros" / "common.tex",
        blueprint_root / "preamble" / "common.tex",
        blueprint_root / "macro" / "common.tex",
    ]
    common_macros = "\n".join(f"\\input{{../../.lake/build/blueprint/library/{library}}}" for library in libraries)
    for file in macros_files_common:
        if file.exists():
            file.write_text(file.read_text() + "\n" + common_macros + "\n")
            break
    else:
        logger.warning(f"{macros_files_common[0]} not found; please add the following to anywhere in the start of LaTeX blueprint:\n{common_macros}")

    # macros_files_print = [
    #     blueprint_root / "macros" / "print.tex",
    #     blueprint_root / "preamble" / "print.tex",
    #     blueprint_root / "macro" / "print.tex",
    # ]
    # print_macros = ""
    # for file in macros_files_print:
    #     if file.exists():
    #         file.write_text(file.read_text() + "\n" + print_macros + "\n")
    #         break
    # else:
    #     logger.warning(f"{macros_files_print[0]} not found; please add the following to the macros file for print.tex:\n{print_macros}")

    # macros_files_web = [
    #     blueprint_root / "macros" / "web.tex",
    #     blueprint_root / "preamble" / "web.tex",
    #     blueprint_root / "macro" / "web.tex",
    # ]
    # web_macros = ""
    # for file in macros_files_web:
    #     if file.exists():
    #         file.write_text(file.read_text() + "\n" + web_macros + "\n")
    #         break
    # else:
    #     logger.warning(f"{macros_files_web[0]} not found; please add the following to the macros file for web.tex:\n{web_macros}")
