import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

from loguru import logger

from common import Node, NodeWithPos
from parse_latex import read_latex_file, parse_nodes, get_bibliography_files
from modify_latex import write_latex_source
from modify_lean import write_blueprint_attributes


def main():
    parser = argparse.ArgumentParser(description="Convert existing leanblueprint file to LeanArchitect format.")
    parser.add_argument(
        "--libraries",
        nargs="*",
        help="The names of Lean libraries for conversion. " +
             "This is only used for adding imports to the LaTeX macros file."
    )
    parser.add_argument(
        "--modules",
        nargs="+",
        required=True,
        help="The names of Lean modules for conversion. " +
             "The blueprint nodes are assumed to be accessible from these modules, " +
             "and their (sub)modules will be modified to add @[blueprint] attributes."
    )
    parser.add_argument(
        "--nodes",
        nargs="*",
        help="The LaTeX labels of blueprint nodes to convert. If not provided, all nodes in the blueprint will be converted."
    )
    parser.add_argument(
        "--blueprint_root",
        type=str,
        default=None,
        help="Path to the blueprint root directory, which should contain web.tex and plastex.cfg (default: blueprint/src or blueprint)."
    )
    parser.add_argument(
        "--root_file",
        type=str,
        default="extra_nodes.lean",
        help="Path to a Lean file for outputting extra nodes."
    )
    # Optional parameters
    parser.add_argument(
        "--extract_only",
        action="store_true",
        help="Only extract the nodes and print them to stdout in JSON; no modification is made to the Lean source."
    )
    parser.add_argument(
        "--convert_informal",
        action="store_true",
        help="Convert informal-only nodes."
    )
    parser.add_argument(
        "--add_uses",
        action="store_true",
        help="Add `uses` and `proofUses` to all nodes (otherwise only adds to nodes with `sorry`)."
    )
    parser.add_argument(
        "--options",
        type=str,
        default=None,
        help="LeanOptions in JSON to pass to running the imports during add_position_info."
    )
    parser.add_argument(
        "--docstring_indent",
        type=int,
        default=4,
        help="The number of spaces to indent the `statement` and `proof` docstrings in `@[blueprint]`."
    )
    parser.add_argument(
        "--docstring_style",
        choices=["hanging", "compact"],
        default="compact",
        help="Whether to insert a line break after `/--` (hanging) or not (compact)."
    )

    args = parser.parse_args()

    logger.info("Converting blueprint to LeanArchitect format")

    # Determine blueprint root directory
    if args.blueprint_root is None:
        blueprint_root = Path("blueprint", "src")
        if not (blueprint_root / "web.tex").exists():
            blueprint_root = Path("blueprint")
            if not (blueprint_root / "web.tex").exists():
                raise FileNotFoundError("web.tex not found in blueprint or blueprint/src")
        blueprint_root = Path(blueprint_root)
    else:
        blueprint_root = Path(args.blueprint_root)

    # Read the blueprint LaTeX file
    logger.info(f"Reading blueprint LaTeX file {blueprint_root / 'web.tex'}")
    source = read_latex_file(blueprint_root / "web.tex")

    # Parse the document into nodes in dependency graph
    logger.info("Parsing nodes in blueprint LaTeX")
    nodes, label_to_raw_source = parse_nodes(source, args.convert_informal)
    if args.nodes:
        nodes = [node for node in nodes if node.latex_label in args.nodes]

    # Convert nodes to JSON
    logger.info("Converting nodes to JSON")
    nodes_json = json.dumps(
        [node.model_dump(mode="json", by_alias=True) for node in nodes],
        ensure_ascii=False
    )

    # Add position information to nodes by passing to a Lean script
    logger.info("Adding position information to nodes using `lake exe add_position_info`")
    add_position_info_command = [
        "lake", "exe", "add_position_info",
        "--imports", ",".join(args.modules),
    ]
    if args.options:
        add_position_info_command += ["--options", args.options]
    nodes_with_pos_json = subprocess.run(
        add_position_info_command,
        input=nodes_json,
        text=True,
        check=True,
        stdout=subprocess.PIPE,
        stderr=sys.stderr,
    ).stdout

    if args.extract_only:
        print(nodes_with_pos_json)
        return

    # Parse the JSON into NodeWithPos
    logger.info("Parsing JSON into NodeWithPos")
    nodes_with_pos = [
        NodeWithPos.model_validate(node) for node in json.loads(nodes_with_pos_json)
    ]

    # Write the blueprint attributes to Lean files
    logger.info("Writing @[blueprint] attributes to Lean files")
    modified_nodes = write_blueprint_attributes(
        nodes_with_pos, args.modules, args.root_file,
        args.convert_informal, True,  # Always convert upstream nodes
        args.add_uses, args.docstring_indent, args.docstring_style
    )

    # Write to LaTeX source
    logger.info("Replacing LaTeX nodes with \\inputleannode")
    write_latex_source(modified_nodes, label_to_raw_source, blueprint_root, args.libraries)


if __name__ == "__main__":
    main()
