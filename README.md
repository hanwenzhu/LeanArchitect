# LeanArchitect

LeanArchitect is a tool for generating the blueprint data of a Lean project directly from Lean.

The blueprint is a high-level plan of a Lean project, consisting of a series of nodes (theorems and definitions) and the dependency relations between them.
The purpose of LeanArchitect is to make it easier to write the blueprint by generating blueprint data directly from Lean.

Start by annotating definitions and theorems in Lean with the `@[blueprint]` tag. They will then be exported to LaTeX, which you may then put in the blueprint.

This tool is built to complement [leanblueprint](https://github.com/PatrickMassot/leanblueprint) and its structure is inspired by [doc-gen4](https://github.com/leanprover/doc-gen4). The idea is inspired by [leanblueprint-extract](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/main/leanblueprint-extract).

## Instructions

First, install [leanblueprint](https://github.com/PatrickMassot/leanblueprint) and follow the instructions there to set up a blueprint project using `leanblueprint new`, if not already done. (See also instructions below for converting from an existing project.)

Add LeanArchitect to the lakefile. For example:

```toml
[[require]]
name = "LeanArchitect"
git = "https://github.com/hanwenzhu/LeanArchitect.git"
rev = "main"
```

To extract the blueprint for a module, first `import Architect` and then annotate key theorems and definitions in the file with `@[blueprint]`:

```lean
import Architect

@[blueprint "thm:my-theorem"]
theorem my_theorem : Foo Bar := by foo
```

(See also a full example below.)

Then input the extracted blueprint source to the blueprint document (typically, `blueprint/src/content.tex`):

```latex
% This makes the macros `\inputleanmodule` and `\inputleannode` available.
\input{../../.lake/build/blueprint/library/Example}

% Input the blueprint theorem `my_theorem`:
\inputleannode{thm:my-theorem}.

% You may also input an entire module:
% \inputleanmodule{Example.MyNat}
```

Then run:

```sh
# Generate the blueprint to .lake/build/blueprint
lake build :blueprint
# Build the blueprint using leanblueprint
leanblueprint pdf
leanblueprint web
```

If you see LaTeX errors here, you may need to manually fix some LaTeX content so that the extracted node compiles.

## Example

This example is hosted at [LeanArchitect-example](https://github.com/hanwenzhu/LeanArchitect-example). Consider the following `MyNat` API:

```lean
-- Example/MyNat.lean

import Architect

@[blueprint]
inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

@[blueprint "def:nat-add"
  (statement := /-- Natural number addition. -/)]
def add (a b : MyNat) : MyNat :=
  match b with
  | zero => a
  | succ b => succ (add a b)

@[simp, blueprint
  (statement := /-- For any natural number $a$, $0 + a = a$,
    where $+$ is \cref{def:nat-add}. -/)]
theorem zero_add (a : MyNat) : add zero a = a := by
  /-- The proof follows by induction. -/
  induction a <;> simp [*, add]

@[blueprint
  (statement := /-- For any natural numbers $a, b$,
    $(a + 1) + b = (a + b) + 1$. -/)]
theorem succ_add (a b : MyNat) : add (succ a) b = succ (add a b) := by
  /-- Proof by induction on $b$. -/
  sorry

@[blueprint
  (statement := /-- For any natural numbers $a, b$,
    $a + b = b + a$. -/)]
theorem add_comm (a b : MyNat) : add a b = add b a := by
  induction b with
  | zero =>
    have := trivial
    /-- The base case follows from \cref{MyNat.zero_add}. -/
    simp [add]
  | succ b ih =>
    /-- The inductive case follows from \cref{MyNat.succ_add}. -/
    sorry_using [succ_add]  -- the `sorry_using` tactic declares dependency

-- Additional content omitted

end MyNat
```

The (automatic) output of the above example Lean script is:

![Blueprint web](https://raw.githubusercontent.com/hanwenzhu/LeanArchitect-example/refs/heads/main/images/web.png)

With dependency graph:

![Depedency graph](https://raw.githubusercontent.com/hanwenzhu/LeanArchitect-example/refs/heads/main/images/depgraph.png)

## Specifying the blueprint

After tagging with `@[blueprint]`, LeanArchitect will:

1. Extract the statement and proof of a node from the `@[blueprint]` annotation and docstrings in the tactic proof.
2. Infer the dependencies of a node from the constants used in the statement or proof.
3. Infer whether the statement or proof is ready (i.e. `\leanok`) from whether it is sorry-free.

You may override the constants used in the statement or proof with the `uses` and `proofUses` options, or with the `using` tactic.

To view the extracted blueprint data of a node, use `@[blueprint?]`.

The supported options of `@[blueprint]` are:

```lean
@[blueprint
  "latex-label"             -- The LaTeX label to use for the node (default: Lean name)
  (statement := /-- ... -/) -- The statement of the node in LaTeX
  (hasProof := true)        -- If the node has a proof part (default: true if the node is a theorem)
  (proof := /-- ... -/)     -- The proof of the node in LaTeX (default: the docstrings in proof tactics)
  (uses := [a, "b"])        -- The dependencies of the node, as Lean constants or LaTeX labels (default: inferred)
  (proofUses := [a, "b"])   -- The dependencies of the proof of the node, as Lean constants or LaTeX labels (default: inferred)
  (title := "Title")        -- The title of the node in LaTeX
  (notReady := true)        -- Whether the node is not ready
  (discussion := 123)       -- The discussion issue number of the node
  (latexEnv := "lemma")     -- The LaTeX environment to use for the node (default: "theorem" or "definition")
]
```

## Informal-only nodes

At the start of a project, theorems or definitions are usually written only in LaTeX, and their statements are not ready to be formalized in Lean.
LeanArchitect supports mixing such *informal* nodes written in LaTeX with *formal* nodes written in Lean. Typically, the workflow of an entire project may look like this:

1. Write a blueprint in LaTeX
2. Set up a new Lean project with this blueprint
3. Formalize a theorem `my_theorem` from LaTeX into Lean, and tag it with `@[blueprint]`
4. Replace this theorem in LaTeX with `\inputleannode{my_theorem}`, and return to (3)

One utility script for automating the conversion is:

```sh
# Convert from a LaTeX node that has a Lean corresponding part (i.e. with `\lean`)
# to a `\inputleannode` command, and try to automatically tag the Lean part with
# `@[blueprint]`.
lake script run blueprintConvert --nodes <label of node>
```

## Converting from existing blueprint format

With a project that uses the existing leanblueprint format, there is a Python script that tries to convert to the LeanArchitect format.

Currently, this script depends on a recent version of Python with `loguru` and `pydantic` installed (install by `pip3 install loguru pydantic`).

First go to a clean branch **without any uncomitted changes**, to prevent overwriting any work you have done.

You can then convert to LeanArchitect format by adding `LeanArchitect` as a dependency to lakefile, run `lake update LeanArchitect`, ensure `leanblueprint checkdecls` works (i.e. all `\lean` are in Lean), and then run:

```sh
lake script run blueprintConvert
```

Note that this conversion is not idempotent, and for large projects it occasionally ends in some small syntax errors.

The informal-only nodes (nodes without `\lean`) are by default retained in LaTeX and not converted to Lean. If you want them to be converted, you may add `--convert_informal` to the command above, and then the script will convert them and save to the root Lean module.

The conversion will remove the `\uses` information in LaTeX and let LeanArchitect automatically infer dependencies in Lean, unless the code contains `sorry` (in which case `uses :=` and `proofUses :=` will be added). If `--add_uses` is specified then all `\uses` information is retained in Lean.

You may use `--blueprint_root <root>` to specify the path to your blueprint, if it is not the default. See `lake script run blueprintConvert -h` for all options.

## GitHub Actions integration

If building the blueprint is part of the GitHub CI action, then you need to run `lake build :blueprint` before building the blueprint,
so that the `\input` line above works. Here are some typical examples for doing this:

- If you use `.github/workflows/blueprint.yml` from leanblueprint, then add the following step:

```yaml
      # Before "Build blueprint and copy to `home_page/blueprint`":
      - name: Extract blueprint
        run: ~/.elan/bin/lake build :blueprint
```

- If you use `.github/workflows/build-project.yml` from LeanProject, then add this `build-args` option to `leanprover/lean-action`:

```yaml
      - name: Build the project
        uses: leanprover/lean-action@...
        with:
          use-github-cache: false
          build-args: :blueprint
```

## Extracting nodes in JSON

To extract the blueprint nodes in machine-readable format, run:

```sh
lake build :blueprintJson
```

The output will be in `.lake/build/blueprint`.

## Miscellaneous

- We encourage to use `\Verb` for inline verbatim code instead of `\verb`, and avoid using `\begin{verbatim}`. You also need to add

  ```latex
  \providecommand{\Verb}{\verb}
  ```

  to `blueprint/src/macros/web.tex` and

  ```latex
  \usepackage{fvextra}
  ```

  to `blueprint/src/macros/print.tex`. These are automatic if you use `blueprintConvert`.

## TODO

See `TODO`s in code.
