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

To view the extracted blueprint data, use `#show_blueprint` or `#show_blueprint theorem_name`.

The supported options of `@[blueprint]` are:

```lean
@[blueprint
  "latex-label"             -- The LaTeX label to use for the node (default: Lean name)
  (statement := /-- ... -/) -- The statement of the node in LaTeX
  (hasProof := true)        -- If the node has a proof part (default: true if the node is a theorem)
  (proof := /-- ... -/)     -- The proof of the node in LaTeX (default: the docstrings in proof tactics)
  (uses := [a, "b"])        -- The dependencies of the node, as Lean constants or LaTeX labels (default: inferred)
  (proofUses := [a, "b"])   -- The dependencies of the proof of the node, as Lean constants or LaTeX labels (default: inferred)
  (title := /-- Title -/)   -- The title of the node in LaTeX
  (notReady := true)        -- Whether the node is not ready
  (discussion := 123)       -- The discussion issue number of the node
  (latexEnv := "lemma")     -- The LaTeX environment to use for the node (default: "theorem" or "definition")
]
```

## Mixing informal and formal blueprints

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

First go to a clean branch **without any uncommitted changes**, to prevent overwriting any work you have done.

You can then convert to LeanArchitect format by adding `LeanArchitect` as a dependency to lakefile, run `lake update LeanArchitect`, ensure `leanblueprint checkdecls` works (i.e. all `\lean` are in Lean), and then run:

```sh
lake script run blueprintConvert
```

Note that this conversion occasionally ends in some small syntax errors.

Please attend to the warnings in the output of the conversion script above. They might be caused by an incomplete or nonstandard blueprint and may cause further problems in the pipeline.

The conversion will remove the `\uses` information in LaTeX and let LeanArchitect automatically infer dependencies in Lean, unless the code contains `sorry` (in which case `uses :=` and `proofUses :=` will be added). If `--add_uses` is specified then all `\uses` information is retained in Lean by `uses :=` and `proofUses :=`.

You may use `--blueprint_root <root>` to specify the path to your blueprint, if it is not the default.

See `lake script run blueprintConvert -h` for all options.

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

## Auto-blueprinting

By default, each declaration must be tagged with `@[blueprint]` to appear in the blueprint. To automatically include all declarations with docstrings, set `blueprint.all`:

```lean
set_option blueprint.all true

/-- Natural number addition. -/
def add (a b : Nat) : Nat := ...          -- auto-blueprinted

/-- Commutativity of addition. -/
theorem add_comm : add a b = add b a := ...  -- auto-blueprinted

theorem helper : ... := ...               -- NOT included (no docstring)
```

The statement text comes from the docstring, dependencies are auto-inferred, and the LaTeX environment is determined by the declaration kind (theorem → `theorem`, def/inductive → `definition`).

To override specific options for a declaration, add `@[blueprint ...]` explicitly — it takes precedence over auto-mode. An explicit `@[blueprint]` with no `statement := ...` also uses the declaration's docstring as its statement:

```lean
/-- Fermat's last theorem. -/
@[blueprint (title := "Taylor-Wiles") (notReady := true)]
theorem flt : ... := ...
```

### Enabling `blueprint.all` for the generated blueprint

`set_option blueprint.all true` written inside a `.lean` file only affects that file *interactively* (e.g. `#blueprint_progress`); it is not visible to `lake build :blueprint`, which runs as a separate process. To auto-blueprint a library in the generated blueprint, set the option in your `lakefile`'s `leanOptions` instead (this also drives the interactive commands, so you don't need the `set_option` line):

```lean
-- lakefile.lean
lean_lib MyProject where
  leanOptions := #[⟨`blueprint.all, true⟩]
```

```toml
# lakefile.toml
[[lean_lib]]
name = "MyProject"
leanOptions = [{ name = "blueprint.all", value = true }]
```

Note: `blueprint.all` only auto-blueprints the modules it is applied to; declarations from imported libraries (e.g. Mathlib) are never auto-blueprinted.

### Customizing the LaTeX environment

Auto-mode picks the LaTeX environment from the kernel-level kind of the declaration: theorem-kind → `\begin{theorem}`, def/inductive/opaque → `\begin{definition}`. Lean does not preserve the surface keyword across macro expansion — for example, Mathlib's `lemma` is a macro that desugars to `theorem` before LeanArchitect sees it, so auto-mode can't tell `lemma foo` apart from `theorem foo` and renders both as `\begin{theorem}`. Two ways to control this:

**Per-declaration override.** Explicit `@[blueprint ...]` takes precedence over auto-mode, so you can selectively pick a different environment:

```lean
@[blueprint (latexEnv := "lemma")]
lemma mul_one (a : G) : a * 1 = a := …
```

**Project-side `macro_rules`.** To avoid tagging each declaration, drop a small file into your project — e.g. `MyProject/Blueprint.lean` — that redirects the surface keyword so it carries the attribute automatically. Mathlib's `lemma` syntax has a single `declModifiers` slot that already includes the attribute position, so the simplest correct shape captures the optional `docComment` separately and lets the RHS attribute land in the rewritten `theorem`'s own modifiers:

```lean
-- MyProject/Blueprint.lean
/-
  Route Mathlib's `lemma` keyword to `\begin{lemma}` in the published
  blueprint. Without this, auto-mode sees only the kernel-level
  declaration kind (theorem-kind for `lemma`) and renders both
  `theorem foo` and `lemma foo` as `\begin{theorem}`.
-/

import Architect
import Mathlib.Tactic.Lemma

macro_rules
  | `(command| $[$doc:docComment]? lemma $id:declId $sig:declSig $val:declVal) =>
    `(command| $[$doc:docComment]? @[blueprint (latexEnv := "lemma")]
        theorem $id:declId $sig:declSig $val:declVal)
```

Then `import MyProject.Blueprint` at the top of any file where you write lemmas. After that, `lemma foo : … := …` and `/-- … -/ lemma foo : … := …` render as `\begin{lemma}` under `blueprint.all` with no per-declaration tags. Apply the same shape to `proposition`/`corollary` (or any other keyword you define) as needed. This recipe is intentionally kept project-side: the right keyword set is opinionated and the recipe avoids coupling LeanArchitect to Mathlib's surface syntax.

**Scope.** The recipe above covers bare and docstring'd lemmas — the typical blueprint case. It does *not* match lemmas with other modifiers (`private`, `noncomputable`, a pre-existing `@[…]`); for those, fall back to the per-declaration override.

## Progress statistics

To view formalization progress, use the `#blueprint_progress` command in Lean:

```lean
#blueprint_progress
-- Blueprint Progress
-- ────────────────────────
-- Total:           10 nodes
-- Formalized:    5/10  (50%)
-- Incomplete:    4/10  (40%)
-- Not ready:     1/10  (10%)
--
-- By module:
--   MyProject.Algebra   3/8  (38%)
--   MyProject.Topology  1/1  (100%)
--   MyProject.Main      1/1  (100%)
```

The command aggregates all blueprint nodes from the current module and its imports, with a per-module breakdown. Place it in a root file that imports the full project to get project-wide statistics. Variants:

- `#blueprint_progress` — project-wide with per-module breakdown.
- `#blueprint_progress nobreakdown` — project-wide without breakdown.
- `#blueprint_progress local` — current module only, with breakdown.
- `#blueprint_progress local nobreakdown` — current module only, without breakdown.

Or from the command line, passing one or more modules:

```sh
lake exe extract_blueprint progress MyProject.Module1 MyProject.Module2
```

Nodes are categorized into three mutually exclusive groups:
- **Formalized**: `sorry`-free, formalization complete.
- **Incomplete**: contains `sorry`, work in progress.
- **Not ready**: marked with `(notReady := true)`, not yet actionable.

## Node status

To inspect a specific declaration and its dependency subtree, use `#blueprint_status`:

```lean
#blueprint_status MyProject.add_comm
-- MyProject.add_comm
-- Status: Incomplete
--
-- Dependencies (3 nodes):
--   Formalized:   1/3  (33%)
--   Incomplete:   2/3  (67%)
--   Not ready:    0/3   (0%)
--
-- Blocking (2 nodes):
--   MyProject.succ_add  1/2  (50%)  Incomplete
--   MyProject.mul       0/1   (0%)  Incomplete
```

Or from the command line:

```sh
lake exe extract_blueprint status MyProject.add_comm MyProject.Module1
```

This works on any `@[blueprint]`-tagged declaration — theorems, lemmas, definitions, and inductives. The output shows:

- **Status**: the node's own formalization status.
- **Dependencies**: aggregate statistics for all transitive blueprint dependencies.
- **Blocking**: the subset of dependencies that are not yet formalized, sorted with not-ready nodes first.

If the node has no blueprint dependencies, the output shows `No dependencies.` instead.

Or from the command line:

```sh
lake exe extract_blueprint status MyProject.add_comm MyProject.Module1
```

The first argument is the fully qualified Lean name; the remaining arguments are the modules to load (the declaration must be reachable from these modules).

## Incomplete nodes

To see all incomplete nodes and how close they are to being unblocked, use `#blueprint_incomplete`:

```lean
#blueprint_incomplete
-- Incomplete (4 nodes):
--   MyProject.mul       0/0  (100%)
--   MyProject.succ_add  2/2  (100%)
--   MyProject.add_comm  3/4   (75%)
--   MyProject.mul_comm  1/2   (50%)
```

Each node shows how many of its blueprint dependencies are formalized. Nodes at **100%** are ready to work on immediately — all their dependencies are done. Nodes marked `(notReady := true)` are excluded.

Variants:

- `#blueprint_incomplete` — search all modules.
- `#blueprint_incomplete local` — search the current module only.

Or from the command line:

```sh
lake exe extract_blueprint incomplete MyProject.Module1 MyProject.Module2
```

### Impact analysis

To see the reverse dependencies of a node — which nodes depend on it and which would be unblocked by formalizing it — use `#blueprint_impact`:

```lean
#blueprint_impact MyProject.succ_add
```

Example output:

```
MyProject.succ_add
Status: Incomplete

Depended on by (2 nodes):
  MyProject.add_comm  3/4  (75%)  Incomplete
  MyProject.flt       0/2   (0%)  Not ready

Would unblock (1 node):
  MyProject.add_comm  3/4  (75%)  Incomplete
```

"Would unblock" lists incomplete nodes whose *only* remaining blocking dependency is the target node. Formalizing the target would make these nodes fully actionable (100% dependency completion in `#blueprint_incomplete`).

Variants:

- `#blueprint_impact name` — search all modules.
- `#blueprint_impact name local` — search the current module only.

Or from the command line:

```sh
lake exe extract_blueprint impact MyProject.succ_add MyProject.Module1 MyProject.Module2
```

## Extracting nodes in JSON

To extract the blueprint nodes in machine-readable format, run:

```sh
lake build :blueprintJson
```

The output will be in `.lake/build/blueprint`.

## Usage details

### Multiple Lean declarations

Multiple Lean declarations may correspond to the same node in the blueprint, by specifying the same label as:

```lean
@[blueprint "thm:a"] theorem a_part_one : ...
@[blueprint "thm:a"] theorem a_part_two : ...
```

The output will use `\lean{a_part_one, a_part_two}`, and `\leanok` only if both `a_part_one` and `a_part_two` are sorryless, and the `\uses` will also be merged.

A special case is for `to_additive` pairs of theorems:

```lean
@[to_additive (attr := blueprint "thm:b")] theorem b_mul : ...
```

should produce a single node with `\lean{b_mul, b_add}`.

### Declarations upstreamed to Mathlib

When a result moves to Mathlib, you can no longer edit its source to add `@[blueprint]`. Instead, tag
it from your own project with the `attribute` command, reusing the original label so the node keeps
its place in the graph:

```lean
attribute [blueprint "thm:my-result" (statement := /-- ... -/)] Mathlib.Path.To.my_result
```

Put this just before the first local node that depends on it, or in the root module if nothing local
does. Delete the old local copy in the same step.

A node is marked `\mathlibok` whenever all of its declarations resolve to a module under `Mathlib`,
`Init`, `Std`, `Batteries`, or `Lean`. This is read off the environment, not maintained by hand, so
the "already in Mathlib" status stays correct after every bump.

`blueprintConvert` applies the same rule during conversion: nodes imported from another project are
emitted as `attribute [blueprint] node_name` rather than a new `@[blueprint]` definition.

### Weird highlight in VS Code

If you notice the syntax highlighting makes entire blocks of Lean code a wrong color, it is likely that somewhere in a LaTeX comment there is something like `<a` which is parsed by VS Code as an HTML tag. Simply change it to `< a` and the highlights should then be fixed.

### Extracting entire Lean file to LaTeX

It is possible to convert an entire Lean file to LaTeX, by using `\inputleanmodule` in LaTeX,
which will convert all nodes in the order they are defined in Lean. For example:

```lean
-- Example.lean
@[blueprint (statement := /-- My definition. -/)] def my_def : ...
blueprint_comment /-- My comment about the definition. -/
@[blueprint (statement := /-- My theorem. -/)] theorem my_theorem : ...
```

Then in LaTeX `\inputleanmodule{Example}` will expand to

```
\begin{definition} \lean{my_def} My definition. \end{definition}

My comment about the definition.

\begin{theorem} \lean{my_def} My theorem. \end{theorem}
\begin{proof} ... \end{proof}
```

It is up to your design choice to use `\inputleanmodule` to have a blueprint that strictly follows the order in a Lean file,
or use multiple `\inputleannode` to include declarations individually for more flexibility.

### Suppressing a dependency relation

If in Lean, `@[blueprint] theorem B` uses `@[blueprint] theorem A`, and you wish this not to appear in the dependency graph, then you may write:

```lean
@[blueprint] theorem A := ...
@[blueprint (proofUses := [-A])] theorem B := ...
```

### Converting unformalized LaTeX nodes

In the `blueprintConvert` script, informal-only nodes (nodes without `\lean`) are by default not converted to Lean. You may add `--convert_informal` to `blueprintConvert` to convert them, which will output Lean declarations like `@[blueprint] def my_def : (sorry : Type) := sorry` and `@[blueprint] theorem my_theorem : (sorry : Prop) := sorry` in the Lean project.
