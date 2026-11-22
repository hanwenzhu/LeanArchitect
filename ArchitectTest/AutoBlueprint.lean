module

import Architect

public section

/-!
# Auto-Blueprint Test

Tests `set_option blueprint.all true` — declarations with docstrings
are automatically included in the blueprint without `@[blueprint]`.
-/

set_option blueprint.all true
set_option warn.sorry false

namespace AutoTest

/-- The base type. -/
inductive MyType : Type where
  | a : MyType
  | b : MyType

/-- A simple function on MyType. -/
def flip : MyType → MyType
  | .a => .b
  | .b => .a

/-- Flip is an involution. -/
theorem flip_flip (x : MyType) : flip (flip x) = x := by
  cases x <;> rfl

/-- Flip applied twice is identity (sorry version). -/
theorem flip_id (x : MyType) : flip (flip x) = x := by sorry

-- No docstring — should NOT appear in blueprint
theorem hidden_thm : True := trivial

-- Explicit @[blueprint] override should still work
/-- A custom node. -/
@[blueprint (title := "Custom Title")]
def custom : MyType := .a

end AutoTest

-- Auto-tagged declarations should appear in progress
-- MyType, flip, flip_flip, flip_id, custom = 5 nodes
-- hidden_thm has no docstring, so excluded
#blueprint_progress local nobreakdown

-- flip_id is incomplete (sorry), rest are formalized
#blueprint_incomplete local
