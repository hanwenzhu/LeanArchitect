/-!
Test for `--all` mode: no `@[blueprint]` attributes anywhere.
This file defines basic types and is imported by `BlueprintAll.Theorems`.
-/

set_option warn.sorry false

/-- A simple type for testing. -/
inductive Color where
  | red : Color
  | blue : Color

namespace Color

/-- Mix two colors. -/
def mix (a b : Color) : Color :=
  match a, b with
  | red, red => red
  | blue, blue => blue
  | _, _ => red

private def helperFn : Color := .red

end Color
