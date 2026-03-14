import ArchitectTest.BlueprintAll.Basic

/-!
Theorems about `Color.mix`, importing `Basic`. No `@[blueprint]` attributes.
Tests that `--all` correctly picks up theorems and tracks sorry status.
-/

set_option warn.sorry false

namespace Color

/-- Mixing is commutative. -/
theorem mix_comm (a b : Color) : mix a b = mix b a := by
  cases a <;> cases b <;> rfl

/-- Associativity of mixing (sorry'd to test leanOk detection). -/
theorem mix_assoc (a b c : Color) : mix (mix a b) c = mix a (mix b c) := by
  sorry

/-- Mixing blue then red equals mixing red then blue.
This theorem uses `mix_comm` in its proof, testing dependency inference. -/
theorem mix_blue_red_comm : mix .blue .red = mix .red .blue :=
  mix_comm ..

end Color
