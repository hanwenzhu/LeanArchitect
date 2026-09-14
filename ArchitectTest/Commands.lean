module

import Architect

public section

/-!
# Test

A dependency graph for testing.

```
              main_thm
             /         \
        path_A         path_B
        /    \            |
 lemma_A1  lemma_A2    lemma_B1
      |        |       /       \
 lemma_A3  lemma_A4  lemma_B2  lemma_B3
      \       /           \      / 
      core_lemma         util_lemma
          |
      base_def
```
-/

set_option warn.sorry false

namespace CommandsTest

/-- -/
@[expose] def base_def : Nat := 42

@[blueprint (statement := /-- The core lemma used by many paths. -/)
  (uses := [base_def])]
theorem core_lemma : base_def = 42 := rfl

@[blueprint (statement := /-- A utility lemma for path B. -/)]
theorem util_lemma : 1 + 1 = 2 := rfl

@[blueprint (statement := /-- Step A3, depends on core. -/)
  (uses := [core_lemma])]
theorem lemma_A3 : base_def + 0 = 42 := by sorry

@[blueprint (statement := /-- Step A4, depends on core. -/)
  (uses := [core_lemma])]
theorem lemma_A4 : base_def * 1 = 42 := by sorry

@[blueprint (statement := /-- Step B2, depends on util. -/)
  (uses := [util_lemma])]
theorem lemma_B2 : 2 = 1 + 1 := by rfl

@[blueprint (statement := /-- Step B3, depends on util. -/)
  (uses := [util_lemma])]
theorem lemma_B3 : 1 + 1 + 1 = 3 := by sorry

@[blueprint (statement := /-- Step A1, depends on A3. -/)
  (uses := [lemma_A3])]
theorem lemma_A1 : base_def + 0 + 0 = 42 := by sorry

@[blueprint (statement := /-- Step A2, depends on A4. -/)
  (uses := [lemma_A4])]
theorem lemma_A2 : base_def * 1 * 1 = 42 := by sorry

@[blueprint (statement := /-- Step B1, depends on B2 and B3. -/)
  (uses := [lemma_B2, lemma_B3])]
theorem lemma_B1 : 1 + 1 + 1 = 3 := by sorry

@[blueprint (statement := /-- Path A converges from A1 and A2. -/)
  (uses := [lemma_A1, lemma_A2])]
theorem path_A : base_def = 42 := by sorry

@[blueprint (statement := /-- Path B goes through B1. -/)
  (uses := [lemma_B1])]
theorem path_B : 1 + 2 = 3 := by sorry

@[blueprint (statement := /-- The main theorem, combining both paths. -/)
  (uses := [path_A, path_B])]
theorem main_thm : base_def = 42 := by sorry

@[blueprint (statement := /-- A corollary of the main theorem. -/)
  (uses := [main_thm])
  (notReady := true)]
theorem future_cor : base_def + 0 = 42 := by sorry

end CommandsTest

open CommandsTest

#blueprint_impact core_lemma

#blueprint_impact lemma_B1

#blueprint_status lemma_A2

#blueprint_status main_thm

#blueprint_incomplete

#blueprint_progress

set_option blueprint.all true

#show_blueprint
