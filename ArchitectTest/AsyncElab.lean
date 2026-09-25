module

public import Lean
public meta import Std.Time.DateTime.Timestamp
import Architect

open Lean Elab Term Std.Time in
local elab "now_ms%" : term => do
  -- Synchronize env
  let env := (← getEnv).checked.get
  let hasC := env.constants.contains `c
  logInfo m!"Contains `c`: {hasC}"
  -- Get time
  let now ← Timestamp.now
  let ms := now.toMillisecondsSinceUnixEpoch.toInt.natAbs
  elabTerm (Syntax.mkNatLit ms) (mkConst ``Nat)

/-- info: Contains `c`: false -/
#guard_msgs in
def old := now_ms%

public theorem a : True := by /-- a -/ sleep 1000; trivial
public theorem b : True := by /-- b -/ sleep 1000; trivial
public theorem c : True := by /-- c -/ sleep 1000; trivial

/-- info: Contains `c`: true -/
#guard_msgs in
def new := now_ms%

open Lean Architect in
run_meta
  -- Running a, b, c should be all parallel and hence the time should be ≈1s and ≪2s
  unless new - old < 1100 do
    throwError "a, b, c were not elaborated in parallel: new - old = {new - old} ms (expected < 1100 ms)"
  assert! getProofDocString (← getEnv) ``a == "a"
  assert! getProofDocString (← getEnv) ``b == "b"
  assert! getProofDocString (← getEnv) ``c == "c"
