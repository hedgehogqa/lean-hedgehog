import Examples.LeanVM

/-!
Runs the examples of `Examples/LeanVM.lean`: `lake exe examples`, or
`MADHOUSE=1 lake exe examples` for the scenario in madhouse mode.

Each example has a bug, so a failed property with a small counterexample
is the result to expect.  The exit status is 0 when every bug was found;
the scenario's bug shows only in madhouse mode, and in the order given
it must pass.
-/

open Hedgehog

/-- Check a property on a random seed and print its report; whether it
failed if `buggy`, or passed if not. -/
def expect (buggy : Bool) (name : String) (p : Property Id) : IO Bool := do
  let r := (p.report (← Seed.random)).run
  IO.println (r.render name)
  pure <| match r.status with
    | .failed _ => buggy
    | .ok => !buggy
    | .gaveUp | .uncovered => false

def main : IO UInt32 := do
  let mode ← Mode.fromEnv
  IO.println "Each example has a bug: ✗ with a small counterexample is \
    the result to expect."
  let results := [
    ← expect true "size round trips" sizeRoundTrips,
    ← expect true "memory is write-once" memory.property,
    ← expect (mode == .madhouse) s!"pc stays in the program ({repr mode})"
      (program mode)]
  pure (if results.all id then 0 else 1)
