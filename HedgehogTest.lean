import HedgehogTest.Basic
import HedgehogTest.Counter
import HedgehogTest.Madhouse
import HedgehogTest.Generators
import HedgehogTest.Runner
import HedgehogTest.Readme

/-!
The test driver, run by `lake test`.  `MADHOUSE=1 lake test` runs the
scenario of `HedgehogTest.Madhouse` in madhouse mode, where it must fail.
-/

open Hedgehog HedgehogTest

/-- Print each fact with its verdict; `true` if all hold. -/
def expectAll (name : String) (facts : List (String × Bool)) : IO Bool := do
  IO.println s!"━━━ {name} ━━━"
  for (fact, holds) in facts do
    IO.println s!"  {if holds then "✓" else "✗"} {fact}"
  pure (facts.all (·.2))

def main : IO UInt32 := do
  let mode ← Mode.fromEnv
  let results := [
    ← expectAll "units" Basic.units,
    ← expectAll "seeds" Generators.seeds,
    ← expectAll "ranges" Generators.ranges,
    ← expectAll "trees" Generators.trees,
    ← expectAll "generators" Generators.generators,
    ← expectAll "generator shrinking" Generators.shrinking,
    ← expectAll "assertions" Runner.assertions,
    ← expectAll "runner" Runner.runner,
    ← expectAll "reports" Runner.rendering,
    ← expectAll "check and effects" (← Runner.effects),
    ← checkGroup "properties" Basic.properties,
    ← checkGroup "effects" [("a reference holds what was set",
        Basic.refHoldsWhatWasSet)],
    ← expectAll "shrinking" Basic.shrinking,
    ← checkGroup "state machine" [("counter agrees with its model",
        Counter.agrees)],
    ← expectAll "state machine shrinking" [
        ("a buggy counter shrinks to four increments", ← Counter.shrinks)],
    ← expectAll "state machine facts" (← Counter.facts),
    ← expectAll "scenario facts" Madhouse.facts,
    ← expectAll "README examples" Readme.facts,
    ← checkGroup s!"scenario ({repr mode})" [("counter stays within 100",
        Madhouse.counter mode)],
    ← expectAll "scenario shrinking" [
        ("madhouse shrinks to a sum of 101", Madhouse.shrinks)]]
  pure (if results.all id then 0 else 1)
