import HedgehogTest.Basic

/-!
Assertions, the journal, the configuration, and what the runner prints
and returns.
-/

namespace HedgehogTest.Runner

open Hedgehog

/-- A pure test's result and journal. -/
def run {α : Type} (test : TestT Id α) : Except Failure α × Journal :=
  Id.run (test.run.run #[])

def passes (test : TestT Id Unit) : Bool :=
  match (run test).1 with
  | .ok () => true
  | .error _ => false

/-- The message a pure test fails with. -/
def message (test : TestT Id Unit) : Option String :=
  match (run test).1 with
  | .ok () => none
  | .error e => some e.message

def assertions : List (String × Bool) := [
  ("success", passes success),
  ("failure", message failure == some "failure"),
  ("failWith", message (failWith "boom") == some "boom"),
  ("ensure true", passes (ensure true)),
  ("ensure false", message (ensure false) == some "ensure failed"),
  ("ensure with a message", message (ensure false "no") == some "no"),
  ("=== on equal values", passes ((1 : Nat) === 1)),
  ("=== on different values", message ((1 : Nat) === 2)
    == some "=== failed\n  lhs: 1\n  rhs: 2"),
  ("/== on different values", passes ((1 : Nat) /== 2)),
  ("/== on equal values", message ((1 : Nat) /== 1)
    == some "/== failed\n  lhs: 1\n  rhs: 1"),
  ("bytesHex", bytesHex ⟨#[0, 10, 255]⟩ == "000aff"
    && bytesHex .empty == ""),
  ("=== on the results of a decoder", passes
    ((.ok 1 : Except String Nat) === .ok 1)
      && !passes ((.ok 1 : Except String Nat) === .ok 2)
      && !passes ((.ok 1 : Except String Nat) === .error "no")
      && passes ((.error "no" : Except String Nat) === .error "no")),
  ("tripping through a decoder into Except", passes (tripping (12 : Nat)
    toString fun s => (s.toNat?.elim (.error "no") .ok : Except String Nat))),
  ("tripping round trip",
    passes (tripping (12 : Nat) toString String.toNat?)),
  ("tripping failure",
    message (tripping (12 : Nat) (fun _ => "x") String.toNat?)
      == some "=== failed\n  lhs: none\n  rhs: some 12"),
  ("annotate", (run (annotate "a" *> annotate "b")).2
    == #[.note "a", .note "b"]),
  ("the journal survives a failure",
    (run (annotate "a" *> failure (α := Unit))).2 == #[.note "a"]),
  ("a failure ends the test",
    (run (failure (α := Unit) *> annotate "a")).2 == #[]),
  ("hang", hang 2 "a\nb\nc" == "a\n  b\n  c")]

def logged : Property Id := property do
  let n ← forAllWith (fun n => s!"<{n}>") (Gen.nat (.constant 7 7))
  annotate "after"
  let m ← forAll (Gen.nat (.constant 8 8))
  n === m

def counts (ok : Bool) : Property Id := property do
  let _ ← forAll (Gen.nat (.linear 0 100))
  ensure ok

def halfDiscarded : Property Id := property do
  let n ← forAll (Gen.nat (.linear 0 100))
  if n % 2 == 1 then discard

def large : Property Id := property do
  let n ← forAll (Gen.nat (.linear 0 1000))
  ensure (n < 500)

def throws : Property IO := propertyM do
  pure do
    evalIO (throw (IO.userError "boom") : IO Unit)

def ioFails : Property IO := propertyM do
  let n ← forAll (Gen.nat (.linear 0 1000))
  pure do
    let r ← IO.mkRef n
    ensure ((← r.get) < 500)

/-- The sizes the runner uses, in order. -/
def sizes : List Nat :=
  (List.range 250).foldl (init := []) fun seen i =>
    let p : Property Id := property do
      let size ← forAll (Gen.sized pure)
      ensure (size != i % 100 || seen.length != i)
    match (p.withTests (i + 1) |>.report (Seed.ofNat 0)).status with
    | .failed _ => seen ++ [i % 100]
    | _ => seen

def failed (r : Report) : Option Counterexample :=
  match r.status with
  | .failed c => some c
  | _ => none

/-- A third of the cases are small; the minimum asked of them varies. -/
def classified (minimum : Nat) : Property Id := property do
  let n ← forAll (Gen.nat (.constant 0 2))
  cover minimum "small" (n == 0)
  classify "large" (n == 2)
  label "any"
  collect (n == 1)

/-- A class named twice in one test case. -/
def twice : Property Id := property do
  cover 10 "a" false
  cover 60 "a" true
  label "a"

/-- A class that only the even cases name, each of them in it. -/
def halfNamed (minimum : Nat) : Property Id := property do
  let n ← forAll (Gen.nat (.constant 0 999))
  if n % 2 == 0 then cover minimum "even" true

/-- The count of a class of a report. -/
def countOf (r : Report) (name : String) : Option Nat :=
  (r.coverage.find? (·.name == name)).map (·.count)

def coverage : List (String × Bool) :=
  let r := ((classified 20).withTests 300 |>.report (Seed.ofNat 0)).run
  let low := ((classified 90).withTests 300 |>.report (Seed.ofNat 0)).run
  let two := (twice.report (Seed.ofNat 0)).run
  let none := ((counts true).report (Seed.ofNat 0)).run
  let labelled := ((property do label "a"; failure).report
    (Seed.ofNat 0)).run
  let third (n : Option Nat) := n.any fun n => 70 ≤ n && n ≤ 130
  [("the journal has the class", (run (cover 5 "a" true)).2
      == #[.label "a" 5 true]),
   ("classify asks for no minimum", (run (classify "a" false)).2
      == #[.label "a" 0 false]),
   ("label counts every case", (run (label "a")).2
      == #[.label "a" 0 true]),
   ("collect names the value", (run (collect (3 : Nat))).2
      == #[.label "3" 0 true]),
   ("no class, no coverage", none.coverage == #[]),
   ("classes are in the order they were named",
     r.coverage.toList.map (·.name) == ["small", "large", "any", "false",
       "true"]),
   ("cover counts the cases that are in the class",
     third (countOf r "small")),
   ("classify counts them too", third (countOf r "large")),
   ("label counts every case of the run", countOf r "any" == some 300),
   ("collect counts each value",
     (do pure ((← countOf r "true") + (← countOf r "false"))) == some 300),
   ("a minimum that is met passes", r.ok && r.tests == 300),
   ("a minimum that is not met fails",
     low.status == .uncovered && !low.ok && low.tests == 300),
   ("an unmet minimum has no counterexample", (failed low).isNone),
   ("a class named twice is counted once", countOf two "a" == some 100),
   ("a class named twice keeps the greater minimum",
     two.coverage.map (·.minimum) == #[60] && two.ok),
   ("a failing case is not counted", labelled.coverage == #[]
     && (failed labelled).isSome),
   ("recheck gives the classes of its case and asks no minimum",
     let one := ((classified 90).recheck 10 (Seed.ofNat 0)).run
     one.ok && countOf one "any" == some 1),
   ("a case that does not name a class counts against its minimum",
     ((halfNamed 30).withTests 300 |>.report (Seed.ofNat 0)).run.ok
       && ((halfNamed 70).withTests 300 |>.report (Seed.ofNat 0)).run.status
         == .uncovered),
   ("exactly the minimum is enough",
     Coverage.sufficient #[⟨"a", 25, 25⟩] 100
       && !Coverage.sufficient #[⟨"a", 25, 24⟩] 100),
   ("no test, no shortfall", Coverage.sufficient #[⟨"a", 25, 0⟩] 0)]

def runner : List (String × Bool) := [
  ("a hundred tests by default",
    ((counts true).report (Seed.ofNat 0)).run == ⟨100, 0, .ok, #[]⟩),
  ("withTests", ((counts true).withTests 7 |>.report (Seed.ofNat 0)).run
    == ⟨7, 0, .ok, #[]⟩),
  ("withTests 0", ((counts false).withTests 0 |>.report (Seed.ofNat 0)).run
    == ⟨0, 0, .ok, #[]⟩),
  ("a failure stops the run",
    ((counts false).report (Seed.ofNat 0)).tests == 0),
  ("discards are counted",
    let r := (halfDiscarded.report (Seed.ofNat 0)).run
    r.ok && r.tests == 100 && r.discards > 0),
  ("withDiscards",
    let r := (halfDiscarded.withDiscards 3 |>.report (Seed.ofNat 0)).run
    r.status == .gaveUp && r.discards == 3),
  ("the journal is in order",
    (failed (logged.report (Seed.ofNat 0))).map (·.journal)
      == some #[.input "<7>", .note "after", .input "8"]),
  ("the failure is kept",
    (failed (logged.report (Seed.ofNat 0))).map (·.failure.message)
      == some "=== failed\n  lhs: 7\n  rhs: 8"),
  ("withShrinks 0 reports the first failure",
    (List.range 20).all fun i =>
      (failed (large.withShrinks 0 |>.report (Seed.ofNat i))).any
        (·.shrinks == 0)),
  ("withShrinks bounds the shrinks", (List.range 20).all fun i =>
    (failed (large.withShrinks 2 |>.report (Seed.ofNat i))).any
      (·.shrinks ≤ 2)),
  ("shrinks are counted", (List.range 20).all fun i =>
    (failed (large.report (Seed.ofNat i))).any fun c =>
      c.journal == #[.input "500"] && c.shrinks > 0),
  ("the size starts at 0 and wraps after 99",
    sizes.take 3 == [0, 1, 2] && (sizes.drop 99).take 3 == [99, 0, 1]),
  ("recheck of a passing case",
    ((counts true).recheck 10 (Seed.ofNat 0)).run == ⟨1, 0, .ok, #[]⟩),
  ("recheck of a discarded case", (List.range 20).any fun i =>
    (halfDiscarded.recheck 50 (Seed.ofNat i)).run == ⟨0, 1, .gaveUp, #[]⟩),
  ("different seeds give different cases",
    (failed (large.withShrinks 0 |>.report (Seed.ofNat 1))).map (·.journal)
      != (failed (large.withShrinks 0 |>.report (Seed.ofNat 2))).map
        (·.journal))]

def sample : Counterexample :=
  ⟨2, ⟨1, 2⟩, 1, #[.input "[0,\n 1]", .note "n"], ⟨"boom\nagain"⟩⟩

def rendering : List (String × Bool) := [
  ("ok", Report.render "p" ⟨100, 0, .ok, #[]⟩
    == "  ✓ p passed 100 tests."),
  ("one test", Report.render "p" ⟨1, 0, .ok, #[]⟩
    == "  ✓ p passed 1 test."),
  ("classes, in the order of their names", Report.render "p"
      ⟨200, 0, .ok, #[⟨"small", 0, 1⟩, ⟨"large", 10, 200⟩,
        ⟨"half", 50, 100⟩]⟩
    == "  ✓ p passed 200 tests.\n     50.0% half, at least 50%\n    \
      100.0% large, at least 10%\n      0.5% small"),
  ("insufficient coverage", Report.render "p" ⟨100, 0, .uncovered,
      #[⟨"rare", 10, 3⟩, ⟨"any", 0, 100⟩]⟩
    == "  ✗ p passed 100 tests, with insufficient coverage.\n    \
      100.0% any\n      3.0% rare, at least 10% ✗"),
  ("classes of no test", Report.render "p" ⟨0, 0, .ok, #[⟨"a", 0, 0⟩]⟩
    == "  ✓ p passed 0 tests.\n      0.0% a"),
  ("gave up", Report.render "p" ⟨3, 100, .gaveUp, #[]⟩
    == "  ⚐ p gave up after 100 discards, passed 3 tests."),
  ("failed", Report.render "p" ⟨0, 0, .failed sample, #[]⟩
    == "  ✗ p failed after 1 test and 1 shrink.\n\n    \
        forAll [0,\n            1]\n    n\n    boom\n    again\n\n    \
        This failure can be reproduced by running:\n    \
        > recheck 2 ⟨1, 2⟩ <property>"),
  ("failed, plural", (Report.render "p"
    ⟨4, 0, .failed { sample with shrinks := 3 }, #[]⟩).startsWith
      "  ✗ p failed after 5 tests and 3 shrinks.")]

/-- Whether the action throws an error that mentions `text`. -/
def throwsWith (text : String) (action : IO Unit) : IO Bool := do
  try
    action
    pure false
  catch e =>
    pure (((toString e).splitOn text).length > 1)

/-- What the action prints, and its result. -/
def captured {α : Type} (action : IO α) : IO (String × α) :=
  IO.FS.withIsolatedStreams action

def effects : IO (List (String × Bool)) := do
  let thrown ← throws.report (Seed.ofNat 0)
  let io ← (List.range 20).allM fun i => do
    match failed (← ioFails.report (Seed.ofNat i)) with
    | some c =>
      let again ← ioFails.recheck c.size c.seed
      pure (c.journal == #[.input "500"] && again.status == .failed c)
    | none => pure false
  let (passed, ()) ← captured (check (counts true) "name")
  let (seeded, ()) ← captured
    (check (counts true) "name" (seed := some (.ofNat 1)))
  let (rechecked, ()) ← captured (recheck 3 (.ofNat 1) (counts true) "name")
  let (group, groupOk) ← captured
    (checkGroup "group" [("good", counts true), ("bad", counts false)])
  let (goodGroup, goodOk) ← captured
    (checkGroup "group" [("good", counts true)])
  let (_, lowOk) ← captured
    (checkGroup "group" [("low", classified 90)])
  let both := [("good", counts true), ("bad", counts false)]
  let (only, onlyOk) ← captured (checkGroup "group" both { only := ["oo"] })
  let (nothing, noneOk) ← captured
    (checkGroup "group" both { only := ["x"] })
  let (_, findingsOk) ← captured
    (checkGroup "group" [("bad", counts false)] (mustFail := true))
  let (_, fixedOk) ← captured (checkGroup "group" both (mustFail := true))
  let (_, gaveUpOk) ← captured (checkGroup "group"
    [("gave up", halfDiscarded.withDiscards 1)] (mustFail := true))
  let (again, againOk) ← captured (checkGroup "group" both
    { only := ["good"], recheck := some (3, .ofNat 1) })
  let unset := (← IO.getEnv "HEDGEHOG_ONLY").isNone
    && (← IO.getEnv "HEDGEHOG_RECHECK").isNone
  let fromEnv ← if unset then (· == {}) <$> Selection.fromEnv else pure true
  let lifted ← (counts false).lift.report (Seed.ofNat 0)
  let sampled ← (List.range 20).allM fun _ => do
    pure ((← Gen.sample (Gen.sized pure) 77) == 77
      && (← Gen.sample (Gen.sized pure)) == 30)
  pure [
    ("evalIO turns an exception into a failure",
      (failed thrown).map (·.failure.message) == some "exception: boom"),
    ("an IO property shrinks and rechecks", io),
    ("check prints a pass", passed == "  ✓ name passed 100 tests.\n"),
    ("check takes a seed", seeded == "  ✓ name passed 100 tests.\n"),
    ("check throws a failure",
      ← throwsWith "✗ name failed after 1 test"
        (check (counts false) "name")),
    ("check throws when it gives up", ← throwsWith "⚐ name gave up"
      (check (halfDiscarded.withDiscards 1) "name" (seed := some (.ofNat 0)))),
    ("check throws on insufficient coverage",
      ← throwsWith "✗ name passed 100 tests, with insufficient coverage"
        (check (classified 90) "name" (seed := some (.ofNat 0)))),
    ("checkGroup fails on insufficient coverage", !lowOk),
    ("check runs an IO property",
      ← throwsWith "exception: boom" (check throws "name")),
    ("recheck prints a pass", rechecked == "  ✓ name passed 1 test.\n"),
    ("recheck throws a failure", ← throwsWith "✗ name failed"
      (recheck 3 (.ofNat 1) (counts false) "name")),
    ("checkGroup reports a failure", !groupOk
      && group.startsWith
        "━━━ group ━━━\n  ✓ good passed 100 tests.\n  ✗ bad"),
    ("checkGroup checks only the properties selected", onlyOk
      && only == "━━━ group ━━━\n  ✓ good passed 100 tests.\n"),
    ("checkGroup with nothing selected prints nothing", noneOk
      && nothing == ""),
    ("a group that must fail passes when each property fails",
      findingsOk),
    ("a group that must fail fails when a property passes", !fixedOk),
    ("a group that must fail fails when a property gives up", !gaveUpOk),
    ("checkGroup rechecks the one test case of a selection", againOk
      && again == "━━━ group ━━━\n  ✓ good passed 1 test.\n"),
    ("a selection reads the numbers of a report line",
      Selection.parseRecheck "26 16002631331520349156 1625543224293002313"
        == some (26, ⟨16002631331520349156, 1625543224293002313⟩)
        && Selection.parseRecheck "26 1" == none
        && Selection.parseRecheck "a 1 2" == none),
    ("a selection with no name selects every property",
      ({} : Selection).selects "any"
        && ({ only := ["a", "b"] } : Selection).selects "xbx"
        && !({ only := ["a", "b"] } : Selection).selects "xcx"),
    ("an environment that asks for nothing selects every property",
      fromEnv),
    ("a lifted pure property fails as it did", (failed lifted).isSome
      && lifted == ((counts false).report (Seed.ofNat 0)).run),
    ("Gen.sample takes a size, 30 unless given", sampled),
    ("checkGroup reports a pass", goodOk
      && goodGroup == "━━━ group ━━━\n  ✓ good passed 100 tests.\n")]

end HedgehogTest.Runner
