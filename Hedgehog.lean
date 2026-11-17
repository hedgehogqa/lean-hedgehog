module

public import Hedgehog.Seed
public import Hedgehog.Shrink
public import Hedgehog.Tree
public import Hedgehog.Range
public import Hedgehog.Gen
public import Hedgehog.Property
public import Hedgehog.Runner
public import Hedgehog.StateMachine

/-!
# Hedgehog

Property-based testing with integrated shrinking, after Jacob Stanley's
Hedgehog for Haskell.  `import Hedgehog` and `open Hedgehog`; the file
USAGE is the guide.

- `Hedgehog.Gen`: generators, each with its shrinks.
- `Hedgehog.Range`: bounds that grow with the test's size.
- `Hedgehog.Property`: `forAll`, `===`, `ensure`, `annotate`.
- `Hedgehog.Runner`: `check`, `recheck`, reports.
- `Hedgehog.StateMachine`: model-based testing, transitions as one type.
-/
