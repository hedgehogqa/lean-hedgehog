# lean-hedgehog

<img src="img/hedgehog-logo.svg" width="128" alt="">

Property-based testing for Lean 4.

```lean
import Hedgehog
open Hedgehog

def reverseReverse : Property Id := property do
  let xs ← forAll (Gen.list (.linear 0 100) Gen.alpha)
  xs.reverse.reverse === xs

#eval check reverseReverse "reverse reverse"
```

In Lean a property can be proved, and a proof beats any number of
tests.  Hedgehog is for where there is no proof, or not yet: it checks
the property on generated inputs and shrinks a failure to a small
counterexample.

- Integrated shrinking, the idea from [Erlang QuickCheck][eqc]: a
  generator carries its own shrinks, so there is no shrinker to write
  and a shrunk value keeps the generator's invariants.
- Systems with state, tested against a model, for
  [the bugs that only emerge from chaos][series]: commands as open
  types, or transitions as one closed type.

The guide is `USAGE`.  The examples are in `Examples/`, each with a bug
to find; `lake exe examples` runs them.

[eqc]: https://www.quviq.com/documentation/eqc/eqc_gen.html
[series]: https://blog.nikosbaxevanis.com/2024/12/01/model-based-stateful-testing-with-madhouse-rs/

## Installation

In `lakefile.toml`, on Lean 4.35.0 or later:

```toml
[[require]]
name = "hedgehog"
git = "https://github.com/hedgehogqa/lean-hedgehog"
rev = "v0.2.0"
```

## AI disclosure

lean-hedgehog was written with strong assistance from AI coding agents,
with humans leading the ideas.  This would not exist without
[haskell-hedgehog][haskell], written by hand.

- [Write you some QuickCheck][wysq] (2016): notes from learning how
  such a library works.
- [Gens N' Roses: Appetite for Reduction][talk] (YOW! 2017): Jacob
  Stanley on the design.

[haskell]: https://github.com/hedgehogqa/haskell-hedgehog
[wysq]: https://blog.nikosbaxevanis.com/2016/02/08/write-you-some-quickcheck/
[talk]: https://www.youtube.com/watch?v=LfD0DHqpeVQ

## In memory of Jacob Stanley

lean-hedgehog is dedicated to Jacob Stanley, author and co-founder of
Hedgehog, who passed away on 9 April 2023.
