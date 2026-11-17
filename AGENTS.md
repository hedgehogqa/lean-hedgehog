# AGENTS.md

Instructions for coding agents, and for anyone else, working on this
repository.  To use the library, read `USAGE` instead.

## The project

lean-hedgehog is a Lean 4 port of Haskell Hedgehog: property-based
testing with integrated shrinking, and model-based testing of stateful
systems in two styles.  It has no dependencies.  The toolchain is pinned
in `lean-toolchain`.

- `Hedgehog.lean`, `Hedgehog/`: the library, one module per concept.
  Each module's docstring says what it is and why it differs from the
  Haskell.
- `HedgehogTest.lean`, `HedgehogTest/`: the tests and their driver.
- `Examples.lean`, `Examples/`: the examples of `README.md`, runnable.
- `README.md`: what the library is.  `USAGE`: the guide.  `NEWS`: the
  user-visible changes.  `COPYING`: the license.

## Commands

    lake build              # Build the library.
    lake test               # Run every check.
    MADHOUSE=1 lake test    # The scenario check, and only it, must fail.
    lake exe examples       # Run the README's examples; each finds a bug.

## Rules

- `lake test` passes before every commit.
- Every public definition has a check in `HedgehogTest/`.  A generator
  has two: what it generates, and what it shrinks to.
- An example in `README.md` or `USAGE` is compiled against the library
  before it is committed.  Those of the README's Counterexamples section
  are `Examples/LeanVM.lean`, word for word; change both together.
- A user-visible change has a line in `NEWS`, and `USAGE` says how to
  use it.
- No `sorry`, `axiom`, `unsafe`, `implemented_by` or `native_decide`.
- Definitions are total.  `partial` is for a function whose termination
  depends on a function it is given, and its docstring says so.
- Library files are Lean modules: `module`, then `@[expose] public
  section`.  Test files are plain files with `import Hedgehog`.
- Do not claim what was not run.  Say what was verified and how, and
  what was not.
- Do not push to `master`, and do not rewrite pushed history, unless
  the maintainer asks.  Show work on a side branch.

## Style

Write prose and code in the style associated with Chris Wellons
(skeeto, `nullprogram.com`): precise, direct and economical, with simple
interfaces, understandable control flow, explicit behavior and minimal
abstraction.  Avoid ceremony, duplication and speculative complexity.
This applies to code, documentation, commit messages and explanations.

- Wrap prose, comments and code at 79 characters.
- A comment or docstring starts with an uppercase letter and ends with a
  period.
- Never use an em-dash.  Write `--`, or better, another sentence.
- Use clear, explicit names.
- Prefer small, reviewable changes.
- A docstring says what a definition is for and anything surprising
  about it, not how the code reads.
- Markdown stays plain: headings, lists, code, links.  No badges, no
  emoji, no tables where a list will do.
- Do not commit secrets, credentials, private keys or tokens.

## Lean notes

Things that cost time once already:

- `assert` is a keyword of `do` blocks, so the assertion is `ensure`.
  `example`, `nonrec` and `rec` are keywords too and cannot name
  definitions or parameters.
- Lean is strict.  A shrink tree suspends each child (`Unit → Tree α`),
  because a child may be a test run and the runner stops at the first
  that fails.  A generator cannot mention itself: recurse on a depth, or
  use `Gen.delay`.
- A `partial def` needs its result type inhabited from its parameters.
  Return a `List`, or take a value of the type.
- A monad cannot go under the tree (`GenT m`): the type would not be
  strictly positive.  Effects belong to the test, in `TestT m`.
- Lake does not resolve a `testDriver` with a hyphen in its name.
- A bare comparison such as `a > b` in a `List (String × Bool)` literal
  elaborates as a `Prop`; wrap it in `decide`.

## Commits

One commit per coherent concept.  The subject is imperative, as in:

    Set foo to bar

A body may follow a blank line: prose, or a short explanation, two or
three bullets, and an optional closing sentence.  It says why, not what
the diff already shows.

- Wrap every line, subject and trailer included, at 79 characters.
- Use real newlines, never a literal `\n`.  Write the message with a
  here-document or `git commit -F`.
- Review the staged diff before committing.

End with a trailer that names the model and the tool, when they can be
discovered from the environment, and nothing else:

    Model: <model> (<provider>)
    Tools: <tool> <version>

Leave the provider out when it is not known, and the trailer out when
the model or the tool is not.  Do not add `Co-Authored-By`.

## Review comments

One line each, direct, warm where possible, attached to the diff lines
they concern.  Do not wrap them: web interfaces render hard-wrapped
lines oddly.
