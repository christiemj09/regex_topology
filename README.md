# Topological Results for Regular Languages

Hi there! 👋 This repository is a place for me to explore the topological properties of regular languages
and related topics as a way to become acquainted with mathematical formalization and the Lean Programming Language.
Hello, Lean! 🤓 I intend to post formalizations and paper lists as I become more familiar and develop the repository more.

## Results

Over any nonempty alphabet Σ, the regular languages are neither the open sets nor the closed sets of any topology on Σ*.

| Result | Lean declaration | File |
|---|---|---|
| Every singleton language `{s}` is regular | `isRegular_singleton` | [`Singleton.lean`](RegexTopology/Singleton.lean) |
| In a regular language, every long enough word has a strictly longer word in the language, at most a bounded number of letters longer | `exists_length_gap_of_isRegular` | [`Pumping.lean`](RegexTopology/Pumping.lean) |
| The words of square length form a non-regular language | `not_isRegular_squareLengths` | [`NonRegular.lean`](RegexTopology/NonRegular.lean) |
| The regular languages are not the open sets of any topology on Σ* | `not_open_sets` | [`NotTopology.lean`](RegexTopology/NotTopology.lean) |
| The regular languages are not the closed sets of any topology on Σ* | `not_closed_sets` | [`NotTopology.lean`](RegexTopology/NotTopology.lean) |

If the regular languages were the open sets of a topology, every singleton would be open, so every language would be
open and hence regular, which is false. Regular languages are closed under complement, so the closed-set case reduces
to the open-set case.

The alphabet must be nonempty: if Σ = ∅, then Σ* = {ε}, every language is regular, and the regular languages form
a topology. The alphabet need not be finite.

## Building

With [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get  # download prebuilt Mathlib
lake build
```

## AI Disclaimer

I am using Claude to write Lean code and to answer questions I have about the mathematics I encounter.
