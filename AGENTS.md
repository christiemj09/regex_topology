# AGENTS.md

Guidance for AI agents working in this repository. See [README.md](README.md) for what is proved and where.

## Purpose

A Lean 4 / Mathlib formalization that the regular languages over a nonempty alphabet are neither the open sets nor
the closed sets of any topology on Σ*. It is also a project for learning Lean and formalization: explain new Lean
concepts and Mathlib conventions as they come up, and prefer community norms unless the maintainer chooses otherwise.

## Workflow

- **The maintainer makes all commits.** Prepare one commit-sized change at a time, verify it, and suggest a commit
  message. Running commands that touch the git index is fine.
- **Commit granularity:** one commit per step of the proof outline (e.g. "every singleton language is regular") or
  per coherent unit of supporting API (e.g. lemmas characterizing a definition's transitions). Not one commit per tiny
  lemma; not several outline steps in one commit. The history should read as a proof outline.
- **Draft outside the repo first.** Prototype a whole result in a scratch file, confirm it compiles, then bring it into
  the project one commit at a time.
- **Never reference `input/`** in committed files. It is gitignored, local-only material.

## Verifying a change

```sh
lake build                     # must finish with zero warnings: this runs the lakefile's Mathlib linters
lake env lean path/to/file.lean  # quick check of a scratch file; does NOT run the lakefile linters
```

Before calling a result done, check it in a scratch file that imports the module:

```lean
#print axioms RegexTopology.someTheorem  -- expect only [propext, Classical.choice, Quot.sound]; no sorryAx
```

`elan` may print `warning: could not canonicalize path` on every command; it is harmless.

## Lean conventions

- Every `.lean` file starts with the Mathlib-style header (copyright, Apache 2.0, `Authors:`), then `module`.
- `public import` only what declaration *statements* need; use plain `import` for anything used only in proofs.
- Wrap declarations in `@[expose] public section` and `namespace RegexTopology`.
- Register each new module in `RegexTopology.lean` (imports in alphabetical order).
- Follow Mathlib naming (`conclusion_of_hypothesis`, e.g. `singletonDFA_step_of_getElem?_eq`).
- Keep comments thin: a title-only module docstring and one- or two-line declaration docstrings. Longer explanation
  belongs in the README or `tex/`, not in source files.
- A plain `simp` that does not close its goal may only be followed by tactics that don't depend on its exact output
  (e.g. `omega`, `grind`); otherwise use `simp only [...]`. The flexible-tactic linter enforces this.

## Gotchas

- `Language α` is a `def` equal to `Set (List α)`, not an abbreviation. `rw` will not see through it; use `exact`
  (which checks up to definitional equality) or `change`.
- Mathlib has no simp lemma for `x ∈ ({y} : Language α) ↔ x = y`; use our `mem_singleton_language`
  (`RegexTopology/Language.lean`), which is `@[simp]`.
- The empty language is written `0` (Mathlib treats `Language α` as a semiring), not `∅`.
- Kleene-star notation `L∗` needs `open scoped Computability`.
- To reason about a topology `t` held in a variable, install it with `let := t` (not `letI`; a linter prefers `let`).

## Documents

- `README.md`: the entry point and table of contents for results. Keep it in sync when results are added or renamed.
- `tex/regex_topology.tex`: a plain-LaTeX proof document that follows the formalization. Each statement is tagged
  with its Lean declaration via `\lean{...}`; keep it in sync when results are added or renamed. Build with
  `tectonic tex/regex_topology.tex`, and view the PDF to check layout, not just that it compiles.
