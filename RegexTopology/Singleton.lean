/-
Copyright (c) 2026 Matt Christie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Christie
-/
module

public import Mathlib.Computability.DFA

/-!
# Singleton languages are regular
-/

@[expose] public section

namespace RegexTopology

variable {α : Type*} [DecidableEq α]

/-- A DFA accepting exactly the word `s`. State `some i` means the first `i` letters of `s` have
been read; `none` is a dead state. -/
def singletonDFA (s : List α) : DFA α (Option (Fin (s.length + 1))) where
  step
    | some i, a => if h : s[(i : ℕ)]? = some a then some ⟨i + 1, by grind⟩ else none
    | none, _ => none
  start := some 0
  accept := {some (Fin.last _)}

/-- Once in the dead state, `singletonDFA s` stays there. -/
theorem singletonDFA_evalFrom_none (s x : List α) : (singletonDFA s).evalFrom none x = none := by
  induction x with
  | nil => rfl
  | cons a x ih => exact ih

/-- The dead state of `singletonDFA s` accepts no words. -/
theorem singletonDFA_acceptsFrom_none (s : List α) : (singletonDFA s).acceptsFrom none = 0 := by
  ext x
  rw [DFA.mem_acceptsFrom, singletonDFA_evalFrom_none]
  simp [singletonDFA]

/-- Reading the next letter of `s` advances `singletonDFA s` by one state. -/
theorem singletonDFA_step_of_getElem?_eq {s : List α} {i : Fin (s.length + 1)} {a : α}
    (h : s[(i : ℕ)]? = some a) :
    (singletonDFA s).step (some i) a = some ⟨i + 1, by grind⟩ := by
  simp [singletonDFA, h]

/-- Reading any other letter sends `singletonDFA s` to the dead state. -/
theorem singletonDFA_step_of_getElem?_ne {s : List α} {i : Fin (s.length + 1)} {a : α}
    (h : s[(i : ℕ)]? ≠ some a) : (singletonDFA s).step (some i) a = none := by
  simp [singletonDFA, h]

end RegexTopology
