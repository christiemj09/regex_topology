/-
Copyright (c) 2026 Matt Christie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Christie
-/
module

public import Mathlib.Computability.DFA

import Mathlib.Data.Nat.Sqrt
import RegexTopology.Pumping

/-!
# A non-regular language
-/

@[expose] public section

namespace RegexTopology

variable {α : Type*}

/-- The words whose length is a perfect square. -/
def squareLengths : Language α := {w | IsSquare w.length}

/-- Over a nonempty alphabet, the words of square length do not form a regular language. -/
theorem not_isRegular_squareLengths [Nonempty α] :
    ¬ (squareLengths : Language α).IsRegular := by
  intro h
  obtain ⟨p, hp⟩ := exists_length_gap_of_isRegular h
  obtain ⟨y, ⟨r, hr⟩, hlt, hle⟩ :=
    hp (List.replicate (p * p) (Classical.arbitrary α)) ⟨p, by simp⟩
      (by simpa using Nat.le_mul_self p)
  simp only [List.length_replicate] at hlt hle
  exact Nat.not_exists_sq hlt (by grind) ⟨r, hr.symm⟩

/-- Over a nonempty alphabet, some language is not regular. -/
theorem exists_not_isRegular [Nonempty α] : ∃ L : Language α, ¬ L.IsRegular :=
  ⟨squareLengths, not_isRegular_squareLengths⟩

end RegexTopology
