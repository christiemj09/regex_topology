/-
Copyright (c) 2026 Matt Christie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Christie
-/
module

public import Mathlib.Computability.DFA

/-!
# Length consequences of the pumping lemma
-/

@[expose] public section

namespace RegexTopology

variable {α : Type*}

/-- In a regular language, every sufficiently long word has a strictly longer word in the
language, at most a bounded number of letters longer. -/
theorem exists_length_gap_of_isRegular {L : Language α} (hL : L.IsRegular) :
    ∃ p, ∀ x ∈ L, p ≤ x.length → ∃ y ∈ L, x.length < y.length ∧ y.length ≤ x.length + p := by
  obtain ⟨σ, _, M, rfl⟩ := hL
  refine ⟨Fintype.card σ, fun x hx hlen => ?_⟩
  obtain ⟨a, b, c, rfl, hab, hb, hpump⟩ := M.pumping_lemma hx hlen
  refine ⟨a ++ (b ++ b) ++ c, hpump ?_, ?_, ?_⟩
  · refine Language.append_mem_mul (Language.append_mem_mul rfl ?_) rfl
    simpa using Language.join_mem_kstar (l := {b}) (L := [b, b])
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, or_self, forall_eq]; exact rfl)
  · simpa using List.length_pos_of_ne_nil hb
  · simp only [List.length_append] at hab ⊢
    omega

end RegexTopology
