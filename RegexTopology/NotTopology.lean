/-
Copyright (c) 2026 Matt Christie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Christie
-/
module

public import Mathlib.Computability.DFA
public import Mathlib.Topology.Defs.Basic

import Mathlib.Topology.Order
import RegexTopology.NonRegular
import RegexTopology.Singleton

/-!
# Regular languages do not form a topology
-/

@[expose] public section

open Topology

namespace RegexTopology

variable {α : Type*}

/-- Over a nonempty alphabet, the regular languages are not the open sets of any topology. -/
theorem not_open_sets [Nonempty α] :
    ¬ ∃ t : TopologicalSpace (List α),
      ∀ L : Language α, IsOpen[t] (L : Set (List α)) ↔ L.IsRegular := by
  rintro ⟨t, ht⟩
  let := t
  have : DiscreteTopology (List α) :=
    discreteTopology_iff_isOpen_singleton.2 fun s => (ht {s}).2 (isRegular_singleton s)
  obtain ⟨L, hL⟩ := exists_not_isRegular (α := α)
  exact hL ((ht L).1 (isOpen_discrete _))

end RegexTopology
