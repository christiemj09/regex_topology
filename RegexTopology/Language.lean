/-
Copyright (c) 2026 Matt Christie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Christie
-/
module

public import Mathlib.Computability.Language

/-!
# Supplementary lemmas about `Language`
-/

@[expose] public section

namespace RegexTopology

variable {α : Type*}

/-- A word belongs to a singleton language exactly when it is that language's word. -/
@[simp]
theorem mem_singleton_language {x y : List α} : x ∈ ({y} : Language α) ↔ x = y :=
  Iff.rfl

end RegexTopology
