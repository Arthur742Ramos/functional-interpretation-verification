import StructuralNormalForms

/-!
Confluence and reachable unique normal forms for the exact endpoint-indexed
ten-rule relation imported from StructuralReasons. No additional rewrite root
or comparison hypothesis is used.
-/
namespace StructuralReasons
universe u v
variable {V : Type u} {E : V → V → Type v}

/-- Any two forward descendants have a common forward descendant. -/
theorem ten_confluent {a b : V} {p q r : Reason E a b}
    (hpq : Steps true p q) (hpr : Steps true p r) :
    ∃ s, Steps true q s ∧ Steps true r s := by
  obtain ⟨nq, hqn, hnq⟩ := exists_normal true q
  obtain ⟨nr, hrn, hnr⟩ := exists_normal true r
  have he : reducedExpansion nq = reducedExpansion nr :=
    (steps_reducedExpansion (hpq.trans hqn)).symm.trans
      (steps_reducedExpansion (hpr.trans hrn))
  have hn := normal_expansion_injective hnq hnr he
  subst nr
  exact ⟨nq, hqn, hrn⟩

/-- Distinct reachable normal reason trees cannot occur. -/
theorem ten_reachable_normal_unique {a b : V} {p q r : Reason E a b}
    (hpq : Steps true p q) (hpr : Steps true p r)
    (hnq : Normal true q) (hnr : Normal true r) : q = r := by
  apply normal_expansion_injective hnq hnr
  exact (steps_reducedExpansion hpq).symm.trans (steps_reducedExpansion hpr)

/-- Every finite typed reason has exactly one reachable irreducible reason. -/
theorem ten_exists_unique_normal {a b : V} (p : Reason E a b) :
    ∃ q, (Steps true p q ∧ Normal true q) ∧
      ∀ r, Steps true p r ∧ Normal true r → r = q := by
  obtain ⟨q, hpq, hnq⟩ := exists_normal true p
  exact ⟨q, ⟨hpq, hnq⟩, fun r hr =>
    ten_reachable_normal_unique hr.1 hpq hr.2 hnq⟩

/-- The unique reachable normal reason spells exactly the invariant word. -/
theorem ten_normal_form_word {a b : V} (p : Reason E a b) :
    ∃ q, Steps true p q ∧ Normal true q ∧ Shape q (reducedExpansion p) ∧
      Words.Reduced (reducedExpansion p) := by
  obtain ⟨q, hpq, hnq⟩ := exists_normal true p
  obtain ⟨w, hsw⟩ := normal_shape hnq
  have hr := normal_shape_reduced hsw hnq
  have he : reducedExpansion p = w :=
    (steps_reducedExpansion hpq).trans (shape_action_word hsw hr)
  rw [he]
  exact ⟨q, hpq, hnq, hsw, hr⟩

end StructuralReasons
