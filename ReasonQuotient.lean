import ReasonCongruence

/-! A correspondence of quotient hom-sets only; no groupoid structure is defined. -/
namespace StructuralReasons
universe u v
variable {V : Type u} {E : V → V → Type v}
open Words

/-- Every composable signed word is literally the expansion of a typed reason. -/
theorem walk_has_reason {a b : V} {w : List (Letter (EdgeId E))} (hw : Walk a w b) :
    ∃ p : Reason E a b, expansion p = w := by
  induction hw with
  | nil a => exact ⟨.rho a, rfl⟩
  | cons x h ih =>
    obtain ⟨p, hp⟩ := ih
    cases x with
    | pos e =>
      exact ⟨.tau (.atom e.2.2) p, by simp [expansion, hp, letterSource]⟩
    | neg e =>
      exact ⟨.tau (.sigma (.atom e.2.2)) p, by simp [expansion, hp, inverseWord, inv, letterSource]⟩

/-- Each Boolean presentation supplies an ordinary setoid on one reason hom-set. -/
def reasonSetoid (complete : Bool) (E : V → V → Type v) (a b : V) :
    Setoid (Reason E a b) where
  r := ReasonCongruence complete
  iseqv := ⟨ReasonCongruence.refl, ReasonCongruence.symm, ReasonCongruence.trans⟩

def wordSetoid (E : V → V → Type v) (a b : V) : Setoid (TypedWord E a b) where
  r := TypedWord.Equiv
  iseqv := ⟨TypedWord.Equiv.refl, TypedWord.Equiv.symm, TypedWord.Equiv.trans⟩

/-- Expansion descends to the ordinary word quotient in the same fixed hom-set. -/
def expansionOnQuotient (complete : Bool) (a b : V) :
    Quotient (reasonSetoid complete E a b) → Quotient (wordSetoid E a b) :=
  Quotient.lift (fun p => Quotient.mk (wordSetoid E a b) (ReasonCongruence.typedExpansion p))
    (fun p q h => Quotient.sound ((ReasonCongruence.iff_typed_word_equiv p q).mp h))

theorem expansionOnQuotient_injective (complete : Bool) (a b : V) :
    Function.Injective (expansionOnQuotient (E := E) complete a b) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro p q h
  apply Quotient.sound
  exact (ReasonCongruence.iff_typed_word_equiv p q).mpr (Quotient.exact h)

theorem expansionOnQuotient_surjective (complete : Bool) (a b : V) :
    Function.Surjective (expansionOnQuotient (E := E) complete a b) := by
  intro x
  refine Quotient.inductionOn x ?_
  intro w
  obtain ⟨p, hp⟩ := walk_has_reason w.property
  refine ⟨Quotient.mk (reasonSetoid complete E a b) p, ?_⟩
  have he : ReasonCongruence.typedExpansion p = w := Subtype.ext hp
  change Quotient.mk (wordSetoid E a b) (ReasonCongruence.typedExpansion p) = _
  rw [he]

/-- A bijection of quotient hom-sets for either of the two selected presentations. -/
theorem expansionOnQuotient_bijective (complete : Bool) (a b : V) :
    Function.Injective (expansionOnQuotient (E := E) complete a b) ∧
      Function.Surjective (expansionOnQuotient (E := E) complete a b) :=
  ⟨expansionOnQuotient_injective complete a b, expansionOnQuotient_surjective complete a b⟩

end StructuralReasons
