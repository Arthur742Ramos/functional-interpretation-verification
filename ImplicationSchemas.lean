import Std.Tactic

/- Original formula-level reconstruction for Chapter 2, I9.
   F is a distinguished constant, not a substitutable atom.
   No lambda labels, operational semantics or historical adequacy are asserted. -/
namespace ImplicationSchemas

inductive Formula where
  | atom : Nat → Formula
  | falsity : Formula
  | imp : Formula → Formula → Formula
  deriving DecidableEq, Repr

infixr:60 " ⇒ " => Formula.imp

def eval (v : Nat → Bool) : Formula → Bool
  | .atom p => v p
  | .falsity => false
  | A ⇒ B => !(eval v A) || eval v B

def Valid (A : Formula) : Prop := ∀ v, eval v A = true

def subst (σ : Nat → Formula) : Formula → Formula
  | .atom p => σ p
  | .falsity => .falsity
  | A ⇒ B => subst σ A ⇒ subst σ B

theorem eval_subst (σ : Nat → Formula) (v : Nat → Bool) (A : Formula) :
    eval v (subst σ A) = eval (fun p => eval v (σ p)) A := by
  induction A with
  | atom p => rfl
  | falsity => rfl
  | imp A B ihA ihB => simp [subst, eval, ihA, ihB]

theorem valid_subst {A : Formula} (h : Valid A) (σ : Nat → Formula) :
    Valid (subst σ A) := by
  intro v
  rw [eval_subst]
  exact h _

/-- Zero is defined for recursion, but contraction and Rose use positive indices only. -/
def repeatArrow (A B : Formula) : Nat → Formula
  | 0 => B
  | n + 1 => A ⇒ repeatArrow A B n

theorem eval_repeat_positive (v : Nat → Bool) (A B : Formula) (n : Nat) :
    eval v (repeatArrow A B (n + 1)) = eval v (A ⇒ B) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (!(eval v A) || eval v (repeatArrow A B (n + 1))) = _
    rw [ih]
    simp only [eval]
    cases eval v A <;> cases eval v B <;> rfl

/-- Schema names are not claims of adequacy for historical labelled calculi. -/
inductive Schema where
  | identity | composition | compositionRev | exchange | contraction | distribution
  | swappedDistribution | weakening | weakeningArrow | exchangeArrow
  | explosion | peirce | weakPeirce
  | contractionPositive (m n : Nat)
  | rosePositive (n : Nat)
  | lukasiewicz3 | lukasiewicz4 | lukasiewicz5 | linearity
  deriving DecidableEq, Repr

/-- A, B, C, D are arbitrary formulas. Numeric parameters encode positive indices by +1. -/
def instanceOf (s : Schema) (A B C D : Formula) : Formula :=
  match s with
  | .identity => A ⇒ A
  | .composition => (A ⇒ B) ⇒ (C ⇒ A) ⇒ C ⇒ B
  | .compositionRev => (A ⇒ B) ⇒ (B ⇒ C) ⇒ A ⇒ C
  | .exchange => (A ⇒ B ⇒ C) ⇒ B ⇒ A ⇒ C
  | .contraction => (A ⇒ A ⇒ B) ⇒ A ⇒ B
  | .distribution => (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
  | .swappedDistribution => (A ⇒ B) ⇒ (A ⇒ B ⇒ C) ⇒ A ⇒ C
  | .weakening => A ⇒ B ⇒ A
  | .weakeningArrow => (A ⇒ B) ⇒ C ⇒ (A ⇒ B)
  | .exchangeArrow => (A ⇒ (B ⇒ C) ⇒ D) ⇒ (B ⇒ C) ⇒ A ⇒ D
  | .explosion => Formula.falsity ⇒ A
  | .peirce => ((A ⇒ B) ⇒ A) ⇒ A
  | .weakPeirce => ((A ⇒ B) ⇒ A) ⇒ (A ⇒ B) ⇒ B
  | .contractionPositive m n => repeatArrow A B (m + 1) ⇒ repeatArrow A B (n + 1)
  | .rosePositive n => (repeatArrow A B (n + 1) ⇒ A) ⇒ A
  | .lukasiewicz3 => ((A ⇒ B) ⇒ B) ⇒ (B ⇒ A) ⇒ A
  | .lukasiewicz4 => ((A ⇒ Formula.falsity) ⇒ (B ⇒ Formula.falsity)) ⇒ B ⇒ A
  | .lukasiewicz5 => ((A ⇒ B) ⇒ (B ⇒ A)) ⇒ B ⇒ A
  | .linearity => ((A ⇒ B) ⇒ C) ⇒ ((B ⇒ A) ⇒ C) ⇒ C

theorem schema_valid (s : Schema) (A B C D : Formula) :
    Valid (instanceOf s A B C D) := by
  intro v
  cases s <;>
    simp only [instanceOf, eval, eval_repeat_positive] <;>
    cases eval v A <;> cases eval v B <;> cases eval v C <;> cases eval v D <;>
    decide

/-- Hilbert proofs contain exactly schema instances, MP and F-fixed substitution. -/
inductive Derives (stock : Schema → Prop) : Formula → Prop where
  | schema (s : Schema) (hs : stock s) (A B C D : Formula) :
      Derives stock (instanceOf s A B C D)
  | mp {A B : Formula} : Derives stock (A ⇒ B) → Derives stock A → Derives stock B
  | uniform {A : Formula} : Derives stock A → (σ : Nat → Formula) →
      Derives stock (subst σ A)

theorem sound {stock : Schema → Prop} {A : Formula} (h : Derives stock A) :
    Valid A := by
  induction h with
  | schema s _ A B C D => exact schema_valid s A B C D
  | @mp A B _ _ ihAB ihA =>
    intro v
    have hAB := ihAB v
    have hA := ihA v
    simpa [eval, hA] using hAB
  | uniform _ σ ih => exact valid_subst ih σ

theorem atom_not_derivable (stock : Schema → Prop) (p : Nat) :
    ¬ Derives stock (.atom p) := by
  intro h
  have bad := sound h (fun _ => false)
  cases bad

theorem falsity_not_derivable (stock : Schema → Prop) :
    ¬ Derives stock .falsity := by
  intro h
  have bad := sound h (fun _ => false)
  cases bad

/-- The eleven reconstructed rows, plus the separately retained weak classical row. -/
inductive Basis where
  | concatenation | bbPrimeI | linear | modalTStrict | relevant | entailment
  | ticketEntailment | strict | minimal | intuitionistic | classical | classicalWeak
  deriving DecidableEq, Repr

def basisSchemas : Basis → List Schema
  | .concatenation => [.identity, .composition]
  | .bbPrimeI => [.identity, .composition, .compositionRev]
  | .linear => [.identity, .composition, .compositionRev, .exchange]
  | .modalTStrict => [.identity, .composition, .compositionRev, .exchange, .contraction]
  | .relevant => [.identity, .composition, .compositionRev, .exchange, .distribution]
  | .entailment => [.identity, .composition, .compositionRev, .distribution, .exchangeArrow]
  | .ticketEntailment => [.identity, .composition, .compositionRev, .distribution,
      .swappedDistribution]
  | .strict => [.identity, .composition, .compositionRev, .exchange, .weakeningArrow]
  | .minimal => [.identity, .composition, .compositionRev, .exchange, .distribution, .weakening]
  | .intuitionistic => [.identity, .composition, .compositionRev, .exchange, .distribution,
      .weakening, .explosion]
  | .classical => [.identity, .composition, .compositionRev, .exchange, .distribution,
      .weakening, .peirce]
  | .classicalWeak => [.identity, .composition, .compositionRev, .exchange, .distribution,
      .weakening, .weakPeirce]

def InBasis (b : Basis) (s : Schema) : Prop := s ∈ basisSchemas b

theorem basis_sound (b : Basis) {A : Formula} (h : Derives (InBasis b) A) :
    Valid A := sound h

theorem basis_atom_not_derivable (b : Basis) (p : Nat) :
    ¬ Derives (InBasis b) (.atom p) := atom_not_derivable _ _

/-- Generalisation to arbitrary selected instances, e.g. restricted C families.
    Selection can depend on parameters. Substitution closure remains explicit and
    may enlarge the selected family; no unprovided historical restriction is inferred. -/
inductive SelectedDerives (selected : Schema → Formula → Formula → Formula → Formula → Prop) :
    Formula → Prop where
  | schema (s : Schema) (A B C D : Formula) (h : selected s A B C D) :
      SelectedDerives selected (instanceOf s A B C D)
  | mp {A B : Formula} : SelectedDerives selected (A ⇒ B) →
      SelectedDerives selected A → SelectedDerives selected B
  | uniform {A : Formula} : SelectedDerives selected A → (σ : Nat → Formula) →
      SelectedDerives selected (subst σ A)

theorem selected_sound {selected} {A : Formula} (h : SelectedDerives selected A) :
    Valid A := by
  induction h with
  | schema s A B C D _ => exact schema_valid s A B C D
  | @mp A B _ _ ihAB ihA =>
    intro v
    have hAB := ihAB v
    have hA := ihA v
    simpa [eval, hA] using hAB
  | uniform _ σ ih => exact valid_subst ih σ

theorem selected_atom_not_derivable (selected) (p : Nat) :
    ¬ SelectedDerives selected (.atom p) := by
  intro h
  have bad := selected_sound h (fun _ => false)
  cases bad

#print axioms eval_subst
#print axioms eval_repeat_positive
#print axioms schema_valid
#print axioms sound
#print axioms atom_not_derivable
#print axioms falsity_not_derivable
#print axioms basis_sound
#print axioms basis_atom_not_derivable
#print axioms selected_sound
#print axioms selected_atom_not_derivable

end ImplicationSchemas
