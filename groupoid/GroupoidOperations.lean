import ReasonQuotient

/-! Quotient operations use the original reason constructors and literal word operations. -/
namespace StructuralReasons
universe u v w x
variable {V : Type u} {E : V → V → Type v}
open Words

namespace TypedWord
/-- The empty word retains its vertex. -/
def identity (a : V) : TypedWord E a a := ⟨[], .nil a⟩
/-- Composition is ordinary concatenation, in traversal order. -/
def compose {a b c : V} (p : TypedWord E a b) (q : TypedWord E b c) :
    TypedWord E a c := ⟨p.val ++ q.val, p.property.append q.property⟩
/-- Inversion reverses the order and signs of all letters. -/
def inverse {a b : V} (p : TypedWord E a b) : TypedWord E b a :=
  ⟨inverseWord p.val, p.property.inverse⟩

theorem equiv_action {a b : V} {p q : TypedWord E a b} (h : Equiv p q) :
    wordAction p.val = wordAction q.val := by
  induction h with
  | refl => rfl
  | step h => exact cancel_wordAction h
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik

theorem equiv_of_action {a b : V} {p q : TypedWord E a b}
    (h : wordAction p.val = wordAction q.val) : Equiv p q := by
  apply (equiv_iff_normalise_eq p q).mpr
  apply Subtype.ext
  change (stack p.val).val = (stack q.val).val
  rw [← wordAction_empty, ← wordAction_empty, h]

theorem compose_respects {a b c : V} {p p' : TypedWord E a b}
    {q q' : TypedWord E b c} (h : Equiv p p') (k : Equiv q q') :
    Equiv (compose p q) (compose p' q') := by
  apply equiv_of_action
  simp only [compose, wordAction_append, equiv_action h, equiv_action k]

theorem inverse_respects {a b : V} {p q : TypedWord E a b} (h : Equiv p q) :
    Equiv (inverse p) (inverse q) := by
  apply equiv_of_action
  simp only [inverse, wordAction_inverseWord, equiv_action h]

theorem compose_assoc {a b c d : V}
    (p : TypedWord E a b) (q : TypedWord E b c) (r : TypedWord E c d) :
    compose (compose p q) r = compose p (compose q r) :=
  Subtype.ext (List.append_assoc _ _ _)

theorem identity_compose {a b : V} (p : TypedWord E a b) :
    compose (identity a) p = p := Subtype.ext (List.nil_append _)

theorem compose_identity {a b : V} (p : TypedWord E a b) :
    compose p (identity b) = p := Subtype.ext (List.append_nil _)

theorem compose_inverse_equiv {a b : V} (p : TypedWord E a b) :
    Equiv (compose p (inverse p)) (identity a) := by
  apply equiv_of_action
  simp [compose, inverse, identity, wordAction]

theorem inverse_compose_equiv {a b : V} (p : TypedWord E a b) :
    Equiv (compose (inverse p) p) (identity b) := by
  apply equiv_of_action
  simp [compose, inverse, identity, wordAction]
end TypedWord

/-- A groupoid on a specified object type, with traversal-order composition. -/
structure PathGroupoid (V : Type u) where
  Hom : V → V → Type v
  identity : (a : V) → Hom a a
  compose : {a b c : V} → Hom a b → Hom b c → Hom a c
  inverse : {a b : V} → Hom a b → Hom b a
  assoc : ∀ {a b c d} (p : Hom a b) (q : Hom b c) (r : Hom c d),
    compose (compose p q) r = compose p (compose q r)
  identity_compose : ∀ {a b} (p : Hom a b), compose (identity a) p = p
  compose_identity : ∀ {a b} (p : Hom a b), compose p (identity b) = p
  compose_inverse : ∀ {a b} (p : Hom a b), compose p (inverse p) = identity a
  inverse_compose : ∀ {a b} (p : Hom a b), compose (inverse p) p = identity b

abbrev ReasonClass (complete : Bool) (E : V → V → Type v) (a b : V) :=
  Quotient (reasonSetoid complete E a b)
abbrev WordClass (E : V → V → Type v) (a b : V) := Quotient (wordSetoid E a b)

namespace ReasonClass
variable {complete : Bool}
def identity (complete : Bool) (a : V) : ReasonClass complete E a a :=
  Quotient.mk _ (.rho a)
def compose {a b c : V} (p : ReasonClass complete E a b) (q : ReasonClass complete E b c) :
    ReasonClass complete E a c :=
  Quotient.liftOn₂ p q (fun p q => Quotient.mk _ (.tau p q))
    (fun _ _ _ _ h k => Quotient.sound (ReasonCongruence.tau h k))
def inverse {a b : V} (p : ReasonClass complete E a b) : ReasonClass complete E b a :=
  Quotient.liftOn p (fun p => Quotient.mk _ (.sigma p))
    (fun _ _ h => Quotient.sound (ReasonCongruence.sigma h))

theorem compose_mk {a b c : V} (p : Reason E a b) (q : Reason E b c) :
    compose (Quotient.mk (reasonSetoid complete E a b) p) (Quotient.mk _ q) =
      Quotient.mk _ (.tau p q) := rfl

theorem inverse_mk {a b : V} (p : Reason E a b) :
    inverse (Quotient.mk (reasonSetoid complete E a b) p) = Quotient.mk _ (.sigma p) := rfl

theorem assoc {a b c d : V} (p : ReasonClass complete E a b)
    (q : ReasonClass complete E b c) (r : ReasonClass complete E c d) :
    compose (compose p q) r = compose p (compose q r) := by
  induction p using Quotient.inductionOn with | _ p =>
    induction q using Quotient.inductionOn with | _ q =>
      induction r using Quotient.inductionOn with | _ r =>
        exact Quotient.sound (ReasonCongruence.root (Root.tt p q r))

theorem identity_compose {a b : V} (p : ReasonClass complete E a b) :
    compose (identity complete a) p = p := by
  induction p using Quotient.inductionOn with | _ p =>
    exact Quotient.sound (ReasonCongruence.root (Root.tlr p))

theorem compose_identity {a b : V} (p : ReasonClass complete E a b) :
    compose p (identity complete b) = p := by
  induction p using Quotient.inductionOn with | _ p =>
    exact Quotient.sound (ReasonCongruence.root (Root.trr p))

theorem compose_inverse {a b : V} (p : ReasonClass complete E a b) :
    compose p (inverse p) = identity complete a := by
  induction p using Quotient.inductionOn with | _ p =>
    exact Quotient.sound (ReasonCongruence.root (Root.tr p))

theorem inverse_compose {a b : V} (p : ReasonClass complete E a b) :
    compose (inverse p) p = identity complete b := by
  induction p using Quotient.inductionOn with | _ p =>
    exact Quotient.sound (ReasonCongruence.root (Root.tsr p))
end ReasonClass

namespace WordClass
def identity (a : V) : WordClass E a a := Quotient.mk _ (TypedWord.identity a)
def compose {a b c : V} (p : WordClass E a b) (q : WordClass E b c) : WordClass E a c :=
  Quotient.liftOn₂ p q (fun p q => Quotient.mk _ (TypedWord.compose p q))
    (fun _ _ _ _ h k => Quotient.sound (TypedWord.compose_respects h k))
def inverse {a b : V} (p : WordClass E a b) : WordClass E b a :=
  Quotient.liftOn p (fun p => Quotient.mk _ (TypedWord.inverse p))
    (fun _ _ h => Quotient.sound (TypedWord.inverse_respects h))

theorem compose_mk {a b c : V} (p : TypedWord E a b) (q : TypedWord E b c) :
    compose (Quotient.mk (wordSetoid E a b) p) (Quotient.mk _ q) =
      Quotient.mk _ (TypedWord.compose p q) := rfl

theorem inverse_mk {a b : V} (p : TypedWord E a b) :
    inverse (Quotient.mk (wordSetoid E a b) p) = Quotient.mk _ (TypedWord.inverse p) := rfl

theorem assoc {a b c d : V} (p : WordClass E a b)
    (q : WordClass E b c) (r : WordClass E c d) :
    compose (compose p q) r = compose p (compose q r) := by
  induction p using Quotient.inductionOn with | _ p =>
    induction q using Quotient.inductionOn with | _ q =>
      induction r using Quotient.inductionOn with | _ r =>
        exact congrArg (Quotient.mk _) (TypedWord.compose_assoc p q r)

theorem identity_compose {a b : V} (p : WordClass E a b) :
    compose (identity a) p = p := by
  induction p using Quotient.inductionOn with | _ p =>
    exact congrArg (Quotient.mk _) (TypedWord.identity_compose p)

theorem compose_identity {a b : V} (p : WordClass E a b) :
    compose p (identity b) = p := by
  induction p using Quotient.inductionOn with | _ p =>
    exact congrArg (Quotient.mk _) (TypedWord.compose_identity p)

theorem compose_inverse {a b : V} (p : WordClass E a b) :
    compose p (inverse p) = identity a := by
  induction p using Quotient.inductionOn with | _ p =>
    exact Quotient.sound (TypedWord.compose_inverse_equiv p)

theorem inverse_compose {a b : V} (p : WordClass E a b) :
    compose (inverse p) p = identity b := by
  induction p using Quotient.inductionOn with | _ p =>
    exact Quotient.sound (TypedWord.inverse_compose_equiv p)
end WordClass

def reasonGroupoid (complete : Bool) (E : V → V → Type v) : PathGroupoid V where
  Hom := ReasonClass complete E
  identity := ReasonClass.identity complete
  compose := ReasonClass.compose
  inverse := ReasonClass.inverse
  assoc := ReasonClass.assoc
  identity_compose := ReasonClass.identity_compose
  compose_identity := ReasonClass.compose_identity
  compose_inverse := ReasonClass.compose_inverse
  inverse_compose := ReasonClass.inverse_compose

def wordGroupoid (E : V → V → Type v) : PathGroupoid V where
  Hom := WordClass E
  identity := WordClass.identity
  compose := WordClass.compose
  inverse := WordClass.inverse
  assoc := WordClass.assoc
  identity_compose := WordClass.identity_compose
  compose_identity := WordClass.compose_identity
  compose_inverse := WordClass.compose_inverse
  inverse_compose := WordClass.inverse_compose

end StructuralReasons
