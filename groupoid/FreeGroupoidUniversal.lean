import GroupoidComparison

/-! The free-groupoid extension theorem for an arbitrary lawful target groupoid. -/
namespace StructuralReasons
universe u v w x
variable {V : Type u} {E : V → V → Type v} {W : Type w}

namespace PathFunctor
variable {G : PathGroupoid.{u,v} V} {H : PathGroupoid.{w,x} W} {obj : V → W}
theorem ext (F K : PathFunctor G H obj)
    (h : ∀ {a b} (p : G.Hom a b), F.map p = K.map p) : F = K := by
  cases F with | mk fm fi fc =>
    cases K with | mk km ki kc =>
      have he : @fm = @km := by funext a b p; exact h p
      cases he
      rfl
end PathFunctor

namespace FreeGroupoid
variable (H : PathGroupoid.{w,x} W) (obj : V → W)
/-- Every edge, including each distinct parallel edge, receives its own target arrow. -/
abbrev GeneratorAssignment (E : V → V → Type v) :=
  {a b : V} → E a b → H.Hom (obj a) (obj b)

variable (edge : GeneratorAssignment H obj E)
/-- Evaluate the typed reason tree using the chosen target groupoid operations. -/
def evaluate : {a b : V} → Reason E a b → H.Hom (obj a) (obj b)
  | _, _, .atom e => edge e
  | _, _, .rho a => H.identity (obj a)
  | _, _, .sigma p => H.inverse (evaluate p)
  | _, _, .tau p q => H.compose (evaluate p) (evaluate q)

theorem evaluate_root {complete : Bool} {a b : V} {p q : Reason E a b}
    (h : Root complete p q) : evaluate H obj edge p = evaluate H obj edge q := by
  cases h with
  | sr a => exact PathGroupoid.inverse_identity (obj a)
  | ss p => exact PathGroupoid.inverse_inverse _
  | tr p => exact H.compose_inverse _
  | tsr p => exact H.inverse_compose _
  | trr p => exact H.compose_identity _
  | tlr p => exact H.identity_compose _
  | st p q => exact PathGroupoid.inverse_compose_eq _ _
  | tt p q r => exact H.assoc _ _ _
  | cancelSuffix _ p q =>
    simp only [evaluate]
    rw [← H.assoc, H.compose_inverse, H.identity_compose]
  | cancelInvSuffix _ p q =>
    simp only [evaluate]
    rw [← H.assoc, H.inverse_compose, H.identity_compose]

theorem evaluate_congruence {complete : Bool} {a b : V} {p q : Reason E a b}
    (h : ReasonCongruence complete p q) : evaluate H obj edge p = evaluate H obj edge q := by
  induction h with
  | root h => exact evaluate_root H obj edge h
  | refl p => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | sigma _ ih => exact congrArg H.inverse ih
  | left r _ ih => exact congrArg (fun p => H.compose p (evaluate H obj edge r)) ih
  | right p _ ih => exact congrArg (H.compose (evaluate H obj edge p)) ih

def reasonGenerator (complete : Bool) {a b : V} (e : E a b) : ReasonClass complete E a b :=
  Quotient.mk _ (.atom e)

def wordGenerator {a b : V} (e : E a b) : WordClass E a b :=
  Quotient.mk _ (⟨[.pos ⟨a, b, e⟩], Walk.cons (.pos ⟨a, b, e⟩) (Walk.nil b)⟩ : TypedWord E a b)

variable (complete : Bool)
/-- Evaluation descends because all selected root equations hold in every groupoid. -/
def reasonMap {a b : V} (p : ReasonClass complete E a b) : H.Hom (obj a) (obj b) :=
  Quotient.liftOn p (evaluate H obj edge) (fun _ _ h => evaluate_congruence H obj edge h)

theorem reasonMap_identity (a : V) :
    reasonMap H obj edge complete (ReasonClass.identity complete a) = H.identity (obj a) := rfl

theorem reasonMap_compose {a b c : V} (p : ReasonClass complete E a b)
    (q : ReasonClass complete E b c) :
    reasonMap H obj edge complete (ReasonClass.compose p q) =
      H.compose (reasonMap H obj edge complete p) (reasonMap H obj edge complete q) := by
  induction p using Quotient.inductionOn with | _ p =>
    induction q using Quotient.inductionOn with | _ q => rfl

def reasonExtension : PathFunctor (reasonGroupoid complete E) H obj where
  map := reasonMap H obj edge complete
  map_identity := reasonMap_identity H obj edge complete
  map_compose := reasonMap_compose H obj edge complete

theorem reasonExtension_generator {a b : V} (e : E a b) :
    (reasonExtension H obj edge complete).map (reasonGenerator complete e) = edge e := rfl

/-- Ordinary functor laws force evaluation of every raw reason. -/
theorem reasonFunctor_evaluate (F : PathFunctor (reasonGroupoid complete E) H obj)
    (he : ∀ {a b} (e : E a b), F.map (reasonGenerator complete e) = edge e)
    {a b : V} (p : Reason E a b) :
    F.map (Quotient.mk (reasonSetoid complete E a b) p) = evaluate H obj edge p := by
  induction p with
  | atom e => exact he e
  | rho a => exact F.map_identity a
  | sigma p ih =>
    change F.map ((reasonGroupoid complete E).inverse (Quotient.mk _ p)) = H.inverse _
    rw [F.map_inverse, ih]
  | tau p q ih ik =>
    change F.map ((reasonGroupoid complete E).compose (Quotient.mk _ p) (Quotient.mk _ q)) = H.compose _ _
    rw [F.map_compose, ih, ik]

theorem reasonExtension_unique (F : PathFunctor (reasonGroupoid complete E) H obj)
    (he : ∀ {a b} (e : E a b), F.map (reasonGenerator complete e) = edge e) :
    F = reasonExtension H obj edge complete := by
  apply PathFunctor.ext
  intro a b p
  induction p using Quotient.inductionOn with | _ p =>
    exact reasonFunctor_evaluate H obj edge complete F he p

/-- Existence and uniqueness quantify over all identity/composition-preserving functors. -/
theorem reason_universal :
    ∃ F : PathFunctor (reasonGroupoid complete E) H obj,
      (∀ {a b} (e : E a b), F.map (reasonGenerator complete e) = edge e) ∧
      ∀ K : PathFunctor (reasonGroupoid complete E) H obj,
        (∀ {a b} (e : E a b), K.map (reasonGenerator complete e) = edge e) → K = F :=
  ⟨reasonExtension H obj edge complete, reasonExtension_generator H obj edge complete,
    reasonExtension_unique H obj edge complete⟩

/-- The word extension uses the proved inverse functor, after the reason evaluation proof. -/
noncomputable def wordExtension : PathFunctor (wordGroupoid E) H obj where
  map p := reasonMap H obj edge false (GroupoidComparison.reconstruction false p)
  map_identity a := by
    change reasonMap H obj edge false (GroupoidComparison.reconstruction false (WordClass.identity a)) = _
    rw [GroupoidComparison.reconstruction_identity]
    exact reasonMap_identity H obj edge false a
  map_compose p q := by
    change reasonMap H obj edge false (GroupoidComparison.reconstruction false (WordClass.compose p q)) = _
    rw [GroupoidComparison.reconstruction_compose]
    exact reasonMap_compose H obj edge false _ _

theorem wordExtension_expansion {a b : V} (p : ReasonClass false E a b) :
    (wordExtension H obj edge).map (expansionOnQuotient false a b p) =
      (reasonExtension H obj edge false).map p := by
  change reasonMap H obj edge false (GroupoidComparison.reconstruction false _) = _
  rw [GroupoidComparison.reconstruction_expansion]
  rfl

theorem wordExtension_generator {a b : V} (e : E a b) :
    (wordExtension H obj edge).map (wordGenerator e) = edge e := by
  change (wordExtension H obj edge).map
    (expansionOnQuotient false a b (reasonGenerator false e)) = edge e
  rw [wordExtension_expansion]
  rfl

/-- Pull a target functor back through the operation-preserving expansion. -/
def precomposeExpansion (F : PathFunctor (wordGroupoid E) H obj) :
    PathFunctor (reasonGroupoid complete E) H obj where
  map p := F.map (expansionOnQuotient complete _ _ p)
  map_identity a := by
    change F.map (expansionOnQuotient complete a a (ReasonClass.identity complete a)) = _
    rw [GroupoidComparison.expansion_identity]
    exact F.map_identity a
  map_compose p q := by
    change F.map (expansionOnQuotient complete _ _ (ReasonClass.compose p q)) = _
    rw [GroupoidComparison.expansion_compose]
    exact F.map_compose _ _

theorem wordExtension_unique (F : PathFunctor (wordGroupoid E) H obj)
    (he : ∀ {a b} (e : E a b), F.map (wordGenerator e) = edge e) :
    F = wordExtension H obj edge := by
  have hr : precomposeExpansion H obj false F = reasonExtension H obj edge false :=
    reasonExtension_unique H obj edge false _ (fun e => he e)
  apply PathFunctor.ext
  intro a b p
  obtain ⟨r, rfl⟩ := expansionOnQuotient_surjective false a b p
  rw [wordExtension_expansion]
  exact congrArg (fun K : PathFunctor (reasonGroupoid false E) H obj => K.map r) hr

/-- The unique extensions commute with expansion for either selected presentation. -/
theorem extension_comparison :
    precomposeExpansion H obj complete (wordExtension H obj edge) =
      reasonExtension H obj edge complete :=
  reasonExtension_unique H obj edge complete _ (fun e => wordExtension_generator H obj edge e)

theorem wordExtension_empty (a : V) :
    (wordExtension H obj edge).map
      (Quotient.mk (wordSetoid E a a) (TypedWord.identity a)) = H.identity (obj a) :=
  (wordExtension H obj edge).map_identity a

theorem wordExtension_concatenation {a b c : V}
    (p : TypedWord E a b) (q : TypedWord E b c) :
    (wordExtension H obj edge).map (Quotient.mk _ (TypedWord.compose p q)) =
      H.compose ((wordExtension H obj edge).map (Quotient.mk _ p))
        ((wordExtension H obj edge).map (Quotient.mk _ q)) :=
  (wordExtension H obj edge).map_compose (Quotient.mk _ p) (Quotient.mk _ q)

theorem wordExtension_reversal {a b : V} (p : TypedWord E a b) :
    (wordExtension H obj edge).map (Quotient.mk _ (TypedWord.inverse p)) =
      H.inverse ((wordExtension H obj edge).map (Quotient.mk _ p)) :=
  (wordExtension H obj edge).map_inverse (Quotient.mk _ p)

/-- The cancellation-word quotient is free on the entire endpoint-indexed graph. -/
theorem word_universal :
    ∃ F : PathFunctor (wordGroupoid E) H obj,
      (∀ {a b} (e : E a b), F.map (wordGenerator e) = edge e) ∧
      ∀ K : PathFunctor (wordGroupoid E) H obj,
        (∀ {a b} (e : E a b), K.map (wordGenerator e) = edge e) → K = F :=
  ⟨wordExtension H obj edge, wordExtension_generator H obj edge,
    wordExtension_unique H obj edge⟩
end FreeGroupoid
end StructuralReasons
