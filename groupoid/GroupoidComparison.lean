import GroupoidOperations

namespace StructuralReasons
universe u v w x
variable {V : Type u} {E : V → V → Type v}

/-- Functors have a specified object map and preserve identity and composition. -/
structure PathFunctor {V : Type u} {W : Type w}
    (G : PathGroupoid.{u,v} V) (H : PathGroupoid.{w,x} W) (obj : V → W) where
  map : {a b : V} → G.Hom a b → H.Hom (obj a) (obj b)
  map_identity : ∀ a, map (G.identity a) = H.identity (obj a)
  map_compose : ∀ {a b c} (p : G.Hom a b) (q : G.Hom b c),
    map (G.compose p q) = H.compose (map p) (map q)

namespace PathGroupoid
variable {G : PathGroupoid.{u,v} V}
/-- Two-sided groupoid laws determine the specified inverse uniquely. -/
theorem inverse_unique {a b : V} (p : G.Hom a b) (q : G.Hom b a)
    (h : G.compose p q = G.identity a) : q = G.inverse p := by
  calc
    q = G.compose (G.identity b) q := (G.identity_compose q).symm
    _ = G.compose (G.compose (G.inverse p) p) q := by rw [G.inverse_compose]
    _ = G.compose (G.inverse p) (G.compose p q) := G.assoc _ _ _
    _ = G.inverse p := by rw [h, G.compose_identity]

theorem inverse_identity (a : V) : G.inverse (G.identity a) = G.identity a :=
  (inverse_unique (G.identity a) (G.identity a) (G.identity_compose _)).symm

theorem inverse_inverse {a b : V} (p : G.Hom a b) : G.inverse (G.inverse p) = p :=
  (inverse_unique (G.inverse p) p (G.inverse_compose p)).symm

theorem inverse_compose_eq {a b c : V} (p : G.Hom a b) (q : G.Hom b c) :
    G.inverse (G.compose p q) = G.compose (G.inverse q) (G.inverse p) := by
  symm
  apply inverse_unique
  calc
    G.compose (G.compose p q) (G.compose (G.inverse q) (G.inverse p)) =
        G.compose p (G.compose q (G.compose (G.inverse q) (G.inverse p))) := G.assoc _ _ _
    _ = G.compose p (G.compose (G.compose q (G.inverse q)) (G.inverse p)) := by rw [G.assoc]
    _ = G.identity a := by rw [G.compose_inverse, G.identity_compose, G.compose_inverse]
end PathGroupoid

namespace PathFunctor
variable {W : Type w} {G : PathGroupoid.{u,v} V} {H : PathGroupoid.{w,x} W} {obj : V → W}
/-- Preservation of inverses follows from the ordinary functor laws. -/
theorem map_inverse (F : PathFunctor G H obj) {a b : V} (p : G.Hom a b) :
    F.map (G.inverse p) = H.inverse (F.map p) := by
  apply PathGroupoid.inverse_unique
  rw [← F.map_compose, G.compose_inverse, F.map_identity]
end PathFunctor

/-- An object-fixing groupoid isomorphism includes functors in both directions. -/
structure ObjectFixingGroupoidIso (G : PathGroupoid.{u,v} V) (H : PathGroupoid.{u,w} V) where
  forward : PathFunctor G H id
  backward : PathFunctor H G id
  backward_forward : ∀ {a b} (p : G.Hom a b), backward.map (forward.map p) = p
  forward_backward : ∀ {a b} (p : H.Hom a b), forward.map (backward.map p) = p

namespace GroupoidComparison
variable (complete : Bool)
theorem expansion_identity (a : V) :
    expansionOnQuotient (E := E) complete a a (ReasonClass.identity complete a) =
      WordClass.identity a := rfl

theorem expansion_compose {a b c : V}
    (p : ReasonClass complete E a b) (q : ReasonClass complete E b c) :
    expansionOnQuotient complete a c (ReasonClass.compose p q) =
      WordClass.compose (expansionOnQuotient complete a b p) (expansionOnQuotient complete b c q) := by
  induction p using Quotient.inductionOn with | _ p =>
    induction q using Quotient.inductionOn with | _ q => rfl

theorem expansion_inverse {a b : V} (p : ReasonClass complete E a b) :
    expansionOnQuotient complete b a (ReasonClass.inverse p) =
      WordClass.inverse (expansionOnQuotient complete a b p) := by
  induction p using Quotient.inductionOn with | _ p => rfl

def expansionFunctor : PathFunctor (reasonGroupoid complete E) (wordGroupoid E) id where
  map := expansionOnQuotient complete _ _
  map_identity := expansion_identity complete
  map_compose := expansion_compose complete

/-- A preimage is chosen only after both quotient groupoids have been defined directly. -/
noncomputable def reconstruction {a b : V} (p : WordClass E a b) : ReasonClass complete E a b :=
  Classical.choose (expansionOnQuotient_surjective complete a b p)

theorem expansion_reconstruction {a b : V} (p : WordClass E a b) :
    expansionOnQuotient complete a b (reconstruction complete p) = p :=
  Classical.choose_spec (expansionOnQuotient_surjective complete a b p)

theorem reconstruction_expansion {a b : V} (p : ReasonClass complete E a b) :
    reconstruction complete (expansionOnQuotient complete a b p) = p := by
  apply expansionOnQuotient_injective complete a b
  exact expansion_reconstruction complete _

theorem reconstruction_identity (a : V) :
    reconstruction complete (WordClass.identity (E := E) a) = ReasonClass.identity complete a := by
  apply expansionOnQuotient_injective complete a a
  rw [expansion_reconstruction, expansion_identity]

theorem reconstruction_compose {a b c : V} (p : WordClass E a b) (q : WordClass E b c) :
    reconstruction complete (WordClass.compose p q) =
      ReasonClass.compose (reconstruction complete p) (reconstruction complete q) := by
  apply expansionOnQuotient_injective complete a c
  rw [expansion_reconstruction, expansion_compose, expansion_reconstruction, expansion_reconstruction]

theorem reconstruction_inverse {a b : V} (p : WordClass E a b) :
    reconstruction complete (WordClass.inverse p) = ReasonClass.inverse (reconstruction complete p) := by
  apply expansionOnQuotient_injective complete b a
  rw [expansion_reconstruction, expansion_inverse, expansion_reconstruction]

noncomputable def reconstructionFunctor :
    PathFunctor (wordGroupoid E) (reasonGroupoid complete E) id where
  map := reconstruction complete
  map_identity := reconstruction_identity complete
  map_compose := reconstruction_compose complete

/-- The two independently defined quotient groupoids are isomorphic over their vertices. -/
noncomputable def isomorphism :
    ObjectFixingGroupoidIso (reasonGroupoid complete E) (wordGroupoid E) where
  forward := expansionFunctor complete
  backward := reconstructionFunctor complete
  backward_forward := reconstruction_expansion complete
  forward_backward := expansion_reconstruction complete

/-- A positive generator has the same complete edge value on both sides. -/
theorem expansion_generator {a b : V} (e : E a b) :
    expansionOnQuotient complete a b (Quotient.mk _ (.atom e)) =
      Quotient.mk (wordSetoid E a b)
        (⟨[.pos ⟨a, b, e⟩], Walk.cons (.pos ⟨a, b, e⟩) (Walk.nil b)⟩ : TypedWord E a b) := rfl
end GroupoidComparison
end StructuralReasons
