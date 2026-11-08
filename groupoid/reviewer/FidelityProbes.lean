import FreeGroupoidUniversal

namespace IndependentFidelity
open StructuralReasons
open StructuralReasons.FreeGroupoid

-- A nontrivial lawful target, independent of either quotient construction.
def parityGroupoid : PathGroupoid Unit where
  Hom := fun _ _ => Bool
  identity := fun _ => false
  compose := Bool.xor
  inverse := id
  assoc := by intro a b c d p q r; cases p <;> cases q <;> cases r <;> rfl
  identity_compose := by intro a b p; cases p <;> rfl
  compose_identity := by intro a b p; cases p <;> rfl
  compose_inverse := by intro a b p; cases p <;> rfl
  inverse_compose := by intro a b p; cases p <;> rfl

def edges : Bool → Bool → Type := fun _ _ => Bool
def collapse : Bool → Unit := fun _ => ()
def assign : GeneratorAssignment parityGroupoid collapse edges := fun e => e

theorem collapsed_vertices : collapse false = collapse true := rfl

theorem distinct_parallel_reasons (complete : Bool) :
    reasonGenerator complete (E := edges) (a := false) (b := true) false ≠
      reasonGenerator complete (E := edges) (a := false) (b := true) true := by
  intro h
  have k := congrArg (fun p => (reasonExtension parityGroupoid collapse assign complete).map p) h
  change false = true at k
  cases k

theorem distinct_parallel_words :
    wordGenerator (E := edges) (a := false) (b := true) false ≠
      wordGenerator (E := edges) (a := false) (b := true) true := by
  intro h
  have k := congrArg (fun p => (wordExtension parityGroupoid collapse assign).map p) h
  have z := (wordExtension_generator parityGroupoid collapse assign (a := false) (b := true) false).symm.trans
    (k.trans (wordExtension_generator parityGroupoid collapse assign (a := false) (b := true) true))
  change false = true at z
  cases z

theorem empty_at_false :
    (wordExtension parityGroupoid collapse assign).map
      (WordClass.identity (E := edges) false) = false :=
  (wordExtension parityGroupoid collapse assign).map_identity false

theorem empty_at_true :
    (wordExtension parityGroupoid collapse assign).map
      (WordClass.identity (E := edges) true) = false :=
  (wordExtension parityGroupoid collapse assign).map_identity true

theorem empty_requires_equal_endpoints {V : Type} {E : V → V → Type}
    {a b : V} (h : Walk (E := E) a [] b) : a = b := by cases h; rfl

universe u v w x
variable {V : Type u} {E : V → V → Type v} {W : Type w}

theorem literal_composition {a b c : V} (p : TypedWord E a b) (q : TypedWord E b c) :
    (TypedWord.compose p q).val = p.val ++ q.val := rfl

theorem literal_inverse {a b : V} (p : TypedWord E a b) :
    (TypedWord.inverse p).val = Words.inverseWord p.val := rfl

-- The return equation for generators in the inverse functor is also forced.
theorem reconstruction_generator (complete : Bool) {a b : V} (e : E a b) :
    GroupoidComparison.reconstruction complete (wordGenerator e) = reasonGenerator complete e := by
  change GroupoidComparison.reconstruction complete
    (expansionOnQuotient complete a b (reasonGenerator complete e)) = _
  exact GroupoidComparison.reconstruction_expansion complete _

-- Re-derive inverse preservation directly from ordinary functor axioms.
theorem ordinary_functor_inverse {G : PathGroupoid.{u,v} V}
    {H : PathGroupoid.{w,x} W} {obj : V → W}
    (F : PathFunctor G H obj) {a b : V} (p : G.Hom a b) :
    F.map (G.inverse p) = H.inverse (F.map p) := by
  calc
    F.map (G.inverse p) = H.compose (H.identity (obj b)) (F.map (G.inverse p)) :=
      (H.identity_compose _).symm
    _ = H.compose (H.compose (H.inverse (F.map p)) (F.map p)) (F.map (G.inverse p)) := by
      rw [H.inverse_compose]
    _ = H.compose (H.inverse (F.map p)) (H.compose (F.map p) (F.map (G.inverse p))) := H.assoc _ _ _
    _ = H.inverse (F.map p) := by
      rw [← F.map_compose, G.compose_inverse, F.map_identity, H.compose_identity]

-- Object and hom universes remain independent; no injectivity hypothesis appears.
theorem arbitrary_word_extension (H : PathGroupoid.{w,x} W) (obj : V → W)
    (edge : GeneratorAssignment H obj E) :
    ∃ F : PathFunctor (wordGroupoid E) H obj,
      (∀ {a b} (e : E a b), F.map (wordGenerator e) = edge e) ∧
      ∀ K : PathFunctor (wordGroupoid E) H obj,
        (∀ {a b} (e : E a b), K.map (wordGenerator e) = edge e) → K = F :=
  word_universal H obj edge

-- Endpoint substitution uses ordinary dependent equality elimination.
theorem transport_identity (complete : Bool) {a b : V} (h : a = b) :
    h ▸ (ReasonClass.identity (E := E) complete a) =
      ReasonClass.identity (E := E) complete b := by cases h; rfl

end IndependentFidelity

#print axioms IndependentFidelity.parityGroupoid
#check @IndependentFidelity.parityGroupoid
#print axioms IndependentFidelity.edges
#check @IndependentFidelity.edges
#print axioms IndependentFidelity.collapse
#check @IndependentFidelity.collapse
#print axioms IndependentFidelity.assign
#check @IndependentFidelity.assign
#print axioms IndependentFidelity.collapsed_vertices
#check @IndependentFidelity.collapsed_vertices
#print axioms IndependentFidelity.distinct_parallel_reasons
#check @IndependentFidelity.distinct_parallel_reasons
#print axioms IndependentFidelity.distinct_parallel_words
#check @IndependentFidelity.distinct_parallel_words
#print axioms IndependentFidelity.empty_at_false
#check @IndependentFidelity.empty_at_false
#print axioms IndependentFidelity.empty_at_true
#check @IndependentFidelity.empty_at_true
#print axioms IndependentFidelity.empty_requires_equal_endpoints
#check @IndependentFidelity.empty_requires_equal_endpoints
#print axioms IndependentFidelity.literal_composition
#check @IndependentFidelity.literal_composition
#print axioms IndependentFidelity.literal_inverse
#check @IndependentFidelity.literal_inverse
#print axioms IndependentFidelity.reconstruction_generator
#check @IndependentFidelity.reconstruction_generator
#print axioms IndependentFidelity.ordinary_functor_inverse
#check @IndependentFidelity.ordinary_functor_inverse
#print axioms IndependentFidelity.arbitrary_word_extension
#check @IndependentFidelity.arbitrary_word_extension
#print axioms IndependentFidelity.transport_identity
#check @IndependentFidelity.transport_identity
