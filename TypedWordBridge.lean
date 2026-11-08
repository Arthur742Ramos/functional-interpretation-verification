import StructuralConfluence
import WordNormalisation

namespace StructuralReasons
universe u v
variable {V : Type u} {E : V → V → Type v}
open Words

/-- Ordinary full expansion, before any cancellation. -/
def expansion : {a b : V} → Reason E a b → List (Letter (EdgeId E))
  | _, _, .atom e => [.pos ⟨_, _, e⟩]
  | _, _, .rho _ => []
  | _, _, .sigma p => inverseWord (expansion p)
  | _, _, .tau p q => expansion p ++ expansion q

/-- The two signs traverse the same complete edge identifier in opposite directions. -/
def letterSource : Letter (EdgeId E) → V
  | .pos e => e.1
  | .neg e => e.2.1

def letterTarget : Letter (EdgeId E) → V
  | .pos e => e.2.1
  | .neg e => e.1

@[simp] theorem letterSource_inv (x : Letter (EdgeId E)) :
    letterSource (inv x) = letterTarget x := by cases x <;> rfl
@[simp] theorem letterTarget_inv (x : Letter (EdgeId E)) :
    letterTarget (inv x) = letterSource x := by cases x <;> rfl

/-- Composability includes the endpoints of the empty word. -/
inductive Walk : V → List (Letter (EdgeId E)) → V → Prop
  | nil (a : V) : Walk a [] a
  | cons (x : Letter (EdgeId E)) {w b} :
      Walk (letterTarget x) w b → Walk (letterSource x) (x :: w) b

namespace Walk
 theorem uncons {a b : V} {x : Letter (EdgeId E)} {w}
     (h : Walk a (x :: w) b) : a = letterSource x ∧ Walk (letterTarget x) w b := by
   cases h
   exact ⟨rfl, ‹_›⟩

 theorem append {a b c : V} {w z : List (Letter (EdgeId E))}
     (h : Walk a w b) (k : Walk b z c) : Walk a (w ++ z) c := by
   induction h with
   | nil => exact k
   | cons x h ih => exact .cons x (ih k)

 theorem split {a c : V} (w z : List (Letter (EdgeId E)))
     (h : Walk a (w ++ z) c) : ∃ b, Walk a w b ∧ Walk b z c := by
   induction w generalizing a with
   | nil => exact ⟨a, .nil a, h⟩
   | cons x xs ih =>
     cases h with
     | cons x h =>
       obtain ⟨b, h₁, h₂⟩ := ih h
       exact ⟨b, .cons x h₁, h₂⟩

 theorem inverse {a b : V} {w : List (Letter (EdgeId E))}
     (h : Walk a w b) : Walk b (inverseWord w) a := by
   induction h with
   | nil a => exact .nil a
   | cons x h ih =>
     rw [inverseWord_cons]
     apply ih.append
     simpa using Walk.cons (inv x) (Walk.nil (letterTarget (inv x)))

 theorem cancel {a b : V} {w z : List (Letter (EdgeId E))}
     (h : Walk a w b) (k : Cancel w z) : Walk a z b := by
   cases k with
   | pair p s x =>
     obtain ⟨c, hp, hs⟩ := split p (x :: inv x :: s) h
     apply hp.append
     obtain ⟨hc, hs⟩ := hs.uncons
     obtain ⟨_, hs⟩ := hs.uncons
     simpa [hc] using hs

 theorem cancels {a b : V} {w z : List (Letter (EdgeId E))}
     (h : Walk a w b) (k : Cancels w z) : Walk a z b := by
   induction k with
   | refl => exact h
   | cons k _ ih => exact ih (h.cancel k)

 theorem stack {a b : V} {w : List (Letter (EdgeId E))}
     (h : Walk a w b) : Walk a (Words.stack w).val b := h.cancels (cancels_stack w)
end Walk

theorem expansion_walk {a b : V} (p : Reason E a b) : Walk a (expansion p) b := by
  induction p with
  | atom e => exact .cons (.pos ⟨_, _, e⟩) (.nil _)
  | rho a => exact .nil a
  | sigma p ih => exact ih.inverse
  | tau p q ihp ihq => exact ihp.append ihq

/-- This equality compares the pre-existing action with literal expansion. -/
theorem expansion_action {a b : V} (p : Reason E a b) :
    wordAction (expansion p) = action p := by
  induction p with
  | atom e => simp [expansion, wordAction, action]
  | rho a => rfl
  | sigma p ih => simp [expansion, wordAction_inverseWord, ih, action]
  | tau p q ihp ihq => simp [expansion, wordAction_append, ihp, ihq, action]

/-- The old invariant is the canonical ordinary word normal form N(E(p)). -/
theorem reducedExpansion_eq_stack_expansion {a b : V} (p : Reason E a b) :
    reducedExpansion p = (stack (expansion p)).val := by
  rw [← wordAction_empty, expansion_action]
  rfl

theorem expansion_cancels_reducedExpansion {a b : V} (p : Reason E a b) :
    Cancels (expansion p) (reducedExpansion p) := by
  rw [reducedExpansion_eq_stack_expansion]
  exact cancels_stack _

theorem reducedExpansion_walk {a b : V} (p : Reason E a b) :
    Walk a (reducedExpansion p) b :=
  (expansion_walk p).cancels (expansion_cancels_reducedExpansion p)

theorem expansion_unique_reduced_descendant {a b : V} (p : Reason E a b) :
    (Cancels (expansion p) (reducedExpansion p) ∧
      Reduced (reducedExpansion p) ∧ Walk a (reducedExpansion p) b) ∧
    ∀ w, Cancels (expansion p) w → Reduced w → w = reducedExpansion p := by
  rw [reducedExpansion_eq_stack_expansion]
  exact ⟨⟨cancels_stack _, (stack _).property, (expansion_walk p).stack⟩,
    fun _ h hr => reduced_descendant_eq h hr⟩

/-- The literal word of a canonical spine is its full expansion. -/
theorem shape_expansion {a b : V} {p : Reason E a b} {w}
    (h : Shape p w) : expansion p = w := by
  induction h with
  | nil => rfl
  | pos => rfl
  | neg => rfl
  | posCons e h hn ih => simp [expansion, ih]
  | negCons e h hn ih => simp [expansion, ih, inverseWord, inv]

/-- The ten-rule normal form spells N(E(p)), with composability retained. -/
theorem ten_normal_form_stack_expansion {a b : V} (p : Reason E a b) :
    ∃ q, Steps true p q ∧ Normal true q ∧
      Shape q (stack (expansion p)).val ∧
      expansion q = (stack (expansion p)).val ∧
      Cancels (expansion p) (expansion q) ∧ Walk a (expansion q) b := by
  obtain ⟨q, hpq, hnq, hs, _⟩ := ten_normal_form_word p
  rw [reducedExpansion_eq_stack_expansion] at hs
  have he := shape_expansion hs
  exact ⟨q, hpq, hnq, hs, he, he ▸ cancels_stack _, expansion_walk q⟩

/-- Every composable word has one reduced descendant in the same hom-set. -/
theorem typed_word_normal_form {a b : V} {w : List (Letter (EdgeId E))}
    (hw : Walk a w b) :
    ∃ z, (Cancels w z ∧ Reduced z ∧ Walk a z b) ∧
      ∀ v, Cancels w v → Reduced v → v = z := by
  exact ⟨(stack w).val, ⟨cancels_stack w, (stack w).property, hw.stack⟩,
    fun _ h hr => reduced_descendant_eq h hr⟩

theorem typed_word_confluent {a b : V} {w v z : List (Letter (EdgeId E))}
    (hw : Walk a w b) (hv : Cancels w v) (hz : Cancels w z) :
    ∃ n, Cancels v n ∧ Cancels z n ∧ Reduced n ∧ Walk a n b := by
  refine ⟨(stack w).val, ?_, ?_, (stack w).property, hw.stack⟩
  · rw [cancels_stack_eq hv]; exact cancels_stack v
  · rw [cancels_stack_eq hz]; exact cancels_stack z

/-- Endpoints remain part of the type, also when the letter list is empty. -/
def TypedWord (E : V → V → Type v) (a b : V) :=
  {w : List (Letter (EdgeId E)) // Walk a w b}

namespace TypedWord
variable {a b : V}

noncomputable def normalise (w : TypedWord E a b) : TypedWord E a b :=
  ⟨(stack w.val).val, w.property.stack⟩

/-- The generated equivalence uses only words in one fixed endpoint hom-set. -/
inductive Equiv : TypedWord E a b → TypedWord E a b → Prop
  | refl (w) : Equiv w w
  | step {w z} : Cancel w.val z.val → Equiv w z
  | symm {w z} : Equiv w z → Equiv z w
  | trans {w z v} : Equiv w z → Equiv z v → Equiv w v

theorem cancels_equiv {w z : TypedWord E a b} (h : Cancels w.val z.val) :
    Equiv w z := by
  generalize hw : w.val = xs at h
  generalize hz : z.val = ys at h
  induction h generalizing w z with
  | refl =>
    have he : w = z := Subtype.ext (hw.trans hz.symm)
    subst z
    exact .refl _
  | @cons xs ys zs h k ih =>
    have ht : Walk a ys b := w.property.cancel (hw ▸ h)
    exact .trans (.step (show Cancel w.val (⟨ys, ht⟩ : TypedWord E a b).val from hw ▸ h))
      (ih (w := ⟨ys, ht⟩) (z := z) rfl hz)

theorem equiv_normalise {w z : TypedWord E a b} (h : Equiv w z) :
    normalise w = normalise z := by
  induction h with
  | refl => rfl
  | step h =>
    apply Subtype.ext
    exact congrArg (fun r : RWord (EdgeId E) => r.val) (cancel_stack h)
  | symm h ih => exact ih.symm
  | trans h k ih₁ ih₂ => exact ih₁.trans ih₂

/-- Word equivalence is precisely equality of reduced typed normal forms. -/
theorem equiv_iff_normalise_eq (w z : TypedWord E a b) :
    Equiv w z ↔ normalise w = normalise z := by
  constructor
  · exact equiv_normalise
  · intro h
    have hw : Equiv w (normalise w) := cancels_equiv (cancels_stack w.val)
    have hz : Equiv z (normalise z) := cancels_equiv (cancels_stack z.val)
    rw [← h] at hz
    exact .trans hw (.symm hz)
end TypedWord

end StructuralReasons
