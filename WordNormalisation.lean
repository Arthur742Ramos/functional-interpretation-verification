import ReducedWords

namespace StructuralReasons.Words
universe u
variable {A : Type u}

/-- Reverse the order and invert each signed letter. -/
def inverseWord (w : List (Letter A)) : List (Letter A) := w.reverse.map inv

@[simp] theorem inverseWord_nil : inverseWord ([] : List (Letter A)) = [] := rfl
@[simp] theorem inverseWord_cons (x : Letter A) (w : List (Letter A)) :
    inverseWord (x :: w) = inverseWord w ++ [inv x] := by
  simp [inverseWord]

/-- One ordinary deletion, at an arbitrary prefix and suffix. -/
inductive Cancel : List (Letter A) → List (Letter A) → Prop
  | pair (u v : List (Letter A)) (x : Letter A) :
      Cancel (u ++ x :: inv x :: v) (u ++ v)

/-- Finite forward deletion only; no insertion is a constructor. -/
inductive Cancels : List (Letter A) → List (Letter A) → Prop
  | refl (w) : Cancels w w
  | cons {u v w} : Cancel u v → Cancels v w → Cancels u w

namespace Cancel
 theorem underPrefix (p : List (Letter A)) {u v} (h : Cancel u v) :
     Cancel (p ++ u) (p ++ v) := by
   cases h with
   | pair u v x => simpa [List.append_assoc] using Cancel.pair (p ++ u) v x
 theorem length {u v : List (Letter A)} (h : Cancel u v) : v.length < u.length := by
   cases h
   simp; omega
end Cancel

theorem cancel_terminating :
    WellFounded (fun v w : List (Letter A) => Cancel w v) := by
  apply Subrelation.wf (r := InvImage Nat.lt List.length)
  · intro v w h; exact h.length
  · exact InvImage.wf List.length Nat.lt_wfRel.wf

namespace Cancels
 theorem single {u v : List (Letter A)} (h : Cancel u v) : Cancels u v := .cons h (.refl _)
 theorem trans {u v w : List (Letter A)} (h : Cancels u v) (k : Cancels v w) :
     Cancels u w := by
   induction h with
   | refl => exact k
   | cons h _ ih => exact .cons h (ih k)
 theorem underPrefix (p : List (Letter A)) {u v} (h : Cancels u v) :
     Cancels (p ++ u) (p ++ v) := by
   induction h with
   | refl => exact .refl _
   | cons h _ ih => exact .cons (h.underPrefix p) ih
end Cancels

/-- Normalisation performs only ordinary adjacent-inverse deletions. -/
theorem cancels_stack (w : List (Letter A)) : Cancels w (stack w).val := by
  classical
  induction w with
  | nil => exact .refl _
  | cons x xs ih =>
    have h := ih.underPrefix [x]
    change Cancels (x :: xs) (x :: (stack xs).val) at h
    change Cancels (x :: xs) (push x (stack xs).val)
    apply h.trans
    generalize (stack xs).val = v
    cases v with
    | nil => exact .refl _
    | cons y ys =>
      by_cases he : y = inv x
      · subst y
        rw [push_cancel]
        exact .single (Cancel.pair [] ys x)
      · simp only [push, if_neg he]
        exact .refl _

noncomputable def wordAction : List (Letter A) → Action (RWord A)
  | [] => Action.one
  | x :: w => Action.mul (letterAction x) (wordAction w)

@[simp] theorem wordAction_append (u v : List (Letter A)) :
    wordAction (u ++ v) = Action.mul (wordAction u) (wordAction v) := by
  induction u with
  | nil => simp [wordAction]
  | cons x xs ih => simp [wordAction, ih, Action.mul_assoc]

@[simp] theorem wordAction_inverseWord (w : List (Letter A)) :
    wordAction (inverseWord w) = Action.reverse (wordAction w) := by
  induction w with
  | nil => rfl
  | cons x xs ih => simp [inverseWord_cons, wordAction_append, wordAction, ih]

theorem wordAction_empty (w : List (Letter A)) :
    (wordAction w).forward empty = stack w := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    change prepend x ((wordAction xs).forward empty) = prepend x (stack xs)
    rw [ih]

theorem cancel_wordAction {u v : List (Letter A)} (h : Cancel u v) :
    wordAction u = wordAction v := by
  cases h with
  | pair u v x => simp [wordAction_append, wordAction, letterAction_inv]

theorem cancel_stack {u v : List (Letter A)} (h : Cancel u v) : stack u = stack v := by
  rw [← wordAction_empty, ← wordAction_empty, cancel_wordAction h]

theorem cancels_stack_eq {u v : List (Letter A)} (h : Cancels u v) : stack u = stack v := by
  induction h with
  | refl => rfl
  | cons h _ ih => exact (cancel_stack h).trans ih

/-- Reducedness is exactly absence of any ordinary deletion. -/
theorem reduced_iff_no_cancel (w : List (Letter A)) :
    Reduced w ↔ ∀ v, ¬ Cancel w v := by
  constructor
  · intro hr v h
    cases h with
    | pair p s x =>
      induction p with
      | nil => exact hr.2 _ _ rfl rfl
      | cons y p ih => exact ih hr.1
  · induction w with
    | nil => intro _; trivial
    | cons x xs ih =>
      intro hn
      refine ⟨ih (fun v h => hn (x :: v) (h.underPrefix [x])), ?_⟩
      intro y ys he hy
      subst y
      subst xs
      exact hn ys (Cancel.pair [] ys x)

/-- Every reduced descendant is the stack value, irrespective of deletion order. -/
theorem reduced_descendant_eq {u v : List (Letter A)}
    (h : Cancels u v) (hr : Reduced v) : v = (stack u).val := by
  rw [cancels_stack_eq h, stack_of_reduced hr]

theorem cancels_confluent {u v w : List (Letter A)}
    (h : Cancels u v) (k : Cancels u w) :
    ∃ z, Cancels v z ∧ Cancels w z := by
  refine ⟨(stack u).val, ?_, ?_⟩
  · rw [cancels_stack_eq h]; exact cancels_stack v
  · rw [cancels_stack_eq k]; exact cancels_stack w

theorem exists_unique_reduced_descendant (w : List (Letter A)) :
    ∃ v, (Cancels w v ∧ Reduced v) ∧
      ∀ z, Cancels w z ∧ Reduced z → z = v := by
  exact ⟨(stack w).val, ⟨cancels_stack w, (stack w).property⟩,
    fun _ h => reduced_descendant_eq h.1 h.2⟩

end StructuralReasons.Words
