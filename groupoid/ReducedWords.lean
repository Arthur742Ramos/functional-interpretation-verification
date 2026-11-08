import Std.Tactic

/-!
Reduced-word actions used in the structural confluence proof.
Signed letters retain their complete atom identifiers. The reduction stack
uses classical equality; its statements impose no decidable-equality assumption.
-/
namespace StructuralReasons.Words

universe u

inductive Letter (A : Type u) where
  | pos : A → Letter A
  | neg : A → Letter A

def inv {A : Type u} : Letter A → Letter A
  | .pos a => .neg a
  | .neg a => .pos a

@[simp] theorem inv_inv {A : Type u} (x : Letter A) : inv (inv x) = x := by
  cases x <;> rfl

@[simp] theorem inv_ne_self {A : Type u} (x : Letter A) : inv x ≠ x := by
  cases x <;> simp [inv]

variable {A : Type u}

/-- Adjacent letters do not form an inverse pair. -/
def Reduced : List (Letter A) → Prop
  | [] => True
  | x :: w => Reduced w ∧ ∀ y ys, w = y :: ys → y ≠ inv x

@[simp] theorem reduced_nil : Reduced ([] : List (Letter A)) := trivial

theorem reduced_tail {x : Letter A} {w : List (Letter A)}
    (h : Reduced (x :: w)) : Reduced w := h.1

noncomputable def push (x : Letter A) (w : List (Letter A)) : List (Letter A) := by
  classical
  exact match w with
    | [] => [x]
    | y :: ys => if y = inv x then ys else x :: y :: ys

@[simp] theorem push_nil (x : Letter A) : push x [] = [x] := rfl

@[simp] theorem push_cancel (x : Letter A) (w : List (Letter A)) :
    push x (inv x :: w) = w := by
  classical
  simp [push]

theorem push_prepend {x : Letter A} {w : List (Letter A)}
    (h : ∀ y ys, w = y :: ys → y ≠ inv x) : push x w = x :: w := by
  classical
  cases w with
  | nil => rfl
  | cons y ys => simp [push, h y ys rfl]

theorem push_reduced (x : Letter A) {w : List (Letter A)}
    (h : Reduced w) : Reduced (push x w) := by
  classical
  cases w with
  | nil => simp [push, Reduced]
  | cons y ys =>
    by_cases he : y = inv x
    · simpa [push, he] using h.1
    · simp only [push, if_neg he, Reduced]
      exact ⟨h, by intro z zs hz; cases hz; exact he⟩

/-- Prepending a letter and then its inverse acts as the identity on reduced words. -/
theorem push_inverse (x : Letter A) {w : List (Letter A)}
    (h : Reduced w) : push (inv x) (push x w) = w := by
  classical
  cases w with
  | nil => simp [push, inv_inv]
  | cons y ys =>
    by_cases he : y = inv x
    · subst y
      rw [push_cancel]
      exact push_prepend h.2
    · simp [push, he, inv_inv]

/-- Reduced words are values, not equivalence classes of words. -/
def RWord (A : Type u) := {w : List (Letter A) // Reduced w}

noncomputable def prepend (x : Letter A) (w : RWord A) : RWord A :=
  ⟨push x w.val, push_reduced x w.property⟩

@[simp] theorem prepend_inverse (x : Letter A) (w : RWord A) :
    prepend (inv x) (prepend x w) = w := by
  apply Subtype.ext
  exact push_inverse x w.property

/-- A bijection together with its specified inverse. -/
structure Action (X : Type u) where
  forward : X → X
  backward : X → X
  backward_forward : ∀ x, backward (forward x) = x
  forward_backward : ∀ x, forward (backward x) = x

namespace Action

variable {X : Type u}

@[ext] theorem ext {f g : Action X}
    (hf : ∀ x, f.forward x = g.forward x)
    (hb : ∀ x, f.backward x = g.backward x) : f = g := by
  cases f
  cases g
  simp only at hf hb
  have h₁ := funext hf
  have h₂ := funext hb
  cases h₁
  cases h₂
  rfl

def one : Action X := ⟨id, id, fun _ => rfl, fun _ => rfl⟩

def reverse (f : Action X) : Action X :=
  ⟨f.backward, f.forward, f.forward_backward, f.backward_forward⟩

/-- Traversal-order product, acting on a suffix from right to left. -/
def mul (f g : Action X) : Action X where
  forward x := f.forward (g.forward x)
  backward x := g.backward (f.backward x)
  backward_forward x := by rw [f.backward_forward, g.backward_forward]
  forward_backward x := by rw [g.forward_backward, f.forward_backward]

@[simp] theorem reverse_one : reverse (one : Action X) = one := rfl
@[simp] theorem reverse_reverse (f : Action X) : reverse (reverse f) = f := rfl
@[simp] theorem mul_one (f : Action X) : mul f one = f := by
  apply ext <;> intro x <;> rfl
@[simp] theorem one_mul (f : Action X) : mul one f = f := by
  apply ext <;> intro x <;> rfl
@[simp] theorem mul_reverse (f : Action X) : mul f (reverse f) = one := by
  apply ext
  · exact f.forward_backward
  · exact f.forward_backward
@[simp] theorem reverse_mul_self (f : Action X) : mul (reverse f) f = one := by
  apply ext
  · exact f.backward_forward
  · exact f.backward_forward
@[simp] theorem reverse_mul (f g : Action X) :
    reverse (mul f g) = mul (reverse g) (reverse f) := by
  apply ext <;> intro x <;> rfl

theorem mul_assoc (f g h : Action X) : mul (mul f g) h = mul f (mul g h) := by
  apply ext <;> intro x <;> rfl

@[simp] theorem cancel_suffix (f g : Action X) : mul f (mul (reverse f) g) = g := by
  rw [← mul_assoc, mul_reverse, one_mul]
@[simp] theorem cancel_inverse_suffix (f g : Action X) :
    mul (reverse f) (mul f g) = g := by
  rw [← mul_assoc, reverse_mul_self, one_mul]

end Action

noncomputable def letterAction (x : Letter A) : Action (RWord A) where
  forward := prepend x
  backward := prepend (inv x)
  backward_forward := prepend_inverse x
  forward_backward w := by simpa using prepend_inverse (inv x) w

@[simp] theorem letterAction_inv (x : Letter A) :
    letterAction (inv x) = Action.reverse (letterAction x) := by
  apply Action.ext
  · intro w; rfl
  · intro w; simp [letterAction, Action.reverse]

/-- Empty words are only used inside a fixed endpoint hom-set later. -/
def empty : RWord A := ⟨[], trivial⟩

noncomputable def stack : List (Letter A) → RWord A
  | [] => empty
  | x :: xs => prepend x (stack xs)

theorem stack_of_reduced {w : List (Letter A)} (h : Reduced w) :
    (stack w).val = w := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    change push x (stack xs).val = x :: xs
    rw [ih h.1]
    exact push_prepend h.2

end StructuralReasons.Words
