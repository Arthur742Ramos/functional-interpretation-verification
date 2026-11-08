import StructuralReasons
import ReducedWords

/-!
The imported base source is an unchanged
copy of the independently checked endpoint-indexed ten-rule presentation.
-/
namespace StructuralReasons

universe u v
variable {V : Type u} {E : V → V → Type v}

/-- A generator identifier includes both endpoints and the actual edge value. -/
abbrev EdgeId (E : V → V → Type v) := Σ a, Σ b, E a b

open Words

/-- Interpret a reason as an invertible action on reduced signed-edge lists. -/
noncomputable def action : {a b : V} → Reason E a b → Action (RWord (EdgeId E))
  | _, _, .atom e => letterAction (.pos ⟨_, _, e⟩)
  | _, _, .rho _ => Action.one
  | _, _, .sigma p => Action.reverse (action p)
  | _, _, .tau p q => Action.mul (action p) (action q)

/-- The auxiliary action forgets typing of lists, but retains full edge identifiers. -/
noncomputable def reducedExpansion {a b : V} (p : Reason E a b) :
    List (Letter (EdgeId E)) := ((action p).forward empty).val

/-- All ten roots preserve both the action and its inverse. -/
theorem root_action {complete : Bool} {a b : V} {p q : Reason E a b}
    (h : Root complete p q) : action p = action q := by
  cases h <;> simp [action, Action.mul_assoc]

/-- The check extends through every constructor context. -/
theorem step_action {complete : Bool} {a b : V} {p q : Reason E a b}
    (h : Step complete p q) : action p = action q := by
  induction h with
  | root h => exact root_action h
  | sigma h ih => exact congrArg Action.reverse ih
  | left r h ih => exact congrArg (fun f => Action.mul f (action r)) ih
  | right p h ih => exact congrArg (Action.mul (action p)) ih

/-- Finite forward reduction, with zero steps included. -/
inductive Steps (complete : Bool) : {a b : V} → Reason E a b → Reason E a b → Prop
  | refl {a b : V} (p : Reason E a b) : Steps complete p p
  | cons {a b : V} {p q r : Reason E a b} :
      Step complete p q → Steps complete q r → Steps complete p r

namespace Steps

variable {complete : Bool} {a b : V} {p q r : Reason E a b}

theorem single (h : Step complete p q) : Steps complete p q := .cons h (.refl _)

theorem trans (h : Steps complete p q) (k : Steps complete q r) :
    Steps complete p r := by
  induction h with
  | refl => exact k
  | cons h _ ih => exact .cons h (ih k)

theorem sigma (h : Steps complete p q) : Steps complete (.sigma p) (.sigma q) := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .cons (.sigma h) ih

theorem left {c : V} (h : Steps complete p q) (r : Reason E b c) :
    Steps complete (.tau p r) (.tau q r) := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .cons (.left r h) ih

theorem right {c : V} (r : Reason E c a) (h : Steps complete p q) :
    Steps complete (.tau r p) (.tau r q) := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .cons (.right r h) ih

end Steps

theorem steps_action {complete : Bool} {a b : V} {p q : Reason E a b}
    (h : Steps complete p q) : action p = action q := by
  induction h with
  | refl => rfl
  | cons h _ ih => exact (step_action h).trans ih

theorem steps_reducedExpansion {complete : Bool} {a b : V} {p q : Reason E a b}
    (h : Steps complete p q) : reducedExpansion p = reducedExpansion q := by
  exact congrArg (fun f : Action (RWord (EdgeId E)) => (f.forward empty).val)
    (steps_action h)

def Normal (complete : Bool) {a b : V} (p : Reason E a b) : Prop :=
  ∀ q, ¬ Step complete p q

theorem normal_steps_eq {complete : Bool} {a b : V} {p q : Reason E a b}
    (hn : Normal complete p) (h : Steps complete p q) : p = q := by
  cases h with
  | refl => rfl
  | cons h _ => exact False.elim (hn _ h)

/-- Existence follows from the already proved termination theorem alone. -/
theorem exists_normal (complete : Bool) {a b : V} (p : Reason E a b) :
    ∃ q, Steps complete p q ∧ Normal complete q := by
  classical
  induction p using (terminating complete a b).induction with
  | h p ih =>
    by_cases h : ∃ q, Step complete p q
    · obtain ⟨q, hpq⟩ := h
      obtain ⟨r, hqr, hnr⟩ := ih q hpq
      exact ⟨r, .cons hpq hqr, hnr⟩
    · exact ⟨p, .refl _, fun q hpq => h ⟨q, hpq⟩⟩

theorem normal_sigma_child {complete : Bool} {a b : V} {p : Reason E a b}
    (h : Normal complete (.sigma p)) : Normal complete p := by
  intro q hpq
  exact h _ (.sigma hpq)

theorem normal_left {complete : Bool} {a b c : V}
    {p : Reason E a b} {q : Reason E b c}
    (h : Normal complete (.tau p q)) : Normal complete p := by
  intro r hpr
  exact h _ (.left q hpr)

theorem normal_right {complete : Bool} {a b c : V}
    {p : Reason E a b} {q : Reason E b c}
    (h : Normal complete (.tau p q)) : Normal complete q := by
  intro r hqr
  exact h _ (.right p hqr)

end StructuralReasons
