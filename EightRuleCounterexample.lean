import ReasonCongruence

/-! The eight-rule peak from manuscript 09a, using the original indexed Step. -/
namespace StructuralReasons.EightRuleCounterexample

inductive Vertex where
  | a | b | c

inductive Edge : Vertex → Vertex → Type where
  | p : Edge .a .b
  | q : Edge .a .c

def p : Reason Edge .a .b := .atom .p
def q : Reason Edge .a .c := .atom .q

def peak : Reason Edge .a .c := .tau (.tau p (.sigma p)) q

def longBranch : Reason Edge .a .c := .tau p (.tau (.sigma p) q)

theorem peak_to_q : Steps false peak q :=
  .cons (.left q (.root (.tr p))) (.single (.root (.tlr q)))

theorem peak_to_longBranch : Steps false peak longBranch :=
  .single (.root (.tt p (.sigma p) q))

theorem atom_normal {V : Type} {E : V → V → Type} {a b : V}
    (complete : Bool) (e : E a b) : Normal complete (.atom e) := by
  intro r h
  cases h with
  | root h => cases h

theorem inverse_atom_normal {V : Type} {E : V → V → Type} {a b : V}
    (complete : Bool) (e : E a b) : Normal complete (.sigma (.atom e)) := by
  intro r h
  cases h with
  | root h => cases h
  | sigma h => exact atom_normal complete e _ h

theorem q_normal : Normal false q := atom_normal false Edge.q

theorem inner_normal : Normal false (.tau (.sigma p) q) := by
  intro r h
  cases h with
  | root h => cases h
  | left r h => exact inverse_atom_normal false Edge.p _ h
  | right r h => exact q_normal _ h

theorem longBranch_normal : Normal false longBranch := by
  intro r h
  cases h with
  | root h =>
    cases h with
    | cancelSuffix enabled => cases enabled
  | left r h => exact atom_normal false Edge.p _ h
  | right r h => exact inner_normal _ h

theorem branches_distinct : q ≠ longBranch := by
  intro h
  cases h

/-- These two actual eight-rule descendants have no common forward descendant. -/
theorem branches_not_joinable :
    ¬ ∃ r, Steps false q r ∧ Steps false longBranch r := by
  rintro ⟨r, hq, hl⟩
  exact branches_distinct ((normal_steps_eq q_normal hq).trans
    (normal_steps_eq longBranch_normal hl).symm)

/-- Failure of confluence in the fixed a-to-c hom-set of this explicit graph. -/
theorem eight_not_confluent :
    ¬ (∀ (s t u : Reason Edge .a .c), Steps false s t → Steps false s u →
      ∃ r, Steps false t r ∧ Steps false u r) := by
  intro h
  exact branches_not_joinable (h peak q longBranch peak_to_q peak_to_longBranch)

theorem branches_congruent : ReasonCongruence false longBranch q :=
  ReasonCongruence.eight_cancelSuffix p q

theorem branches_same_reduced_word :
    (Words.stack (expansion longBranch)).val = (Words.stack (expansion q)).val :=
  (ReasonCongruence.iff_stack_expansion_eq longBranch q).mp branches_congruent

/-- The completed system contracts the long branch at its root. -/
theorem ten_joins_peak : Step true longBranch q :=
  .root (.cancelSuffix rfl p q)

end StructuralReasons.EightRuleCounterexample
