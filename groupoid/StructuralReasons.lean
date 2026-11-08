import Std.Tactic

/-!
Finite endpoint-indexed reasons and the eight- and ten-rule structural fragments.
This file imports only Lean's bundled standard library. The additional two rules
are enabled by a Boolean parameter; the second has the endpoint-preserving result.
-/
namespace StructuralReasons

universe u v

/-- A fixed directed graph, with its vertices and edge family left arbitrary. -/
inductive Reason {V : Type u} (E : V → V → Type v) : V → V → Type (max u v) where
  | atom {a b : V} : E a b → Reason E a b
  | rho (a : V) : Reason E a a
  | sigma {a b : V} : Reason E a b → Reason E b a
  | tau {a b c : V} : Reason E a b → Reason E b c → Reason E a c

variable {V : Type u} {E : V → V → Type v}

structure Counts where
  t : Nat
  d : Nat
  s : Nat
  a : Nat

def counts : {a b : V} → Reason E a b → Counts
  | _, _, .atom _ => ⟨0, 0, 1, 0⟩
  | _, _, .rho _ => ⟨0, 0, 1, 0⟩
  | _, _, .sigma p =>
      let x := counts p
      ⟨x.t, x.d + x.t, x.s + 1, x.a⟩
  | _, _, .tau p q =>
      let x := counts p
      let y := counts q
      ⟨x.t + y.t + 1, x.d + y.d, x.s + y.s + 1, x.a + y.a + x.t⟩

/-- The lexicographic order on (d,s,a), with the smaller argument first. -/
def Smaller (x y : Counts) : Prop :=
  x.d < y.d ∨ x.d = y.d ∧ (x.s < y.s ∨ x.s = y.s ∧ x.a < y.a)

def measure {a b : V} (p : Reason E a b) : Nat × (Nat × Nat) :=
  ((counts p).d, (counts p).s, (counts p).a)

/-- Root rules. For `complete = false`, the last two constructors are unavailable. -/
inductive Root (complete : Bool) :
    {a b : V} → Reason E a b → Reason E a b → Prop where
  | sr (a : V) : Root complete (.sigma (.rho a)) (.rho a)
  | ss {a b : V} (p : Reason E a b) : Root complete (.sigma (.sigma p)) p
  | tr {a b : V} (p : Reason E a b) : Root complete (.tau p (.sigma p)) (.rho a)
  | tsr {a b : V} (p : Reason E a b) : Root complete (.tau (.sigma p) p) (.rho b)
  | trr {a b : V} (p : Reason E a b) : Root complete (.tau p (.rho b)) p
  | tlr {a b : V} (p : Reason E a b) : Root complete (.tau (.rho a) p) p
  | st {a b c : V} (p : Reason E a b) (q : Reason E b c) :
      Root complete (.sigma (.tau p q)) (.tau (.sigma q) (.sigma p))
  | tt {a b c d : V} (p : Reason E a b) (q : Reason E b c) (r : Reason E c d) :
      Root complete (.tau (.tau p q) r) (.tau p (.tau q r))
  | cancelSuffix {a b c : V} (enabled : complete = true)
      (p : Reason E a b) (q : Reason E a c) :
      Root complete (.tau p (.tau (.sigma p) q)) q
  | cancelInvSuffix {a b c : V} (enabled : complete = true)
      (p : Reason E a b) (q : Reason E b c) :
      Root complete (.tau (.sigma p) (.tau p q)) q

/-- Exactly one root contraction, closed under all typed constructor positions. -/
inductive Step (complete : Bool) :
    {a b : V} → Reason E a b → Reason E a b → Prop where
  | root {a b : V} {p q : Reason E a b} :
      Root complete p q → Step complete p q
  | sigma {a b : V} {p q : Reason E a b} :
      Step complete p q → Step complete (.sigma p) (.sigma q)
  | left {a b c : V} {p q : Reason E a b} (r : Reason E b c) :
      Step complete p q → Step complete (.tau p r) (.tau q r)
  | right {a b c : V} (p : Reason E a b) {q r : Reason E b c} :
      Step complete q r → Step complete (.tau p q) (.tau p r)

/-- Each root contraction preserves the auxiliary inequality and decreases (d,s,a). -/
theorem root_decreases {complete : Bool} {a b : V} {p q : Reason E a b}
    (h : Root complete p q) :
    (counts q).t ≤ (counts p).t ∧ Smaller (counts q) (counts p) := by
  cases h <;> simp [counts, Smaller] <;> omega

/-- The same statement holds at every finite constructor position. -/
theorem step_decreases {complete : Bool} {a b : V} {p q : Reason E a b}
    (h : Step complete p q) :
    (counts q).t ≤ (counts p).t ∧ Smaller (counts q) (counts p) := by
  induction h with
  | root h => exact root_decreases h
  | sigma h ih =>
      simp only [counts, Smaller] at *
      omega
  | left r h ih =>
      simp only [counts, Smaller] at *
      omega
  | right p h ih =>
      simp only [counts, Smaller] at *
      omega

def TripleLT : (Nat × (Nat × Nat)) → (Nat × (Nat × Nat)) → Prop :=
  Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)

theorem triple_wellFounded : WellFounded TripleLT :=
  (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel Nat.lt_wfRel)).wf

theorem step_measure_decreases {complete : Bool} {a b : V}
    {p q : Reason E a b} (h : Step complete p q) :
    TripleLT (measure q) (measure p) := by
  simpa only [TripleLT, Prod.lex_def, measure] using (step_decreases h).2

/-- Termination is well-foundedness with the reduction direction reversed. -/
theorem terminating (complete : Bool) (a b : V) :
    WellFounded (fun q p : Reason E a b => Step complete p q) := by
  apply Subrelation.wf (r := InvImage TripleLT measure)
  · intro q p h
    exact step_measure_decreases h
  · exact InvImage.wf measure triple_wellFounded

theorem eight_terminating (a b : V) :
    WellFounded (fun q p : Reason E a b => Step false p q) :=
  terminating false a b

theorem ten_terminating (a b : V) :
    WellFounded (fun q p : Reason E a b => Step true p q) :=
  terminating true a b

/-- No infinite sequence of contextual contractions exists in a fixed hom-set. -/
theorem no_infinite_reduction (complete : Bool) (a b : V)
    (f : Nat → Reason E a b) : ¬ (∀ n, Step complete (f n) (f (n + 1))) := by
  intro h
  have impossible : ∀ p : Reason E a b,
      ∀ f : Nat → Reason E a b, f 0 = p →
      (∀ n, Step complete (f n) (f (n + 1))) → False := by
    intro p
    induction p using (terminating complete a b).induction with
    | h p ih =>
      intro f first steps
      have next : Step complete p (f 1) := by
        simpa only [first] using steps 0
      exact ih (f 1) next (fun n => f (n + 1)) rfl (fun n => steps (n + 1))
  exact impossible (f 0) f rfl h

end StructuralReasons

#print axioms StructuralReasons.root_decreases
#print axioms StructuralReasons.step_decreases
#print axioms StructuralReasons.step_measure_decreases
#print axioms StructuralReasons.eight_terminating
#print axioms StructuralReasons.ten_terminating
#print axioms StructuralReasons.no_infinite_reduction

