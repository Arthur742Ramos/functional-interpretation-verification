import Std.Tactic

/-!
The exact raw 37-rule equality-reason skeleton. No typed interpretation or
additional identity-coherence, product, universal or beta-residual rules are included.
All contexts have exactly one hole; their fixed children are arbitrary raw trees.
-/
namespace EqualitySkeleton
universe u
inductive Reason (Atom : Type u) where
  | atom : Atom → Reason Atom
  | rho : Reason Atom
  | sigma : Reason Atom → Reason Atom
  | tau : Reason Atom → Reason Atom → Reason Atom
  | subL : Reason Atom → Reason Atom → Reason Atom
  | subR : Reason Atom → Reason Atom → Reason Atom
  | xi1 : Reason Atom → Reason Atom
  | xi2 : Reason Atom → Reason Atom → Reason Atom
  | mu1 : Reason Atom → Reason Atom
  | mu2 : Reason Atom → Reason Atom → Reason Atom
  | mu3 : Reason Atom → Reason Atom → Reason Atom → Reason Atom
  | nu1 : Reason Atom → Reason Atom

variable {A : Type u}
open Reason

def W : Reason A → Nat
  | .atom _ | .rho => 1
  | .sigma p => 2 * W p
  | .tau p q => 1 + W p + W q
  | .subL p q => 1 + W p + W q
  | .subR p q => 1 + W p + W q
  | .xi1 p => 1 + W p
  | .xi2 p q => 1 + W p + W q
  | .mu1 p => 1 + W p
  | .mu2 p q => 1 + W p + W q
  | .mu3 p q r => 1 + W p + W q + W r
  | .nu1 p => 1 + W p

def Q : Reason A → Nat
  | .atom _ | .rho => 0
  | .sigma p => Q p
  | .tau p q => Q p + Q q + W p
  | .subL p q => Q p + Q q
  | .subR p q => Q p + Q q
  | .xi1 p => Q p
  | .xi2 p q => Q p + Q q
  | .mu1 p => Q p
  | .mu2 p q => Q p + Q q
  | .mu3 p q r => Q p + Q q + Q r
  | .nu1 p => Q p

theorem W_pos (p : Reason A) : 0 < W p := by
  induction p <;> simp_all [W] <;> omega

inductive Context (A : Type u) where
  | hole : Context A
  | sigma : Context A → Context A
  | tau1 : Context A → Reason A → Context A
  | tau2 : Reason A → Context A → Context A
  | subL1 : Context A → Reason A → Context A
  | subL2 : Reason A → Context A → Context A
  | subR1 : Context A → Reason A → Context A
  | subR2 : Reason A → Context A → Context A
  | xi1 : Context A → Context A
  | xi21 : Context A → Reason A → Context A
  | xi22 : Reason A → Context A → Context A
  | mu1 : Context A → Context A
  | mu21 : Context A → Reason A → Context A
  | mu22 : Reason A → Context A → Context A
  | mu31 : Context A → Reason A → Reason A → Context A
  | mu32 : Reason A → Context A → Reason A → Context A
  | mu33 : Reason A → Reason A → Context A → Context A
  | nu1 : Context A → Context A

namespace Context

def fill : Context A → Reason A → Reason A
  | .hole, p => p
  | .sigma C, p => .sigma (fill C p)
  | .tau1 C s1, p => .tau (fill C p) s1
  | .tau2 s0 C, p => .tau s0 (fill C p)
  | .subL1 C s1, p => .subL (fill C p) s1
  | .subL2 s0 C, p => .subL s0 (fill C p)
  | .subR1 C s1, p => .subR (fill C p) s1
  | .subR2 s0 C, p => .subR s0 (fill C p)
  | .xi1 C, p => .xi1 (fill C p)
  | .xi21 C s1, p => .xi2 (fill C p) s1
  | .xi22 s0 C, p => .xi2 s0 (fill C p)
  | .mu1 C, p => .mu1 (fill C p)
  | .mu21 C s1, p => .mu2 (fill C p) s1
  | .mu22 s0 C, p => .mu2 s0 (fill C p)
  | .mu31 C s1 s2, p => .mu3 (fill C p) s1 s2
  | .mu32 s0 C s2, p => .mu3 s0 (fill C p) s2
  | .mu33 s0 s1 C, p => .mu3 s0 s1 (fill C p)
  | .nu1 C, p => .nu1 (fill C p)

/-- Positive coefficient of the one hole in the primary weight. -/
def coeff : Context A → Nat
  | .hole => 1
  | .sigma C => 2 * coeff C
  | .tau1 C _ => coeff C
  | .tau2 _ C => coeff C
  | .subL1 C _ => coeff C
  | .subL2 _ C => coeff C
  | .subR1 C _ => coeff C
  | .subR2 _ C => coeff C
  | .xi1 C => coeff C
  | .xi21 C _ => coeff C
  | .xi22 _ C => coeff C
  | .mu1 C => coeff C
  | .mu21 C _ => coeff C
  | .mu22 _ C => coeff C
  | .mu31 C _ _ => coeff C
  | .mu32 _ C _ => coeff C
  | .mu33 _ _ C => coeff C
  | .nu1 C => coeff C

def offset : Context A → Nat
  | .hole => 0
  | .sigma C => 2 * offset C
  | .tau1 C s1 => 1 + offset C + W s1
  | .tau2 s0 C => 1 + W s0 + offset C
  | .subL1 C s1 => 1 + offset C + W s1
  | .subL2 s0 C => 1 + W s0 + offset C
  | .subR1 C s1 => 1 + offset C + W s1
  | .subR2 s0 C => 1 + W s0 + offset C
  | .xi1 C => 1 + offset C
  | .xi21 C s1 => 1 + offset C + W s1
  | .xi22 s0 C => 1 + W s0 + offset C
  | .mu1 C => 1 + offset C
  | .mu21 C s1 => 1 + offset C + W s1
  | .mu22 s0 C => 1 + W s0 + offset C
  | .mu31 C s1 s2 => 1 + offset C + W s1 + W s2
  | .mu32 s0 C s2 => 1 + W s0 + offset C + W s2
  | .mu33 s0 s1 C => 1 + W s0 + W s1 + offset C
  | .nu1 C => 1 + offset C

theorem coeff_pos (C : Context A) : 0 < C.coeff := by
  induction C <;> simp_all [coeff] <;> omega

theorem weight_affine (C : Context A) (p : Reason A) :
    W (C.fill p) = C.coeff * W p + C.offset := by
  induction C <;> simp_all [fill, W, coeff, offset, Nat.mul_add, Nat.mul_assoc] <;> omega

theorem weight_mono (C : Context A) {p q : Reason A} (h : W p ≤ W q) :
    W (C.fill p) ≤ W (C.fill q) := by
  induction C <;> simp_all [fill, W] <;> omega

theorem weight_strict (C : Context A) {p q : Reason A} (h : W p < W q) :
    W (C.fill p) < W (C.fill q) := by
  induction C <;> simp_all [fill, W] <;> omega

theorem weight_equal (C : Context A) {p q : Reason A} (h : W p = W q) :
    W (C.fill p) = W (C.fill q) := by
  simp only [weight_affine, h]

theorem secondary_strict (C : Context A) {p q : Reason A}
    (hw : W p = W q) (hq : Q p < Q q) :
    Q (C.fill p) < Q (C.fill q) := by
  induction C <;> simp_all [fill, Q]
  rename_i C s ih
  have hc := C.weight_equal hw
  omega

end Context

/-- Smaller target first; the primary component has priority. -/
def Smaller (p q : Reason A) : Prop :=
  W p < W q ∨ W p = W q ∧ Q p < Q q

theorem context_decreases (C : Context A) {p q : Reason A}
    (h : Smaller p q) : Smaller (C.fill p) (C.fill q) := by
  rcases h with h | ⟨hw, hq⟩
  · exact Or.inl (C.weight_strict h)
  · exact Or.inr ⟨C.weight_equal hw, C.secondary_strict hw hq⟩

/-- Exactly the 37 numbered patterns, with the corrected tail in rule 37. -/
inductive Root : Reason A → Reason A → Prop where
  | r01  : Root (sigma rho) rho
  | r02 (r : Reason A) : Root (sigma (sigma r)) r
  | r03 (C : Context A) (r : Reason A) : Root (tau (C.fill r) (C.fill (sigma r))) (C.fill rho)
  | r04 (C : Context A) (r : Reason A) : Root (tau (C.fill (sigma r)) (C.fill r)) (C.fill rho)
  | r05 (C : Context A) (r : Reason A) : Root (tau (C.fill r) (C.fill rho)) (C.fill r)
  | r06 (C : Context A) (r : Reason A) : Root (tau (C.fill rho) (C.fill r)) (C.fill r)
  | r07 (C : Context A) (r : Reason A) : Root (subL (C.fill r) (C.fill rho)) (C.fill r)
  | r08 (C : Context A) (r : Reason A) : Root (subR (C.fill rho) (C.fill r)) (C.fill r)
  | r09 (C : Context A) (s r : Reason A) : Root (subL (subL s (C.fill r)) (C.fill (sigma r))) s
  | r10 (C : Context A) (s r : Reason A) : Root (subL (subL s (C.fill (sigma r))) (C.fill r)) s
  | r11 (C : Context A) (s r : Reason A) : Root (subR (C.fill s) (subR (C.fill (sigma s)) r)) r
  | r12 (C : Context A) (s r : Reason A) : Root (subR (C.fill (sigma s)) (subR (C.fill s) r)) r
  | r13 (r s : Reason A) : Root (mu1 (xi2 r s)) r
  | r14 (r s : Reason A) : Root (mu1 (xi2 r s)) s
  | r15 (r s u : Reason A) : Root (mu3 (xi1 r) s u) s
  | r16 (r s u : Reason A) : Root (mu3 (xi1 r) s u) u
  | r17 (s r : Reason A) : Root (mu2 s (xi1 r)) r
  | r18 (r s : Reason A) : Root (mu2 (xi1 r) s) s
  | r19 (r : Reason A) : Root (xi1 (mu1 r)) r
  | r20 (t r s : Reason A) : Root (mu3 t (xi1 r) (xi1 s)) t
  | r21 (r s : Reason A) : Root (xi1 (mu2 r s)) s
  | r22 (s r : Reason A) : Root (mu2 s (xi1 r)) s
  | r23 (r s : Reason A) : Root (sigma (tau r s)) (tau (sigma s) (sigma r))
  | r24 (r s : Reason A) : Root (sigma (subL r s)) (subR (sigma s) (sigma r))
  | r25 (r s : Reason A) : Root (sigma (subR r s)) (subL (sigma s) (sigma r))
  | r26 (r : Reason A) : Root (sigma (xi1 r)) (xi1 (sigma r))
  | r27 (s r : Reason A) : Root (sigma (xi2 s r)) (xi2 (sigma s) (sigma r))
  | r28 (r : Reason A) : Root (sigma (mu1 r)) (mu1 (sigma r))
  | r29 (s r : Reason A) : Root (sigma (mu2 s r)) (mu2 (sigma s) (sigma r))
  | r30 (r u v : Reason A) : Root (sigma (mu3 r u v)) (mu3 (sigma r) (sigma u) (sigma v))
  | r31 (r s : Reason A) : Root (tau r (subL rho s)) (subL r s)
  | r32 (r s : Reason A) : Root (tau r (subR s rho)) (subL r s)
  | r33 (r s t : Reason A) : Root (tau (subL r s) t) (tau r (subR s t))
  | r34 (s t u : Reason A) : Root (tau (subR s t) u) (subR s (tau t u))
  | r35 (t r s : Reason A) : Root (tau (tau t r) s) (tau t (tau r s))
  | r36 (C : Context A) (u v : Reason A) : Root (tau (C.fill u) (tau (C.fill (sigma u)) v)) v
  | r37 (C : Context A) (u v : Reason A) : Root (tau (C.fill (sigma u)) (tau (C.fill u) v)) v

theorem root_decreases {p q : Reason A} (h : Root p q) : Smaller q p := by
  have hp := W_pos q
  cases h with
  | r01  =>
      simp only [Smaller, W, Q]
      omega
  | r02 r =>
      simp only [Smaller, W, Q]
      omega
  | r03 C r =>
      have hr : W (rho : Reason A) ≤ W r := by have := W_pos r; simp only [W]; omega
      have hc := C.weight_mono hr
      simp only [Smaller, W, Q]
      omega
  | r04 C r =>
      have hr : W (rho : Reason A) ≤ W r := by have := W_pos r; simp only [W]; omega
      have hc := C.weight_mono hr
      simp only [Smaller, W, Q]
      omega
  | r05 C r =>
      simp only [Smaller, W, Q]
      omega
  | r06 C r =>
      simp only [Smaller, W, Q]
      omega
  | r07 C r =>
      simp only [Smaller, W, Q]
      omega
  | r08 C r =>
      simp only [Smaller, W, Q]
      omega
  | r09 C s r =>
      simp only [Smaller, W, Q]
      omega
  | r10 C s r =>
      simp only [Smaller, W, Q]
      omega
  | r11 C s r =>
      simp only [Smaller, W, Q]
      omega
  | r12 C s r =>
      simp only [Smaller, W, Q]
      omega
  | r13 r s =>
      simp only [Smaller, W, Q]
      omega
  | r14 r s =>
      simp only [Smaller, W, Q]
      omega
  | r15 r s u =>
      simp only [Smaller, W, Q]
      omega
  | r16 r s u =>
      simp only [Smaller, W, Q]
      omega
  | r17 s r =>
      simp only [Smaller, W, Q]
      omega
  | r18 r s =>
      simp only [Smaller, W, Q]
      omega
  | r19 r =>
      simp only [Smaller, W, Q]
      omega
  | r20 t r s =>
      simp only [Smaller, W, Q]
      omega
  | r21 r s =>
      simp only [Smaller, W, Q]
      omega
  | r22 s r =>
      simp only [Smaller, W, Q]
      omega
  | r23 r s =>
      simp only [Smaller, W, Q]
      omega
  | r24 r s =>
      simp only [Smaller, W, Q]
      omega
  | r25 r s =>
      simp only [Smaller, W, Q]
      omega
  | r26 r =>
      simp only [Smaller, W, Q]
      omega
  | r27 s r =>
      simp only [Smaller, W, Q]
      omega
  | r28 r =>
      simp only [Smaller, W, Q]
      omega
  | r29 s r =>
      simp only [Smaller, W, Q]
      omega
  | r30 r u v =>
      simp only [Smaller, W, Q]
      omega
  | r31 r s =>
      simp only [Smaller, W, Q]
      omega
  | r32 r s =>
      simp only [Smaller, W, Q]
      omega
  | r33 r s t =>
      simp only [Smaller, W, Q]
      omega
  | r34 s t u =>
      simp only [Smaller, W, Q]
      omega
  | r35 t r s =>
      simp only [Smaller, W, Q]
      omega
  | r36 C u v =>
      simp only [Smaller, W, Q]
      omega
  | r37 C u v =>
      simp only [Smaller, W, Q]
      omega

/-- One root instance at one arbitrary finite constructor position. -/
inductive Step : Reason A → Reason A → Prop where
  | under (C : Context A) {p q : Reason A} :
      Root p q → Step (C.fill p) (C.fill q)

theorem step_decreases {p q : Reason A} (h : Step p q) : Smaller q p := by
  cases h with
  | under C h => exact context_decreases C (root_decreases h)

def rank (p : Reason A) : Nat × Nat := (W p, Q p)
def RankLT : (Nat × Nat) → (Nat × Nat) → Prop := Prod.Lex Nat.lt Nat.lt

theorem rank_wellFounded : WellFounded RankLT :=
  (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

theorem step_rank_decreases {p q : Reason A} (h : Step p q) :
    RankLT (rank q) (rank p) := by
  simpa only [RankLT, Prod.lex_def, rank, Smaller] using step_decreases h

/-- Strong normalisation for every finite raw tree, with arbitrary atoms. -/
theorem terminating : WellFounded (fun q p : Reason A => Step p q) := by
  apply Subrelation.wf (r := InvImage RankLT rank)
  · intro q p h
    exact step_rank_decreases h
  · exact InvImage.wf rank rank_wellFounded

theorem no_infinite_reduction (f : Nat → Reason A) :
    ¬ (∀ n, Step (f n) (f (n + 1))) := by
  intro h
  have impossible : ∀ p : Reason A, ∀ f : Nat → Reason A, f 0 = p →
      (∀ n, Step (f n) (f (n + 1))) → False := by
    intro p
    induction p using terminating.induction with
    | h p ih =>
      intro f first steps
      have next : Step p (f 1) := by simpa only [first] using steps 0
      exact ih (f 1) next (fun n => f (n + 1)) rfl (fun n => steps (n + 1))
  exact impossible (f 0) f rfl h

/-- Compose two one-hole contexts without duplicating the hole. -/
def Context.comp : Context A → Context A → Context A
  | .hole, D => D
  | .sigma C, D => .sigma (C.comp D)
  | .tau1 C s1, D => .tau1 (C.comp D) s1
  | .tau2 s0 C, D => .tau2 s0 (C.comp D)
  | .subL1 C s1, D => .subL1 (C.comp D) s1
  | .subL2 s0 C, D => .subL2 s0 (C.comp D)
  | .subR1 C s1, D => .subR1 (C.comp D) s1
  | .subR2 s0 C, D => .subR2 s0 (C.comp D)
  | .xi1 C, D => .xi1 (C.comp D)
  | .xi21 C s1, D => .xi21 (C.comp D) s1
  | .xi22 s0 C, D => .xi22 s0 (C.comp D)
  | .mu1 C, D => .mu1 (C.comp D)
  | .mu21 C s1, D => .mu21 (C.comp D) s1
  | .mu22 s0 C, D => .mu22 s0 (C.comp D)
  | .mu31 C s1 s2, D => .mu31 (C.comp D) s1 s2
  | .mu32 s0 C s2, D => .mu32 s0 (C.comp D) s2
  | .mu33 s0 s1 C, D => .mu33 s0 s1 (C.comp D)
  | .nu1 C, D => .nu1 (C.comp D)

theorem Context.fill_comp (C D : Context A) (p : Reason A) :
    (C.comp D).fill p = C.fill (D.fill p) := by
  induction C <;> simp_all [comp, fill]

theorem Step.root {p q : Reason A} (h : Root p q) : Step p q :=
  Step.under .hole h

theorem Step.context (C : Context A) {p q : Reason A} (h : Step p q) :
    Step (C.fill p) (C.fill q) := by
  cases h with
  | under D h =>
      simpa only [Context.fill_comp] using Step.under (C.comp D) h

inductive Steps : Reason A → Reason A → Prop where
  | refl (p) : Steps p p
  | cons {p q r} : Step p q → Steps q r → Steps p r

def Normal (p : Reason A) : Prop := ∀ q, ¬ Step p q

theorem no_root_below_rho (C : Context A) (p q : Reason A)
    (e : C.fill p = rho) (h : Root p q) : False := by
  cases C <;> simp_all [Context.fill] <;> cases h

theorem no_root_below_xi1_rho (C : Context A) (p q : Reason A)
    (e : C.fill p = xi1 rho) (h : Root p q) : False := by
  cases C <;> simp_all [Context.fill]
  · cases h
  · exact no_root_below_rho _ _ _ e h

theorem rho_normal : Normal (rho : Reason A) := by
  intro q h
  generalize e : (rho : Reason A) = p at h
  cases h with
  | under C h => exact no_root_below_rho C _ _ e.symm h

theorem xi1_rho_normal : Normal (xi1 (rho : Reason A)) := by
  intro q h
  generalize e : (xi1 (rho : Reason A)) = p at h
  cases h with
  | under C h => exact no_root_below_xi1_rho C _ _ e.symm h

theorem normal_steps_eq {p q : Reason A} (hn : Normal p) (h : Steps p q) : q = p := by
  cases h with
  | refl => rfl
  | cons h _ => exact False.elim (hn _ h)

/-- The injection-shaped raw peak already exists with the reflexivity reason. -/
def peak : Reason A := tau (xi1 rho) (sigma (xi1 rho))

theorem peak_to_rho : Steps (peak : Reason A) rho :=
  .cons (.root (.r03 .hole (xi1 rho))) (.refl _)

theorem peak_to_xi1_rho : Steps (peak : Reason A) (xi1 rho) := by
  apply Steps.cons (q := tau (xi1 rho) (xi1 (sigma rho)))
  · exact Step.under (.tau2 (xi1 rho) .hole) (Root.r26 rho)
  · exact .cons (.root (.r03 (.xi1 .hole) rho)) (.refl _)

def Confluent : Prop := ∀ (p q r : Reason A), Steps p q → Steps p r →
  ∃ s, Steps q s ∧ Steps r s

theorem not_confluent : ¬ Confluent (A := A) := by
  intro h
  obtain ⟨s, hs, ht⟩ := h peak rho (xi1 rho) peak_to_rho peak_to_xi1_rho
  have h₁ := normal_steps_eq rho_normal hs
  have h₂ := normal_steps_eq xi1_rho_normal ht
  cases h₁.symm.trans h₂

end EqualitySkeleton

#print axioms EqualitySkeleton.Reason
#print axioms EqualitySkeleton.W
#print axioms EqualitySkeleton.Q
#print axioms EqualitySkeleton.W_pos
#print axioms EqualitySkeleton.Context
#print axioms EqualitySkeleton.Context.fill
#print axioms EqualitySkeleton.Context.coeff
#print axioms EqualitySkeleton.Context.offset
#print axioms EqualitySkeleton.Context.coeff_pos
#print axioms EqualitySkeleton.Context.weight_affine
#print axioms EqualitySkeleton.Context.weight_mono
#print axioms EqualitySkeleton.Context.weight_strict
#print axioms EqualitySkeleton.Context.weight_equal
#print axioms EqualitySkeleton.Context.secondary_strict
#print axioms EqualitySkeleton.Smaller
#print axioms EqualitySkeleton.context_decreases
#print axioms EqualitySkeleton.Root
#print axioms EqualitySkeleton.root_decreases
#print axioms EqualitySkeleton.Step
#print axioms EqualitySkeleton.step_decreases
#print axioms EqualitySkeleton.rank
#print axioms EqualitySkeleton.RankLT
#print axioms EqualitySkeleton.rank_wellFounded
#print axioms EqualitySkeleton.step_rank_decreases
#print axioms EqualitySkeleton.terminating
#print axioms EqualitySkeleton.no_infinite_reduction
#print axioms EqualitySkeleton.Context.comp
#print axioms EqualitySkeleton.Context.fill_comp
#print axioms EqualitySkeleton.Step.root
#print axioms EqualitySkeleton.Step.context
#print axioms EqualitySkeleton.Steps
#print axioms EqualitySkeleton.Normal
#print axioms EqualitySkeleton.no_root_below_rho
#print axioms EqualitySkeleton.no_root_below_xi1_rho
#print axioms EqualitySkeleton.rho_normal
#print axioms EqualitySkeleton.xi1_rho_normal
#print axioms EqualitySkeleton.normal_steps_eq
#print axioms EqualitySkeleton.peak
#print axioms EqualitySkeleton.peak_to_rho
#print axioms EqualitySkeleton.peak_to_xi1_rho
#print axioms EqualitySkeleton.Confluent
#print axioms EqualitySkeleton.not_confluent
