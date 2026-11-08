import StructuralInvariant

namespace StructuralReasons
universe u v
variable {V : Type u} {E : V → V → Type v}
open Words

/-- Right-associated signed-atom trees without a trailing reflexivity. -/
inductive Shape : {a b : V} → Reason E a b → List (Letter (EdgeId E)) → Prop
  | nil (a : V) : Shape (.rho a) []
  | pos {a b : V} (e : E a b) : Shape (.atom e) [.pos ⟨a, b, e⟩]
  | neg {a b : V} (e : E a b) : Shape (.sigma (.atom e)) [.neg ⟨a, b, e⟩]
  | posCons {a b c : V} (e : E a b) {p : Reason E b c} {w} :
      Shape p w → w ≠ [] → Shape (.tau (.atom e) p) (.pos ⟨a, b, e⟩ :: w)
  | negCons {a b c : V} (e : E b a) {p : Reason E b c} {w} :
      Shape p w → w ≠ [] → Shape (.tau (.sigma (.atom e)) p) (.neg ⟨b, a, e⟩ :: w)

/-- Every irreducible reason has the required shape. Reduction of the word is separate. -/
theorem normal_shape {a b : V} {p : Reason E a b} (hn : Normal true p) :
    ∃ w, Shape p w := by
  induction p with
  | atom e => exact ⟨_, .pos e⟩
  | rho a => exact ⟨_, .nil a⟩
  | sigma p ih =>
    cases p with
    | atom e => exact ⟨_, .neg e⟩
    | rho a => exact False.elim (hn _ (.root (.sr _)))
    | sigma p => exact False.elim (hn _ (.root (.ss p)))
    | tau p q => exact False.elim (hn _ (.root (.st p q)))
  | tau p q ihp ihq =>
    obtain ⟨w, hw⟩ := ihq (normal_right hn)
    have hne : w ≠ [] := by
      intro he
      subst w
      cases hw
      exact hn _ (.root (.trr p))
    cases p with
    | atom e => exact ⟨_, .posCons e hw hne⟩
    | rho a => exact False.elim (hn _ (.root (.tlr q)))
    | tau p r => exact False.elim (hn _ (.root (.tt p r q)))
    | sigma p =>
      cases p with
      | atom e => exact ⟨_, .negCons e hw hne⟩
      | rho a => exact False.elim ((normal_left hn) _ (.root (.sr _)))
      | sigma p => exact False.elim ((normal_left hn) _ (.root (.ss p)))
      | tau p r => exact False.elim ((normal_left hn) _ (.root (.st p r)))

/-- Equality of complete generator identifiers recovers the endpoints and edge. -/
theorem edgeId_heq {a b c d : V} {e : E a b} {f : E c d}
    (h : (⟨a, b, e⟩ : EdgeId E) = ⟨c, d, f⟩) : a = c ∧ b = d ∧ HEq e f := by
  cases h
  exact ⟨rfl, rfl, HEq.rfl⟩

/-- A shape beginning with a positive letter starts with the corresponding atom. -/
theorem shape_pos_head {a b c d : V} {e : E a b} {p : Reason E c d} {w}
    (h : Shape p (.pos ⟨a, b, e⟩ :: w)) :
    c = a ∧ ( (w = [] ∧ d = b ∧ HEq p (Reason.atom e)) ∨
      ∃ q : Reason E b d, HEq p (Reason.tau (.atom e) q) ∧ Shape q w ∧ w ≠ []) := by
  cases h with
  | pos f => exact ⟨rfl, Or.inl ⟨rfl, rfl, HEq.rfl⟩⟩
  | posCons f h hn => exact ⟨rfl, Or.inr ⟨_, HEq.rfl, h, hn⟩⟩

/-- A shape beginning with a negative letter starts with the corresponding inverse atom. -/
theorem shape_neg_head {a b c d : V} {e : E a b} {p : Reason E c d} {w}
    (h : Shape p (.neg ⟨a, b, e⟩ :: w)) :
    c = b ∧ ( (w = [] ∧ d = a ∧ HEq p (Reason.sigma (.atom e))) ∨
      ∃ q : Reason E a d, HEq p (Reason.tau (.sigma (.atom e)) q) ∧ Shape q w ∧ w ≠ []) := by
  cases h with
  | neg f => exact ⟨rfl, Or.inl ⟨rfl, rfl, HEq.rfl⟩⟩
  | negCons f h hn => exact ⟨rfl, Or.inr ⟨_, HEq.rfl, h, hn⟩⟩

/-- Normality excludes the adjacent inverse pair at every spine position. -/
theorem normal_shape_reduced {a b : V} {p : Reason E a b} {w}
    (hs : Shape p w) (hn : Normal true p) : Reduced w := by
  induction hs with
  | nil => trivial
  | pos => simp [Reduced]
  | neg => simp [Reduced]
  | @posCons a b c e p w hs hne ih =>
    refine ⟨ih (normal_right hn), ?_⟩
    intro y ys he hy
    subst y
    change w = .neg ⟨a, b, e⟩ :: ys at he
    rw [he] at hs
    obtain ⟨_, h⟩ := shape_neg_head hs
    rcases h with ⟨_, hend, hp⟩ | ⟨q, hp, _, _⟩
    · subst c
      cases hp
      exact hn _ (.root (.tr (.atom e)))
    · cases hp
      exact hn _ (.root (.cancelSuffix rfl (.atom e) q))
  | @negCons a b c e p w hs hne ih =>
    refine ⟨ih (normal_right hn), ?_⟩
    intro y ys he hy
    subst y
    change w = .pos ⟨b, a, e⟩ :: ys at he
    rw [he] at hs
    obtain ⟨_, h⟩ := shape_pos_head hs
    rcases h with ⟨_, hend, hp⟩ | ⟨q, hp, _, _⟩
    · subst c
      cases hp
      exact hn _ (.root (.tsr (.atom e)))
    · cases hp
      exact hn _ (.root (.cancelInvSuffix rfl (.atom e) q))

/-- On a reduced canonical spine, the action reads off its literal word. -/
theorem shape_action_word {a b : V} {p : Reason E a b} {w}
    (hs : Shape p w) (hr : Reduced w) : reducedExpansion p = w := by
  induction hs with
  | nil => rfl
  | pos => rfl
  | neg => rfl
  | posCons e hs hne ih =>
    change push (.pos ⟨_, _, e⟩) (reducedExpansion _) = _
    rw [ih hr.1]
    exact push_prepend hr.2
  | negCons e hs hne ih =>
    change push (.neg ⟨_, _, e⟩) (reducedExpansion _) = _
    rw [ih hr.1]
    exact push_prepend hr.2

/-- In a fixed hom-set a literal spine word determines its complete reason tree. -/
theorem shape_injective {a b : V} {p q : Reason E a b} {w}
    (hp : Shape p w) (hq : Shape q w) : p = q := by
  induction hp with
  | nil => cases hq; rfl
  | pos e =>
    cases hq with
    | pos => rfl
    | posCons f h hn => exact False.elim (hn rfl)
  | neg e =>
    cases hq with
    | neg => rfl
    | negCons f h hn => exact False.elim (hn rfl)
  | posCons e h hn ih =>
    cases hq with
    | pos => exact False.elim (hn rfl)
    | posCons f hq hqn => exact congrArg (Reason.tau (.atom e)) (ih hq)
  | negCons e h hn ih =>
    cases hq with
    | neg => exact False.elim (hn rfl)
    | negCons f hq hqn => exact congrArg (Reason.tau (.sigma (.atom e))) (ih hq)

/-- A reduced spine has no root contraction, including either completion root. -/
theorem shape_root_normal {a b : V} {p q : Reason E a b} {w}
    (hs : Shape p w) (hr : Reduced w) : ¬ Root true p q := by
  intro h
  cases hs with
  | nil => cases h
  | pos => cases h
  | neg => cases h
  | posCons e hs hn =>
    cases h with
    | tr =>
      cases hs
      exact hr.2 _ _ rfl rfl
    | trr =>
      cases hs
      exact hn rfl
    | cancelSuffix enabled p q =>
      cases hs
      exact hr.2 _ _ rfl rfl
  | negCons e hs hn =>
    cases h with
    | tr => cases hs
    | tsr =>
      cases hs
      exact hr.2 _ _ rfl rfl
    | trr =>
      cases hs
      exact hn rfl
    | cancelSuffix enabled p q => cases hs
    | cancelInvSuffix enabled p q =>
      cases hs
      exact hr.2 _ _ rfl rfl

/-- Conversely, no contextual contraction is possible in a reduced spine. -/
theorem shape_normal {a b : V} {p : Reason E a b} {w}
    (hs : Shape p w) (hr : Reduced w) : Normal true p := by
  have atom_normal : ∀ {a b : V} (e : E a b), Normal true (.atom e) := by
    intro a b e q h
    cases h with
    | root h => cases h
  have neg_normal : ∀ {a b : V} (e : E a b), Normal true (.sigma (.atom e)) := by
    intro a b e q h
    cases h with
    | root h => cases h
    | sigma h => exact atom_normal e _ h
  induction hs with
  | nil =>
    intro q h
    cases h with
    | root h => cases h
  | pos e => exact atom_normal e
  | neg e => exact neg_normal e
  | posCons e hs hn ih =>
    intro q h
    cases h with
    | root h => exact shape_root_normal (.posCons e hs hn) hr h
    | left r h => exact atom_normal e _ h
    | right p h => exact ih hr.1 _ h
  | negCons e hs hn ih =>
    intro q h
    cases h with
    | root h => exact shape_root_normal (.negCons e hs hn) hr h
    | left r h => exact neg_normal e _ h
    | right p h => exact ih hr.1 _ h

/-- Complete classification for the specified ten-rule relation. -/
theorem normal_iff_reduced_shape {a b : V} (p : Reason E a b) :
    Normal true p ↔ ∃ w, Shape p w ∧ Reduced w := by
  constructor
  · intro hn
    obtain ⟨w, hs⟩ := normal_shape hn
    exact ⟨w, hs, normal_shape_reduced hs hn⟩
  · rintro ⟨w, hs, hr⟩
    exact shape_normal hs hr

/-- Normal reasons are separated by their reduced expansion. -/
theorem normal_expansion_injective {a b : V} {p q : Reason E a b}
    (hp : Normal true p) (hq : Normal true q)
    (he : reducedExpansion p = reducedExpansion q) : p = q := by
  obtain ⟨wp, hsp⟩ := normal_shape hp
  obtain ⟨wq, hsq⟩ := normal_shape hq
  have ep := shape_action_word hsp (normal_shape_reduced hsp hp)
  have eq := shape_action_word hsq (normal_shape_reduced hsq hq)
  have hw : wp = wq := ep.symm.trans (he.trans eq)
  exact shape_injective hsp (hw.symm ▸ hsq)

end StructuralReasons
