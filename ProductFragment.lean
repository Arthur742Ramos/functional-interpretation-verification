import Std.Tactic

/-!
Finite raw product terms and exactly the three product contractions.
All results concern this presentation only, with syntactic repeated terms.
-/
namespace ProductFragment

universe u
inductive Term (Atom : Type u) where
  | atom : Atom → Term Atom
  | pair : Term Atom → Term Atom → Term Atom
  | fst : Term Atom → Term Atom
  | snd : Term Atom → Term Atom
  deriving DecidableEq

open Term
variable {Atom : Type u}

def size : Term Atom → Nat
  | .atom _ => 1
  | .pair a b => size a + size b + 1
  | .fst a => size a + 1
  | .snd a => size a + 1

inductive Root : Term Atom → Term Atom → Prop where
  | fst (a b) : Root (.fst (.pair a b)) a
  | snd (a b) : Root (.snd (.pair a b)) b
  | eta (a) : Root (.pair (.fst a) (.snd a)) a

inductive Step : Term Atom → Term Atom → Prop where
  | root : Root a b → Step a b
  | pairLeft : Step a a' → Step (.pair a b) (.pair a' b)
  | pairRight : Step b b' → Step (.pair a b) (.pair a b')
  | fst : Step a a' → Step (.fst a) (.fst a')
  | snd : Step a a' → Step (.snd a) (.snd a')

theorem root_size_decreases {a b : Term Atom} (h : Root a b) : size b < size a := by
  cases h <;> simp only [size] <;> omega

theorem step_size_decreases {a b : Term Atom} (h : Step a b) : size b < size a := by
  induction h with
  | root h => exact root_size_decreases h
  | pairLeft _ ih => simp only [size]; omega
  | pairRight _ ih => simp only [size]; omega
  | fst _ ih => simp only [size]; omega
  | snd _ ih => simp only [size]; omega

theorem step_wellFounded : WellFounded (fun b a : Term Atom => Step a b) :=
  Subrelation.wf (fun h => step_size_decreases h) (measure size).wf

inductive Steps : Term Atom → Term Atom → Prop where
  | refl (a) : Steps a a
  | cons : Step a b → Steps b c → Steps a c

theorem Steps.single {a b : Term Atom} (h : Step a b) : Steps a b :=
  .cons h (.refl _)

theorem Steps.trans {a b c : Term Atom} (h : Steps a b) (k : Steps b c) :
    Steps a c := by
  induction h with
  | refl => exact k
  | cons h _ ih => exact .cons h (ih k)

theorem Steps.map {a b : Term Atom} (f : Term Atom → Term Atom)
    (hf : ∀ {x y}, Step x y → Step (f x) (f y)) (h : Steps a b) :
    Steps (f a) (f b) := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .cons (hf h) ih

def Normal (a : Term Atom) : Prop := ∀ b, ¬ Step a b
def Joinable (a b : Term Atom) : Prop := ∃ c, Steps a c ∧ Steps b c
def LocallyConfluent (Atom : Type u) : Prop :=
  ∀ {a b c : Term Atom}, Step a b → Step a c → Joinable b c
def Confluent (Atom : Type u) : Prop :=
  ∀ {a b c : Term Atom}, Steps a b → Steps a c → Joinable b c

theorem Joinable.refl (a : Term Atom) : Joinable a a := ⟨a, .refl _, .refl _⟩
theorem Joinable.symm {a b : Term Atom} (h : Joinable a b) : Joinable b a := by
  obtain ⟨c, ha, hb⟩ := h
  exact ⟨c, hb, ha⟩

theorem Joinable.map {a b : Term Atom} (f : Term Atom → Term Atom)
    (hf : ∀ {x y}, Step x y → Step (f x) (f y)) (h : Joinable a b) :
    Joinable (f a) (f b) := by
  obtain ⟨c, ha, hb⟩ := h
  exact ⟨f c, ha.map f hf, hb.map f hf⟩

/-- A contraction in one copy is repeated in the other before eta contracts. -/
theorem eta_left_residual {m a : Term Atom} (h : Step (.fst m) a) :
    Joinable m (.pair a (.snd m)) := by
  cases h with
  | root h =>
    cases h with
    | fst x y =>
      exact ⟨_, .refl _,
        .single (.pairRight (.root (.snd _ _)))⟩
  | fst h =>
    exact ⟨_, .single h,
      .cons (.pairRight (.snd h)) (.single (.root (.eta _)))⟩

theorem eta_right_residual {m b : Term Atom} (h : Step (.snd m) b) :
    Joinable m (.pair (.fst m) b) := by
  cases h with
  | root h =>
    cases h with
    | snd x y =>
      exact ⟨_, .refl _,
        .single (.pairLeft (.root (.fst _ _)))⟩
  | snd h =>
    exact ⟨_, .single h,
      .cons (.pairLeft (.fst h)) (.single (.root (.eta _)))⟩

/-- All overlaps with an outer root contraction, including erased subterms. -/
theorem root_step_join {a b c : Term Atom} (h : Root a b) (k : Step a c) :
    Joinable b c := by
  cases h with
  | fst x y =>
    cases k with
    | root k => cases k; exact .refl _
    | fst k =>
      cases k with
      | root k => cases k; exact .refl _
      | pairLeft k =>
        exact ⟨_, .single k, .single (.root (.fst _ _))⟩
      | pairRight k =>
        exact ⟨_, .refl _, .single (.root (.fst _ _))⟩
  | snd x y =>
    cases k with
    | root k => cases k; exact .refl _
    | snd k =>
      cases k with
      | root k => cases k; exact .refl _
      | pairLeft k =>
        exact ⟨_, .refl _, .single (.root (.snd _ _))⟩
      | pairRight k =>
        exact ⟨_, .single k, .single (.root (.snd _ _))⟩
  | eta m =>
    cases k with
    | root k => cases k; exact .refl _
    | pairLeft k => exact eta_left_residual k
    | pairRight k => exact eta_right_residual k

theorem locally_confluent : LocallyConfluent Atom := by
  intro a b c h
  induction h generalizing c with
  | root h => exact root_step_join h
  | @pairLeft a a' b h ih =>
    intro k
    cases k with
    | root k => exact (root_step_join k (.pairLeft h)).symm
    | pairLeft k => exact (ih k).map (fun t => .pair t b) (fun s => .pairLeft s)
    | pairRight k =>
      exact ⟨_, .single (.pairRight k), .single (.pairLeft h)⟩
  | @pairRight b b' a h ih =>
    intro k
    cases k with
    | root k => exact (root_step_join k (.pairRight h)).symm
    | pairLeft k =>
      exact ⟨_, .single (.pairLeft k), .single (.pairRight h)⟩
    | pairRight k => exact (ih k).map (fun t => .pair a t) (fun s => .pairRight s)
  | fst h ih =>
    intro k
    cases k with
    | root k => exact (root_step_join k (.fst h)).symm
    | fst k => exact (ih k).map Term.fst (fun s => .fst s)
  | snd h ih =>
    intro k
    cases k with
    | root k => exact (root_step_join k (.snd h)).symm
    | snd k => exact (ih k).map Term.snd (fun s => .snd s)

theorem steps_size_le {a b : Term Atom} (h : Steps a b) : size b ≤ size a := by
  induction h with
  | refl => exact Nat.le_refl _
  | cons h _ ih => have := step_size_decreases h; omega

/-- Newman's induction, using the strictly decreasing raw-tree size. -/
theorem confluent : Confluent Atom := by
  intro a
  induction a using (measure size).wf.induction with
  | h a ih =>
    intro b c hab hac
    cases hab with
    | refl => exact ⟨c, hac, .refl _⟩
    | @cons _ b₀ _ hab hbb =>
      cases hac with
      | refl => exact ⟨b, .refl _, .cons hab hbb⟩
      | @cons _ c₀ _ hac hcc =>
        obtain ⟨d, hbd, hcd⟩ := locally_confluent hab hac
        obtain ⟨e, hbe, hde⟩ := ih b₀ (step_size_decreases hab) hbb hbd
        obtain ⟨f, hcf, hdf⟩ := ih c₀ (step_size_decreases hac) hcc hcd
        have hd : size d < size a := by
          have := steps_size_le hbd
          have := step_size_decreases hab
          omega
        obtain ⟨g, heg, hfg⟩ := ih d hd hde hdf
        exact ⟨g, hbe.trans heg, hcf.trans hfg⟩

theorem normal_steps_eq {a b : Term Atom} (hn : Normal a) (h : Steps a b) : a = b := by
  cases h with
  | refl => rfl
  | cons h _ => exact False.elim (hn _ h)

theorem reachable_normal_unique {a b c : Term Atom} (hb : Steps a b) (hc : Steps a c)
    (hbn : Normal b) (hcn : Normal c) : b = c := by
  obtain ⟨d, hbd, hcd⟩ := confluent hb hc
  exact (normal_steps_eq hbn hbd).trans (normal_steps_eq hcn hcd).symm

theorem exists_normal (a : Term Atom) : ∃ b, Steps a b ∧ Normal b := by
  classical
  induction a using step_wellFounded.induction with
  | h a ih =>
    by_cases h : ∃ b, Step a b
    · obtain ⟨b, hab⟩ := h
      obtain ⟨c, hbc, hcn⟩ := ih b hab
      exact ⟨c, .cons hab hbc, hcn⟩
    · exact ⟨a, .refl _, fun b hab => h ⟨b, hab⟩⟩

theorem exists_unique_normal (a : Term Atom) :
    ∃ b, (Steps a b ∧ Normal b) ∧
      ∀ c, Steps a c ∧ Normal c → c = b := by
  obtain ⟨b, hab, hbn⟩ := exists_normal a
  exact ⟨b, ⟨hab, hbn⟩, fun c hc =>
    reachable_normal_unique hc.1 hab hc.2 hbn⟩

/-- Root redex search; comparison in eta is comparison of the two raw trees. -/
def rootTargets [DecidableEq Atom] : Term Atom → List (Term Atom)
  | .fst (.pair a _) => [a]
  | .snd (.pair _ b) => [b]
  | .pair (.fst a) (.snd b) => if a = b then [a] else []
  | _ => []

theorem rootTargets_sound [DecidableEq Atom] {a b : Term Atom}
    (h : b ∈ rootTargets a) : Root a b := by
  cases a with
  | atom a => simp [rootTargets] at h
  | fst a =>
    cases a <;> simp [rootTargets] at h
    case pair x y => subst b; exact .fst x y
  | snd a =>
    cases a <;> simp [rootTargets] at h
    case pair x y => subst b; exact .snd x y
  | pair a c =>
    cases a <;> cases c <;> simp [rootTargets] at h
    case fst.snd x y =>
      obtain ⟨rfl, rfl⟩ := h
      exact .eta _

theorem rootTargets_complete [DecidableEq Atom] {a b : Term Atom}
    (h : Root a b) : b ∈ rootTargets a := by
  cases h <;> simp [rootTargets]

/-- Enumerate every one-step reduct, including all four context positions. -/
def successors [DecidableEq Atom] (a : Term Atom) : List (Term Atom) :=
  rootTargets a ++ match a with
  | .atom _ => []
  | .pair b c => (successors b).map (fun t => .pair t c) ++
                  (successors c).map (fun t => .pair b t)
  | .fst b => (successors b).map Term.fst
  | .snd b => (successors b).map Term.snd

theorem successors_sound [DecidableEq Atom] {a b : Term Atom}
    (h : b ∈ successors a) : Step a b := by
  induction a generalizing b with
  | atom a =>
    simp only [successors, List.mem_append, List.not_mem_nil, or_false] at h
    exact .root (rootTargets_sound h)
  | pair a c iha ihc =>
    simp only [successors, List.mem_append, List.mem_map] at h
    rcases h with h | (⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩)
    · exact .root (rootTargets_sound h)
    · exact .pairLeft (iha hd)
    · exact .pairRight (ihc hd)
  | fst a ih =>
    simp only [successors, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨d, hd, rfl⟩
    · exact .root (rootTargets_sound h)
    · exact .fst (ih hd)
  | snd a ih =>
    simp only [successors, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨d, hd, rfl⟩
    · exact .root (rootTargets_sound h)
    · exact .snd (ih hd)

theorem successors_complete [DecidableEq Atom] {a b : Term Atom}
    (h : Step a b) : b ∈ successors a := by
  induction h with
  | root h =>
    cases h <;> simp [successors, rootTargets]
  | pairLeft h ih =>
    simp only [successors, List.mem_append, List.mem_map]
    exact Or.inr (Or.inl ⟨_, ih, rfl⟩)
  | pairRight h ih =>
    simp only [successors, List.mem_append, List.mem_map]
    exact Or.inr (Or.inr ⟨_, ih, rfl⟩)
  | fst h ih =>
    simp only [successors, List.mem_append, List.mem_map]
    exact Or.inr ⟨_, ih, rfl⟩
  | snd h ih =>
    simp only [successors, List.mem_append, List.mem_map]
    exact Or.inr ⟨_, ih, rfl⟩

theorem successors_iff [DecidableEq Atom] {a b : Term Atom} :
    b ∈ successors a ↔ Step a b :=
  ⟨successors_sound, successors_complete⟩

/-- The algorithm returns a raw tree together with reachability and normality. -/
def normalise [DecidableEq Atom] (a : Term Atom) :
    {b : Term Atom // Steps a b ∧ Normal b} :=
  match h : successors a with
  | [] => ⟨a, .refl _, by
      intro b hab
      have hm := successors_complete hab
      simp [h] at hm⟩
  | b :: rest =>
    have hab : Step a b := successors_sound (by simp [h])
    let result := normalise b
    ⟨result.val, .cons hab result.property.1, result.property.2⟩
termination_by size a
decreasing_by exact step_size_decreases hab

def nf [DecidableEq Atom] (a : Term Atom) : Term Atom := (normalise a).val

theorem nf_reachable [DecidableEq Atom] (a : Term Atom) : Steps a (nf a) :=
  (normalise a).property.1

theorem nf_normal [DecidableEq Atom] (a : Term Atom) : Normal (nf a) :=
  (normalise a).property.2

theorem steps_preserve_nf [DecidableEq Atom] {a b : Term Atom} (h : Steps a b) :
    nf a = nf b :=
  reachable_normal_unique (nf_reachable a) (h.trans (nf_reachable b))
    (nf_normal a) (nf_normal b)

/-- The least congruence generated by the three root equations. -/
inductive Equal : Term Atom → Term Atom → Prop where
  | refl (a) : Equal a a
  | root : Root a b → Equal a b
  | symm : Equal a b → Equal b a
  | trans : Equal a b → Equal b c → Equal a c
  | pairLeft : Equal a a' → Equal (.pair a b) (.pair a' b)
  | pairRight : Equal b b' → Equal (.pair a b) (.pair a b')
  | fst : Equal a a' → Equal (.fst a) (.fst a')
  | snd : Equal a a' → Equal (.snd a) (.snd a')

theorem step_equal {a b : Term Atom} (h : Step a b) : Equal a b := by
  induction h with
  | root h => exact .root h
  | pairLeft _ ih => exact .pairLeft ih
  | pairRight _ ih => exact .pairRight ih
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih

theorem steps_equal {a b : Term Atom} (h : Steps a b) : Equal a b := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .trans (step_equal h) ih

theorem Joinable.trans {a b c : Term Atom} (h : Joinable a b) (k : Joinable b c) :
    Joinable a c := by
  obtain ⟨d, had, hbd⟩ := h
  obtain ⟨e, hbe, hce⟩ := k
  obtain ⟨f, hdf, hef⟩ := confluent hbd hbe
  exact ⟨f, had.trans hdf, hce.trans hef⟩

theorem equal_joinable {a b : Term Atom} (h : Equal a b) : Joinable a b := by
  induction h with
  | refl => exact .refl _
  | root h => exact ⟨_, .single (.root h), .refl _⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | @pairLeft a a' b _ ih =>
    exact ih.map (fun t => .pair t b) (fun s => .pairLeft s)
  | @pairRight b b' a _ ih =>
    exact ih.map (fun t => .pair a t) (fun s => .pairRight s)
  | fst _ ih => exact ih.map Term.fst (fun s => .fst s)
  | snd _ ih => exact ih.map Term.snd (fun s => .snd s)

theorem equal_iff_nf [DecidableEq Atom] (a b : Term Atom) :
    Equal a b ↔ nf a = nf b := by
  constructor
  · intro h
    obtain ⟨c, hac, hbc⟩ := equal_joinable h
    exact (steps_preserve_nf hac).trans (steps_preserve_nf hbc).symm
  · intro h
    exact .trans (steps_equal (nf_reachable a))
      (h ▸ (steps_equal (nf_reachable b)).symm)

def decideEqual [DecidableEq Atom] (a b : Term Atom) : Bool := decide (nf a = nf b)

theorem decideEqual_correct [DecidableEq Atom] (a b : Term Atom) :
    decideEqual a b = true ↔ Equal a b := by
  simp only [decideEqual, decide_eq_true_eq]
  exact (equal_iff_nf a b).symm

end ProductFragment

#print axioms ProductFragment.root_size_decreases
#print axioms ProductFragment.step_size_decreases
#print axioms ProductFragment.step_wellFounded
#print axioms ProductFragment.Steps.single
#print axioms ProductFragment.Steps.trans
#print axioms ProductFragment.Steps.map
#print axioms ProductFragment.Joinable.refl
#print axioms ProductFragment.Joinable.symm
#print axioms ProductFragment.Joinable.map
#print axioms ProductFragment.eta_left_residual
#print axioms ProductFragment.eta_right_residual
#print axioms ProductFragment.root_step_join
#print axioms ProductFragment.locally_confluent
#print axioms ProductFragment.steps_size_le
#print axioms ProductFragment.confluent
#print axioms ProductFragment.normal_steps_eq
#print axioms ProductFragment.reachable_normal_unique
#print axioms ProductFragment.exists_normal
#print axioms ProductFragment.exists_unique_normal
#print axioms ProductFragment.rootTargets_sound
#print axioms ProductFragment.rootTargets_complete
#print axioms ProductFragment.successors_sound
#print axioms ProductFragment.successors_complete
#print axioms ProductFragment.successors_iff
#print axioms ProductFragment.nf_reachable
#print axioms ProductFragment.nf_normal
#print axioms ProductFragment.steps_preserve_nf
#print axioms ProductFragment.step_equal
#print axioms ProductFragment.steps_equal
#print axioms ProductFragment.Joinable.trans
#print axioms ProductFragment.equal_joinable
#print axioms ProductFragment.equal_iff_nf
#print axioms ProductFragment.decideEqual_correct
#print axioms ProductFragment.normalise
#print axioms ProductFragment.nf
#print axioms ProductFragment.decideEqual
