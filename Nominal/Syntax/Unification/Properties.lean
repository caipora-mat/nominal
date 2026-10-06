import Nominal.Syntax.Unification.Algorithm

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

/-! ### Entailment helpers -/

/-- Convert + applySubst commute. -/
@[simp] lemma UnifConstraint.toConstraint_applySubst (c : UnifConstraint F X 𝔸)
    (σ : Subst F X 𝔸) :
    (c.applySubst σ).toConstraint = c.toConstraint.applySubst σ := by
  cases c <;> simp [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                    Constraint.applySubst]

@[simp] lemma UnifProblem.toConstraint_applySubst (Pr : UnifProblem F X 𝔸)
    (σ : Subst F X 𝔸) :
    (Pr.applySubst σ).toConstraint = Pr.toConstraint.applySubst σ := by
  simp [UnifProblem.toConstraint, UnifProblem.applySubst, Problem.applySubst,
        List.map_map, Function.comp_def]

@[simp] lemma UnifProblem.applySubst_cons (c : UnifConstraint F X 𝔸)
    (rest : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) :
    UnifProblem.applySubst (c :: rest) σ =
      c.applySubst σ :: UnifProblem.applySubst rest σ := rfl

@[simp] lemma UnifProblem.toConstraint_cons (c : UnifConstraint F X 𝔸)
    (rest : UnifProblem F X 𝔸) :
    UnifProblem.toConstraint (c :: rest) =
      c.toConstraint :: UnifProblem.toConstraint rest := rfl

/-- `Problem.Entails` on a cons. -/
lemma Problem.Entails_cons {Γ : Context 𝔸 X} {c : Constraint F X 𝔸}
    {P : Problem F X 𝔸} :
    Problem.Entails Γ (c :: P) ↔ c.Entails Γ ∧ Problem.Entails Γ P := by
  constructor
  · intro h
    refine ⟨h c List.mem_cons_self, fun c' hc' => h c' (List.mem_cons_of_mem _ hc')⟩
  · rintro ⟨hc, hP⟩ c' hc'
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact hc
    · exact hP c' hc'

/-- Pairwise entailment on `ss.zip ts` (substituted form) gives `alphaEquivList`
    on the substituted lists. -/
lemma alphaEquivList_of_zip_subst_entails (Γ : Context 𝔸 X) (σ : Subst F X 𝔸) :
    ∀ (ss ts : List (ntm F X 𝔸)),
      ss.length = ts.length →
      Problem.Entails Γ
        ((ss.zip ts).map (fun p => Constraint.alpha (p.1.subst σ) (p.2.subst σ))) →
      alphaEquivList Γ (ss.map (·.subst σ)) (ts.map (·.subst σ)) = true
  | [], [], _, _ => by simp [alphaEquivList]
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | s :: ss', t :: ts', hlen, hzip => by
    simp only [List.zip_cons_cons, List.map_cons, Problem.Entails_cons] at hzip
    obtain ⟨hst, htail⟩ := hzip
    simp only [Constraint.Entails] at hst
    simp only [List.map_cons, alphaEquivList, hst, true_and,
               decide_eq_true_eq]
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    exact alphaEquivList_of_zip_subst_entails Γ σ ss' ts' hlen htail


mutual
  /-- If `simplifyFresh a t = some cs` and the substituted leaves are entailed
      by Γ, then `Γ ⊢ a # t.subst τ`. -/
  lemma fresh_subst_of_simplifyFresh_entails (Γ : Context 𝔸 X) (a : 𝔸)
      (τ : Subst F X 𝔸) :
      ∀ (t : ntm F X 𝔸) (cs : Problem F X 𝔸),
        simplifyFresh a t = some cs →
        Problem.Entails Γ (cs.applySubst τ) →
        (Γ ⊢ a # t.subst τ) = true
    | .atm b, cs, hs, _ => by
      simp only [simplifyFresh] at hs
      by_cases hab : a = b
      · rw [if_pos hab] at hs; cases hs
      · rw [if_neg hab] at hs
        simp [ntm.subst_atm, fresh_atm, hab]
    | .mvar π x, cs, hs, hcs => by
      simp only [simplifyFresh] at hs
      injection hs with hcs_eq
      subst hcs_eq
      rw [ntm.subst_mvar]
      rw [show a = LPermApply π (LPermApply π.reverse a)
            from (LPermApply_reverse_right π a).symm]
      rw [← fresh_equivariance]
      have hmem : Constraint.fresh (LPermApply π.reverse a)
          ((ntm.mvar (F := F) [] x).subst τ) ∈
          Problem.applySubst
            [Constraint.fresh (LPermApply π.reverse a)
              ((ntm.mvar (F := F) [] x : ntm F X 𝔸))] τ := by
        simp [Problem.applySubst, Constraint.applySubst]
      have := hcs _ hmem
      simp only [Constraint.Entails] at this
      exact this
    | .fapp _ ts, cs, hs, hcs => by
      simp only [simplifyFresh] at hs
      simp only [ntm.subst_fapp, fresh]
      exact freshList_subst_of_simplifyFreshList_entails Γ a τ ts cs hs hcs
    | .abs b t', cs, hs, hcs => by
      simp only [simplifyFresh] at hs
      split_ifs at hs with hab
      · simp [ntm.subst_abs, fresh, hab]
      · simp [ntm.subst_abs, fresh]
        right
        exact fresh_subst_of_simplifyFresh_entails Γ a τ t' cs hs hcs

  lemma freshList_subst_of_simplifyFreshList_entails (Γ : Context 𝔸 X) (a : 𝔸)
      (τ : Subst F X 𝔸) :
      ∀ (ts : List (ntm F X 𝔸)) (cs : Problem F X 𝔸),
        simplifyFreshList a ts = some cs →
        Problem.Entails Γ (cs.applySubst τ) →
        freshList Γ a (ts.map (·.subst τ)) = true
    | [], cs, hs, _ => by
      simp only [simplifyFreshList] at hs
      injection hs with hcs_eq
      subst hcs_eq
      simp [freshList]
    | t :: ts', cs, hs, hcs => by
      simp only [simplifyFreshList] at hs
      cases hf : simplifyFresh a t with
      | none => rw [hf] at hs; cases hs
      | some cs₁ =>
        cases hg : simplifyFreshList a ts' with
        | none => rw [hf, hg] at hs; cases hs
        | some cs₂ =>
          rw [hf, hg] at hs
          injection hs with hcs_eq
          subst hcs_eq
          have hcs' : Problem.Entails Γ (cs₁.applySubst τ) ∧
                      Problem.Entails Γ (cs₂.applySubst τ) := by
            rw [show (cs₁ ++ cs₂).applySubst τ = cs₁.applySubst τ ++ cs₂.applySubst τ from by
                  simp [Problem.applySubst, List.map_append],
                Problem.Entails_append_iff] at hcs
            exact hcs
          simp [List.map_cons, freshList]
          refine ⟨?_, ?_⟩
          · exact fresh_subst_of_simplifyFresh_entails Γ a τ t cs₁ hf hcs'.1
          · exact freshList_subst_of_simplifyFreshList_entails Γ a τ ts' cs₂ hg hcs'.2
end

/-! ### `σ` only grows -/

/-- `unifStep` extends σ, at the level of the *action* on terms: there is an `ε`
    with `t.subst σ_next = (t.subst σ).subst ε` for every `t`.  For
    non-instantiation cases `ε = []`; for the instantiation cases `σ_next` is
    `σ.comp [binding]` and `ε = [binding]` (via `subst_comp`).  (Under
    simultaneous substitution `σ_next` is not literally `σ ++ ε`, but it acts as
    the composition, which is what the soundness proof consumes.) -/
lemma unifStep_σ_extends (c : UnifConstraint F X 𝔸) (rest : UnifProblem F X 𝔸)
    (σ : Subst F X 𝔸) (Pr' : UnifProblem F X 𝔸) (σ_next : Subst F X 𝔸)
    (h : unifStep c rest σ = .next Pr' σ_next) :
    ∃ ε, ∀ t : ntm F X 𝔸, t.subst σ_next = (t.subst σ).subst ε := by
  cases UnifRule.of_unifStep h with
  | instL π x u _ | instR π x u _ =>
    exact ⟨[(x, u.permute π.reverse)], fun t => ntm.subst_comp t σ _⟩
  | _ => exact ⟨[], fun t => (ntm.subst_nil _).symm⟩

/-- `unify` extends σ at the level of the action: `t.subst σ' = (t.subst σ).subst τ`
    for some `τ` and every `t`.  (Action-level form of "σ' extends σ", the
    composition being `Subst.comp`.) -/
lemma unify_σ_prefix : ∀ (Pr : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) (ds : List (𝔸 × X)),
    ∀ (ds' : List (𝔸 × X)) (σ' : Subst F X 𝔸),
      unify Pr σ ds = some (ds', σ') →
      ∃ τ, ∀ t : ntm F X 𝔸, t.subst σ' = (t.subst σ).subst τ := by
  intro Pr σ ds
  induction Pr, σ, ds using unify.induct with
  | case1 σ ds =>
    intro ds' σ' h
    simp only [unify, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨[], fun t => by rw [h.2, ntm.subst_nil]⟩
  | case2 σ ds c rest hfail =>
    intro ds' σ' h
    rw [unify, hfail] at h; cases h
  | case3 σ ds c rest a x hctx ih =>
    intro ds' σ' h
    rw [unify, hctx] at h
    exact ih ds' σ' h
  | case4 σ ds c rest Pr' σ_next hnext ih =>
    intro ds' σ' h
    rw [unify, hnext] at h
    obtain ⟨ε1, hε1⟩ := unifStep_σ_extends c rest σ Pr' σ_next hnext
    obtain ⟨ε2, hε2⟩ := ih ds' σ' h
    exact ⟨ε1.comp ε2, fun t => by rw [hε2 t, hε1 t, ntm.subst_comp]⟩

/-! ### Metavariables and the disjointness invariant -/

/-- Metavariables of a single unification constraint. -/
def UnifConstraint.metavars : UnifConstraint F X 𝔸 → Finset X
  | .fresh _ t => t.metavars
  | .unif s t  => s.metavars ∪ t.metavars

/-- All metavariables appearing in a problem (both `.unif` and `.fresh` sides). -/
def UnifProblem.allMetavars : UnifProblem F X 𝔸 → Finset X
  | [] => ∅
  | c :: rest => c.metavars ∪ UnifProblem.allMetavars rest

@[simp] lemma UnifProblem.allMetavars_nil :
    UnifProblem.allMetavars ([] : UnifProblem F X 𝔸) = ∅ := rfl

@[simp] lemma UnifProblem.allMetavars_cons (c : UnifConstraint F X 𝔸)
    (rest : UnifProblem F X 𝔸) :
    UnifProblem.allMetavars (c :: rest) = c.metavars ∪ UnifProblem.allMetavars rest := rfl

@[simp] lemma UnifProblem.allMetavars_append (Pr Pr' : UnifProblem F X 𝔸) :
    UnifProblem.allMetavars (Pr ++ Pr') =
      UnifProblem.allMetavars Pr ∪ UnifProblem.allMetavars Pr' := by
  induction Pr with
  | nil => simp
  | cons c rest ih =>
    simp [UnifProblem.allMetavars_cons, ih, Finset.union_assoc]

/-- `σ` is disjoint from `Pr`'s metavariables. -/
def Subst.disjointPr (σ : Subst F X 𝔸) (Pr : UnifProblem F X 𝔸) : Prop :=
  ∀ x ∈ UnifProblem.allMetavars Pr, x ∉ Subst.dom σ

lemma Subst.disjointPr_cons {σ : Subst F X 𝔸} {c : UnifConstraint F X 𝔸}
    {rest : UnifProblem F X 𝔸} (h : σ.disjointPr (c :: rest)) :
    σ.disjointPr rest := by
  intro x hx; exact h x (by simp [hx])

lemma Subst.disjointPr_cons_head {σ : Subst F X 𝔸} {c : UnifConstraint F X 𝔸}
    {rest : UnifProblem F X 𝔸} (h : σ.disjointPr (c :: rest)) :
    ∀ x ∈ c.metavars, x ∉ Subst.dom σ := by
  intro x hx; exact h x (by simp [hx])

lemma Subst.disjointPr_append {σ : Subst F X 𝔸} {Pr Pr' : UnifProblem F X 𝔸}
    (h : σ.disjointPr (Pr ++ Pr')) :
    σ.disjointPr Pr ∧ σ.disjointPr Pr' := by
  refine ⟨?_, ?_⟩ <;> intro x hx <;> exact h x (by simp [hx])

lemma Subst.disjointPr_append_of {σ : Subst F X 𝔸} {Pr Pr' : UnifProblem F X 𝔸}
    (h1 : σ.disjointPr Pr) (h2 : σ.disjointPr Pr') :
    σ.disjointPr (Pr ++ Pr') := by
  intro x hx
  simp only [UnifProblem.allMetavars_append, Finset.mem_union] at hx
  rcases hx with hx | hx
  · exact h1 x hx
  · exact h2 x hx

lemma Subst.disjointPr_subset {σ : Subst F X 𝔸} {Pr Pr' : UnifProblem F X 𝔸}
    (h : UnifProblem.allMetavars Pr' ⊆ UnifProblem.allMetavars Pr)
    (hdisj : σ.disjointPr Pr) : σ.disjointPr Pr' :=
  fun x hx => hdisj x (h hx)

/-- Disjoint extends to `σ ++ [(x, u)]` if the added binding doesn't introduce
    new dom-conflict with Pr's metavars (x ∉ allMetavars Pr). -/
lemma Subst.disjointPr_append_singleton {σ : Subst F X 𝔸} {Pr : UnifProblem F X 𝔸}
    {x : X} {u : ntm F X 𝔸}
    (hdisj : σ.disjointPr Pr) (hx : x ∉ UnifProblem.allMetavars Pr) :
    (σ ++ [(x, u)]).disjointPr Pr := by
  intro y hy
  have hy_dom : y ∉ Subst.dom σ := hdisj y hy
  rw [Subst.dom_append, Subst.dom_singleton]
  intro hmem
  rcases Finset.mem_union.mp hmem with h | h
  · exact hy_dom h
  · rw [Finset.mem_singleton] at h
    subst h
    exact hx hy

mutual
  lemma simplifyFresh_metavars_subset (a : 𝔸) :
      ∀ (t : ntm F X 𝔸) (cs : Problem F X 𝔸),
        simplifyFresh a t = some cs →
        ∀ c ∈ cs, ∀ x ∈ c.toUnif.metavars, x ∈ t.metavars
    | .atm b, cs, h, c, hc => by
      simp only [simplifyFresh] at h
      by_cases hab : a = b
      · rw [if_pos hab] at h; cases h
      · rw [if_neg hab] at h
        injection h with heq; subst heq
        nomatch hc
    | .mvar π y, cs, h, c, hc => by
      simp only [simplifyFresh] at h
      injection h with heq; subst heq
      rw [List.mem_singleton] at hc
      subst hc
      intro x hx
      simp [Constraint.toUnif, UnifConstraint.metavars, ntm.metavars] at hx
      simp [ntm.metavars, hx]
    | .fapp _ ts, cs, h, c, hc => by
      simp only [simplifyFresh] at h
      exact simplifyFreshList_metavars_subset a ts cs h c hc
    | .abs b t', cs, h, c, hc => by
      simp only [simplifyFresh] at h
      by_cases hab : a = b
      · rw [if_pos hab] at h
        injection h with heq; subst heq
        nomatch hc
      · rw [if_neg hab] at h
        intro x hx
        have := simplifyFresh_metavars_subset a t' cs h c hc x hx
        simp [ntm.metavars]; exact this

  lemma simplifyFreshList_metavars_subset (a : 𝔸) :
      ∀ (ts : List (ntm F X 𝔸)) (cs : Problem F X 𝔸),
        simplifyFreshList a ts = some cs →
        ∀ c ∈ cs, ∀ x ∈ c.toUnif.metavars, x ∈ ntmList.metavars ts
    | [], cs, h, c, hc => by
      simp only [simplifyFreshList] at h
      injection h with heq; subst heq; nomatch hc
    | t :: ts', cs, h, c, hc => by
      simp only [simplifyFreshList] at h
      cases hf : simplifyFresh a t with
      | none => rw [hf] at h; cases h
      | some cs₁ =>
        cases hg : simplifyFreshList a ts' with
        | none => rw [hf, hg] at h; cases h
        | some cs₂ =>
          rw [hf, hg] at h
          injection h with heq; subst heq
          rcases List.mem_append.mp hc with hc | hc
          · intro x hx
            have := simplifyFresh_metavars_subset a t cs₁ hf c hc x hx
            simp [ntmList.metavars]; left; exact this
          · intro x hx
            have := simplifyFreshList_metavars_subset a ts' cs₂ hg c hc x hx
            simp [ntmList.metavars]; right; exact this
end

/-- Subset bound: metavars of a mapped-toUnif problem are bounded by the
    aggregated bound of each leaf. -/
lemma allMetavars_map_toUnif_subset (cs : Problem F X 𝔸) (target : Finset X)
    (h : ∀ c ∈ cs, ∀ x ∈ c.toUnif.metavars, x ∈ target) :
    UnifProblem.allMetavars (cs.map (·.toUnif)) ⊆ target := by
  induction cs with
  | nil => simp
  | cons c cs' ih =>
    intro x hx
    simp only [List.map_cons, UnifProblem.allMetavars_cons, Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact h c List.mem_cons_self x hx
    · exact ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')) hx

mutual
  lemma ntm.applyOne_metavars_subset (t : ntm F X 𝔸) (x : X) (u : ntm F X 𝔸) :
      (t.applyOne x u).metavars ⊆ (t.metavars \ {x}) ∪ u.metavars := by
    match t with
    | .atm _ => simp [ntm.applyOne, ntm.metavars]
    | .mvar π y =>
      simp only [ntm.applyOne]
      by_cases hy : y = x
      · rw [if_pos hy, ntm.permute_metavars]
        intro z hz; simp [Finset.mem_union]; right; exact hz
      · rw [if_neg hy]
        intro z hz
        simp only [ntm.metavars, Finset.mem_singleton] at hz
        subst hz
        simp [ntm.metavars, hy]
    | .fapp f ts =>
      simp only [ntm.applyOne, ntm.metavars]
      exact ntmList.applyOne_metavars_subset ts x u
    | .abs b t' =>
      simp only [ntm.applyOne, ntm.metavars]
      exact ntm.applyOne_metavars_subset t' x u

  lemma ntmList.applyOne_metavars_subset (ts : List (ntm F X 𝔸)) (x : X)
      (u : ntm F X 𝔸) :
      ntmList.metavars (ts.map (·.applyOne x u)) ⊆
        (ntmList.metavars ts \ {x}) ∪ u.metavars := by
    match ts with
    | [] => simp [ntmList.metavars]
    | t :: ts' =>
      simp only [List.map_cons, ntmList.metavars]
      intro z hz
      simp only [Finset.mem_union] at hz
      rcases hz with hz | hz
      · have := ntm.applyOne_metavars_subset t x u hz
        simp only [Finset.mem_union, Finset.mem_sdiff,
                   Finset.mem_singleton] at this ⊢
        rcases this with ⟨hz1, hz2⟩ | hz
        · left; refine ⟨?_, hz2⟩; left; exact hz1
        · right; exact hz
      · have := ntmList.applyOne_metavars_subset ts' x u hz
        simp only [Finset.mem_union, Finset.mem_sdiff,
                   Finset.mem_singleton] at this ⊢
        rcases this with ⟨hz1, hz2⟩ | hz
        · left; refine ⟨?_, hz2⟩; right; exact hz1
        · right; exact hz
end

lemma ntm.subst_singleton_metavars_subset (t : ntm F X 𝔸) (x : X) (u : ntm F X 𝔸) :
    (t.subst [(x, u)]).metavars ⊆ (t.metavars \ {x}) ∪ u.metavars := by
  rw [ntm.subst_singleton]
  exact ntm.applyOne_metavars_subset t x u

lemma UnifConstraint.applySubst_singleton_metavars_subset (c : UnifConstraint F X 𝔸)
    (x : X) (u : ntm F X 𝔸) :
    (c.applySubst [(x, u)]).metavars ⊆ (c.metavars \ {x}) ∪ u.metavars := by
  cases c with
  | fresh a t =>
    simp only [UnifConstraint.applySubst, UnifConstraint.metavars]
    exact ntm.subst_singleton_metavars_subset t x u
  | unif s t =>
    simp only [UnifConstraint.applySubst, UnifConstraint.metavars]
    intro z hz
    simp only [Finset.mem_union] at hz
    rcases hz with hz | hz
    · have := ntm.subst_singleton_metavars_subset s x u hz
      simp only [Finset.mem_union, Finset.mem_sdiff,
                 Finset.mem_singleton] at this ⊢
      rcases this with ⟨h1, h2⟩ | h
      · left; refine ⟨?_, h2⟩; left; exact h1
      · right; exact h
    · have := ntm.subst_singleton_metavars_subset t x u hz
      simp only [Finset.mem_union, Finset.mem_sdiff,
                 Finset.mem_singleton] at this ⊢
      rcases this with ⟨h1, h2⟩ | h
      · left; refine ⟨?_, h2⟩; right; exact h1
      · right; exact h

lemma UnifProblem.applySubst_singleton_metavars_subset (Pr : UnifProblem F X 𝔸)
    (x : X) (u : ntm F X 𝔸) :
    UnifProblem.allMetavars (Pr.applySubst [(x, u)]) ⊆
      (UnifProblem.allMetavars Pr \ {x}) ∪ u.metavars := by
  induction Pr with
  | nil => intro z hz; simp [UnifProblem.applySubst, UnifProblem.allMetavars] at hz
  | cons c rest ih =>
    intro z hz
    simp only [UnifProblem.applySubst, List.map_cons,
               UnifProblem.allMetavars_cons, Finset.mem_union] at hz
    rcases hz with hz | hz
    · have := UnifConstraint.applySubst_singleton_metavars_subset c x u hz
      simp only [Finset.mem_union, Finset.mem_sdiff,
                 UnifProblem.allMetavars_cons, Finset.mem_singleton] at this ⊢
      rcases this with ⟨h1, h2⟩ | h
      · left; refine ⟨?_, h2⟩; left; exact h1
      · right; exact h
    · have := ih hz
      simp only [Finset.mem_union, Finset.mem_sdiff,
                 UnifProblem.allMetavars_cons, Finset.mem_singleton] at this ⊢
      rcases this with ⟨h1, h2⟩ | h
      · left; refine ⟨?_, h2⟩; right; exact h1
      · right; exact h

/-- t.metavars ⊆ ntmList.metavars ts if t ∈ ts. -/
lemma ntmList.mem_metavars_of_mem {t : ntm F X 𝔸} {ts : List (ntm F X 𝔸)}
    (h : t ∈ ts) {z : X} (hz : z ∈ t.metavars) :
    z ∈ ntmList.metavars ts := by
  induction ts with
  | nil => cases h
  | cons t' ts' ih =>
    simp only [ntmList.metavars, Finset.mem_union]
    rcases List.mem_cons.mp h with rfl | h
    · left; exact hz
    · right; exact ih h

/-- General: allMetavars of mapped list bounded by per-element target. -/
lemma allMetavars_map_subset {α : Type*} (l : List α) (f : α → UnifConstraint F X 𝔸)
    (target : Finset X) (h : ∀ a ∈ l, ∀ x ∈ (f a).metavars, x ∈ target) :
    UnifProblem.allMetavars (l.map f) ⊆ target := by
  induction l with
  | nil => simp
  | cons a l' ih =>
    intro x hx
    simp only [List.map_cons, UnifProblem.allMetavars_cons, Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact h a List.mem_cons_self x hx
    · exact ih (fun a' ha' => h a' (List.mem_cons_of_mem _ ha')) hx

/-! ### One step preserves idempotence -/

/-- Common pattern for unifStep instantiation: σ_next = σ ++ [(x, u_perm)],
    Pr' = rest.applySubst [(x, u_perm)]. -/
lemma instantiation_invariant
    (σ : Subst F X 𝔸) (rest : UnifProblem F X 𝔸) (c : UnifConstraint F X 𝔸)
    (x : X) (u_perm : ntm F X 𝔸)
    (hσ : σ.IsIdempotent)
    (hdisj : σ.disjointPr (c :: rest))
    (hx_in_c : x ∈ c.metavars)
    (hu_perm_in_c : ∀ z ∈ u_perm.metavars, z ∈ c.metavars)
    (hocc : u_perm.occursIn x = false) :
    (σ.comp [(x, u_perm)]).IsIdempotent ∧
    (σ.comp [(x, u_perm)]).disjointPr (rest.applySubst [(x, u_perm)]) := by
  have hx_dom : x ∉ Subst.dom σ := by
    apply hdisj
    simp [UnifProblem.allMetavars_cons]; left; exact hx_in_c
  have hu_fixed : u_perm.subst σ = u_perm := by
    apply ntm.subst_of_disjoint_dom
    intro y hy
    rw [ntm.occursIn_false_iff_not_mem_metavars]
    intro hy_in
    have hy_c : y ∈ c.metavars := hu_perm_in_c y hy_in
    exact hdisj y (by simp [UnifProblem.allMetavars_cons]; left; exact hy_c) hy
  refine ⟨Subst.IsIdempotent.comp_singleton hσ hu_fixed hocc, ?_⟩
  intro y hy
  have hperm := UnifProblem.applySubst_singleton_metavars_subset rest x u_perm hy
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton] at hperm
  rw [Subst.dom_comp, Subst.dom_singleton]
  intro hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hperm with ⟨hy_rest, hy_ne⟩ | hy_perm
  · rcases hmem with hmem | hmem
    · exact hdisj y (by simp [UnifProblem.allMetavars_cons]; right; exact hy_rest) hmem
    · exact hy_ne hmem
  · rcases hmem with hmem | hmem
    · have hy_c : y ∈ c.metavars := hu_perm_in_c y hy_perm
      exact hdisj y (by simp [UnifProblem.allMetavars_cons]; left; exact hy_c) hmem
    · subst hmem
      rw [ntm.occursIn_false_iff_not_mem_metavars] at hocc
      exact hocc hy_perm

/-- One unifStep preserves σ.IsIdempotent and σ.disjointPr (under invariant). -/
lemma unifStep_next_idempotent_and_disjoint
    (c : UnifConstraint F X 𝔸) (rest : UnifProblem F X 𝔸) (σ : Subst F X 𝔸)
    (Pr' : UnifProblem F X 𝔸) (σ_next : Subst F X 𝔸)
    (h : unifStep c rest σ = .next Pr' σ_next)
    (hσ : σ.IsIdempotent)
    (hdisj : σ.disjointPr (c :: rest)) :
    σ_next.IsIdempotent ∧ σ_next.disjointPr Pr' := by
  cases UnifRule.of_unifStep h with
  | fresh a t cs ht hcs =>
    refine ⟨hσ, ?_⟩
    apply Subst.disjointPr_append_of (Subst.disjointPr_cons hdisj)
    apply Subst.disjointPr_subset
      (allMetavars_map_toUnif_subset cs (UnifProblem.allMetavars
        (UnifConstraint.fresh a t :: rest))
        (fun c' hc' x hx => by
          simp only [UnifProblem.allMetavars_cons, Finset.mem_union]
          left
          exact simplifyFresh_metavars_subset a t cs hcs c' hc' x hx))
    exact hdisj
  | atm a => exact ⟨hσ, Subst.disjointPr_cons hdisj⟩
  | mvarSame π π' x =>
    refine ⟨hσ, ?_⟩
    apply Subst.disjointPr_append_of (Subst.disjointPr_cons hdisj)
    apply Subst.disjointPr_subset
      (allMetavars_map_subset (dsList π π')
        (fun a => UnifConstraint.fresh a (ntm.mvar [] x))
        (UnifProblem.allMetavars
          (UnifConstraint.unif (ntm.mvar π x) (ntm.mvar (X := X) π' x) :: rest))
        (fun a _ z hz => by
          simp only [UnifConstraint.metavars, ntm.metavars,
                     Finset.mem_singleton] at hz
          subst hz
          simp [UnifProblem.allMetavars_cons, UnifConstraint.metavars,
                ntm.metavars]))
    exact hdisj
  | instL π x u hocc =>
    refine instantiation_invariant σ rest _ x (u.permute π.reverse) hσ hdisj ?_ ?_ ?_
    · simp [UnifConstraint.metavars, ntm.metavars]
    · intro z hz
      rw [ntm.permute_metavars] at hz
      simp [UnifConstraint.metavars, hz]
    · rw [ntm.occursIn_permute]; exact hocc
  | instR π x u hocc =>
    refine instantiation_invariant σ rest _ x (u.permute π.reverse) hσ hdisj ?_ ?_ ?_
    · simp [UnifConstraint.metavars, ntm.metavars]
    · intro z hz
      rw [ntm.permute_metavars] at hz
      simp [UnifConstraint.metavars, hz]
    · rw [ntm.occursIn_permute]; exact hocc
  | fapp f ss ts hlen =>
    refine ⟨hσ, ?_⟩
    apply Subst.disjointPr_append_of
    · apply Subst.disjointPr_subset
        (allMetavars_map_subset (ss.zip ts)
          (fun p => UnifConstraint.unif p.1 p.2)
          (UnifProblem.allMetavars
            (UnifConstraint.unif (ntm.fapp (X := X) (𝔸 := 𝔸) f ss)
                                 (ntm.fapp (X := X) (𝔸 := 𝔸) f ts) :: rest))
          (fun p hp z hz => by
            obtain ⟨hp1, hp2⟩ := List.of_mem_zip hp
            simp only [UnifConstraint.metavars, Finset.mem_union] at hz
            simp only [UnifProblem.allMetavars_cons, UnifConstraint.metavars,
                       ntm.metavars, Finset.mem_union]
            left
            rcases hz with hz | hz
            · left; exact ntmList.mem_metavars_of_mem hp1 hz
            · right; exact ntmList.mem_metavars_of_mem hp2 hz))
      exact hdisj
    · exact Subst.disjointPr_cons hdisj
  | absSame a s t =>
    refine ⟨hσ, ?_⟩
    intro y hy
    exact hdisj y (by
      simp only [UnifProblem.allMetavars_cons, UnifConstraint.metavars,
                 ntm.metavars] at hy ⊢
      exact hy)
  | absDiff a b s t hab =>
    refine ⟨hσ, ?_⟩
    intro y hy
    exact hdisj y (by
      simp only [UnifProblem.allMetavars_cons, UnifConstraint.metavars,
                 ntm.metavars, ntm.permute_metavars,
                 Finset.mem_union] at hy ⊢
      tauto)

/-! ### Soundness of one step -/

/-- Under the invariants of `unify`, the final substitution τ "resolves" the
    binding `(x, u_perm)` produced by the instantiation step:
    `(mvar [] x).subst τ = u_perm.subst τ`. -/
lemma mvar_subst_eq_binding {σ τ : Subst F X 𝔸} {x : X} {u : ntm F X 𝔸}
    {σ_extra : Subst F X 𝔸}
    (hσ : Subst.IsIdempotent σ)
    (hx_dom : x ∉ Subst.dom σ)
    (hu_fixed : u.subst σ = u)
    (hxu : u.occursIn x = false)
    (hτ_act : ∀ t : ntm F X 𝔸,
        t.subst τ = ((t.subst σ).subst [(x, u)]).subst σ_extra) :
    (ntm.mvar (F := F) [] x).subst τ = u.subst τ := by
  have h1 : (ntm.mvar (F := F) [] x).subst τ = u.subst σ_extra := by
    rw [hτ_act, ntm.subst_mvar_nil_of_not_mem_dom hx_dom]
    simp [ntm.subst_singleton, ntm.applyOne, ntm.permute_nil]
  have h2 : u.subst τ = u.subst σ_extra := by
    rw [hτ_act, hu_fixed]
    simp [ntm.subst_singleton, ntm.applyOne_of_not_occursIn _ _ _ hxu]
  rw [h1, h2]

mutual
  /-- If τ resolves the binding `x ↦ u`, then applyOne becomes a no-op under τ. -/
  lemma ntm.applyOne_subst_eq (t : ntm F X 𝔸) (x : X) (u : ntm F X 𝔸)
      (τ : Subst F X 𝔸)
      (h : (ntm.mvar (F := F) [] x).subst τ = u.subst τ) :
      (t.applyOne x u).subst τ = t.subst τ := by
    match t with
    | .atm _ => simp [ntm.applyOne]
    | .mvar π y =>
      simp only [ntm.applyOne]
      by_cases hy : y = x
      · rw [if_pos hy]
        rw [ntm.subst_permute, ntm.subst_mvar]
        subst hy
        rw [h]
      · rw [if_neg hy]
    | .fapp f ts =>
      simp only [ntm.applyOne, ntm.subst_fapp]
      congr 1
      exact ntmList.applyOne_subst_eq ts x u τ h
    | .abs b t' =>
      simp only [ntm.applyOne, ntm.subst_abs]
      congr 1
      exact ntm.applyOne_subst_eq t' x u τ h

  lemma ntmList.applyOne_subst_eq (ts : List (ntm F X 𝔸)) (x : X) (u : ntm F X 𝔸)
      (τ : Subst F X 𝔸)
      (h : (ntm.mvar (F := F) [] x).subst τ = u.subst τ) :
      (ts.map (·.applyOne x u)).map (·.subst τ) = ts.map (·.subst τ) := by
    match ts with
    | [] => rfl
    | t :: ts' =>
      simp only [List.map_cons]
      rw [ntm.applyOne_subst_eq t x u τ h,
          ntmList.applyOne_subst_eq ts' x u τ h]
end

lemma UnifConstraint.applySubst_singleton_subst_eq (c : UnifConstraint F X 𝔸)
    (x : X) (u : ntm F X 𝔸) (τ : Subst F X 𝔸)
    (h : (ntm.mvar (F := F) [] x).subst τ = u.subst τ) :
    (c.applySubst [(x, u)]).applySubst τ = c.applySubst τ := by
  cases c with
  | fresh a t =>
    simp only [UnifConstraint.applySubst, ntm.subst_singleton]
    rw [ntm.applyOne_subst_eq t x u τ h]
  | unif s t =>
    simp only [UnifConstraint.applySubst, ntm.subst_singleton]
    rw [ntm.applyOne_subst_eq s x u τ h, ntm.applyOne_subst_eq t x u τ h]

lemma UnifProblem.applySubst_singleton_subst_eq (Pr : UnifProblem F X 𝔸)
    (x : X) (u : ntm F X 𝔸) (τ : Subst F X 𝔸)
    (h : (ntm.mvar (F := F) [] x).subst τ = u.subst τ) :
    (Pr.applySubst [(x, u)]).applySubst τ = Pr.applySubst τ := by
  induction Pr with
  | nil => rfl
  | cons c rest ih =>
    simp only [UnifProblem.applySubst_cons]
    rw [UnifConstraint.applySubst_singleton_subst_eq c x u τ h, ih]

/-- π.reverse ++ π acts as identity on atoms, so permuting a term by it gives
    an α-equivalent term. -/
lemma ntm.alphaEquiv_permute_reverse_permute_self (Γ : Context 𝔸 X)
    (t : ntm F X 𝔸) (π : LPerm 𝔸) :
    (Γ ⊢ (t.permute π.reverse).permute π ≈α t) = true := by
  have h1 : (t.permute π.reverse).permute π = t.permute (π.reverse ++ π) :=
    ntm.permute_append t π.reverse π
  rw [h1]
  have h2 : t = t.permute [] := (ntm.permute_nil t).symm
  rw (config := { occs := .pos [2] }) [h2]
  apply ntm.alphaEquiv_of_perm_fresh
  intro n hn
  exfalso
  simp only [ds, Finset.mem_filter] at hn
  obtain ⟨_, hne⟩ := hn
  apply hne
  rw [LPermApply_append, LPermApply_reverse_right]
  rfl

/-- `Entails` distributes over the append of two unification problems. -/
lemma UnifProblem.entails_applySubst_append {Γ : Context 𝔸 X} {τ : Subst F X 𝔸}
    {Pr Pr' : UnifProblem F X 𝔸} :
    Problem.Entails Γ (UnifProblem.toConstraint (UnifProblem.applySubst (Pr ++ Pr') τ)) ↔
      Problem.Entails Γ (UnifProblem.toConstraint (UnifProblem.applySubst Pr τ)) ∧
      Problem.Entails Γ (UnifProblem.toConstraint (UnifProblem.applySubst Pr' τ)) := by
  simp only [UnifProblem.applySubst, UnifProblem.toConstraint, List.map_append,
    Problem.Entails_append_iff]

/-- Entailment of `cs` seen as unification constraints is entailment of `cs`. -/
lemma Problem.entails_applySubst_of_toUnif {Γ : Context 𝔸 X} {τ : Subst F X 𝔸}
    {cs : Problem F X 𝔸}
    (h : Problem.Entails Γ (UnifProblem.toConstraint
      (UnifProblem.applySubst (cs.map (·.toUnif)) τ))) :
    Problem.Entails Γ (Problem.applySubst cs τ) := by
  intro c hc
  simp only [Problem.applySubst, List.mem_map] at hc
  obtain ⟨c0, hc0, rfl⟩ := hc
  have heq : (c0.toUnif.applySubst τ).toConstraint = c0.applySubst τ := by
    cases c0 <;> simp [Constraint.toUnif, UnifConstraint.applySubst,
                       UnifConstraint.toConstraint, Constraint.applySubst]
  have hin : c0.applySubst τ ∈
      UnifProblem.toConstraint (UnifProblem.applySubst (cs.map (·.toUnif)) τ) := by
    simp only [UnifProblem.toConstraint, UnifProblem.applySubst, List.map_map,
               List.mem_map, Function.comp_apply]
    exact ⟨c0, hc0, heq⟩
  exact h _ hin

/-- Soundness of an instantiation step `x ↦ π⁻¹ · u`: the rest of the problem is still
    entailed, and `π · x` and `u` become α-equivalent under `τ`. -/
lemma instantiation_sound (rest : UnifProblem F X 𝔸) {σ τ σ_extra : Subst F X 𝔸}
    (Γ : Context 𝔸 X) (π : LPerm 𝔸) (x : X) (u : ntm F X 𝔸)
    (hσ : Subst.IsIdempotent σ) (hx_dom : x ∉ Subst.dom σ)
    (hu : ∀ z ∈ u.metavars, z ∉ Subst.dom σ) (hxu : u.occursIn x = false)
    (hτ_act : ∀ t : ntm F X 𝔸,
      t.subst τ = (t.subst (σ.comp [(x, u.permute π.reverse)])).subst σ_extra)
    (hΓ : Problem.Entails Γ (UnifProblem.toConstraint
      (UnifProblem.applySubst (rest.applySubst [(x, u.permute π.reverse)]) τ))) :
    Problem.Entails Γ (UnifProblem.toConstraint (UnifProblem.applySubst rest τ)) ∧
      alphaEquiv Γ ((ntm.mvar π x).subst τ) (u.subst τ) = true := by
  have hu_fixed : (u.permute π.reverse).subst σ = u.permute π.reverse := by
    apply ntm.subst_of_disjoint_dom
    intro z hz
    rw [ntm.occursIn_false_iff_not_mem_metavars, ntm.permute_metavars]
    exact fun hz_in => hu z hz_in hz
  have hxu' : (u.permute π.reverse).occursIn x = false := by
    rw [ntm.occursIn_permute]; exact hxu
  have hresolve : (ntm.mvar (F := F) [] x).subst τ = (u.permute π.reverse).subst τ :=
    mvar_subst_eq_binding hσ hx_dom hu_fixed hxu'
      (fun t => (hτ_act t).trans (by rw [ntm.subst_comp]))
  rw [UnifProblem.applySubst_singleton_subst_eq rest x _ τ hresolve] at hΓ
  refine ⟨hΓ, ?_⟩
  rw [ntm.subst_mvar π x τ, hresolve, ntm.subst_permute]
  exact ntm.alphaEquiv_permute_reverse_permute_self Γ (u.subst τ) π

/-- Soundness of `.next` outcomes: if `Γ` entails `Pr'.applySubst τ` for ANY
    target substitution `τ`, then `Γ` entails `(c :: rest).applySubst τ`.
    `τ` is independent of the `.next` output `σ'` so this lemma composes with
    deeper recursion (where the final σ extends σ'). -/
lemma unifStep_next_sound
    (c : UnifConstraint F X 𝔸) (rest : UnifProblem F X 𝔸) (σ : Subst F X 𝔸)
    (Pr' : UnifProblem F X 𝔸) (σ' : Subst F X 𝔸) (Γ : Context 𝔸 X)
    (τ : Subst F X 𝔸) (σ_extra : Subst F X 𝔸)
    (h : unifStep c rest σ = .next Pr' σ')
    (hσ : Subst.IsIdempotent σ)
    (hdisj : Subst.disjointPr σ (c :: rest))
    (hτ_act : ∀ t : ntm F X 𝔸, t.subst τ = (t.subst σ').subst σ_extra)
    (hΓ : Problem.Entails Γ (UnifProblem.toConstraint (UnifProblem.applySubst Pr' τ))) :
    Problem.Entails Γ (UnifProblem.toConstraint (UnifProblem.applySubst (c :: rest) τ)) := by
  have hmv : ∀ z ∈ c.metavars, z ∉ Subst.dom σ := fun z hz =>
    hdisj z (by simp [UnifProblem.allMetavars_cons, hz])
  cases UnifRule.of_unifStep h with
  | fresh a t cs ht hcs =>
    obtain ⟨hrest, hcsE⟩ := UnifProblem.entails_applySubst_append.mp hΓ
    simp only [UnifProblem.applySubst_cons, UnifProblem.toConstraint_cons,
               Problem.Entails_cons]
    exact ⟨fresh_subst_of_simplifyFresh_entails Γ a τ t cs hcs
      (Problem.entails_applySubst_of_toUnif hcsE), hrest⟩
  | atm a =>
    simp only [UnifProblem.applySubst_cons, UnifProblem.toConstraint_cons,
               Problem.Entails_cons]
    refine ⟨?_, hΓ⟩
    simp [UnifConstraint.applySubst, UnifConstraint.toConstraint,
          Constraint.applySubst, Constraint.Entails, alphaEquiv]
  | mvarSame π π' x =>
    obtain ⟨hrest, hfresh⟩ := UnifProblem.entails_applySubst_append.mp hΓ
    simp only [UnifProblem.applySubst_cons, UnifProblem.toConstraint_cons,
               Problem.Entails_cons]
    refine ⟨?_, hrest⟩
    simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint,
               Constraint.Entails]
    rw [ntm.subst_mvar π x τ, ntm.subst_mvar π' x τ]
    apply ntm.alphaEquiv_of_perm_fresh
    intro n hn
    have hmem : n ∈ dsList π π' := (mem_dsList_iff_mem_ds n π π').mpr hn
    have hcfresh : Constraint.fresh n (((ntm.mvar (F := F) [] x : ntm F X 𝔸).subst τ)) ∈
        UnifProblem.toConstraint
          ((UnifProblem.applySubst
            ((dsList π π').map (fun a => UnifConstraint.fresh a (ntm.mvar [] x))) τ)) := by
      simp only [UnifProblem.applySubst, UnifProblem.toConstraint, List.map_map,
                 List.mem_map, Function.comp_def]
      exact ⟨n, hmem, by simp [UnifConstraint.applySubst, UnifConstraint.toConstraint]⟩
    have := hfresh _ hcfresh
    simp only [Constraint.Entails] at this
    exact this
  | instL π x u hocc =>
    obtain ⟨hrest, hα⟩ := instantiation_sound rest Γ π x u hσ
      (hmv x (by simp [UnifConstraint.metavars, ntm.metavars]))
      (fun z hz => hmv z (by simp [UnifConstraint.metavars, hz])) hocc hτ_act hΓ
    simp only [UnifProblem.applySubst_cons, UnifProblem.toConstraint_cons,
               Problem.Entails_cons]
    exact ⟨hα, hrest⟩
  | instR π x u hocc =>
    obtain ⟨hrest, hα⟩ := instantiation_sound rest Γ π x u hσ
      (hmv x (by simp [UnifConstraint.metavars, ntm.metavars]))
      (fun z hz => hmv z (by simp [UnifConstraint.metavars, hz])) hocc hτ_act hΓ
    simp only [UnifProblem.applySubst_cons, UnifProblem.toConstraint_cons,
               Problem.Entails_cons]
    exact ⟨alphaEquiv_symm Γ _ _ hα, hrest⟩
  | fapp f ss ts hlen =>
    obtain ⟨hzip, hrest⟩ := UnifProblem.entails_applySubst_append.mp hΓ
    simp only [UnifProblem.applySubst_cons, UnifProblem.toConstraint_cons,
               Problem.Entails_cons]
    refine ⟨?_, hrest⟩
    simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint,
               Constraint.Entails, ntm.subst_fapp, alphaEquiv,
               Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨trivial, ?_⟩
    apply alphaEquivList_of_zip_subst_entails Γ τ ss ts hlen
    simp only [UnifProblem.applySubst, UnifProblem.toConstraint,
               List.map_map, Function.comp_def,
               UnifConstraint.applySubst, UnifConstraint.toConstraint] at hzip
    exact hzip
  | absSame a s t =>
    simp only [UnifProblem.applySubst_cons, UnifProblem.toConstraint_cons,
               Problem.Entails_cons] at hΓ ⊢
    obtain ⟨hst, hrest⟩ := hΓ
    refine ⟨?_, hrest⟩
    simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint,
               Constraint.Entails, ntm.subst_abs, alphaEquiv,
               decide_eq_true_eq, if_pos rfl] at hst ⊢
    exact hst
  | absDiff a b s t hab =>
    simp only [UnifProblem.applySubst_cons, UnifProblem.toConstraint_cons,
               Problem.Entails_cons] at hΓ ⊢
    obtain ⟨hperm, hfresh, hrest⟩ := hΓ
    refine ⟨?_, hrest⟩
    simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint,
               Constraint.Entails, ntm.subst_abs, alphaEquiv,
               decide_eq_true_eq, if_neg hab] at hperm hfresh ⊢
    refine ⟨?_, hfresh⟩
    rw [ntm.subst_permute] at hperm
    exact hperm


/-! ### Soundness of `finalizeDeferred` -/

mutual
  /-- Freshness is monotone in the context. -/
  theorem fresh_mono {Γ Γ' : Context 𝔸 X} (hsub : Γ ⊆ Γ') (a : 𝔸) (t : ntm F X 𝔸)
      (h : (Γ ⊢ a # t) = true) : (Γ' ⊢ a # t) = true := by
    match t with
    | ntm.atm _ => exact h
    | ntm.mvar π x =>
      simp only [fresh, decide_eq_true_eq] at h ⊢
      exact hsub h
    | ntm.fapp _ ts =>
      simp only [fresh] at h ⊢
      exact freshList_mono hsub a ts h
    | ntm.abs b s =>
      simp [fresh] at h ⊢
      rcases h with hab | hs
      · exact Or.inl hab
      · exact Or.inr (fresh_mono hsub a s hs)

  theorem freshList_mono {Γ Γ' : Context 𝔸 X} (hsub : Γ ⊆ Γ') (a : 𝔸)
      (ts : List (ntm F X 𝔸)) (h : freshList Γ a ts = true) :
      freshList Γ' a ts = true := by
    match ts with
    | [] => rfl
    | t :: ts' =>
      simp [freshList] at h ⊢
      obtain ⟨h1, h2⟩ := h
      exact ⟨fresh_mono hsub a t h1, freshList_mono hsub a ts' h2⟩
end


/-- A reduced constraint has the shape `.fresh _ (.mvar [] _)`. -/
lemma Constraint.reduced_destr {c : Constraint F X 𝔸} (h : c.IsReduced = true) :
    ∃ a x, c = .fresh a (.mvar [] x) := by
  cases c with
  | fresh a t =>
    cases t with
    | mvar π x =>
      cases π with
      | nil => exact ⟨a, x, rfl⟩
      | cons _ _ => simp [Constraint.IsReduced] at h
    | atm _  => simp [Constraint.IsReduced] at h
    | fapp _ _ => simp [Constraint.IsReduced] at h
    | abs _ _ => simp [Constraint.IsReduced] at h
  | alpha _ _ => simp [Constraint.IsReduced] at h

lemma foldl_ctxStep_mono (Γ : Context 𝔸 X) (cs : List (Constraint F X 𝔸)) :
    Γ ⊆ cs.foldl ctxStep Γ := by
  induction cs generalizing Γ with
  | nil => simp
  | cons c cs' ih =>
    simp only [List.foldl_cons]
    refine Finset.Subset.trans ?_ (ih _)
    cases c with
    | fresh a' t =>
      cases t with
      | mvar π x =>
        cases π with
        | nil => exact Finset.subset_insert _ _
        | cons _ _ => exact Finset.Subset.refl _
      | _ => exact Finset.Subset.refl _
    | alpha _ _ => exact Finset.Subset.refl _

/-- Reduced constraints in cs are entailed by the foldl-built context. -/
lemma foldl_ctxStep_entails (Γ : Context 𝔸 X) (cs : List (Constraint F X 𝔸))
    (hred : Problem.IsReduced cs) :
    Problem.Entails (cs.foldl ctxStep Γ) cs := by
  intro c hc
  obtain ⟨a', x', rfl⟩ := Constraint.reduced_destr (hred c hc)
  simp only [Constraint.Entails, fresh, List.reverse_nil, LPermApply_nil,
             decide_eq_true_eq]
  clear hred
  induction cs generalizing Γ with
  | nil => cases hc
  | cons c0 cs' ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hc with hh | hmem
    · subst hh
      apply foldl_ctxStep_mono
      exact Finset.mem_insert_self _ _
    · exact ih _ hmem

/-- Specialised Problem-entailment monotonicity for reduced problems. -/
lemma Problem.Entails_mono_reduced {Γ Γ' : Context 𝔸 X} (hsub : Γ ⊆ Γ')
    {P : Problem F X 𝔸} (hred : Problem.IsReduced P)
    (h : Problem.Entails Γ P) : Problem.Entails Γ' P := by
  intro c hc
  obtain ⟨a', x', rfl⟩ := Constraint.reduced_destr (hred c hc)
  have := h _ hc
  simp only [Constraint.Entails] at this ⊢
  exact fresh_mono hsub _ _ this

/-- Soundness of `finalizeDeferred`: every deferred `(a, x)` is satisfied by the
    returned context, and the initial context is preserved. -/
lemma finalizeDeferred_sound (σ : Subst F X 𝔸) :
    ∀ (ds : List (𝔸 × X)) (Γ₀ Γ : Context 𝔸 X),
      finalizeDeferred ds σ Γ₀ = some Γ →
      Γ₀ ⊆ Γ ∧ ∀ p ∈ ds, (Γ ⊢ p.1 # (ntm.mvar (F := F) [] p.2).subst σ) = true
  | [], Γ₀, Γ, h => by
    simp only [finalizeDeferred, Option.some.injEq] at h
    subst h
    exact ⟨Finset.Subset.refl _, by intro p hp; cases hp⟩
  | (a, x) :: tl, Γ₀, Γ, h => by
    simp only [finalizeDeferred] at h
    cases hcs : simplifyFresh a ((ntm.mvar (F := F) [] x).subst σ) with
    | none => rw [hcs] at h; cases h
    | some cs =>
      rw [hcs] at h
      have hrec := finalizeDeferred_sound σ tl (cs.foldl ctxStep Γ₀) Γ
        (show finalizeDeferred tl σ (cs.foldl ctxStep Γ₀) = some Γ from h)
      refine ⟨?_, ?_⟩
      · exact Finset.Subset.trans (foldl_ctxStep_mono Γ₀ cs) hrec.1
      · rintro p hp
        rcases List.mem_cons.mp hp with hh | hmem
        · subst hh
          have hred : Problem.IsReduced cs := simplifyFresh_isReduced a _ hcs
          have hent : Problem.Entails (cs.foldl ctxStep Γ₀) cs :=
            foldl_ctxStep_entails Γ₀ cs hred
          have hent' : Problem.Entails Γ cs :=
            Problem.Entails_mono_reduced hrec.1 hred hent
          exact (simplifyFresh_sound Γ a _ hcs).mpr hent'
        · exact hrec.2 p hmem


/-! ### Soundness of `unify` and `solve` -/

/-- Inversion of `.ctx`: only `.fresh _ (.mvar _ _)` produces it. -/
lemma unifStep_ctx_inv (c : UnifConstraint F X 𝔸) (rest : UnifProblem F X 𝔸)
    (σ : Subst F X 𝔸) (a : 𝔸) (x : X) (h : unifStep c rest σ = .ctx a x) :
    ∃ (b : 𝔸) (π : LPerm 𝔸), c = .fresh b (.mvar π x) ∧ a = LPermApply π.reverse b := by
  cases c with
  | fresh b t =>
    cases t with
    | mvar π y =>
      simp only [unifStep, StepResult.ctx.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨b, π, rfl, rfl⟩
    | atm a' =>
      simp only [unifStep] at h
      cases hcs : simplifyFresh b (.atm (F := F) (X := X) a') with
      | none => rw [hcs] at h; cases h
      | some cs => rw [hcs] at h; cases h
    | fapp f ts =>
      simp only [unifStep] at h
      cases hcs : simplifyFresh b (.fapp f ts) with
      | none => rw [hcs] at h; cases h
      | some cs => rw [hcs] at h; cases h
    | abs c t =>
      simp only [unifStep] at h
      cases hcs : simplifyFresh b (.abs c t) with
      | none => rw [hcs] at h; cases h
      | some cs => rw [hcs] at h; cases h
  | unif s t =>
    cases s <;> cases t <;>
      first
        | (simp only [unifStep] at h; split_ifs at h)
        | (simp only [unifStep] at h; cases h)

/-- Soundness of `unify`: if the final deferred is satisfied by `Γ` under `σ'`,
    then `Γ` satisfies the original problem under `σ'` and the original deferred. -/
theorem unify_sound (Γ : Context 𝔸 X) :
    ∀ (Pr : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) (ds : List (𝔸 × X)),
      ∀ (ds' : List (𝔸 × X)) (σ' : Subst F X 𝔸),
        unify Pr σ ds = some (ds', σ') →
        Subst.IsIdempotent σ →
        Subst.disjointPr σ Pr →
        (∀ p ∈ ds', (Γ ⊢ p.1 # (ntm.mvar (F := F) [] p.2).subst σ') = true) →
        Problem.Entails Γ (UnifProblem.applySubst Pr σ').toConstraint ∧
        (∀ p ∈ ds, (Γ ⊢ p.1 # (ntm.mvar (F := F) [] p.2).subst σ') = true) := by
  intro Pr σ ds
  induction Pr, σ, ds using unify.induct with
  | case1 σ ds =>
    intro ds' σ' h _ _ hf
    simp only [unify, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, hf⟩
    intro c hc
    simp [UnifProblem.applySubst, UnifProblem.toConstraint] at hc
  | case2 σ ds c rest hfail =>
    intro ds' σ' h _ _ _
    rw [unify] at h
    rw [hfail] at h
    cases h
  | case3 σ ds c rest a x hctx ih =>
    intro ds' σ' h hσ hdisj hf
    rw [unify] at h
    rw [hctx] at h
    obtain ⟨hpr, hds_all⟩ := ih ds' σ' h hσ (Subst.disjointPr_cons hdisj) hf
    obtain ⟨b, π, rfl, rfl⟩ := unifStep_ctx_inv c rest σ a x hctx
    refine ⟨?_, ?_⟩
    · simp only [UnifProblem.applySubst_cons, UnifProblem.toConstraint_cons,
                 Problem.Entails_cons]
      refine ⟨?_, hpr⟩
      have ha := hds_all (LPermApply π.reverse b, x) List.mem_cons_self
      simp only [Constraint.Entails, UnifConstraint.applySubst, UnifConstraint.toConstraint]
      rw [ntm.subst_mvar]
      rw [show b = LPermApply π (LPermApply π.reverse b)
            from (LPermApply_reverse_right π b).symm]
      rw [← fresh_equivariance]
      exact ha
    · intro p hp
      exact hds_all p (List.mem_cons_of_mem _ hp)
  | case4 σ ds c rest Pr' σ_next hnext ih =>
    intro ds' σ' h hσ hdisj hf
    rw [unify] at h
    rw [hnext] at h
    obtain ⟨hσ_next, hdisj_next⟩ :=
      unifStep_next_idempotent_and_disjoint c rest σ Pr' σ_next hnext hσ hdisj
    obtain ⟨hpr', hds⟩ := ih ds' σ' h hσ_next hdisj_next hf
    refine ⟨?_, hds⟩
    obtain ⟨σ_extra, hσ_ext⟩ := unify_σ_prefix Pr' σ_next ds ds' σ' h
    exact unifStep_next_sound c rest σ Pr' σ_next Γ σ' σ_extra
      hnext hσ hdisj hσ_ext hpr'


/-- `solve Pr = some (Γ, σ)` produces a context that entails `Pr` under σ. -/
theorem UnifProblem.solve_sound (Pr : UnifProblem F X 𝔸) (Γ : Context 𝔸 X)
    (σ : Subst F X 𝔸) (h : Pr.solve = some (Γ, σ)) :
    Problem.Entails Γ (Pr.applySubst σ).toConstraint := by
  simp only [UnifProblem.solve] at h
  cases hu : unify Pr [] [] with
  | none => rw [hu] at h; cases h
  | some result =>
    rw [hu] at h
    obtain ⟨ds, σ_u⟩ := result
    simp only at h
    cases hf : finalizeDeferred ds σ_u ∅ with
    | none => rw [hf] at h; cases h
    | some Γ_fin =>
      rw [hf] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hΓeq, hσeq⟩ := h
      subst hΓeq
      subst hσeq
      have ⟨_, hfresh⟩ := finalizeDeferred_sound σ_u ds ∅ Γ_fin hf
      have hσ_empty : Subst.IsIdempotent ([] : Subst F X 𝔸) := by
        intro x; simp
      have hdisj_empty : Subst.disjointPr ([] : Subst F X 𝔸) Pr := by
        intro x _; simp [Subst.dom]
      exact (unify_sound Γ_fin Pr [] [] ds σ_u hu hσ_empty hdisj_empty hfresh).1

/-! ### Idempotence of the computed substitution -/

/-- `unify` preserves idempotence of σ under the disjointness invariant. -/
theorem unify_preserves_idempotent :
    ∀ (Pr : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) (ds : List (𝔸 × X))
      (ds' : List (𝔸 × X)) (σ' : Subst F X 𝔸),
      unify Pr σ ds = some (ds', σ') →
      Subst.IsIdempotent σ →
      Subst.disjointPr σ Pr →
      σ'.IsIdempotent := by
  intro Pr σ ds
  induction Pr, σ, ds using unify.induct with
  | case1 σ ds =>
    intro ds' σ' h hσ _
    simp only [unify, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact hσ
  | case2 σ ds c rest hfail =>
    intro ds' σ' h _ _
    rw [unify, hfail] at h
    cases h
  | case3 σ ds c rest a x hctx ih =>
    intro ds' σ' h hσ hdisj
    rw [unify, hctx] at h
    exact ih ds' σ' h hσ (Subst.disjointPr_cons hdisj)
  | case4 σ ds c rest Pr' σ_next hnext ih =>
    intro ds' σ' h hσ hdisj
    rw [unify, hnext] at h
    obtain ⟨hσ_next, hdisj_next⟩ :=
      unifStep_next_idempotent_and_disjoint c rest σ Pr' σ_next hnext hσ hdisj
    exact ih ds' σ' h hσ_next hdisj_next

/-- `solve Pr = some (Γ, σ)` produces an idempotent σ.  Direct corollary of
    `unify_preserves_idempotent` with σ_initial = []. -/
theorem UnifProblem.solve_idempotent (Pr : UnifProblem F X 𝔸) (Γ : Context 𝔸 X)
    (σ : Subst F X 𝔸) (h : Pr.solve = some (Γ, σ)) :
    Subst.IsIdempotent σ := by
  simp only [UnifProblem.solve] at h
  cases hu : unify Pr [] [] with
  | none => rw [hu] at h; cases h
  | some result =>
    rw [hu] at h
    obtain ⟨ds, σ_u⟩ := result
    simp only at h
    cases hf : finalizeDeferred ds σ_u ∅ with
    | none => rw [hf] at h; cases h
    | some Γ_fin =>
      rw [hf] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, hσeq⟩ := h
      subst hσeq
      have hσ_empty : Subst.IsIdempotent ([] : Subst F X 𝔸) := by
        intro x; simp
      have hdisj_empty : Subst.disjointPr ([] : Subst F X 𝔸) Pr := by
        intro x _; simp [Subst.dom]
      exact unify_preserves_idempotent Pr [] [] ds σ_u hu hσ_empty hdisj_empty

/-- Maribel Definition 27 + Theorem 35 : if `solve Pr = some (Γ, σ)`, then
    `(Γ, σ)` is a solution of Pr in the sense that Γ
    entails `Pr.applySubst σ` AND σ is idempotent. -/
theorem UnifProblem.solve_satisfies (Pr : UnifProblem F X 𝔸) (Γ : Context 𝔸 X)
    (σ : Subst F X 𝔸) (h : Pr.solve = some (Γ, σ)) :
    Solution.Satisfies Γ σ Pr :=
  ⟨UnifProblem.solve_sound Pr Γ σ h, UnifProblem.solve_idempotent Pr Γ σ h⟩

end Nominal
