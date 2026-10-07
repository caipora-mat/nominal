import Nominal.Syntax.Unification.Mgu

/-!
# The algorithm introduces no new metavariables

Every metavariable occurring in the output of `UnifProblem.solve`, in the domain or the range of
the substitution or in the freshness context, already occurs in the problem
(`UnifProblem.solve_metavars_subset`).
-/

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

/-- Every metavariable of `σ`, bound or occurring in a bound term, lies in `V`. -/
def Subst.VarsIn (σ : Subst F X 𝔸) (V : Finset X) : Prop :=
  ∀ p ∈ σ, p.1 ∈ V ∧ p.2.metavars ⊆ V

lemma Subst.VarsIn.nil (V : Finset X) : Subst.VarsIn ([] : Subst F X 𝔸) V := by
  intro p hp; cases hp

mutual
  /-- Applying a substitution with variables in `V` keeps the variables of a term in `V`. -/
  lemma ntm.subst_metavars_subset {σ : Subst F X 𝔸} {V : Finset X} (hσ : σ.VarsIn V) :
      ∀ t : ntm F X 𝔸, t.metavars ⊆ V → (t.subst σ).metavars ⊆ V
    | .atm a, _ => by simp [ntm.metavars]
    | .mvar π x, h => by
        rw [ntm.subst_mvar, ntm.permute_metavars, ntm.subst_mvar_nil]
        cases hl : σ.lookup x with
        | none => simpa [ntm.metavars] using h
        | some s => exact (hσ _ (Subst.lookup_mem hl)).2
    | .fapp f ts, h => by
        simp only [ntm.subst_fapp, ntm.metavars] at h ⊢
        exact ntmList.subst_metavars_subset hσ ts h
    | .abs a t, h => by
        simp only [ntm.subst_abs, ntm.metavars] at h ⊢
        exact ntm.subst_metavars_subset hσ t h

  lemma ntmList.subst_metavars_subset {σ : Subst F X 𝔸} {V : Finset X} (hσ : σ.VarsIn V) :
      ∀ ts : List (ntm F X 𝔸), ntmList.metavars ts ⊆ V →
        ntmList.metavars (ts.map (·.subst σ)) ⊆ V
    | [], _ => by simp [ntmList.metavars]
    | t :: ts, h => by
        simp only [List.map_cons, ntmList.metavars] at h ⊢
        exact Finset.union_subset
          (ntm.subst_metavars_subset hσ t (Finset.union_subset_left h))
          (ntmList.subst_metavars_subset hσ ts (Finset.union_subset_right h))
end

lemma Subst.VarsIn.comp_singleton {σ : Subst F X 𝔸} {V : Finset X} (hσ : σ.VarsIn V)
    {x : X} {u : ntm F X 𝔸} (hx : x ∈ V) (hu : u.metavars ⊆ V) :
    (σ.comp [(x, u)]).VarsIn V := by
  have hτ : Subst.VarsIn [(x, u)] V := by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact ⟨hx, hu⟩
  intro p hp
  simp only [Subst.comp, List.mem_append, List.mem_map] at hp
  rcases hp with ⟨q, hq, rfl⟩ | hp
  · exact ⟨(hσ q hq).1, ntm.subst_metavars_subset hτ q.2 (hσ q hq).2⟩
  · exact hτ p hp

/-- One step keeps the metavariables of the problem and of the substitution in `V`. -/
lemma unifStep_next_metavars {c : UnifConstraint F X 𝔸} {rest Pr' : UnifProblem F X 𝔸}
    {σ σ' : Subst F X 𝔸} {V : Finset X}
    (h : unifStep c rest σ = .next Pr' σ')
    (hV : UnifProblem.allMetavars (c :: rest) ⊆ V) (hσ : σ.VarsIn V) :
    UnifProblem.allMetavars Pr' ⊆ V ∧ σ'.VarsIn V := by
  have hc : c.metavars ⊆ V := fun z hz => hV (by simp [hz])
  have hrest : UnifProblem.allMetavars rest ⊆ V := fun z hz => hV (by simp [hz])
  cases UnifRule.of_unifStep h with
  | fresh a t cs ht hcs =>
    refine ⟨?_, hσ⟩
    rw [UnifProblem.allMetavars_append]
    exact Finset.union_subset hrest (allMetavars_map_toUnif_subset cs V
      (fun c' hc' z hz => hc (simplifyFresh_metavars_subset a t cs hcs c' hc' z hz)))
  | atm a => exact ⟨hrest, hσ⟩
  | mvarSame π π' x =>
    refine ⟨?_, hσ⟩
    rw [UnifProblem.allMetavars_append]
    refine Finset.union_subset hrest (allMetavars_map_subset _ _ V (fun a _ z hz => ?_))
    simp only [UnifConstraint.metavars, ntm.metavars, Finset.mem_singleton] at hz
    subst hz
    exact hc (by simp [UnifConstraint.metavars, ntm.metavars])
  | instL π x u hocc =>
    have hx : x ∈ V := hc (by simp [UnifConstraint.metavars, ntm.metavars])
    have hu : (u.permute π.reverse).metavars ⊆ V := by
      rw [ntm.permute_metavars]
      exact fun z hz => hc (by simp [UnifConstraint.metavars, hz])
    refine ⟨fun z hz => ?_, hσ.comp_singleton hx hu⟩
    have := UnifProblem.applySubst_singleton_metavars_subset rest x _ hz
    simp only [Finset.mem_union, Finset.mem_sdiff] at this
    rcases this with ⟨hz', _⟩ | hz'
    · exact hrest hz'
    · exact hu hz'
  | instR π x u hocc =>
    have hx : x ∈ V := hc (by simp [UnifConstraint.metavars, ntm.metavars])
    have hu : (u.permute π.reverse).metavars ⊆ V := by
      rw [ntm.permute_metavars]
      exact fun z hz => hc (by simp [UnifConstraint.metavars, hz])
    refine ⟨fun z hz => ?_, hσ.comp_singleton hx hu⟩
    have := UnifProblem.applySubst_singleton_metavars_subset rest x _ hz
    simp only [Finset.mem_union, Finset.mem_sdiff] at this
    rcases this with ⟨hz', _⟩ | hz'
    · exact hrest hz'
    · exact hu hz'
  | fapp f ss ts hlen =>
    refine ⟨?_, hσ⟩
    rw [UnifProblem.allMetavars_append]
    refine Finset.union_subset (allMetavars_map_subset (ss.zip ts)
      (fun p => UnifConstraint.unif p.1 p.2) V (fun p hp z hz => ?_)) hrest
    obtain ⟨hp1, hp2⟩ := List.of_mem_zip hp
    simp only [UnifConstraint.metavars, Finset.mem_union] at hz
    apply hc
    simp only [UnifConstraint.metavars, ntm.metavars, Finset.mem_union]
    rcases hz with hz | hz
    · exact Or.inl (ntmList.mem_metavars_of_mem hp1 hz)
    · exact Or.inr (ntmList.mem_metavars_of_mem hp2 hz)
  | absSame a s t =>
    refine ⟨fun z hz => hV ?_, hσ⟩
    simpa [UnifConstraint.metavars, ntm.metavars] using hz
  | absDiff a b s t hab =>
    refine ⟨fun z hz => hV ?_, hσ⟩
    simp only [UnifProblem.allMetavars_cons, UnifConstraint.metavars, ntm.metavars,
      ntm.permute_metavars, Finset.mem_union] at hz ⊢
    tauto

/-- The first stage keeps the metavariables of the substitution and of the deferred
    obligations in `V`. -/
lemma unify_metavars {V : Finset X} :
    ∀ (Pr : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) (ds : List (𝔸 × X))
      (ds' : List (𝔸 × X)) (σ' : Subst F X 𝔸),
      unify Pr σ ds = some (ds', σ') →
      UnifProblem.allMetavars Pr ⊆ V → σ.VarsIn V → (∀ p ∈ ds, p.2 ∈ V) →
      σ'.VarsIn V ∧ ∀ p ∈ ds', p.2 ∈ V := by
  intro Pr σ ds
  induction Pr, σ, ds using unify.induct with
  | case1 σ ds =>
    intro ds' σ' h _ hσ hds
    simp only [unify, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hσ, hds⟩
  | case2 σ ds c rest hfail =>
    intro ds' σ' h _ _ _
    rw [unify, hfail] at h
    cases h
  | case3 σ ds c rest a x hctx ih =>
    intro ds' σ' h hV hσ hds
    rw [unify, hctx] at h
    obtain ⟨b, π, rfl, _⟩ := unifStep_ctx_inv c rest σ a x hctx
    have hx : x ∈ V := hV (by simp [UnifConstraint.metavars, ntm.metavars])
    refine ih ds' σ' h (fun z hz => hV (by simp [hz])) hσ (fun p hp => ?_)
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hx
    · exact hds p hp
  | case4 σ ds c rest Pr' σ_next hnext ih =>
    intro ds' σ' h hV hσ hds
    rw [unify, hnext] at h
    obtain ⟨hV', hσ'⟩ := unifStep_next_metavars hnext hV hσ
    exact ih ds' σ' h hV' hσ' hds

/-- Collecting primitive obligations with variables in `V` keeps the context in `V`. -/
lemma foldl_ctxStep_metavars {V : Finset X} (cs : Problem F X 𝔸) :
    ∀ Γ₀ : Context 𝔸 X, (∀ p ∈ Γ₀, p.2 ∈ V) →
      (∀ c ∈ cs, ∀ z ∈ c.toUnif.metavars, z ∈ V) →
      ∀ p ∈ cs.foldl ctxStep Γ₀, p.2 ∈ V := by
  induction cs with
  | nil => intro Γ₀ hΓ₀ _ p hp; exact hΓ₀ p hp
  | cons c cs ih =>
    intro Γ₀ hΓ₀ hcs p hp
    rw [List.foldl_cons] at hp
    refine ih _ ?_ (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) p hp
    have hc := hcs c List.mem_cons_self
    cases c with
    | fresh a' t =>
      cases t with
      | mvar π x' =>
        cases π with
        | nil =>
          intro q hq
          rcases Finset.mem_insert.mp hq with rfl | hq
          · exact hc x' (by simp [Constraint.toUnif, UnifConstraint.metavars, ntm.metavars])
          · exact hΓ₀ q hq
        | cons _ _ => exact hΓ₀
      | atm _ => exact hΓ₀
      | fapp _ _ => exact hΓ₀
      | abs _ _ => exact hΓ₀
    | alpha _ _ => exact hΓ₀

/-- The second stage keeps the metavariables of the context in `V`. -/
lemma finalizeDeferred_metavars {V : Finset X} {σ : Subst F X 𝔸} (hσ : σ.VarsIn V) :
    ∀ (ds : List (𝔸 × X)) (Γ₀ Γ : Context 𝔸 X),
      finalizeDeferred ds σ Γ₀ = some Γ →
      (∀ p ∈ ds, p.2 ∈ V) → (∀ p ∈ Γ₀, p.2 ∈ V) → ∀ p ∈ Γ, p.2 ∈ V
  | [], Γ₀, Γ, h, _, hΓ₀ => by
    simp only [finalizeDeferred, Option.some.injEq] at h
    subst h
    exact hΓ₀
  | (a, x) :: tl, Γ₀, Γ, h, hds, hΓ₀ => by
    simp only [finalizeDeferred] at h
    cases hcs : simplifyFresh a ((ntm.mvar (F := F) [] x).subst σ) with
    | none => rw [hcs] at h; cases h
    | some cs =>
      rw [hcs] at h
      have hx : (ntm.mvar (F := F) (𝔸 := 𝔸) [] x).metavars ⊆ V := by
        simpa [ntm.metavars] using hds (a, x) List.mem_cons_self
      exact finalizeDeferred_metavars hσ tl (cs.foldl ctxStep Γ₀) Γ h
        (fun p hp => hds p (List.mem_cons_of_mem _ hp))
        (foldl_ctxStep_metavars cs Γ₀ hΓ₀ (fun c hc z hz =>
          ntm.subst_metavars_subset hσ _ hx
            (simplifyFresh_metavars_subset a _ cs hcs c hc z hz)))

/-- **The algorithm introduces no new metavariables**: those of the computed substitution, in
    its domain or in its bound terms, and those of the computed freshness context all occur in
    the problem. -/
theorem UnifProblem.solve_metavars_subset (Pr : UnifProblem F X 𝔸) (Γ : Context 𝔸 X)
    (σ : Subst F X 𝔸) (h : Pr.solve = some (Γ, σ)) :
    σ.VarsIn (UnifProblem.allMetavars Pr) ∧ ∀ p ∈ Γ, p.2 ∈ UnifProblem.allMetavars Pr := by
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
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hσ, hds⟩ := unify_metavars Pr [] [] ds σ_u hu (Finset.Subset.refl _)
        (Subst.VarsIn.nil _) (by intro p hp; cases hp)
      exact ⟨hσ, finalizeDeferred_metavars hσ ds ∅ Γ_fin hf hds (by intro p hp; simp at hp)⟩

end Nominal
