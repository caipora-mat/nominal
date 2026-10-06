import Nominal.Syntax.Unification.Properties

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

/-- The accumulated substitution `σ` is consistent with `θ` modulo `Δ`:
    inductive invariant carried through `unify_le`.  Maribel Theorem 35. -/
def Subst.absorbedBy (Δ : Context 𝔸 X) (σ θ : Subst F X 𝔸) : Prop :=
  ∀ x : X, (Δ ⊢ ((ntm.mvar (F := F) [] x).subst σ).subst θ ≈α
               (ntm.mvar (F := F) [] x).subst θ) = true

@[simp] lemma Subst.absorbedBy_nil (Δ : Context 𝔸 X) (θ : Subst F X 𝔸) :
    Subst.absorbedBy Δ ([] : Subst F X 𝔸) θ := by
  intro x
  simp only [ntm.subst_nil]
  exact alphaEquiv_refl _ _

mutual
  /-- If `u.subst θ ≈α (.mvar [] x).subst θ` in Δ, then for any term `t`,
      applying `[(x, u)]` before `θ` gives an α-equivalent result to `θ` alone. -/
  lemma alphaEquiv_applyOne_subst (Δ : Context 𝔸 X) (θ : Subst F X 𝔸)
      (x : X) (u : ntm F X 𝔸)
      (hu : (Δ ⊢ u.subst θ ≈α (ntm.mvar (F := F) [] x).subst θ) = true) :
      ∀ t : ntm F X 𝔸,
        (Δ ⊢ (t.applyOne x u).subst θ ≈α t.subst θ) = true
    | .atm a => by
        simp only [ntm.applyOne]; exact alphaEquiv_refl _ _
    | .mvar π y => by
        simp only [ntm.applyOne]
        by_cases hxy : y = x
        · subst hxy
          rw [if_pos rfl, ntm.subst_permute, ntm.subst_mvar]
          exact alphaEquiv_permute_congr Δ _ _ π hu
        · rw [if_neg hxy]
          exact alphaEquiv_refl _ _
    | .fapp f ts => by
        simp only [ntm.applyOne, ntm.subst_fapp, alphaEquiv, decide_eq_true_eq,
                   true_and, List.map_map]
        exact alphaEquivList_applyOne_subst Δ θ x u hu ts
    | .abs a t' => by
        simp only [ntm.applyOne, ntm.subst_abs, alphaEquiv, if_pos rfl]
        exact alphaEquiv_applyOne_subst Δ θ x u hu t'

  lemma alphaEquivList_applyOne_subst (Δ : Context 𝔸 X) (θ : Subst F X 𝔸)
      (x : X) (u : ntm F X 𝔸)
      (hu : (Δ ⊢ u.subst θ ≈α (ntm.mvar (F := F) [] x).subst θ) = true) :
      ∀ ts : List (ntm F X 𝔸),
        alphaEquivList Δ (ts.map (fun t => (t.applyOne x u).subst θ))
                         (ts.map (·.subst θ)) = true
    | [] => by simp [alphaEquivList]
    | t :: ts' => by
        simp only [List.map_cons, alphaEquivList, decide_eq_true_eq]
        exact ⟨alphaEquiv_applyOne_subst Δ θ x u hu t,
               alphaEquivList_applyOne_subst Δ θ x u hu ts'⟩
end

mutual
  /-- Pointwise congruence: if `ρ₁` and `ρ₂` agree up to `≈α` in `Δ` on every
      bare metavariable, they agree on every term. -/
  lemma ntm.alphaEquiv_subst_pointwise (Δ : Context 𝔸 X) (ρ₁ ρ₂ : Subst F X 𝔸)
      (h : ∀ y : X, (Δ ⊢ (ntm.mvar (F := F) [] y).subst ρ₁
                      ≈α (ntm.mvar (F := F) [] y).subst ρ₂) = true) :
      ∀ t : ntm F X 𝔸, (Δ ⊢ t.subst ρ₁ ≈α t.subst ρ₂) = true
    | .atm a => by simp only [ntm.subst_atm]; exact alphaEquiv_refl _ _
    | .mvar π y => by
        rw [ntm.subst_mvar π y ρ₁, ntm.subst_mvar π y ρ₂]
        exact alphaEquiv_permute_congr Δ _ _ π (h y)
    | .fapp f ts => by
        simp only [ntm.subst_fapp, alphaEquiv, decide_eq_true_eq, true_and]
        exact ntm.alphaEquivList_subst_pointwise Δ ρ₁ ρ₂ h ts
    | .abs a t' => by
        simp only [ntm.subst_abs, alphaEquiv]
        exact ntm.alphaEquiv_subst_pointwise Δ ρ₁ ρ₂ h t'

  lemma ntm.alphaEquivList_subst_pointwise (Δ : Context 𝔸 X) (ρ₁ ρ₂ : Subst F X 𝔸)
      (h : ∀ y : X, (Δ ⊢ (ntm.mvar (F := F) [] y).subst ρ₁
                      ≈α (ntm.mvar (F := F) [] y).subst ρ₂) = true) :
      ∀ ts : List (ntm F X 𝔸),
        alphaEquivList Δ (ts.map (·.subst ρ₁)) (ts.map (·.subst ρ₂)) = true
    | [] => by simp [alphaEquivList]
    | t :: ts' => by
        simp only [List.map_cons, alphaEquivList, decide_eq_true_eq]
        exact ⟨ntm.alphaEquiv_subst_pointwise Δ ρ₁ ρ₂ h t,
               ntm.alphaEquivList_subst_pointwise Δ ρ₁ ρ₂ h ts'⟩
end

/-- Applying `π` then `π.reverse` is α-equivalent to identity. -/
lemma ntm.alphaEquiv_permute_permute_reverse_self (Γ : Context 𝔸 X)
    (t : ntm F X 𝔸) (π : LPerm 𝔸) :
    (Γ ⊢ (t.permute π).permute π.reverse ≈α t) = true := by
  have := ntm.alphaEquiv_permute_reverse_permute_self Γ t π.reverse
  rw [List.reverse_reverse] at this
  exact this

/-- Arm 3 of `unifStep` (mvar-vs-rhs): shifts the permutation to derive the
    consistency precondition needed by `Subst.absorbedBy_append`. -/
lemma alphaEquiv_imp_consistency_arm3
    (Δ : Context 𝔸 X) (θ : Subst F X 𝔸) (π : LPerm 𝔸) (x : X) (u : ntm F X 𝔸)
    (hc : (Δ ⊢ (ntm.mvar (F := F) π x).subst θ ≈α u.subst θ) = true) :
    (Δ ⊢ (u.permute π.reverse).subst θ ≈α (ntm.mvar (F := F) [] x).subst θ) = true := by
  rw [ntm.subst_mvar] at hc
  have hperm := alphaEquiv_permute_congr Δ _ _ π.reverse hc
  rw [ntm.subst_permute]
  have hself := ntm.alphaEquiv_permute_permute_reverse_self Δ
    ((ntm.mvar (F := F) [] x).subst θ) π
  exact alphaEquiv_trans Δ _ _ _ (alphaEquiv_symm Δ _ _ hperm) hself

lemma alphaEquiv_imp_consistency_arm4
    (Δ : Context 𝔸 X) (θ : Subst F X 𝔸) (π : LPerm 𝔸) (x : X) (u : ntm F X 𝔸)
    (hc : (Δ ⊢ u.subst θ ≈α (ntm.mvar (F := F) π x).subst θ) = true) :
    (Δ ⊢ (u.permute π.reverse).subst θ ≈α (ntm.mvar (F := F) [] x).subst θ) = true :=
  alphaEquiv_imp_consistency_arm3 Δ θ π x u (alphaEquiv_symm Δ _ _ hc)

lemma Subst.absorbedBy_append (Δ : Context 𝔸 X) (σ θ : Subst F X 𝔸)
    (x : X) (u_perm : ntm F X 𝔸)
    (habs : Subst.absorbedBy Δ σ θ)
    (hu : (Δ ⊢ u_perm.subst θ ≈α (ntm.mvar (F := F) [] x).subst θ) = true) :
    Subst.absorbedBy Δ (σ.comp [(x, u_perm)]) θ := by
  intro y
  rw [ntm.subst_mvar_nil_comp]
  simp only [ntm.subst_singleton]
  have hcong := alphaEquiv_applyOne_subst Δ θ x u_perm hu
      ((ntm.mvar (F := F) [] y).subst σ)
  exact alphaEquiv_trans Δ _ _ _ hcong (habs y)

/-- Under consistency `u.subst θ ≈α θ(x)` in `Δ`, the binding `[(x, u)]` is
    invisible at the constraint-entailment level. -/
lemma UnifConstraint.entails_applyOne_of_entails
    (Δ : Context 𝔸 X) (θ : Subst F X 𝔸) (x : X) (u : ntm F X 𝔸)
    (hu : (Δ ⊢ u.subst θ ≈α (ntm.mvar (F := F) [] x).subst θ) = true)
    (c : UnifConstraint F X 𝔸)
    (h : Constraint.Entails Δ (c.applySubst θ).toConstraint = true) :
    Constraint.Entails Δ ((c.applySubst [(x, u)]).applySubst θ).toConstraint = true := by
  cases c with
  | fresh a t =>
    simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint,
               Constraint.Entails, ntm.subst_singleton] at *
    have hcong := alphaEquiv_applyOne_subst Δ θ x u hu t
    exact freshPreserves_alphaEquiv Δ a (t.subst θ) ((t.applyOne x u).subst θ) h
      (alphaEquiv_symm Δ _ _ hcong)
  | unif s t =>
    simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint,
               Constraint.Entails, ntm.subst_singleton] at *
    have hcongS := alphaEquiv_applyOne_subst Δ θ x u hu s
    have hcongT := alphaEquiv_applyOne_subst Δ θ x u hu t
    exact alphaEquiv_trans Δ _ _ _
      (alphaEquiv_trans Δ _ _ _ hcongS h) (alphaEquiv_symm Δ _ _ hcongT)

/-- Lift of `UnifConstraint.entails_applyOne_of_entails` to `UnifProblem`. -/
lemma UnifProblem.entails_applyOne_of_entails
    (Δ : Context 𝔸 X) (θ : Subst F X 𝔸) (x : X) (u : ntm F X 𝔸)
    (hu : (Δ ⊢ u.subst θ ≈α (ntm.mvar (F := F) [] x).subst θ) = true)
    (Pr : UnifProblem F X 𝔸)
    (h : Problem.Entails Δ (Pr.applySubst θ).toConstraint) :
    Problem.Entails Δ ((Pr.applySubst [(x, u)]).applySubst θ).toConstraint := by
  intro c' hc'
  simp only [UnifProblem.applySubst, UnifProblem.toConstraint, List.map_map,
             List.mem_map, Function.comp] at hc'
  obtain ⟨c, hc_mem, rfl⟩ := hc'
  apply UnifConstraint.entails_applyOne_of_entails Δ θ x u hu c
  apply h
  simp only [UnifProblem.applySubst, UnifProblem.toConstraint, List.mem_map]
  exact ⟨c.applySubst θ, ⟨c, hc_mem, rfl⟩, rfl⟩

mutual
  /-- Converse of `fresh_subst_of_simplifyFresh_entails` (from Properties).
      If `simplifyFresh a t = some cs` and `Γ ⊢ a # t.subst τ`, then every
      constraint in `cs.applySubst τ` is entailed by `Γ`. -/
  lemma simplifyFresh_subst_imp_entails (Γ : Context 𝔸 X) (a : 𝔸) (τ : Subst F X 𝔸) :
      ∀ (t : ntm F X 𝔸) (cs : Problem F X 𝔸),
        simplifyFresh a t = some cs →
        (Γ ⊢ a # t.subst τ) = true →
        Problem.Entails Γ (cs.applySubst τ)
    | .atm b, cs, hs, _ => by
        simp only [simplifyFresh] at hs
        by_cases hab : a = b
        · rw [if_pos hab] at hs; cases hs
        · rw [if_neg hab] at hs
          injection hs with hs_eq; subst hs_eq
          exact Problem.Entails.nil
    | .mvar π x, cs, hs, hf => by
        simp only [simplifyFresh] at hs
        injection hs with hs_eq; subst hs_eq
        intro c' hc'
        simp only [Problem.applySubst, List.map_cons, List.map_nil,
                   List.mem_cons, List.not_mem_nil, or_false] at hc'
        subst hc'
        simp only [Constraint.applySubst, Constraint.Entails]
        rw [ntm.subst_mvar] at hf
        rw [fresh_equivariance Γ (LPermApply π.reverse a)
              ((ntm.mvar (F := F) [] x).subst τ) π,
            LPermApply_reverse_right]
        exact hf
    | .abs b t', cs, hs, hf => by
        simp only [simplifyFresh] at hs
        split_ifs at hs with hab
        · cases hs
          simp [Problem.applySubst, Problem.Entails.nil]
        · have hft : (Γ ⊢ a # t'.subst τ) = true := by
            simp only [ntm.subst_abs, fresh] at hf
            rw [decide_eq_true_eq] at hf
            rcases hf with rfl | h
            · exact absurd rfl hab
            · exact h
          exact simplifyFresh_subst_imp_entails Γ a τ t' cs hs hft
    | .fapp f ts, cs, hs, hf => by
        simp only [simplifyFresh] at hs
        rw [ntm.subst_fapp] at hf
        simp only [fresh] at hf
        exact simplifyFreshList_subst_imp_entails Γ a τ ts cs hs hf

  lemma simplifyFreshList_subst_imp_entails (Γ : Context 𝔸 X) (a : 𝔸) (τ : Subst F X 𝔸) :
      ∀ (ts : List (ntm F X 𝔸)) (cs : Problem F X 𝔸),
        simplifyFreshList a ts = some cs →
        freshList Γ a (ts.map (·.subst τ)) = true →
        Problem.Entails Γ (cs.applySubst τ)
    | [], cs, hs, _ => by
        simp only [simplifyFreshList] at hs; cases hs
        simp [Problem.applySubst, Problem.Entails.nil]
    | t :: ts', cs, hs, hfl => by
        simp only [simplifyFreshList] at hs
        cases hsf : simplifyFresh a t with
        | none => rw [hsf] at hs; cases hs
        | some cs₁ =>
          rw [hsf] at hs
          cases hsfl : simplifyFreshList a ts' with
          | none => rw [hsfl] at hs; cases hs
          | some cs₂ =>
            rw [hsfl] at hs; cases hs
            simp only [List.map_cons, freshList, decide_eq_true_eq] at hfl
            obtain ⟨hft, hftail⟩ := hfl
            have ih1 := simplifyFresh_subst_imp_entails Γ a τ t cs₁ hsf hft
            have ih2 := simplifyFreshList_subst_imp_entails Γ a τ ts' cs₂ hsfl hftail
            intro c' hc'
            simp only [Problem.applySubst, List.map_append, List.mem_append] at hc'
            rcases hc' with hc'' | hc''
            · exact ih1 c' hc''
            · exact ih2 c' hc''
end

/-- Converse of `alphaEquivList_of_zip_subst_entails` (from Properties);
    used in the fapp-fapp completeness case. -/
private lemma alphaEquivList_imp_zip_entails {Γ : Context 𝔸 X} {σ : Subst F X 𝔸} :
    ∀ (ss ts : List (ntm F X 𝔸)),
      ss.length = ts.length →
      alphaEquivList Γ (ss.map (·.subst σ)) (ts.map (·.subst σ)) = true →
      Problem.Entails Γ
        ((ss.zip ts).map (fun p => Constraint.alpha (p.1.subst σ) (p.2.subst σ)))
  | [], [], _, _ => Problem.Entails.nil
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | s :: ss', t :: ts', hlen, halist => by
      simp only [List.zip_cons_cons, List.map_cons]
      simp only [List.map_cons, alphaEquivList, decide_eq_true_eq] at halist
      obtain ⟨hst, htail⟩ := halist
      rw [Problem.Entails_cons]
      refine ⟨?_, ?_⟩
      · simp [Constraint.Entails]; exact hst
      · simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        exact alphaEquivList_imp_zip_entails ss' ts' hlen htail

/-- From a satisfied `c :: rest`, extract that `c` is entailed after `applySubst`. -/
private lemma entails_head_of_satisfies
    (c : UnifConstraint F X 𝔸) (rest : UnifProblem F X 𝔸)
    (Δ : Context 𝔸 X) (θ : Subst F X 𝔸)
    (hsat : Solution.Satisfies Δ θ (c :: rest)) :
    Constraint.Entails Δ (c.applySubst θ).toConstraint = true := by
  obtain ⟨hΓ, _⟩ := hsat
  have hmem : (c.applySubst θ).toConstraint ∈
      (UnifProblem.applySubst (c :: rest) θ).toConstraint := by
    simp [UnifProblem.applySubst, UnifProblem.toConstraint]
  exact hΓ _ hmem

/-- Step-level converse for `.next Pr' σ_next`: a solution of `c :: rest`
    carries over to `Pr'` under the same `θ`, and `σ_next` remains absorbed
    by `θ`.  Analogue of Isabelle's `P1-from-P2-sred`. -/
lemma unifStep_next_le
    (c : UnifConstraint F X 𝔸) (rest : UnifProblem F X 𝔸)
    (σ σ_next : Subst F X 𝔸) (Pr' : UnifProblem F X 𝔸)
    (Δ : Context 𝔸 X) (θ : Subst F X 𝔸)
    (h : unifStep c rest σ = .next Pr' σ_next)
    (hθ : Solution.Satisfies Δ θ (c :: rest))
    (habs : Subst.absorbedBy Δ σ θ) :
    Solution.Satisfies Δ θ Pr' ∧ Subst.absorbedBy Δ σ_next θ := by
  obtain ⟨hΓ, hidem⟩ := hθ
  have hc : Constraint.Entails Δ (c.applySubst θ).toConstraint = true :=
    entails_head_of_satisfies c rest Δ θ ⟨hΓ, hidem⟩
  have hrest : Problem.Entails Δ (rest.applySubst θ).toConstraint := by
    intro c' hc'
    apply hΓ c'
    rw [UnifProblem.applySubst_cons, UnifProblem.toConstraint_cons]
    exact List.mem_cons_of_mem _ hc'
  cases c with
  | fresh a t =>
    cases t with
    | mvar π x =>
      simp [unifStep] at h
    | atm b =>
      by_cases hab : a = b
      · subst hab; simp [unifStep, simplifyFresh] at h
      · have heq : unifStep (UnifConstraint.fresh (X := X) a (ntm.atm b)) rest σ
            = .next rest σ := by simp [unifStep, simplifyFresh, hab]
        rw [heq] at h; injection h with hPr hσ
        subst hPr; subst hσ
        exact ⟨⟨hrest, hidem⟩, habs⟩
    | abs b t' =>
      cases hsf : simplifyFresh a (ntm.abs (F := F) (X := X) b t') with
      | none => simp [unifStep, hsf] at h
      | some cs =>
        have heq : unifStep (UnifConstraint.fresh (X := X) a (ntm.abs b t')) rest σ
            = .next (rest ++ cs.map (·.toUnif)) σ := by simp [unifStep, hsf]
        rw [heq] at h; injection h with hPr hσ
        subst hPr; subst hσ
        refine ⟨⟨?_, hidem⟩, habs⟩
        have hfreshT : (Δ ⊢ a # (ntm.abs b t').subst θ) = true := by
          simpa [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                 Constraint.Entails] using hc
        have hcs := simplifyFresh_subst_imp_entails Δ a θ (ntm.abs b t') cs hsf hfreshT
        intro c' hc'
        simp only [UnifProblem.applySubst, UnifProblem.toConstraint, List.map_append,
                   List.mem_append] at hc'
        rcases hc' with hc''_rest | hc''_cs
        · exact hrest c' hc''_rest
        · simp only [List.map_map, List.mem_map, Function.comp] at hc''_cs
          obtain ⟨c'', hc''_mem, rfl⟩ := hc''_cs
          have hround : ((Constraint.toUnif c'').applySubst θ).toConstraint
              = c''.applySubst θ := by
            cases c'' <;> simp [Constraint.toUnif, UnifConstraint.applySubst,
                                UnifConstraint.toConstraint, Constraint.applySubst]
          rw [hround]
          exact hcs (c''.applySubst θ) (List.mem_map_of_mem hc''_mem)
    | fapp f ts =>
      cases hsf : simplifyFresh a (ntm.fapp (X := X) (𝔸 := 𝔸) f ts) with
      | none => simp [unifStep, hsf] at h
      | some cs =>
        have heq : unifStep (UnifConstraint.fresh (X := X) a (ntm.fapp f ts)) rest σ
            = .next (rest ++ cs.map (·.toUnif)) σ := by simp [unifStep, hsf]
        rw [heq] at h; injection h with hPr hσ
        subst hPr; subst hσ
        refine ⟨⟨?_, hidem⟩, habs⟩
        have hfreshT : (Δ ⊢ a # (ntm.fapp f ts).subst θ) = true := by
          simpa [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                 Constraint.Entails] using hc
        have hcs := simplifyFresh_subst_imp_entails Δ a θ (ntm.fapp f ts) cs hsf hfreshT
        intro c' hc'
        simp only [UnifProblem.applySubst, UnifProblem.toConstraint, List.map_append,
                   List.mem_append] at hc'
        rcases hc' with hc''_rest | hc''_cs
        · exact hrest c' hc''_rest
        · simp only [List.map_map, List.mem_map, Function.comp] at hc''_cs
          obtain ⟨c'', hc''_mem, rfl⟩ := hc''_cs
          have hround : ((Constraint.toUnif c'').applySubst θ).toConstraint
              = c''.applySubst θ := by
            cases c'' <;> simp [Constraint.toUnif, UnifConstraint.applySubst,
                                UnifConstraint.toConstraint, Constraint.applySubst]
          rw [hround]
          exact hcs (c''.applySubst θ) (List.mem_map_of_mem hc''_mem)
  | unif s t =>
    cases s with
    | atm a =>
      cases t with
      | atm b =>
        by_cases hab : a = b
        · subst hab
          have heq : unifStep (UnifConstraint.unif (X := X) (ntm.atm a) (ntm.atm a)) rest σ
              = .next rest σ := by simp [unifStep]
          rw [heq] at h; injection h with hPr hσ
          subst hPr; subst hσ
          exact ⟨⟨hrest, hidem⟩, habs⟩
        · simp [unifStep, hab] at h
      | mvar π x =>
        have heq : unifStep (UnifConstraint.unif (X := X) (ntm.atm a) (ntm.mvar π x)) rest σ
            = .next (rest.applySubst [(x, (ntm.atm (F := F) a).permute π.reverse)])
                    (σ.comp [(x, (ntm.atm (F := F) a).permute π.reverse)]) := by
          simp [unifStep, ntm.occursIn]
        rw [heq] at h; injection h with hPr hσ
        subst hPr; subst hσ
        set u_perm : ntm F X 𝔸 := ntm.atm (LPermApply π.reverse a) with hu_perm_def
        have hu : (Δ ⊢ u_perm.subst θ ≈α (ntm.mvar (F := F) [] x).subst θ) = true := by
          have hu_subst : u_perm.subst θ = u_perm := by simp [u_perm]
          rw [hu_subst]
          have hc_simpl : (Δ ⊢ ntm.atm (F := F) (X := X) a ≈α
                              (ntm.mvar (F := F) π x).subst θ) = true := by
            simpa [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                   Constraint.Entails] using hc
          rw [ntm.subst_mvar] at hc_simpl
          have hperm := alphaEquiv_permute_congr Δ _ _ π.reverse hc_simpl
          have hatm_perm : (ntm.atm (F := F) (X := X) a).permute π.reverse = u_perm := by
            simp [ntm.permute, u_perm]
          rw [hatm_perm] at hperm
          have hself := ntm.alphaEquiv_permute_permute_reverse_self Δ
            ((ntm.mvar (F := F) [] x).subst θ) π
          exact alphaEquiv_trans Δ _ _ _ hperm hself
        have huperm_eq : (ntm.atm (F := F) (X := X) a).permute π.reverse = u_perm := by
          simp [ntm.permute, u_perm]
        rw [huperm_eq]
        refine ⟨⟨?_, hidem⟩, ?_⟩
        · exact UnifProblem.entails_applyOne_of_entails Δ θ x u_perm hu rest hrest
        · exact Subst.absorbedBy_append Δ σ θ x u_perm habs hu
      | fapp _ _ => simp [unifStep] at h
      | abs _ _  => simp [unifStep] at h
    | mvar π x =>
      cases t with
      | atm a =>
        have heq : unifStep (UnifConstraint.unif (X := X) (ntm.mvar π x) (ntm.atm a)) rest σ
            = .next (rest.applySubst [(x, (ntm.atm (F := F) a).permute π.reverse)])
                    (σ.comp [(x, (ntm.atm (F := F) a).permute π.reverse)]) := by
          simp [unifStep, ntm.occursIn]
        rw [heq] at h; injection h with hPr hσ
        subst hPr; subst hσ
        set u_perm : ntm F X 𝔸 := ntm.atm (LPermApply π.reverse a) with hu_perm_def
        have hu : (Δ ⊢ u_perm.subst θ ≈α (ntm.mvar (F := F) [] x).subst θ) = true := by
          have hu_subst : u_perm.subst θ = u_perm := by simp [u_perm]
          rw [hu_subst]
          have hc_simpl : (Δ ⊢ (ntm.mvar (F := F) π x).subst θ ≈α
                              ntm.atm (F := F) (X := X) a) = true := by
            simpa [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                   Constraint.Entails] using hc
          have hc_symm := alphaEquiv_symm Δ _ _ hc_simpl
          rw [ntm.subst_mvar] at hc_symm
          have hperm := alphaEquiv_permute_congr Δ _ _ π.reverse hc_symm
          have hatm_perm : (ntm.atm (F := F) (X := X) a).permute π.reverse = u_perm := by
            simp [ntm.permute, u_perm]
          rw [hatm_perm] at hperm
          have hself := ntm.alphaEquiv_permute_permute_reverse_self Δ
            ((ntm.mvar (F := F) [] x).subst θ) π
          exact alphaEquiv_trans Δ _ _ _ hperm hself
        have huperm_eq : (ntm.atm (F := F) (X := X) a).permute π.reverse = u_perm := by
          simp [ntm.permute, u_perm]
        rw [huperm_eq]
        refine ⟨⟨?_, hidem⟩, ?_⟩
        · exact UnifProblem.entails_applyOne_of_entails Δ θ x u_perm hu rest hrest
        · exact Subst.absorbedBy_append Δ σ θ x u_perm habs hu
      | mvar π' y =>
        by_cases hxy : x = y
        · -- mvar-mvar same: σ_next = σ.
          subst hxy
          have heq : unifStep (UnifConstraint.unif (X := X) (ntm.mvar π x) (ntm.mvar π' x)) rest σ
              = .next (rest ++ (dsList π π').map (UnifConstraint.fresh · (ntm.mvar [] x))) σ
              := by simp [unifStep]
          rw [heq] at h; injection h with hPr hσ
          subst hPr; subst hσ
          refine ⟨⟨?_, hidem⟩, habs⟩
          have hcα : (Δ ⊢ ((ntm.mvar (F := F) [] x).subst θ).permute π ≈α
                          ((ntm.mvar (F := F) [] x).subst θ).permute π') = true := by
            have hraw : alphaEquiv Δ ((ntm.mvar (F := F) π x).subst θ)
                                       ((ntm.mvar (F := F) π' x).subst θ) = true := by
              have := hc
              simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                         Constraint.Entails] at this
              exact this
            rw [ntm.subst_mvar (π := π), ntm.subst_mvar (π := π')] at hraw
            exact hraw
          have hfreshAll := alphaEquiv_invariance_mpr Δ
            ((ntm.mvar (F := F) [] x).subst θ) π π' hcα
          intro c' hc'
          simp only [UnifProblem.applySubst, UnifProblem.toConstraint, List.map_append,
                     List.mem_append] at hc'
          rcases hc' with hc''_rest | hc''_ds
          · -- from rest.
            apply hrest c'
            simp only [UnifProblem.applySubst, UnifProblem.toConstraint, List.mem_map] at *
            exact hc''_rest
          · -- from dsList.
            simp only [List.map_map, List.mem_map, Function.comp] at hc''_ds
            obtain ⟨n, hn_dsList, rfl⟩ := hc''_ds
            simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                       Constraint.Entails]
            exact hfreshAll n ((mem_dsList_iff_mem_ds n π π').mp hn_dsList)
        · -- mvar-mvar diff: instantiation with u = .mvar π' y.
          have heq : unifStep (UnifConstraint.unif (X := X) (ntm.mvar π x)
                                (ntm.mvar π' y)) rest σ
              = .next (rest.applySubst [(x, (ntm.mvar (F := F) π' y).permute π.reverse)])
                      (σ.comp [(x, (ntm.mvar (F := F) π' y).permute π.reverse)]) := by
            simp [unifStep, hxy]
          rw [heq] at h; injection h with hPr hσ
          subst hPr; subst hσ
          set u_perm : ntm F X 𝔸 := (ntm.mvar π' y).permute π.reverse
          have hu : (Δ ⊢ u_perm.subst θ ≈α (ntm.mvar (F := F) [] x).subst θ) = true := by
            apply alphaEquiv_imp_consistency_arm3 Δ θ π x (ntm.mvar π' y)
            simpa [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                   Constraint.Entails] using hc
          refine ⟨⟨?_, hidem⟩, ?_⟩
          · exact UnifProblem.entails_applyOne_of_entails Δ θ x u_perm hu rest hrest
          · exact Subst.absorbedBy_append Δ σ θ x u_perm habs hu
      | fapp f ts =>
        by_cases hocc : (ntm.fapp (X := X) (𝔸 := 𝔸) f ts).occursIn x
        · simp [unifStep, hocc] at h
        · have hocc_false : (ntm.fapp (X := X) (𝔸 := 𝔸) f ts).occursIn x = false :=
            Bool.eq_false_iff.mpr hocc
          have heq : unifStep (UnifConstraint.unif (X := X) (ntm.mvar π x)
                                (ntm.fapp f ts)) rest σ
              = .next (rest.applySubst [(x, (ntm.fapp (X := X) f ts).permute π.reverse)])
                      (σ.comp [(x, (ntm.fapp (X := X) f ts).permute π.reverse)]) := by
            simp [unifStep, hocc_false]
          rw [heq] at h; injection h with hPr hσ
          subst hPr; subst hσ
          set u_perm : ntm F X 𝔸 := (ntm.fapp f ts).permute π.reverse
          have hu : (Δ ⊢ u_perm.subst θ ≈α (ntm.mvar (F := F) [] x).subst θ) = true := by
            apply alphaEquiv_imp_consistency_arm3 Δ θ π x (ntm.fapp f ts)
            simpa [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                   Constraint.Entails] using hc
          refine ⟨⟨?_, hidem⟩, ?_⟩
          · exact UnifProblem.entails_applyOne_of_entails Δ θ x u_perm hu rest hrest
          · exact Subst.absorbedBy_append Δ σ θ x u_perm habs hu
      | abs b t' =>
        by_cases hocc : (ntm.abs (F := F) (X := X) b t').occursIn x
        · simp [unifStep, hocc] at h
        · have hocc_false : (ntm.abs (F := F) (X := X) b t').occursIn x = false :=
            Bool.eq_false_iff.mpr hocc
          have heq : unifStep (UnifConstraint.unif (X := X) (ntm.mvar π x)
                                (ntm.abs b t')) rest σ
              = .next (rest.applySubst [(x, (ntm.abs (F := F) b t').permute π.reverse)])
                      (σ.comp [(x, (ntm.abs (F := F) b t').permute π.reverse)]) := by
            simp [unifStep, hocc_false]
          rw [heq] at h; injection h with hPr hσ
          subst hPr; subst hσ
          set u_perm : ntm F X 𝔸 := (ntm.abs b t').permute π.reverse
          have hu : (Δ ⊢ u_perm.subst θ ≈α (ntm.mvar (F := F) [] x).subst θ) = true := by
            apply alphaEquiv_imp_consistency_arm3 Δ θ π x (ntm.abs b t')
            simpa [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                   Constraint.Entails] using hc
          refine ⟨⟨?_, hidem⟩, ?_⟩
          · exact UnifProblem.entails_applyOne_of_entails Δ θ x u_perm hu rest hrest
          · exact Subst.absorbedBy_append Δ σ θ x u_perm habs hu
    | fapp f ss =>
      cases t with
      | atm _ => simp [unifStep] at h
      | mvar π x =>
        by_cases hocc : (ntm.fapp (X := X) (𝔸 := 𝔸) f ss).occursIn x
        · simp [unifStep, hocc] at h
        · have hocc_false : (ntm.fapp (X := X) (𝔸 := 𝔸) f ss).occursIn x = false :=
            Bool.eq_false_iff.mpr hocc
          have heq : unifStep (UnifConstraint.unif (X := X) (ntm.fapp f ss)
                                (ntm.mvar π x)) rest σ
              = .next (rest.applySubst [(x, (ntm.fapp (X := X) f ss).permute π.reverse)])
                      (σ.comp [(x, (ntm.fapp (X := X) f ss).permute π.reverse)]) := by
            simp [unifStep, hocc_false]
          rw [heq] at h; injection h with hPr hσ
          subst hPr; subst hσ
          set u_perm : ntm F X 𝔸 := (ntm.fapp f ss).permute π.reverse
          have hu : (Δ ⊢ u_perm.subst θ ≈α (ntm.mvar (F := F) [] x).subst θ) = true := by
            apply alphaEquiv_imp_consistency_arm4 Δ θ π x (ntm.fapp f ss)
            simpa [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                   Constraint.Entails] using hc
          refine ⟨⟨?_, hidem⟩, ?_⟩
          · exact UnifProblem.entails_applyOne_of_entails Δ θ x u_perm hu rest hrest
          · exact Subst.absorbedBy_append Δ σ θ x u_perm habs hu
      | fapp g ts =>
        by_cases hfg : f = g ∧ ss.length = ts.length
        · -- fapp-fapp matching: σ_next = σ.
          obtain ⟨hf_eq, hlen⟩ := hfg
          subst hf_eq
          have heq : unifStep (UnifConstraint.unif (X := X) (ntm.fapp f ss) (ntm.fapp f ts))
                              rest σ
              = .next ((ss.zip ts).map (fun (s, t) => UnifConstraint.unif s t) ++ rest) σ := by
            simp [unifStep, hlen]
          rw [heq] at h; injection h with hPr hσ
          subst hPr; subst hσ
          refine ⟨⟨?_, hidem⟩, habs⟩
          simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                     Constraint.Entails, ntm.subst_fapp, alphaEquiv,
                     decide_eq_true_eq] at hc
          obtain ⟨_, halist⟩ := hc
          intro c' hc'
          simp only [UnifProblem.applySubst, UnifProblem.toConstraint, List.map_append,
                     List.mem_append] at hc'
          rcases hc' with hc''_zip | hc''_rest
          · -- zip-mapped: use alphaEquivList_imp_zip_entails.
            have hzip := alphaEquivList_imp_zip_entails ss ts hlen halist
            simp only [UnifProblem.applySubst, UnifProblem.toConstraint, List.map_map,
                       List.mem_map, Function.comp] at hc''_zip
            obtain ⟨p, hp_mem, rfl⟩ := hc''_zip
            obtain ⟨s_i, t_i⟩ := p
            apply hzip
            simp only [List.mem_map]
            exact ⟨(s_i, t_i), hp_mem, rfl⟩
          · exact hrest c' hc''_rest
        · simp [unifStep, hfg] at h
      | abs _ _ => simp [unifStep] at h
    | abs a s' =>
      cases t with
      | atm _ => simp [unifStep] at h
      | mvar π x =>
        by_cases hocc : (ntm.abs (F := F) (X := X) a s').occursIn x
        · simp [unifStep, hocc] at h
        · have hocc_false : (ntm.abs (F := F) (X := X) a s').occursIn x = false :=
            Bool.eq_false_iff.mpr hocc
          have heq : unifStep (UnifConstraint.unif (X := X) (ntm.abs a s')
                                (ntm.mvar π x)) rest σ
              = .next (rest.applySubst [(x, (ntm.abs (F := F) a s').permute π.reverse)])
                      (σ.comp [(x, (ntm.abs (F := F) a s').permute π.reverse)]) := by
            simp [unifStep, hocc_false]
          rw [heq] at h; injection h with hPr hσ
          subst hPr; subst hσ
          set u_perm : ntm F X 𝔸 := (ntm.abs a s').permute π.reverse
          have hu : (Δ ⊢ u_perm.subst θ ≈α (ntm.mvar (F := F) [] x).subst θ) = true := by
            apply alphaEquiv_imp_consistency_arm4 Δ θ π x (ntm.abs a s')
            simpa [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                   Constraint.Entails] using hc
          refine ⟨⟨?_, hidem⟩, ?_⟩
          · exact UnifProblem.entails_applyOne_of_entails Δ θ x u_perm hu rest hrest
          · exact Subst.absorbedBy_append Δ σ θ x u_perm habs hu
      | fapp _ _ => simp [unifStep] at h
      | abs b t' =>
        by_cases hab : a = b
        · -- abs-abs same binder: σ_next = σ, Pr' = .unif s' t' :: rest.
          subst hab
          have heq : unifStep (UnifConstraint.unif (X := X) (ntm.abs a s') (ntm.abs a t')) rest σ
              = .next (UnifConstraint.unif s' t' :: rest) σ := by simp [unifStep]
          rw [heq] at h; injection h with hPr hσ
          subst hPr; subst hσ
          refine ⟨⟨?_, hidem⟩, habs⟩
          intro c' hc'
          rcases List.mem_cons.mp hc' with rfl | hc''
          · -- head case: alphaEquiv Δ (s'.subst θ) (t'.subst θ).
            simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                       Constraint.Entails] at *
            simp only [ntm.subst_abs, alphaEquiv, if_pos rfl] at hc
            exact hc
          · -- tail in rest.applySubst θ.toConstraint.
            exact hrest c' hc''
        · -- abs-abs different binder: σ_next = σ.
          have heq : unifStep (UnifConstraint.unif (X := X) (ntm.abs a s') (ntm.abs b t')) rest σ
              = .next (UnifConstraint.unif (s'.permute [(b, a)]) t'
                       :: UnifConstraint.fresh b s' :: rest) σ := by
            simp [unifStep, hab]
          rw [heq] at h; injection h with hPr hσ
          subst hPr; subst hσ
          refine ⟨⟨?_, hidem⟩, habs⟩
          simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                     Constraint.Entails, ntm.subst_abs, alphaEquiv, if_neg hab,
                     decide_eq_true_eq] at hc
          obtain ⟨hcα, hcfr⟩ := hc
          intro c' hc'
          rcases List.mem_cons.mp hc' with rfl | hc''
          · -- head: .alpha ((s'.permute [(b, a)]).subst θ) (t'.subst θ).
            simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint, Constraint.Entails]
            rw [ntm.subst_permute]
            exact hcα
          · rcases List.mem_cons.mp hc'' with rfl | hc'''
            · -- second: .fresh b (s'.subst θ).
              simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint, Constraint.Entails]
              exact hcfr
            · exact hrest c' hc'''

lemma unifStep_ctx_le
    (c : UnifConstraint F X 𝔸) (rest : UnifProblem F X 𝔸) (σ : Subst F X 𝔸)
    (a : 𝔸) (x : X)
    (Δ : Context 𝔸 X) (θ : Subst F X 𝔸)
    (h : unifStep c rest σ = .ctx a x)
    (hθ : Solution.Satisfies Δ θ (c :: rest)) :
    Solution.Satisfies Δ θ rest ∧
    (Δ ⊢ a # (ntm.mvar (F := F) [] x).subst θ) = true := by
  obtain ⟨hΓ, hidem⟩ := hθ
  have hrest : Problem.Entails Δ (rest.applySubst θ).toConstraint := by
    intro c' hc'
    apply hΓ c'
    rw [UnifProblem.applySubst_cons, UnifProblem.toConstraint_cons]
    exact List.mem_cons_of_mem _ hc'
  cases c with
  | unif s t =>
    exfalso
    cases s <;> cases t <;> simp [unifStep, ntm.occursIn] at h <;>
      first
        | (split_ifs at h <;> cases h)
        | cases h
  | fresh b t =>
    cases t with
    | atm _ =>
      exfalso
      simp [unifStep, simplifyFresh] at h
      split_ifs at h <;> cases h
    | abs b' t' =>
      exfalso
      cases hsf : simplifyFresh b (ntm.abs (F := F) (X := X) b' t') with
      | none =>
        have heq : unifStep (UnifConstraint.fresh (X := X) b (ntm.abs b' t')) rest σ
            = .fail := by simp [unifStep, hsf]
        rw [heq] at h; cases h
      | some cs =>
        have heq : unifStep (UnifConstraint.fresh (X := X) b (ntm.abs b' t')) rest σ
            = .next (rest ++ cs.map (·.toUnif)) σ := by simp [unifStep, hsf]
        rw [heq] at h; cases h
    | fapp f ts =>
      exfalso
      cases hsf : simplifyFresh b (ntm.fapp (X := X) (𝔸 := 𝔸) f ts) with
      | none =>
        have heq : unifStep (UnifConstraint.fresh (X := X) b (ntm.fapp f ts)) rest σ
            = .fail := by simp [unifStep, hsf]
        rw [heq] at h; cases h
      | some cs =>
        have heq : unifStep (UnifConstraint.fresh (X := X) b (ntm.fapp f ts)) rest σ
            = .next (rest ++ cs.map (·.toUnif)) σ := by simp [unifStep, hsf]
        rw [heq] at h; cases h
    | mvar π x' =>
      have heq : unifStep (UnifConstraint.fresh (X := X) b (ntm.mvar π x')) rest σ
          = .ctx (LPermApply π.reverse b) x' := by simp [unifStep]
      rw [heq] at h
      injection h with ha hx
      subst ha; subst hx
      refine ⟨⟨hrest, hidem⟩, ?_⟩
      have hcfresh : (Δ ⊢ b # (ntm.mvar (F := F) π x').subst θ) = true := by
        have hcent := entails_head_of_satisfies
            (UnifConstraint.fresh (X := X) b (ntm.mvar π x')) rest Δ θ ⟨hΓ, hidem⟩
        simpa [UnifConstraint.applySubst, UnifConstraint.toConstraint,
               Constraint.Entails] using hcent
      rw [ntm.subst_mvar] at hcfresh
      rw [fresh_equivariance Δ (LPermApply π.reverse b)
            ((ntm.mvar (F := F) [] x').subst θ) π,
          LPermApply_reverse_right]
      exact hcfresh

mutual
  def ntm.size : ntm F X 𝔸 → ℕ
    | .atm _     => 1
    | .mvar _ _  => 1
    | .fapp _ ts => 1 + ntmList.sumSize ts
    | .abs _ t   => 1 + t.size

  def ntmList.sumSize : List (ntm F X 𝔸) → ℕ
    | []      => 0
    | t :: ts => t.size + ntmList.sumSize ts
end

@[simp] lemma ntm.size_atm (a : 𝔸) : (ntm.atm (F := F) (X := X) a).size = 1 := rfl
@[simp] lemma ntm.size_mvar (π : LPerm 𝔸) (x : X) :
    (ntm.mvar (F := F) π x).size = 1 := rfl
@[simp] lemma ntm.size_fapp (f : F) (ts : List (ntm F X 𝔸)) :
    (ntm.fapp f ts).size = 1 + ntmList.sumSize ts := rfl
@[simp] lemma ntm.size_abs (a : 𝔸) (t : ntm F X 𝔸) :
    (ntm.abs a t).size = 1 + t.size := rfl

@[simp] lemma ntmList.sumSize_nil : ntmList.sumSize ([] : List (ntm F X 𝔸)) = 0 := rfl
@[simp] lemma ntmList.sumSize_cons (t : ntm F X 𝔸) (ts : List (ntm F X 𝔸)) :
    ntmList.sumSize (t :: ts) = t.size + ntmList.sumSize ts := rfl

mutual
  lemma ntm.size_permute (t : ntm F X 𝔸) (π : LPerm 𝔸) :
      (t.permute π).size = t.size := by
    match t with
    | .atm _    => simp [ntm.permute, ntm.size]
    | .mvar _ _ => simp [ntm.permute, ntm.size]
    | .fapp _ ts =>
        simp only [ntm.permute, ntm.size_fapp]
        congr 1
        exact ntmList.sumSize_permute ts π
    | .abs _ t' =>
        simp only [ntm.permute, ntm.size_abs]
        rw [ntm.size_permute t' π]

  lemma ntmList.sumSize_permute (ts : List (ntm F X 𝔸)) (π : LPerm 𝔸) :
      ntmList.sumSize (ts.map (·.permute π)) = ntmList.sumSize ts := by
    match ts with
    | []      => rfl
    | t :: ts' =>
        simp only [List.map_cons, ntmList.sumSize_cons]
        rw [ntm.size_permute t π, ntmList.sumSize_permute ts' π]
end

mutual
  lemma ntm.alphaEquiv_size (Γ : Context 𝔸 X) (s t : ntm F X 𝔸)
      (h : (Γ ⊢ s ≈α t) = true) : s.size = t.size := by
    match s, t with
    | .atm _, .atm _ => rfl
    | .mvar _ _, .mvar _ _ => rfl
    | .fapp _ ss, .fapp _ ts =>
        simp only [alphaEquiv, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨_, hL⟩ := h
        simp only [ntm.size_fapp]
        congr 1
        exact ntm.alphaEquivList_sumSize Γ ss ts hL
    | .abs a s', .abs b t' =>
        simp only [alphaEquiv] at h
        by_cases hab : a = b
        · subst hab
          rw [if_pos rfl] at h
          simp only [ntm.size_abs]
          congr 1
          exact ntm.alphaEquiv_size Γ s' t' h
        · rw [if_neg hab] at h
          simp only [decide_eq_true_eq] at h
          obtain ⟨hperm, _⟩ := h
          have := ntm.alphaEquiv_size Γ (s'.permute [(b, a)]) t' hperm
          rw [ntm.size_permute] at this
          simp only [ntm.size_abs]
          exact congrArg (1 + ·) this
    | .atm _, .mvar _ _ | .atm _, .fapp _ _ | .atm _, .abs _ _
    | .mvar _ _, .atm _ | .mvar _ _, .fapp _ _ | .mvar _ _, .abs _ _
    | .fapp _ _, .atm _ | .fapp _ _, .mvar _ _ | .fapp _ _, .abs _ _
    | .abs _ _, .atm _ | .abs _ _, .mvar _ _ | .abs _ _, .fapp _ _ =>
        simp [alphaEquiv] at h

  lemma ntm.alphaEquivList_sumSize (Γ : Context 𝔸 X)
      (ss ts : List (ntm F X 𝔸)) (h : alphaEquivList Γ ss ts = true) :
      ntmList.sumSize ss = ntmList.sumSize ts := by
    match ss, ts with
    | [], []   => rfl
    | [], _ :: _ | _ :: _, [] => simp [alphaEquivList] at h
    | s :: ss', t :: ts' =>
        simp [alphaEquivList] at h
        simp only [ntmList.sumSize_cons]
        rw [ntm.alphaEquiv_size Γ s t h.1, ntm.alphaEquivList_sumSize Γ ss' ts' h.2]
end

mutual
  /-- `(.mvar [] x).subst θ` is bounded by `t.subst θ` in size when `x ∈ vars(t)`. -/
  lemma ntm.size_subst_ge_var (t : ntm F X 𝔸) (θ : Subst F X 𝔸) (x : X)
      (h : t.occursIn x = true) :
      ((ntm.mvar (F := F) [] x).subst θ).size ≤ (t.subst θ).size := by
    match t with
    | .atm _ => simp [ntm.occursIn] at h
    | .mvar π y =>
        simp only [ntm.occursIn, beq_iff_eq] at h
        subst h
        conv_rhs => rw [ntm.subst_mvar]
        rw [ntm.size_permute]
    | .fapp _ ts =>
        simp only [ntm.occursIn] at h
        simp only [ntm.subst_fapp, ntm.size_fapp]
        have := ntmList.sumSize_subst_ge_var ts θ x h
        omega
    | .abs _ t' =>
        simp only [ntm.occursIn] at h
        simp only [ntm.subst_abs, ntm.size_abs]
        have := ntm.size_subst_ge_var t' θ x h
        omega

  lemma ntmList.sumSize_subst_ge_var (ts : List (ntm F X 𝔸)) (θ : Subst F X 𝔸)
      (x : X) (h : ntmList.occursIn x ts = true) :
      ((ntm.mvar (F := F) [] x).subst θ).size ≤ ntmList.sumSize (ts.map (·.subst θ)) := by
    match ts with
    | [] => simp [ntmList.occursIn] at h
    | t :: ts' =>
        simp only [ntmList.occursIn, Bool.or_eq_true] at h
        simp only [List.map_cons, ntmList.sumSize_cons]
        cases h with
        | inl h =>
            have := ntm.size_subst_ge_var t θ x h
            have : 0 ≤ ntmList.sumSize (ts'.map (·.subst θ)) := Nat.zero_le _
            omega
        | inr h =>
            have := ntmList.sumSize_subst_ge_var ts' θ x h
            have : 0 ≤ (t.subst θ).size := Nat.zero_le _
            omega
end

lemma ntm.size_subst_gt_var_of_nonmvar (u : ntm F X 𝔸) (θ : Subst F X 𝔸) (x : X)
    (hocc : u.occursIn x = true)
    (hnon : ∀ π y, u ≠ ntm.mvar π y) :
    ((ntm.mvar (F := F) [] x).subst θ).size < (u.subst θ).size := by
  match u with
  | .atm _ => simp [ntm.occursIn] at hocc
  | .mvar π y => exact absurd rfl (hnon π y)
  | .fapp _ ts =>
      simp only [ntm.occursIn] at hocc
      simp only [ntm.subst_fapp, ntm.size_fapp]
      have := ntmList.sumSize_subst_ge_var ts θ x hocc
      omega
  | .abs _ t' =>
      simp only [ntm.occursIn] at hocc
      simp only [ntm.subst_abs, ntm.size_abs]
      have := ntm.size_subst_ge_var t' θ x hocc
      omega

mutual
  lemma simplifyFresh_none_subst_not_fresh (a : 𝔸) (t : ntm F X 𝔸)
      (h : simplifyFresh (X := X) a t = none) (Γ : Context 𝔸 X) (θ : Subst F X 𝔸) :
      (Γ ⊢ a # t.subst θ) = false := by
    match t with
    | .atm b =>
        simp only [simplifyFresh] at h
        split_ifs at h with hab
        subst hab
        simp [fresh]
    | .mvar π x =>
        simp [simplifyFresh] at h
    | .abs b t' =>
        simp only [simplifyFresh] at h
        split_ifs at h with hab
        have ih := simplifyFresh_none_subst_not_fresh a t' h Γ θ
        show (Γ ⊢ a # (ntm.abs b t').subst θ) = false
        rw [ntm.subst_abs]
        show fresh Γ a (ntm.abs b (t'.subst θ)) = false
        unfold fresh
        apply decide_eq_false
        rintro (heq | hfresh)
        · exact hab heq
        · rw [hfresh] at ih; cases ih
    | .fapp f ts =>
        simp only [simplifyFresh] at h
        have ih := simplifyFreshList_none_subst_not_freshList a ts h Γ θ
        simp only [ntm.subst_fapp, fresh]
        exact ih

  lemma simplifyFreshList_none_subst_not_freshList (a : 𝔸) (ts : List (ntm F X 𝔸))
      (h : simplifyFreshList (X := X) a ts = none) (Γ : Context 𝔸 X) (θ : Subst F X 𝔸) :
      freshList Γ a (ts.map (·.subst θ)) = false := by
    match ts with
    | [] => simp [simplifyFreshList] at h
    | t :: ts' =>
        simp only [simplifyFreshList] at h
        cases hsf : simplifyFresh a t with
        | none =>
            have := simplifyFresh_none_subst_not_fresh a t hsf Γ θ
            simp [freshList, this]
        | some cs₁ =>
            rw [hsf] at h
            cases hsfl : simplifyFreshList a ts' with
            | none =>
                have := simplifyFreshList_none_subst_not_freshList a ts' hsfl Γ θ
                simp [freshList, this]
            | some cs₂ => rw [hsfl] at h; cases h
end

private lemma alphaEquivList_length_eq {Γ : Context 𝔸 X} :
    ∀ {l1 l2 : List (ntm F X 𝔸)}, alphaEquivList Γ l1 l2 = true → l1.length = l2.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [alphaEquivList] at h
  | _ :: _, [], h => by simp [alphaEquivList] at h
  | _ :: ss, _ :: ts, h => by
      simp [alphaEquivList] at h
      exact congrArg (· + 1) (alphaEquivList_length_eq h.2)

-- Analogue of Maribel's claim that `.fail` is terminal: clash (atm/fapp) or
lemma unifStep_fail_no_solution
    (c : UnifConstraint F X 𝔸) (rest : UnifProblem F X 𝔸) (σ : Subst F X 𝔸)
    (h : unifStep c rest σ = .fail) :
    ¬ ∃ (Δ : Context 𝔸 X) (θ : Subst F X 𝔸),
        Solution.Satisfies Δ θ (c :: rest) := by
  rintro ⟨Δ, θ, hsat⟩
  have hc := entails_head_of_satisfies c rest Δ θ hsat
  cases c with
  | fresh a t =>
    cases t with
    | mvar π x =>
      simp [unifStep] at h
    | atm b =>
      by_cases hab : a = b
      · subst hab
        simp [UnifConstraint.applySubst, UnifConstraint.toConstraint, Constraint.Entails,
              fresh] at hc
      · simp [unifStep, simplifyFresh, hab] at h
    | abs b t' =>
      cases hsf : simplifyFresh a (ntm.abs (F := F) (X := X) b t') with
      | none =>
        have hno := simplifyFresh_none_subst_not_fresh a (ntm.abs b t') hsf Δ θ
        simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                   Constraint.Entails] at hc
        rw [hno] at hc; cases hc
      | some cs =>
        simp [unifStep, hsf] at h
    | fapp f ts =>
      cases hsf : simplifyFresh a (ntm.fapp (X := X) (𝔸 := 𝔸) f ts) with
      | none =>
        have hno := simplifyFresh_none_subst_not_fresh a (ntm.fapp f ts) hsf Δ θ
        simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                   Constraint.Entails] at hc
        rw [hno] at hc; cases hc
      | some cs =>
        simp [unifStep, hsf] at h
  | unif s t =>
    cases s with
    | atm a =>
      cases t with
      | atm b =>
        by_cases hab : a = b
        · simp [unifStep, hab] at h
        · simp [UnifConstraint.applySubst, UnifConstraint.toConstraint, Constraint.Entails,
                alphaEquiv, hab] at hc
      | mvar π x =>
        simp [unifStep, ntm.occursIn] at h
      | fapp _ _ =>
        simp [UnifConstraint.applySubst, UnifConstraint.toConstraint, Constraint.Entails,
              alphaEquiv] at hc
      | abs _ _ =>
        simp [UnifConstraint.applySubst, UnifConstraint.toConstraint, Constraint.Entails,
              alphaEquiv] at hc
    | mvar π x =>
      cases t with
      | atm _ =>
        simp [unifStep, ntm.occursIn] at h
      | mvar π' y =>
        by_cases hxy : x = y
        · simp [unifStep, hxy] at h
        · simp [unifStep, hxy] at h
      | fapp f ts =>
        have hocc : (ntm.fapp (X := X) (𝔸 := 𝔸) f ts).occursIn x = true := by
          by_contra hne
          have hne' : (ntm.fapp (X := X) (𝔸 := 𝔸) f ts).occursIn x = false :=
            Bool.eq_false_iff.mpr hne
          simp [unifStep, hne'] at h
        simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                   Constraint.Entails] at hc
        have hsize := ntm.alphaEquiv_size _ _ _ hc
        have hgt := ntm.size_subst_gt_var_of_nonmvar
          (ntm.fapp (X := X) (𝔸 := 𝔸) f ts) θ x hocc (by intro _ _ heq; cases heq)
        rw [ntm.subst_mvar, ntm.size_permute] at hsize
        omega
      | abs b t' =>
        have hocc : (ntm.abs (F := F) (X := X) b t').occursIn x = true := by
          by_contra hne
          have hne' : (ntm.abs (F := F) (X := X) b t').occursIn x = false :=
            Bool.eq_false_iff.mpr hne
          simp [unifStep, hne'] at h
        simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                   Constraint.Entails] at hc
        have hsize := ntm.alphaEquiv_size _ _ _ hc
        have hgt := ntm.size_subst_gt_var_of_nonmvar
          (ntm.abs (F := F) (X := X) b t') θ x hocc (by intro _ _ heq; cases heq)
        rw [ntm.subst_mvar, ntm.size_permute] at hsize
        omega
    | fapp f ss =>
      cases t with
      | atm _ =>
        simp [UnifConstraint.applySubst, UnifConstraint.toConstraint, Constraint.Entails,
              alphaEquiv] at hc
      | mvar π x =>
        have hocc : (ntm.fapp (X := X) (𝔸 := 𝔸) f ss).occursIn x = true := by
          by_contra hne
          have hne' : (ntm.fapp (X := X) (𝔸 := 𝔸) f ss).occursIn x = false :=
            Bool.eq_false_iff.mpr hne
          simp [unifStep, hne'] at h
        simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                   Constraint.Entails] at hc
        have hsize := ntm.alphaEquiv_size _ _ _ hc
        have hgt := ntm.size_subst_gt_var_of_nonmvar
          (ntm.fapp (X := X) (𝔸 := 𝔸) f ss) θ x hocc (by intro _ _ heq; cases heq)
        rw [ntm.subst_mvar (π := π) (y := x), ntm.size_permute] at hsize
        omega
      | fapp g ts =>
        by_cases hfg : f = g ∧ ss.length = ts.length
        · simp [unifStep, hfg] at h
        · -- f ≠ g or |ss| ≠ |ts|.
          simp [UnifConstraint.applySubst, UnifConstraint.toConstraint, Constraint.Entails,
                alphaEquiv] at hc
          obtain ⟨hfeq, halist⟩ := hc
          subst hfeq
          have hlen := alphaEquivList_length_eq halist
          simp at hlen
          exact hfg ⟨rfl, hlen⟩
      | abs _ _ =>
        simp [UnifConstraint.applySubst, UnifConstraint.toConstraint, Constraint.Entails,
              alphaEquiv] at hc
    | abs a s' =>
      cases t with
      | atm _ =>
        simp [UnifConstraint.applySubst, UnifConstraint.toConstraint, Constraint.Entails,
              alphaEquiv] at hc
      | mvar π x =>
        have hocc : (ntm.abs (F := F) (X := X) a s').occursIn x = true := by
          by_contra hne
          have hne' : (ntm.abs (F := F) (X := X) a s').occursIn x = false :=
            Bool.eq_false_iff.mpr hne
          simp [unifStep, hne'] at h
        simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                   Constraint.Entails] at hc
        have hsize := ntm.alphaEquiv_size _ _ _ hc
        have hgt := ntm.size_subst_gt_var_of_nonmvar
          (ntm.abs (F := F) (X := X) a s') θ x hocc (by intro _ _ heq; cases heq)
        rw [ntm.subst_mvar (π := π) (y := x), ntm.size_permute] at hsize
        omega
      | fapp _ _ =>
        simp [UnifConstraint.applySubst, UnifConstraint.toConstraint, Constraint.Entails,
              alphaEquiv] at hc
      | abs b t' =>
        by_cases hab : a = b
        · simp [unifStep, hab] at h
        · simp [unifStep, hab] at h

lemma unify_le :
    ∀ (Pr : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) (ds : List (𝔸 × X))
      (ds' : List (𝔸 × X)) (σ' : Subst F X 𝔸)
      (Δ : Context 𝔸 X) (θ : Subst F X 𝔸),
      unify Pr σ ds = some (ds', σ') →
      Solution.Satisfies Δ θ Pr →
      Subst.absorbedBy Δ σ θ →
      (∀ p ∈ ds, (Δ ⊢ p.1 # (ntm.mvar (F := F) [] p.2).subst θ) = true) →
      Subst.absorbedBy Δ σ' θ ∧
      (∀ p ∈ ds', (Δ ⊢ p.1 # (ntm.mvar (F := F) [] p.2).subst θ) = true) := by
  intro Pr σ ds
  induction Pr, σ, ds using unify.induct with
  | case1 σ ds =>
    intro ds' σ' Δ θ h hθ habs hds
    simp only [unify, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hdseq, hσeq⟩ := h
    subst hdseq; subst hσeq
    exact ⟨habs, hds⟩
  | case2 σ ds c rest hfail =>
    intro ds' σ' Δ θ h _ _ _
    rw [unify, hfail] at h
    cases h
  | case3 σ ds c rest a x hctx ih =>
    intro ds' σ' Δ θ h hθ habs hds
    rw [unify, hctx] at h
    obtain ⟨hθrest, hfresh⟩ := unifStep_ctx_le c rest σ a x Δ θ hctx hθ
    have hds_new : ∀ p ∈ (a, x) :: ds,
        (Δ ⊢ p.1 # (ntm.mvar (F := F) [] p.2).subst θ) = true := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact hfresh
      · exact hds p hp'
    exact ih ds' σ' Δ θ h hθrest habs hds_new
  | case4 σ ds c rest Pr' σ_next hnext ih =>
    intro ds' σ' Δ θ h hθ habs hds
    rw [unify, hnext] at h
    obtain ⟨hθPr', habs_next⟩ :=
      unifStep_next_le c rest σ σ_next Pr' Δ θ hnext hθ habs
    exact ih ds' σ' Δ θ h hθPr' habs_next hds

/-- If `unify` fails, `Pr` has no solution. Absorption is threaded so the
    recursion can carry `unifStep_fail_no_solution` back through each step. -/
lemma unify_none_no_solution :
    ∀ (Pr : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) (ds : List (𝔸 × X)),
      unify Pr σ ds = none →
      ∀ (Δ : Context 𝔸 X) (θ : Subst F X 𝔸),
        Subst.absorbedBy Δ σ θ → ¬ Solution.Satisfies Δ θ Pr := by
  intro Pr σ ds
  induction Pr, σ, ds using unify.induct with
  | case1 σ ds =>
      intro h; rw [unify] at h; simp at h
  | case2 σ ds c rest hfail =>
      intro _ Δ θ _ hsat
      exact unifStep_fail_no_solution c rest σ hfail ⟨Δ, θ, hsat⟩
  | case3 σ ds c rest a x hctx ih =>
      intro h Δ θ habs hsat
      rw [unify, hctx] at h
      obtain ⟨hΓ, hidem⟩ := hsat
      refine ih h Δ θ habs ⟨?_, hidem⟩
      intro c' hc'
      apply hΓ c'
      rw [UnifProblem.applySubst_cons, UnifProblem.toConstraint_cons]
      exact List.mem_cons_of_mem _ hc'
  | case4 σ ds c rest Pr' σ_next hnext ih =>
      intro h Δ θ habs hsat
      rw [unify, hnext] at h
      obtain ⟨hsat', habs'⟩ := unifStep_next_le c rest σ σ_next Pr' Δ θ hnext hsat habs
      exact ih h Δ θ habs' hsat'

-- This step has no direct Isabelle counterpart.
lemma finalizeDeferred_le :
    ∀ (deferred : List (𝔸 × X)) (σ : Subst F X 𝔸)
      (Γ_init Γ : Context 𝔸 X) (Δ : Context 𝔸 X) (θ : Subst F X 𝔸),
      finalizeDeferred deferred σ Γ_init = some Γ →
      Subst.absorbedBy Δ σ θ →
      (∀ p ∈ deferred, (Δ ⊢ p.1 # (ntm.mvar (F := F) [] p.2).subst θ) = true) →
      Γ_init.EntailsUnder Δ θ = true →
      Γ.EntailsUnder Δ θ = true
  | [], _, Γ_init, Γ, _, _, h, _, _, hinit => by
      simp only [finalizeDeferred, Option.some.injEq] at h
      subst h; exact hinit
  | (a, x) :: tl, σ, Γ_init, Γ, Δ, θ, h, habs, hdef, hinit => by
      simp only [finalizeDeferred] at h
      cases hsf : simplifyFresh a ((ntm.mvar (F := F) [] x).subst σ) with
      | none => rw [hsf] at h; cases h
      | some cs =>
        rw [hsf] at h
        have hfresh_θ : (Δ ⊢ a # ((ntm.mvar (F := F) [] x).subst σ).subst θ) = true := by
          have h_a_in : (a, x) ∈ (a, x) :: tl := List.mem_cons_self
          have hfresh_θ_x := hdef (a, x) h_a_in
          have habs_x := habs x
          exact freshPreserves_alphaEquiv Δ a ((ntm.mvar (F := F) [] x).subst θ)
            (((ntm.mvar (F := F) [] x).subst σ).subst θ)
            hfresh_θ_x (alphaEquiv_symm Δ _ _ habs_x)
        have hcs := simplifyFresh_subst_imp_entails Δ a θ
          ((ntm.mvar (F := F) [] x).subst σ) cs hsf hfresh_θ
        set Γ_init' : Context 𝔸 X := cs.foldl ctxStep Γ_init with hΓ_init'_def
        have hinit' : Γ_init'.EntailsUnder Δ θ = true := by
          simp only [Context.EntailsUnder, decide_eq_true_eq]
          intro p hp
          have hfold_prop : ∀ (cs_pre : Problem F X 𝔸) (Γ₀ : Context 𝔸 X),
              (∀ q ∈ Γ₀, (Δ ⊢ q.1 # (ntm.mvar (F := F) [] q.2).subst θ) = true) →
              (∀ c' ∈ cs_pre, Constraint.Entails Δ (c'.applySubst θ) = true) →
              ∀ q ∈ cs_pre.foldl ctxStep Γ₀,
                (Δ ⊢ q.1 # (ntm.mvar (F := F) [] q.2).subst θ) = true := by
            intro cs_pre
            induction cs_pre with
            | nil => intro Γ₀ hΓ₀ _ q hq; exact hΓ₀ q hq
            | cons c0 cs_rest ih =>
              intro Γ₀ hΓ₀ hentails q hq
              simp only [List.foldl] at hq
              apply ih _ ?_ ?_ q hq
              · -- New Γ₀ after one foldl step.
                cases c0 with
                | fresh a' t' =>
                  cases t' with
                  | mvar π x' =>
                    cases π with
                    | nil =>
                      intro q' hq'
                      rcases Finset.mem_insert.mp hq' with rfl | hq''
                      · -- q' = (a', x').  Use hentails on c0 = .fresh a' (.mvar [] x').
                        have := hentails (Constraint.fresh a' (ntm.mvar [] x'))
                          List.mem_cons_self
                        simpa [Constraint.applySubst, Constraint.Entails] using this
                      · exact hΓ₀ q' hq''
                    | cons _ _ => intro q' hq'; exact hΓ₀ q' hq'
                  | atm _   => intro q' hq'; exact hΓ₀ q' hq'
                  | fapp _ _ => intro q' hq'; exact hΓ₀ q' hq'
                  | abs _ _ => intro q' hq'; exact hΓ₀ q' hq'
                | alpha _ _ => intro q' hq'; exact hΓ₀ q' hq'
              · -- entailment hyp for rest.
                intro c' hc'
                exact hentails c' (List.mem_cons_of_mem _ hc')
          have hΓ_init_prop : ∀ q ∈ Γ_init, (Δ ⊢ q.1 # (ntm.mvar (F := F) [] q.2).subst θ) = true := by
            have hinit_decide := hinit
            simp only [Context.EntailsUnder, decide_eq_true_eq] at hinit_decide
            exact hinit_decide
          have hcs_prop : ∀ c' ∈ cs, Constraint.Entails Δ (c'.applySubst θ) = true := by
            intro c' hc'
            apply hcs (c'.applySubst θ)
            simp only [Problem.applySubst, List.mem_map]
            exact ⟨c', hc', rfl⟩
          exact hfold_prop cs Γ_init hΓ_init_prop hcs_prop p hp
        have hdef_tl : ∀ p ∈ tl, (Δ ⊢ p.1 # (ntm.mvar (F := F) [] p.2).subst θ) = true := by
          intro p hp; exact hdef p (List.mem_cons_of_mem _ hp)
        exact finalizeDeferred_le tl σ Γ_init' Γ Δ θ h habs hdef_tl hinit'

/-- If `finalizeDeferred` fails, no absorbing `θ` satisfies every deferred leaf:
    the failing leaf is rigidly non-fresh under `σθ`, contradicting absorption. -/
lemma finalizeDeferred_none_no_solution :
    ∀ (ds : List (𝔸 × X)) (σ : Subst F X 𝔸) (Γ_init : Context 𝔸 X),
      finalizeDeferred ds σ Γ_init = none →
      ∀ (Δ : Context 𝔸 X) (θ : Subst F X 𝔸),
        Subst.absorbedBy Δ σ θ →
        ¬ (∀ p ∈ ds, (Δ ⊢ p.1 # (ntm.mvar (F := F) [] p.2).subst θ) = true)
  | [], σ, Γ_init, h, Δ, θ, _, _ => by
      simp [finalizeDeferred] at h
  | (a, x) :: tl, σ, Γ_init, h, Δ, θ, habs, hdef => by
      simp only [finalizeDeferred] at h
      cases hsf : simplifyFresh a ((ntm.mvar (F := F) [] x).subst σ) with
      | none =>
          have hfresh_leaf := hdef (a, x) List.mem_cons_self
          have hfresh_σ : (Δ ⊢ a # ((ntm.mvar (F := F) [] x).subst σ).subst θ) = true :=
            freshPreserves_alphaEquiv Δ a ((ntm.mvar (F := F) [] x).subst θ)
              (((ntm.mvar (F := F) [] x).subst σ).subst θ)
              hfresh_leaf (alphaEquiv_symm Δ _ _ (habs x))
          have hnot := simplifyFresh_none_subst_not_fresh a
            ((ntm.mvar (F := F) [] x).subst σ) hsf Δ θ
          rw [hfresh_σ] at hnot
          simp at hnot
      | some cs =>
          rw [hsf] at h
          exact finalizeDeferred_none_no_solution tl σ _ h Δ θ habs
            (fun p hp => hdef p (List.mem_cons_of_mem _ hp))

-- Final theorem — Maribel Theorem 35.
theorem UnifProblem.solve_principal
    (Pr : UnifProblem F X 𝔸) (Γ : Context 𝔸 X) (σ : Subst F X 𝔸)
    (h : Pr.solve = some (Γ, σ)) :
    Pr.IsPrincipalSolution (Γ, σ) := by
  refine ⟨?membership, ?generality⟩
  case membership =>
    exact UnifProblem.solve_satisfies Pr Γ σ h
  case generality =>
    intro q hq
    obtain ⟨Δ, θ⟩ := q
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
        subst hΓeq; subst hσeq
        have habs0 : Subst.absorbedBy Δ ([] : Subst F X 𝔸) θ :=
          Subst.absorbedBy_nil Δ θ
        have hds0 : ∀ p ∈ ([] : List (𝔸 × X)),
            (Δ ⊢ p.1 # (ntm.mvar (F := F) [] p.2).subst θ) = true := by
          intros _ h; cases h
        obtain ⟨habs_u, hds_u⟩ :=
          unify_le Pr [] [] ds σ_u Δ θ hu hq habs0 hds0
        have hinit_empty : (∅ : Context 𝔸 X).EntailsUnder Δ θ = true := by
          simp [Context.EntailsUnder]
        have hΓ_under := finalizeDeferred_le ds σ_u ∅ Γ_fin Δ θ hf habs_u hds_u hinit_empty
        refine ⟨θ, ?_, ?_⟩
        · -- ∀ x, Δ ⊢ ((mvar [] x).subst σ).subst θ ≈α (mvar [] x).subst θ.
          exact habs_u
        · -- Γ.EntailsUnder Δ θ.
          exact hΓ_under

/-- Existence half of completeness: `solve = none` ⟹ no solution, failing in
    `unify` or in `finalizeDeferred`. Contrapositive: a solvable problem makes
    `solve` succeed. -/
theorem UnifProblem.solve_none_no_solution (Pr : UnifProblem F X 𝔸)
    (h : Pr.solve = none) : Pr.Solutions = ∅ := by
  ext ⟨Δ, θ⟩
  simp only [UnifProblem.Solutions, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hsat
  simp only [UnifProblem.solve] at h
  cases hu : unify Pr [] [] with
  | none =>
      exact unify_none_no_solution Pr [] [] hu Δ θ (Subst.absorbedBy_nil Δ θ) hsat
  | some result =>
      obtain ⟨ds, σ_u⟩ := result
      rw [hu] at h
      simp only at h
      cases hf : finalizeDeferred ds σ_u ∅ with
      | none =>
          have habs0 : Subst.absorbedBy Δ ([] : Subst F X 𝔸) θ := Subst.absorbedBy_nil Δ θ
          have hds0 : ∀ p ∈ ([] : List (𝔸 × X)),
              (Δ ⊢ p.1 # (ntm.mvar (F := F) [] p.2).subst θ) = true := by
            intro _ hp; cases hp
          obtain ⟨habs_u, hds_u⟩ := unify_le Pr [] [] ds σ_u Δ θ hu hsat habs0 hds0
          exact finalizeDeferred_none_no_solution ds σ_u ∅ hf Δ θ habs_u hds_u
      | some Γ_fin =>
          rw [hf] at h; simp at h

/-- `solve` fails exactly when the problem is unsolvable. The forward direction
    is `solve_none_no_solution`; the converse is soundness (`solve_satisfies`),
    since a successful run exhibits a solution. -/
theorem UnifProblem.solve_none_iff_no_solution (Pr : UnifProblem F X 𝔸) :
    Pr.solve = none ↔ Pr.Solutions = ∅ := by
  constructor
  · exact UnifProblem.solve_none_no_solution Pr
  · intro hempty
    by_contra hne
    obtain ⟨⟨Γ, σ⟩, hsome⟩ := Option.ne_none_iff_exists'.mp hne
    have hmem : (Γ, σ) ∈ Pr.Solutions := UnifProblem.solve_satisfies Pr Γ σ hsome
    rw [hempty] at hmem
    simp at hmem

end Nominal
