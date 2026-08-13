import Nominal.Syntax.Unification.Properties

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

-- Completeness of the nominal unification algorithm.
-- Goal: `UnifProblem.solve_principal` — Maribel Theorem 35.
-- The result produced by `solve` is the most general unifier (mgu) in the
-- sense of `UnifProblem.IsPrincipalSolution` (Definition 30).
--
-- This file establishes the *converse* of soundness: every solution of `Pr`
-- factors through `(Γ, σ)` returned by `solve`.  Roadmap mirrors the Isabelle
-- formalisation (`P1-from-P2-sred/cred` + `mgu` lemma), adapted to our
-- recursive `unify` + `finalizeDeferred` (Plan A) architecture.

-- The accumulated substitution σ is consistent with θ modulo Δ.
-- This is the inductive invariant we carry through `unify_le`.  Initially
-- (σ = []) it is trivially true; each `unifStep_next_le` step preserves it.
def Subst.absorbedBy (Δ : Context 𝔸 X) (σ θ : Subst F X 𝔸) : Prop :=
  ∀ x : X, (Δ ⊢ ((ntm.mvar (F := F) [] x).subst σ).subst θ ≈α
               (ntm.mvar (F := F) [] x).subst θ) = true

@[simp] lemma Subst.absorbedBy_nil (Δ : Context 𝔸 X) (θ : Subst F X 𝔸) :
    Subst.absorbedBy Δ ([] : Subst F X 𝔸) θ := by
  intro x
  simp only [ntm.subst_nil]
  exact alphaEquiv_refl _ _

-- Congruence: if `u.subst θ` is α-equivalent to `(.mvar [] x).subst θ` in Δ,
-- then for any term `t`, applying `[(x, u)]` before `θ` gives an α-equivalent
-- result to applying `θ` directly.  This is the key lemma for proving that
-- `θ` "absorbs" an instantiation binding consistent with it.
mutual
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

-- Variant of `ntm.alphaEquiv_permute_reverse_permute_self` for the opposite
-- order: applying `π` then `π.reverse` is α-equivalent to identity.
lemma ntm.alphaEquiv_permute_permute_reverse_self (Γ : Context 𝔸 X)
    (t : ntm F X 𝔸) (π : LPerm 𝔸) :
    (Γ ⊢ (t.permute π).permute π.reverse ≈α t) = true := by
  have := ntm.alphaEquiv_permute_reverse_permute_self Γ t π.reverse
  rw [List.reverse_reverse] at this
  exact this

-- From an α-equivalence between `(.mvar π x).subst θ` and `u.subst θ` in Δ,
-- derive consistency `(u.permute π.reverse).subst θ ≈α (.mvar [] x).subst θ`
-- in Δ.  This is the precondition needed for `Subst.absorbedBy_append` in
-- the instantiation cases (arms 3 and 4 of `unifStep`).
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

-- absorbedBy extension by a consistent binding.
lemma Subst.absorbedBy_append (Δ : Context 𝔸 X) (σ θ : Subst F X 𝔸)
    (x : X) (u_perm : ntm F X 𝔸)
    (habs : Subst.absorbedBy Δ σ θ)
    (hu : (Δ ⊢ u_perm.subst θ ≈α (ntm.mvar (F := F) [] x).subst θ) = true) :
    Subst.absorbedBy Δ (σ ++ [(x, u_perm)]) θ := by
  intro y
  rw [ntm.subst_append]
  -- ((mvar [] y).subst σ).subst [(x, u_perm)] = ((mvar [] y).subst σ).applyOne x u_perm.
  simp only [ntm.subst_cons, ntm.subst_nil]
  -- Goal: Δ ⊢ (((mvar [] y).subst σ).applyOne x u_perm).subst θ ≈α (mvar [] y).subst θ.
  -- Use congruence to swap to (((mvar [] y).subst σ).subst θ), then habs.
  have hcong := alphaEquiv_applyOne_subst Δ θ x u_perm hu
      ((ntm.mvar (F := F) [] y).subst σ)
  exact alphaEquiv_trans Δ _ _ _ hcong (habs y)

-- Constraint-level congruence: under consistency `u.subst θ ≈α θ(x)` in Δ,
-- the binding `[(x, u)]` is invisible at the entailment level.
lemma UnifConstraint.entails_applyOne_of_entails
    (Δ : Context 𝔸 X) (θ : Subst F X 𝔸) (x : X) (u : ntm F X 𝔸)
    (hu : (Δ ⊢ u.subst θ ≈α (ntm.mvar (F := F) [] x).subst θ) = true)
    (c : UnifConstraint F X 𝔸)
    (h : Constraint.Entails Δ (c.applySubst θ).toConstraint = true) :
    Constraint.Entails Δ ((c.applySubst [(x, u)]).applySubst θ).toConstraint = true := by
  cases c with
  | fresh a t =>
    simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint,
               Constraint.Entails, ntm.subst_cons, ntm.subst_nil] at *
    have hcong := alphaEquiv_applyOne_subst Δ θ x u hu t
    exact freshPreserves_alphaEquiv Δ a (t.subst θ) ((t.applyOne x u).subst θ) h
      (alphaEquiv_symm Δ _ _ hcong)
  | unif s t =>
    simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint,
               Constraint.Entails, ntm.subst_cons, ntm.subst_nil] at *
    have hcongS := alphaEquiv_applyOne_subst Δ θ x u hu s
    have hcongT := alphaEquiv_applyOne_subst Δ θ x u hu t
    -- h : alphaEquiv Δ (s.subst θ) (t.subst θ).
    -- Want: alphaEquiv Δ ((s.applyOne x u).subst θ) ((t.applyOne x u).subst θ).
    exact alphaEquiv_trans Δ _ _ _
      (alphaEquiv_trans Δ _ _ _ hcongS h) (alphaEquiv_symm Δ _ _ hcongT)

-- Lift to UnifProblem.
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

-- Reverse of `fresh_subst_of_simplifyFresh_entails` from Properties.
-- If `simplifyFresh a t = some cs` and `Γ ⊢ a # t.subst τ`, then every
-- constraint in `cs.applySubst τ` is entailed by Γ.  Used in fresh-abs and
-- fresh-fapp completeness cases.
mutual
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
        · -- a ≠ b. cs = simplifyFresh a t'.
          -- Decompose hf: fresh Γ a (.abs b (t'.subst τ)) = (a = b ∨ fresh Γ a t'.subst τ).
          have hft : (Γ ⊢ a # t'.subst τ) = true := by
            simp only [ntm.subst_abs, fresh] at hf
            -- hf : decide (a = b ∨ (Γ ⊢ a # t'.subst τ) = true) = true.
            rw [decide_eq_true_eq] at hf
            rcases hf with rfl | h
            · exact absurd rfl hab
            · exact h
          exact simplifyFresh_subst_imp_entails Γ a τ t' cs hs hft
    | .fapp f ts, cs, hs, hf => by
        simp only [simplifyFresh] at hs
        -- cs = simplifyFreshList a ts.
        -- hf : Γ ⊢ a # (.fapp f ts).subst τ = freshList Γ a (ts.map (·.subst τ)).
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
            -- Need: Problem.Entails Γ ((cs₁ ++ cs₂).applySubst τ).
            intro c' hc'
            simp only [Problem.applySubst, List.map_append, List.mem_append] at hc'
            rcases hc' with hc'' | hc''
            · exact ih1 c' hc''
            · exact ih2 c' hc''
end

-- Helper (reverse of `alphaEquivList_of_zip_subst_entails` from Properties).
-- Used in the fapp-fapp completeness case.
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

-- Helper: from a satisfied (c :: rest), extract that c is entailed (after applySubst).
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

-- (4a) Step-level converse for the recursive case `.next Pr' σ_next`.
-- Analogue of Isabelle's `P1-from-P2-sred`: a solution of `c::rest` carries
-- over to `Pr'` (under the same θ), and σ_next remains absorbed by θ.
-- The factorization `θ ≈_Δ σ_next ; ρ` of `SolutionLe` is recovered globally
-- via the `Subst.absorbedBy` invariant with ρ = θ throughout.
lemma unifStep_next_le
    (c : UnifConstraint F X 𝔸) (rest : UnifProblem F X 𝔸)
    (σ σ_next : Subst F X 𝔸) (Pr' : UnifProblem F X 𝔸)
    (Δ : Context 𝔸 X) (θ : Subst F X 𝔸)
    (h : unifStep c rest σ = .next Pr' σ_next)
    (hθ : Solution.Satisfies Δ θ (c :: rest))
    (habs : Subst.absorbedBy Δ σ θ) :
    Solution.Satisfies Δ θ Pr' ∧ Subst.absorbedBy Δ σ_next θ := by
  obtain ⟨hΓ, hidem⟩ := hθ
  -- Helper: c entailment for use in instantiation cases.
  have hc : Constraint.Entails Δ (c.applySubst θ).toConstraint = true :=
    entails_head_of_satisfies c rest Δ θ ⟨hΓ, hidem⟩
  -- Helper: rest entailment (used in non-instantiation cases).
  have hrest : Problem.Entails Δ (rest.applySubst θ).toConstraint := by
    intro c' hc'
    apply hΓ c'
    rw [UnifProblem.applySubst_cons, UnifProblem.toConstraint_cons]
    exact List.mem_cons_of_mem _ hc'
  cases c with
  | fresh a t =>
    cases t with
    | mvar π x =>
      -- unifStep returns .ctx — contradicts h.
      simp [unifStep] at h
    | atm b =>
      -- a = b ⇒ simplifyFresh = none ⇒ .fail (contradicts h).
      -- a ≠ b ⇒ simplifyFresh = some [] ⇒ .next rest σ.
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
          -- c'' ∈ cs.  Goal: ((c''.toUnif).applySubst θ).toConstraint entailed.
          -- Reduce via toConstraint_applySubst + toConstraint of toUnif = id.
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
        -- atm-mvar: instantiation with u = .atm a, u_perm = .atm (π.reverse·a).
        have heq : unifStep (UnifConstraint.unif (X := X) (ntm.atm a) (ntm.mvar π x)) rest σ
            = .next (rest.applySubst [(x, (ntm.atm (F := F) a).permute π.reverse)])
                    (σ ++ [(x, (ntm.atm (F := F) a).permute π.reverse)]) := by
          simp [unifStep, ntm.occursIn]
        rw [heq] at h; injection h with hPr hσ
        subst hPr; subst hσ
        -- u_perm = .atm (π.reverse·a). Establish consistency hu.
        set u_perm : ntm F X 𝔸 := ntm.atm (LPermApply π.reverse a) with hu_perm_def
        have hu : (Δ ⊢ u_perm.subst θ ≈α (ntm.mvar (F := F) [] x).subst θ) = true := by
          -- u_perm.subst θ = u_perm (atom is fixed).
          have hu_subst : u_perm.subst θ = u_perm := by simp [u_perm]
          rw [hu_subst]
          -- From hc: Δ ⊢ .atm a ≈α (mvar π x).subst θ.
          have hc_simpl : (Δ ⊢ ntm.atm (F := F) (X := X) a ≈α
                              (ntm.mvar (F := F) π x).subst θ) = true := by
            simpa [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                   Constraint.Entails] using hc
          rw [ntm.subst_mvar] at hc_simpl
          -- Apply permute π.reverse to both sides.
          have hperm := alphaEquiv_permute_congr Δ _ _ π.reverse hc_simpl
          -- LHS: (.atm a).permute π.reverse = .atm (π.reverse·a) = u_perm.
          -- RHS: ((mvar [] x).subst θ .permute π).permute π.reverse ≈α (mvar [] x).subst θ.
          have hatm_perm : (ntm.atm (F := F) (X := X) a).permute π.reverse = u_perm := by
            simp [ntm.permute, u_perm]
          rw [hatm_perm] at hperm
          have hself := ntm.alphaEquiv_permute_permute_reverse_self Δ
            ((ntm.mvar (F := F) [] x).subst θ) π
          exact alphaEquiv_trans Δ _ _ _ hperm hself
        -- Goal still uses the raw permute form; convert via hu_perm_def.
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
        -- mvar-atm: instantiation, arm 3 with u = .atm a.
        have heq : unifStep (UnifConstraint.unif (X := X) (ntm.mvar π x) (ntm.atm a)) rest σ
            = .next (rest.applySubst [(x, (ntm.atm (F := F) a).permute π.reverse)])
                    (σ ++ [(x, (ntm.atm (F := F) a).permute π.reverse)]) := by
          simp [unifStep, ntm.occursIn]
        rw [heq] at h; injection h with hPr hσ
        subst hPr; subst hσ
        set u_perm : ntm F X 𝔸 := ntm.atm (LPermApply π.reverse a) with hu_perm_def
        have hu : (Δ ⊢ u_perm.subst θ ≈α (ntm.mvar (F := F) [] x).subst θ) = true := by
          have hu_subst : u_perm.subst θ = u_perm := by simp [u_perm]
          rw [hu_subst]
          -- hc: Δ ⊢ (mvar π x).subst θ ≈α .atm a.  Symm + same as atm-mvar.
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
          -- Extract α-equivalence from hc, convert to fresh constraints via invariance_mpr.
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
          -- c' ∈ ((rest ++ dsList.map ...).applySubst θ).toConstraint.
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
                      (σ ++ [(x, (ntm.mvar (F := F) π' y).permute π.reverse)]) := by
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
        -- mvar-fapp: arm 3 instantiation if occursIn = false.
        by_cases hocc : (ntm.fapp (X := X) (𝔸 := 𝔸) f ts).occursIn x
        · simp [unifStep, hocc] at h
        · have hocc_false : (ntm.fapp (X := X) (𝔸 := 𝔸) f ts).occursIn x = false :=
            Bool.eq_false_iff.mpr hocc
          have heq : unifStep (UnifConstraint.unif (X := X) (ntm.mvar π x)
                                (ntm.fapp f ts)) rest σ
              = .next (rest.applySubst [(x, (ntm.fapp (X := X) f ts).permute π.reverse)])
                      (σ ++ [(x, (ntm.fapp (X := X) f ts).permute π.reverse)]) := by
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
        -- mvar-abs: arm 3 instantiation.
        by_cases hocc : (ntm.abs (F := F) (X := X) b t').occursIn x
        · simp [unifStep, hocc] at h
        · have hocc_false : (ntm.abs (F := F) (X := X) b t').occursIn x = false :=
            Bool.eq_false_iff.mpr hocc
          have heq : unifStep (UnifConstraint.unif (X := X) (ntm.mvar π x)
                                (ntm.abs b t')) rest σ
              = .next (rest.applySubst [(x, (ntm.abs (F := F) b t').permute π.reverse)])
                      (σ ++ [(x, (ntm.abs (F := F) b t').permute π.reverse)]) := by
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
        -- fapp-mvar: arm 4 instantiation if occursIn = false.
        by_cases hocc : (ntm.fapp (X := X) (𝔸 := 𝔸) f ss).occursIn x
        · simp [unifStep, hocc] at h
        · have hocc_false : (ntm.fapp (X := X) (𝔸 := 𝔸) f ss).occursIn x = false :=
            Bool.eq_false_iff.mpr hocc
          have heq : unifStep (UnifConstraint.unif (X := X) (ntm.fapp f ss)
                                (ntm.mvar π x)) rest σ
              = .next (rest.applySubst [(x, (ntm.fapp (X := X) f ss).permute π.reverse)])
                      (σ ++ [(x, (ntm.fapp (X := X) f ss).permute π.reverse)]) := by
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
          -- Extract alphaEquivList from hc.
          simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                     Constraint.Entails, ntm.subst_fapp, alphaEquiv,
                     decide_eq_true_eq] at hc
          obtain ⟨_, halist⟩ := hc
          -- Entailment for zip-mapped constraints + rest.
          intro c' hc'
          simp only [UnifProblem.applySubst, UnifProblem.toConstraint, List.map_append,
                     List.mem_append] at hc'
          rcases hc' with hc''_zip | hc''_rest
          · -- zip-mapped: use alphaEquivList_imp_zip_entails.
            have hzip := alphaEquivList_imp_zip_entails ss ts hlen halist
            -- Rewrite c''_zip's shape to apply hzip.
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
        -- abs-mvar: arm 4 instantiation.
        by_cases hocc : (ntm.abs (F := F) (X := X) a s').occursIn x
        · simp [unifStep, hocc] at h
        · have hocc_false : (ntm.abs (F := F) (X := X) a s').occursIn x = false :=
            Bool.eq_false_iff.mpr hocc
          have heq : unifStep (UnifConstraint.unif (X := X) (ntm.abs a s')
                                (ntm.mvar π x)) rest σ
              = .next (rest.applySubst [(x, (ntm.abs (F := F) a s').permute π.reverse)])
                      (σ ++ [(x, (ntm.abs (F := F) a s').permute π.reverse)]) := by
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
          -- head: from hc (alphaEquiv abs-abs same reduces to children).
          -- tail: from hrest.
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
          -- Pr' = .unif (s'.permute [(b, a)]) t' :: .fresh b s' :: rest.
          have heq : unifStep (UnifConstraint.unif (X := X) (ntm.abs a s') (ntm.abs b t')) rest σ
              = .next (UnifConstraint.unif (s'.permute [(b, a)]) t'
                       :: UnifConstraint.fresh b s' :: rest) σ := by
            simp [unifStep, hab]
          rw [heq] at h; injection h with hPr hσ
          subst hPr; subst hσ
          refine ⟨⟨?_, hidem⟩, habs⟩
          -- Decompose hc: alphaEquiv (.abs a ...) (.abs b ...) with a ≠ b.
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

-- (4a, ctx variant) Same converse for the `.ctx a x` case: the freshness
-- constraint `(a, x)` is deferred, σ is unchanged, and θ carries to `rest`.
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
  -- .ctx only arises from c = .fresh b (.mvar π x'), a = π.reverse · b, x = x'.
  cases c with
  | unif s t =>
    exfalso
    -- unifStep on .unif never returns .ctx.
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
      -- hΓ gives Δ ⊢ b # (mvar π x').subst θ; convert via fresh_equivariance.
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

-- Term size (counts every node, including leaves).  Used for the occurs-check
-- completeness argument: if `x` occurs strictly inside `u`, then `u.subst θ`
-- is strictly larger than `(.mvar π x).subst θ`, contradicting α-equivalence
-- (which preserves size).
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

-- Permutation preserves size (renames atoms only, no structural change).
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

-- α-equivalence preserves size.
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

-- size of (u.subst θ) for non-mvar `u` containing `x`: strictly larger than
-- `(.mvar [] x).subst θ`. Used to refute occurs-check failures.
mutual
  /-- The size of `t.subst θ` is at least the size of every variable substitution
      `(.mvar [] x).subst θ` for every `x ∈ vars(t)`. -/
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

-- The strict version: if `u` is not a bare metavariable (has a non-trivial head
-- constructor) and `x ∈ vars(u)`, then `u.subst θ` is strictly larger than
-- `(.mvar [] x).subst θ`.
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

-- Helper: `simplifyFresh` failure means `a` cannot be made fresh for `t.subst θ`
-- in any context.  Proven by mutual induction over `t`.
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
        -- simplifyFresh on .mvar never returns none.
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

-- Helper: alphaEquivList preserves length.
private lemma alphaEquivList_length_eq {Γ : Context 𝔸 X} :
    ∀ {l1 l2 : List (ntm F X 𝔸)}, alphaEquivList Γ l1 l2 = true → l1.length = l2.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [alphaEquivList] at h
  | _ :: _, [], h => by simp [alphaEquivList] at h
  | _ :: ss, _ :: ts, h => by
      simp [alphaEquivList] at h
      exact congrArg (· + 1) (alphaEquivList_length_eq h.2)

-- (4b) Failure implies no solution.
-- Analogue of Maribel's claim that `.fail` is terminal: clash (atm/fapp) or
-- occurs-check violation rules out every potential (Δ, θ).
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
      -- unifStep returns .ctx — not .fail. Contradiction.
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
    -- Clash and occurs-check cases.  Strategy: case-analyse s and t, then for
    -- each pair reduce `unifStep` by `simp [unifStep]`.  Clash cases derive
    -- contradiction from α-equivalence; occurs-check cases require the
    -- forthcoming size lemma and are STUBBED.
    cases s with
    | atm a =>
      cases t with
      | atm b =>
        by_cases hab : a = b
        · simp [unifStep, hab] at h
        · simp [UnifConstraint.applySubst, UnifConstraint.toConstraint, Constraint.Entails,
                alphaEquiv, hab] at hc
      | mvar π x =>
        -- arm 4 (.atm a, .mvar π x): occursIn x of atm is false ⇒ .next.
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
        -- mvar/mvar: both branches return .next.
        by_cases hxy : x = y
        · simp [unifStep, hxy] at h
        · simp [unifStep, hxy] at h
      | fapp f ts =>
        -- arm 3: occurs-check failure ⇒ u.occursIn x = true.
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
        -- arm 4: occurs-check for fapp side.
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
          -- hc : f = g ∧ alphaEquivList Δ ... ... = true.
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
        -- arm 4: occurs-check for abs side.
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

-- (4c) Transitive converse: every solution of the input `Pr` factors through
-- the substitution produced by `unify`, modulo the deferred freshness pairs.
-- Analogue of `P1-from-P2-red-plus`.
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
    -- New deferred = (a, x) :: ds.
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

-- (4d) `finalizeDeferred` compatibility: if the deferred pairs are satisfied
-- by θ in Δ, then Δ entails the resulting Γ under θ.
-- This step has no direct Isabelle counterpart (Plan A divergence).
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
        -- Inductive hypothesis to apply: need EntailsUnder for the new Γ' after foldl.
        -- Step 1: derive Δ ⊢ a # ((mvar [] x).subst σ).subst θ from absorbedBy + hdef.
        have hfresh_θ : (Δ ⊢ a # ((ntm.mvar (F := F) [] x).subst σ).subst θ) = true := by
          have h_a_in : (a, x) ∈ (a, x) :: tl := List.mem_cons_self
          have hfresh_θ_x := hdef (a, x) h_a_in
          -- Δ ⊢ a # (mvar [] x).subst θ. Use absorbedBy + symm for substituted form.
          have habs_x := habs x
          -- habs_x : Δ ⊢ ((mvar [] x).subst σ).subst θ ≈α (mvar [] x).subst θ.
          exact freshPreserves_alphaEquiv Δ a ((ntm.mvar (F := F) [] x).subst θ)
            (((ntm.mvar (F := F) [] x).subst σ).subst θ)
            hfresh_θ_x (alphaEquiv_symm Δ _ _ habs_x)
        -- Step 2: apply simplifyFresh_subst_imp_entails to get Problem.Entails Δ (cs.applySubst θ).
        have hcs := simplifyFresh_subst_imp_entails Δ a θ
          ((ntm.mvar (F := F) [] x).subst σ) cs hsf hfresh_θ
        -- Step 3: the foldl inserts leaves (.fresh a' (mvar [] x')) into Γ_init. Each is
        -- entailed by Δ under θ from hcs.  Build new Γ_init' and recurse.
        set Γ_init' : Context 𝔸 X := cs.foldl (fun g c =>
          match c with
          | .fresh a' (.mvar [] x') => insert (a', x') g
          | _                       => g) Γ_init with hΓ_init'_def
        have hinit' : Γ_init'.EntailsUnder Δ θ = true := by
          -- Show every entry in Γ_init' is satisfied under θ.
          simp only [Context.EntailsUnder, decide_eq_true_eq]
          intro p hp
          -- p ∈ Γ_init' = foldl over cs starting from Γ_init.
          -- Either p ∈ Γ_init (use hinit) or p was inserted from a .fresh a' (mvar [] x') in cs.
          -- Helper claim: foldl insert preserves the property.
          have hfold_prop : ∀ (cs_pre : Problem F X 𝔸) (Γ₀ : Context 𝔸 X),
              (∀ q ∈ Γ₀, (Δ ⊢ q.1 # (ntm.mvar (F := F) [] q.2).subst θ) = true) →
              (∀ c' ∈ cs_pre, Constraint.Entails Δ (c'.applySubst θ) = true) →
              ∀ q ∈ cs_pre.foldl (fun g c =>
                match c with
                | .fresh a' (.mvar [] x') => insert (a', x') g
                | _                       => g) Γ₀,
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
                      -- Insert (a', x').
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
        -- Step 4: recurse.
        have hdef_tl : ∀ p ∈ tl, (Δ ⊢ p.1 # (ntm.mvar (F := F) [] p.2).subst θ) = true := by
          intro p hp; exact hdef p (List.mem_cons_of_mem _ hp)
        exact finalizeDeferred_le tl σ Γ_init' Γ Δ θ h habs hdef_tl hinit'

-- (Fase 5) Final theorem — Maribel Theorem 35 forward.
-- `solve` returns the most general unifier of `Pr`.
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
    -- Unpack `solve` into `unify` + `finalizeDeferred`.
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
        -- σ starts empty: absorbedBy trivially holds.
        have habs0 : Subst.absorbedBy Δ ([] : Subst F X 𝔸) θ :=
          Subst.absorbedBy_nil Δ θ
        -- ds starts empty: deferred property trivially holds.
        have hds0 : ∀ p ∈ ([] : List (𝔸 × X)),
            (Δ ⊢ p.1 # (ntm.mvar (F := F) [] p.2).subst θ) = true := by
          intros _ h; cases h
        -- Apply unify_le.
        obtain ⟨habs_u, hds_u⟩ :=
          unify_le Pr [] [] ds σ_u Δ θ hu hq habs0 hds0
        -- Apply finalizeDeferred_le.
        have hinit_empty : (∅ : Context 𝔸 X).EntailsUnder Δ θ = true := by
          simp [Context.EntailsUnder]
        have hΓ_under := finalizeDeferred_le ds σ_u ∅ Γ_fin Δ θ hf habs_u hds_u hinit_empty
        -- Assemble SolutionLe (Γ, σ) (Δ, θ) with witness σ' = θ.
        refine ⟨θ, ?_, ?_⟩
        · -- ∀ x, Δ ⊢ ((mvar [] x).subst σ).subst θ ≈α (mvar [] x).subst θ.
          exact habs_u
        · -- Γ.EntailsUnder Δ θ.
          exact hΓ_under

end Nominal
