import Nominal.Syntax.Unification.Properties

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

-- Completeness of the nominal unification algorithm.
-- Goal: `UnifProblem.solve_principal` — Maribel Theorem 36.
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
        -- instantiation case.
        sorry
      | fapp _ _ => simp [unifStep] at h
      | abs _ _  => simp [unifStep] at h
    | mvar π x =>
      cases t with
      | atm _ =>
        -- instantiation case.
        sorry
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
        · -- mvar-mvar diff: instantiation.
          sorry
      | fapp f ts =>
        -- instantiation (arm 3, if occursIn = false).
        sorry
      | abs _ _ =>
        sorry
    | fapp f ss =>
      cases t with
      | atm _ => simp [unifStep] at h
      | mvar π x =>
        -- instantiation (arm 4).
        sorry
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
        sorry
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
  -- Will be filled in subsequent sessions.  Structure: ctx case only arises
  -- from `c = .fresh b (.mvar π x')`, with `a = π.reverse · b` and `x = x'`.
  -- The freshness witness comes from `fresh_equivariance` applied to the
  -- α-equivalence solution θ provides for the constraint.
  sorry

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
lemma unify_le
    (Pr : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) (ds : List (𝔸 × X))
    (ds' : List (𝔸 × X)) (σ' : Subst F X 𝔸)
    (Δ : Context 𝔸 X) (θ : Subst F X 𝔸)
    (h : unify Pr σ ds = some (ds', σ'))
    (hθ : Solution.Satisfies Δ θ Pr) :
    -- θ is more specific than σ' (witness ρ).
    (∃ ρ : Subst F X 𝔸,
      ∀ x : X,
        (Δ ⊢ ((ntm.mvar (F := F) [] x).subst σ').subst ρ ≈α
              (ntm.mvar (F := F) [] x).subst θ) = true) ∧
    -- Δ already satisfies every deferred freshness pair under θ.
    (∀ p ∈ ds', (Δ ⊢ p.1 # (ntm.mvar (F := F) [] p.2).subst θ) = true) := by
  sorry

-- (4d) `finalizeDeferred` compatibility: if the deferred pairs are satisfied
-- by θ in Δ, then Δ entails the resulting Γ under θ.
-- This step has no direct Isabelle counterpart (Plan A divergence).
lemma finalizeDeferred_le
    (deferred : List (𝔸 × X)) (σ : Subst F X 𝔸) (Γ : Context 𝔸 X)
    (Δ : Context 𝔸 X) (θ : Subst F X 𝔸)
    (h : finalizeDeferred deferred σ ∅ = some Γ)
    (hθ_def : ∀ p ∈ deferred,
        (Δ ⊢ p.1 # ((ntm.mvar (F := F) [] p.2).subst σ).subst θ) = true)
    (hρ : ∀ x : X,
        (Δ ⊢ ((ntm.mvar (F := F) [] x).subst σ).subst θ ≈α
              (ntm.mvar (F := F) [] x).subst θ) = true) :
    Γ.EntailsUnder Δ θ = true := by
  sorry

-- (Fase 5) Final theorem — Maribel Theorem 36 forward.
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
    -- hq : Solution.Satisfies Δ θ Pr
    -- target : SolutionLe (Γ, σ) (Δ, θ)
    -- Plan: unpack solve into unify + finalizeDeferred, apply unify_le and
    -- finalizeDeferred_le, then assemble the SolutionLe witness.
    sorry

end Nominal
