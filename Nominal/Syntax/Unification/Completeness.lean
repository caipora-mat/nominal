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

-- (4a) Step-level converse for the recursive case `.next Pr' σ_next`.
-- Analogue of Isabelle's `P1-from-P2-sred`: a solution of `c::rest` carries
-- over to `Pr'` (under the same θ) AND θ is more specific than σ_next
-- through some `ρ` (which is `θ` itself in the non-instantiation cases,
-- and `θ` augmented with the bound `x ↦ u` in instantiation cases).
lemma unifStep_next_le
    (c : UnifConstraint F X 𝔸) (rest : UnifProblem F X 𝔸)
    (σ σ_next : Subst F X 𝔸) (Pr' : UnifProblem F X 𝔸)
    (Δ : Context 𝔸 X) (θ : Subst F X 𝔸)
    (h : unifStep c rest σ = .next Pr' σ_next)
    (hθ : Solution.Satisfies Δ θ (c :: rest)) :
    Solution.Satisfies Δ θ Pr' ∧
    ∃ ρ : Subst F X 𝔸,
      ∀ x : X,
        (Δ ⊢ ((ntm.mvar (F := F) [] x).subst σ_next).subst ρ ≈α
              (ntm.mvar (F := F) [] x).subst θ) = true := by
  sorry

-- (4a, ctx variant) Same converse for the `.ctx a x` case: the freshness
-- constraint `(a, x)` is deferred, and θ carries unchanged to `rest`.
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
