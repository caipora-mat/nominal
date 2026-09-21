import Nominal.Syntax.Problems.Basic
import Nominal.Syntax.Problems.Properties
import Nominal.Syntax.Substitution.Basic
import Nominal.Syntax.Substitution.Properties
import Nominal.Syntax.AlphaEquiv

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

/-- Freshness constraint `a #? t` or unification constraint `s ≈? t`. -/
inductive UnifConstraint (F X 𝔸 : Type*) [DecidableEq F] [DecidableEq X] [Name 𝔸] where
  | fresh : 𝔸 → ntm F X 𝔸 → UnifConstraint F X 𝔸
  | unif  : ntm F X 𝔸 → ntm F X 𝔸 → UnifConstraint F X 𝔸

/-- A unification problem (Def. 26): list of unification constraints. -/
abbrev UnifProblem (F X 𝔸 : Type*) [DecidableEq F] [DecidableEq X] [Name 𝔸] :=
  List (UnifConstraint F X 𝔸)


def UnifConstraint.applySubst (c : UnifConstraint F X 𝔸) (σ : Subst F X 𝔸) : UnifConstraint F X 𝔸 :=
  match c with
  | .fresh a t => .fresh a (t.subst σ)
  | .unif  s t => .unif  (s.subst σ) (t.subst σ)

def UnifProblem.applySubst (Pr : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) : UnifProblem F X 𝔸 :=
  Pr.map (·.applySubst σ)

@[simp] lemma UnifConstraint.applySubst_nil (c : UnifConstraint F X 𝔸) :
    c.applySubst [] = c := by
  cases c <;> simp [UnifConstraint.applySubst]

@[simp] lemma UnifProblem.applySubst_nil (Pr : UnifProblem F X 𝔸) :
    Pr.applySubst [] = Pr := by
  simp [UnifProblem.applySubst]


def UnifConstraint.toConstraint : UnifConstraint F X 𝔸 → Constraint F X 𝔸
  | .fresh a t => .fresh a t
  | .unif  s t => .alpha s t

/-- `Pr'` in Def. 27: `≈?` becomes `≈α`. -/
def UnifProblem.toConstraint (Pr : UnifProblem F X 𝔸) : Problem F X 𝔸 :=
  Pr.map UnifConstraint.toConstraint


/-- Solution to `Pr` (Def. 27): `Γ ⊢ Pr'σ` and `σ` is idempotent. -/
def Solution.Satisfies (Γ : Context 𝔸 X) (σ : Subst F X 𝔸) (Pr : UnifProblem F X 𝔸) : Prop :=
  Problem.Entails Γ (Pr.applySubst σ).toConstraint ∧ σ.IsIdempotent

/-- `𝒰(Pr)`: set of solutions to `Pr`. -/
def UnifProblem.Solutions (Pr : UnifProblem F X 𝔸) : Set (Context 𝔸 X × Subst F X 𝔸) :=
  { p | Solution.Satisfies p.1 p.2 Pr }


/-- `Γ₂ ⊢ Γ₁σ'`: for every `(a, Y) ∈ Γ₁`, `Γ₂ ⊢ a # Yσ'`. -/
def Context.EntailsUnder (Γ₁ : Context 𝔸 X) (Γ₂ : Context 𝔸 X) (σ : Subst F X 𝔸) : Bool :=
  decide (∀ p ∈ Γ₁, (Γ₂ ⊢ p.1 # (ntm.mvar (F := F) [] p.2).subst σ) = true)

/-- Instantiation ordering (Def. 28): `(Γ₁, σ₁) ≤ (Γ₂, σ₂)` iff some `σ'`
    factors `σ₁σ' ≈α σ₂` under `Γ₂` and entails `Γ₁σ'`. -/
def SolutionLe (p₁ p₂ : Context 𝔸 X × Subst F X 𝔸) : Prop :=
  ∃ σ' : Subst F X 𝔸,
    (∀ x : X, (p₂.1 ⊢ ((ntm.mvar (F := F) [] x).subst p₁.2).subst σ' ≈α
                        (ntm.mvar (F := F) [] x).subst p₂.2) = true) ∧
    p₁.1.EntailsUnder p₂.1 σ' = true


/-- `SolutionLe` is reflexive: the identity substitution mediates `p ≤ p`. -/
lemma SolutionLe_refl (p : Context 𝔸 X × Subst F X 𝔸) : SolutionLe p p := by
  refine ⟨[], ?_, ?_⟩
  · intro x
    simpa [ntm.subst_nil] using
      alphaEquiv_refl p.1 ((ntm.mvar (F := F) [] x).subst p.2)
  · simp only [Context.EntailsUnder, decide_eq_true_eq]
    intro q hq
    rw [ntm.subst_nil, fresh_mvar_id]
    simpa using hq

/-- `SolutionLe` is transitive: mediators compose via `σ' ◇ σ''`.  Together with
    `SolutionLe_refl` this makes `SolutionLe` a preorder — Maribel's Lemma 29,
    whose proof likewise establishes only reflexivity and transitivity.  (It is
    not a partial order on `Context × Subst`: mutually related solutions coincide
    only up to `≈α`, so antisymmetry fails on the raw type.) -/
lemma SolutionLe_trans {p₁ p₂ p₃ : Context 𝔸 X × Subst F X 𝔸}
    (h₁₂ : SolutionLe p₁ p₂) (h₂₃ : SolutionLe p₂ p₃) : SolutionLe p₁ p₃ := by
  obtain ⟨σ', hfac₁, hctx₁⟩ := h₁₂
  obtain ⟨σ'', hfac₂, hctx₂⟩ := h₂₃
  simp only [Context.EntailsUnder, decide_eq_true_eq] at hctx₁ hctx₂
  refine ⟨σ'.comp σ'', ?_, ?_⟩
  · intro x
    -- Transport the first factoring under `σ''` from `p₂.1` to `p₃.1`.
    have hstep :
        (p₃.1 ⊢ (((ntm.mvar (F := F) [] x).subst p₁.2).subst σ').subst σ''
                ≈α ((ntm.mvar (F := F) [] x).subst p₂.2).subst σ'') = true :=
      ntm.alphaEquiv_subst p₂.1 p₃.1 σ''
        (((ntm.mvar (F := F) [] x).subst p₁.2).subst σ')
        ((ntm.mvar (F := F) [] x).subst p₂.2) hctx₂ (hfac₁ x)
    rw [ntm.subst_comp]
    exact alphaEquiv_trans p₃.1 _ _ _ hstep (hfac₂ x)
  · simp only [Context.EntailsUnder, decide_eq_true_eq]
    intro q hq
    have h2 := ntm.fresh_subst p₂.1 p₃.1 σ'' q.1
      ((ntm.mvar (F := F) [] q.2).subst σ') hctx₂ (hctx₁ q hq)
    rw [ntm.subst_comp]
    exact h2

instance : Std.Refl (SolutionLe (F := F) (X := X) (𝔸 := 𝔸)) := ⟨SolutionLe_refl⟩

instance : IsTrans (Context 𝔸 X × Subst F X 𝔸) SolutionLe :=
  ⟨fun _ _ _ h₁₂ h₂₃ => SolutionLe_trans h₁₂ h₂₃⟩

/-- `SolutionLe` is a preorder (Maribel's Lemma 29). -/
instance : IsPreorder (Context 𝔸 X × Subst F X 𝔸) SolutionLe := ⟨⟩

/-- Two solutions are equivalent when each is an instance of the other.  Modulo
    this equivalence `SolutionLe` is antisymmetric, so it induces a partial order
    on solutions.  Concretely, `SolEquiv` identifies solutions that agree up to
    `≈α` on the substitution and mutual entailment of the contexts. -/
def SolEquiv (p q : Context 𝔸 X × Subst F X 𝔸) : Prop :=
  SolutionLe p q ∧ SolutionLe q p

/-- `SolEquiv` is an equivalence relation (immediate from `SolutionLe` being a
    preorder): reflexive and transitive from `SolutionLe`, symmetric by swapping
    the two conjuncts. -/
theorem SolEquiv.equivalence :
    Equivalence (SolEquiv (F := F) (X := X) (𝔸 := 𝔸)) where
  refl p := ⟨SolutionLe_refl p, SolutionLe_refl p⟩
  symm h := ⟨h.2, h.1⟩
  trans h₁ h₂ := ⟨SolutionLe_trans h₁.1 h₂.1, SolutionLe_trans h₂.2 h₁.2⟩

/-- Solutions form a setoid under `SolEquiv`. -/
instance solSetoid : Setoid (Context 𝔸 X × Subst F X 𝔸) where
  r := SolEquiv
  iseqv := SolEquiv.equivalence

/-- Solutions up to equivalence: `Context × Subst` quotiented by `SolEquiv`. -/
def SolClass (F X 𝔸 : Type*) [DecidableEq F] [DecidableEq X] [Name 𝔸] : Type _ :=
  Quotient (solSetoid (F := F) (X := X) (𝔸 := 𝔸))

/-- `SolutionLe` is a genuine partial order on solutions taken up to `SolEquiv`.
    Antisymmetry holds by construction: two classes below each other are equal
    because their representatives are `SolEquiv`.  On the raw type `SolutionLe`
    is only a preorder — antisymmetry fails up to `≈α`. -/
instance : PartialOrder (SolClass F X 𝔸) where
  le := Quotient.lift₂ SolutionLe (by
    intro a b a' b' ha hb
    exact propext
      ⟨fun h => SolutionLe_trans (SolutionLe_trans ha.2 h) hb.1,
       fun h => SolutionLe_trans (SolutionLe_trans ha.1 h) hb.2⟩)
  le_refl := by
    refine Quotient.ind ?_; intro p; exact SolutionLe_refl p
  le_trans := by
    refine Quotient.ind fun p => Quotient.ind fun q => Quotient.ind fun r => ?_
    intro h₁ h₂; exact SolutionLe_trans h₁ h₂
  le_antisymm := by
    refine Quotient.ind fun p => Quotient.ind fun q => ?_
    intro h₁ h₂; exact Quotient.sound ⟨h₁, h₂⟩


/-- Principal (mgu) solution (Def. 30): least element of `𝒰(Pr)` under `SolutionLe`. -/
def UnifProblem.IsPrincipalSolution (Pr : UnifProblem F X 𝔸)
    (p : Context 𝔸 X × Subst F X 𝔸) : Prop :=
  p ∈ Pr.Solutions ∧ ∀ q ∈ Pr.Solutions, SolutionLe p q


mutual
  /-- `x` occurs in `t`. -/
  def ntm.occursIn (x : X) : ntm F X 𝔸 → Bool
    | .atm _     => false
    | .mvar _ y  => x == y
    | .fapp _ ts => ntmList.occursIn x ts
    | .abs _ t   => t.occursIn x

  def ntmList.occursIn (x : X) : List (ntm F X 𝔸) → Bool
    | []      => false
    | t :: ts => t.occursIn x || ntmList.occursIn x ts
end


mutual
  lemma ntm.occursIn_permute (t : ntm F X 𝔸) (π : LPerm 𝔸) (x : X) :
      (t.permute π).occursIn x = t.occursIn x := by
    match t with
    | .atm _ => simp [ntm.permute, ntm.occursIn]
    | .mvar _ _ => simp [ntm.permute, ntm.occursIn]
    | .fapp _ ts =>
      simp only [ntm.permute, ntm.occursIn]
      exact ntmList.occursIn_permute ts π x
    | .abs _ t' =>
      simp only [ntm.permute, ntm.occursIn]
      exact ntm.occursIn_permute t' π x

  lemma ntmList.occursIn_permute (ts : List (ntm F X 𝔸)) (π : LPerm 𝔸) (x : X) :
      ntmList.occursIn x (ts.map (·.permute π)) = ntmList.occursIn x ts := by
    match ts with
    | [] => rfl
    | t :: ts' =>
      simp only [List.map_cons, ntmList.occursIn]
      rw [ntm.occursIn_permute t π x, ntmList.occursIn_permute ts' π x]
end


mutual
  /-- `applyOne x s` is a no-op when `x` does not occur in `t`. -/
  lemma ntm.applyOne_of_not_occursIn (t : ntm F X 𝔸) (x : X) (s : ntm F X 𝔸)
      (h : t.occursIn x = false) : t.applyOne x s = t := by
    match t with
    | .atm _ => simp [ntm.applyOne]
    | .mvar π y =>
      simp only [ntm.applyOne]
      split_ifs with hxy
      · subst hxy; simp [ntm.occursIn] at h
      · rfl
    | .fapp f ts =>
      simp only [ntm.occursIn] at h
      simp only [ntm.applyOne]
      congr 1
      exact ntmList.applyOne_of_not_occursIn ts x s h
    | .abs a t' =>
      simp only [ntm.occursIn] at h
      simp only [ntm.applyOne, ntm.applyOne_of_not_occursIn t' x s h]

  lemma ntmList.applyOne_of_not_occursIn (ts : List (ntm F X 𝔸)) (x : X) (s : ntm F X 𝔸)
      (h : ntmList.occursIn x ts = false) :
      ts.map (·.applyOne x s) = ts := by
    match ts with
    | [] => rfl
    | t :: ts' =>
      simp only [ntmList.occursIn, Bool.or_eq_false_iff] at h
      simp only [List.map_cons]
      rw [ntm.applyOne_of_not_occursIn t x s h.1,
          ntmList.applyOne_of_not_occursIn ts' x s h.2]
end

mutual
lemma ntm.subst_of_disjoint_dom : ∀ (t : ntm F X 𝔸) (σ : Subst F X 𝔸),
    (∀ x ∈ Subst.dom σ, t.occursIn x = false) → t.subst σ = t
  | .atm a, σ, _ => by simp
  | .mvar π x, σ, h => by
      rw [ntm.subst_mvar]
      have hx : x ∉ Subst.dom σ := by
        intro hmem
        have hocc := h x hmem
        simp [ntm.occursIn] at hocc
      rw [ntm.subst_mvar_nil, (Subst.lookup_eq_none_iff_not_mem_dom σ x).mpr hx]
      simp [ntm.permute]
  | .fapp f ts, σ, h => by
      rw [ntm.subst_fapp, ntmList.substList_of_disjoint_dom ts σ
        (fun x hx => by have := h x hx; simpa only [ntm.occursIn] using this)]
  | .abs a t, σ, h => by
      rw [ntm.subst_abs, ntm.subst_of_disjoint_dom t σ
        (fun x hx => by have := h x hx; simpa only [ntm.occursIn] using this)]

lemma ntmList.substList_of_disjoint_dom : ∀ (ts : List (ntm F X 𝔸)) (σ : Subst F X 𝔸),
    (∀ x ∈ Subst.dom σ, ntmList.occursIn x ts = false) → ts.map (·.subst σ) = ts
  | [], _, _ => rfl
  | t :: ts', σ, h => by
      simp only [List.map_cons]
      rw [ntm.subst_of_disjoint_dom t σ (fun x hx => by
            have := h x hx; simp only [ntmList.occursIn, Bool.or_eq_false_iff] at this
            exact this.1),
          ntmList.substList_of_disjoint_dom ts' σ (fun x hx => by
            have := h x hx; simp only [ntmList.occursIn, Bool.or_eq_false_iff] at this
            exact this.2)]
end

/-- If `x` doesn't occur in `u`, the singleton substitution `[(x, u)]` is idempotent. -/
lemma Subst.IsIdempotent.singleton_of_not_occursIn {x : X} {u : ntm F X 𝔸}
    (h : u.occursIn x = false) :
    Subst.IsIdempotent ([(x, u)] : Subst F X 𝔸) := by
  intro y
  by_cases hxy : y = x
  · subst hxy
    have h1 : (ntm.mvar (F := F) [] y).subst [(y, u)] = u := by
      rw [ntm.subst_mvar_nil]; simp [Subst.lookup_cons]
    rw [h1, ntm.subst_of_disjoint_dom u [(y, u)] (fun z hz => by
      simp only [Subst.dom_singleton, Finset.mem_singleton] at hz
      subst hz; exact h)]
  · have h1 : (ntm.mvar (F := F) [] y).subst [(x, u)] = ntm.mvar [] y := by
      rw [ntm.subst_mvar_nil]; simp [Subst.lookup_cons, if_neg hxy]
    rw [h1, h1]

/-- Corollary: if `x ∉ Subst.dom σ`, then `σ` fixes the bare metavariable `(mvar [] x)`. -/
lemma ntm.subst_mvar_nil_of_not_mem_dom {x : X} {σ : Subst F X 𝔸}
    (h : x ∉ Subst.dom σ) :
    (ntm.mvar (F := F) [] x).subst σ = ntm.mvar [] x := by
  apply ntm.subst_of_disjoint_dom
  intro z hz
  simp only [ntm.occursIn]
  by_contra hzx
  simp only [ne_eq, Bool.not_eq_false, beq_iff_eq] at hzx
  subst hzx
  exact h hz


mutual
  /-- `applyOne x u` commutes with `subst σ` when `x` is fresh for `σ`
      (out of `dom`, out of range) and `u` is `σ`-fixed. -/
  lemma ntm.applyOne_subst_comm (t : ntm F X 𝔸) (x : X) (u : ntm F X 𝔸) (σ : Subst F X 𝔸)
      (hx_dom : x ∉ Subst.dom σ)
      (hu_fixed : u.subst σ = u)
      (hx_img : ∀ y, ((ntm.mvar (F := F) [] y).subst σ).occursIn x = false) :
      (t.applyOne x u).subst σ = (t.subst σ).applyOne x u := by
    match t with
    | .atm a => simp [ntm.applyOne]
    | .mvar π z =>
      by_cases hz : z = x
      · obtain rfl := hz.symm
        have hap : (ntm.mvar π x : ntm F X 𝔸).applyOne x u = u.permute π := by
          simp [ntm.applyOne]
        have h1 : ((ntm.mvar π x : ntm F X 𝔸).applyOne x u).subst σ = u.permute π := by
          rw [hap, ntm.subst_permute, hu_fixed]
        have h2 : ((ntm.mvar π x : ntm F X 𝔸).subst σ).applyOne x u = u.permute π := by
          rw [ntm.subst_mvar, ntm.subst_mvar_nil_of_not_mem_dom hx_dom]
          simp [ntm.permute, ntm.applyOne]
        rw [h1, h2]
      · simp only [ntm.applyOne, if_neg hz]
        have hocc : ((ntm.mvar π z : ntm F X 𝔸).subst σ).occursIn x = false := by
          rw [ntm.subst_mvar, ntm.occursIn_permute]
          exact hx_img z
        rw [ntm.applyOne_of_not_occursIn _ x u hocc]
    | .fapp f ts =>
      simp only [ntm.applyOne, ntm.subst_fapp]
      congr 1
      exact ntmList.applyOne_subst_comm ts x u σ hx_dom hu_fixed hx_img
    | .abs a t' =>
      simp only [ntm.applyOne, ntm.subst_abs]
      rw [ntm.applyOne_subst_comm t' x u σ hx_dom hu_fixed hx_img]

  lemma ntmList.applyOne_subst_comm (ts : List (ntm F X 𝔸)) (x : X) (u : ntm F X 𝔸)
      (σ : Subst F X 𝔸)
      (hx_dom : x ∉ Subst.dom σ)
      (hu_fixed : u.subst σ = u)
      (hx_img : ∀ y, ((ntm.mvar (F := F) [] y).subst σ).occursIn x = false) :
      (ts.map (·.applyOne x u)).map (·.subst σ) =
      (ts.map (·.subst σ)).map (·.applyOne x u) := by
    match ts with
    | [] => rfl
    | t :: ts' =>
      simp only [List.map_cons]
      rw [ntm.applyOne_subst_comm t x u σ hx_dom hu_fixed hx_img,
          ntmList.applyOne_subst_comm ts' x u σ hx_dom hu_fixed hx_img]
end


mutual
  lemma ntm.occursIn_applyOne_self (t : ntm F X 𝔸) (x : X) (u : ntm F X 𝔸)
      (hu : u.occursIn x = false) :
      (t.applyOne x u).occursIn x = false := by
    match t with
    | .atm _ => simp [ntm.applyOne, ntm.occursIn]
    | .mvar π z =>
      by_cases hz : z = x
      · obtain rfl := hz.symm
        simp [ntm.applyOne, ntm.occursIn_permute, hu]
      · simp only [ntm.applyOne, if_neg hz, ntm.occursIn, beq_eq_false_iff_ne]
        exact fun heq => hz heq.symm
    | .fapp _ ts =>
      simp only [ntm.applyOne, ntm.occursIn]
      exact ntmList.occursIn_applyOne_self ts x u hu
    | .abs _ t' =>
      simp only [ntm.applyOne, ntm.occursIn]
      exact ntm.occursIn_applyOne_self t' x u hu

  lemma ntmList.occursIn_applyOne_self (ts : List (ntm F X 𝔸)) (x : X) (u : ntm F X 𝔸)
      (hu : u.occursIn x = false) :
      ntmList.occursIn x (ts.map (·.applyOne x u)) = false := by
    match ts with
    | [] => rfl
    | t :: ts' =>
      simp only [List.map_cons, ntmList.occursIn]
      rw [ntm.occursIn_applyOne_self t x u hu,
          ntmList.occursIn_applyOne_self ts' x u hu]
      rfl
end


mutual
  /-- `(t.applyOne x u).subst σ = t.applyOne x u` when both `t` and `u` are
      `σ`-fixed.  No hypothesis on `x` vs. `σ`. -/
  lemma ntm.applyOne_subst_of_stable (t : ntm F X 𝔸) (x : X) (u : ntm F X 𝔸)
      (σ : Subst F X 𝔸) (ht : t.subst σ = t) (hu : u.subst σ = u) :
      (t.applyOne x u).subst σ = t.applyOne x u := by
    match t with
    | .atm b => simp [ntm.applyOne]
    | .mvar π y =>
      simp only [ntm.applyOne]
      by_cases hy : y = x
      · rw [if_pos hy, ntm.subst_permute, hu]
      · rw [if_neg hy]; exact ht
    | .fapp f ts =>
      simp only [ntm.applyOne, ntm.subst_fapp]
      have hts : ts.map (·.subst σ) = ts := by
        have htmp := ht
        simp [ntm.subst_fapp] at htmp
        exact htmp
      congr 1
      exact ntmList.applyOne_subst_of_stable ts x u σ hts hu
    | .abs b t' =>
      simp only [ntm.applyOne, ntm.subst_abs]
      have ht' : t'.subst σ = t' := by
        have htmp := ht
        simp [ntm.subst_abs] at htmp
        exact htmp
      congr 1
      exact ntm.applyOne_subst_of_stable t' x u σ ht' hu

  lemma ntmList.applyOne_subst_of_stable (ts : List (ntm F X 𝔸)) (x : X) (u : ntm F X 𝔸)
      (σ : Subst F X 𝔸) (hts : ts.map (·.subst σ) = ts) (hu : u.subst σ = u) :
      (ts.map (·.applyOne x u)).map (·.subst σ) = ts.map (·.applyOne x u) := by
    match ts with
    | [] => rfl
    | t :: ts' =>
      simp only [List.map_cons] at hts
      injection hts with ht hts'
      simp only [List.map_cons]
      rw [ntm.applyOne_subst_of_stable t x u σ ht hu,
          ntmList.applyOne_subst_of_stable ts' x u σ hts' hu]
end

lemma ntm.subst_singleton : ∀ (t : ntm F X 𝔸) (x : X) (u : ntm F X 𝔸),
    t.subst [(x, u)] = t.applyOne x u
  | .atm a, x, u => by simp [ntm.applyOne]
  | .mvar π z, x, u => by
      rw [ntm.subst_mvar]
      simp only [ntm.applyOne]
      by_cases hz : z = x
      · subst hz; rw [ntm.subst_mvar_nil]; simp [Subst.lookup_cons]
      · rw [if_neg hz, ntm.subst_mvar_nil]
        simp [Subst.lookup_cons, if_neg hz, ntm.permute]
  | .fapp f ts, x, u => by
      rw [ntm.subst_fapp]; simp only [ntm.applyOne]
      congr 1; exact List.map_congr_left (fun t _ => ntm.subst_singleton t x u)
  | .abs a t, x, u => by
      rw [ntm.subst_abs]; simp only [ntm.applyOne]
      rw [ntm.subst_singleton t x u]


/-- `σ.comp [(x, u)]` is idempotent when `σ` is idempotent, `u` is `σ`-fixed,
    and `x ∉ u`. -/
lemma Subst.IsIdempotent.comp_singleton {σ : Subst F X 𝔸} {x : X} {u : ntm F X 𝔸}
    (hσ : σ.IsIdempotent)
    (hu_fixed : u.subst σ = u)
    (hxu : u.occursIn x = false) :
    Subst.IsIdempotent (σ.comp [(x, u)]) := by
  intro y
  set r := (ntm.mvar (F := F) [] y).subst σ with hr
  have hr_stable : r.subst σ = r := hr ▸ ntm.subst_idempotent hσ _
  have hStep1 : (r.applyOne x u).subst σ = r.applyOne x u :=
    ntm.applyOne_subst_of_stable r x u σ hr_stable hu_fixed
  have hA : (ntm.mvar (F := F) [] y).subst (σ.comp [(x, u)]) = r.applyOne x u := by
    rw [ntm.subst_mvar_nil_comp, ← hr, ntm.subst_singleton]
  rw [hA, ntm.subst_comp, ntm.subst_singleton, hStep1]
  exact (ntm.applyOne_of_not_occursIn _ x u (ntm.occursIn_applyOne_self r x u hxu)).symm

/-- When `x` is fresh for the range of `σ`, `σ.comp [(x, u)] = σ ++ [(x, u)]`. -/
lemma Subst.comp_singleton_eq_append {σ : Subst F X 𝔸} {x : X} {u : ntm F X 𝔸}
    (hx : ∀ p ∈ σ, p.2.occursIn x = false) :
    σ.comp [(x, u)] = σ ++ [(x, u)] := by
  unfold Subst.comp
  congr 1
  induction σ with
  | nil => rfl
  | cons p σ' ih =>
      obtain ⟨Y, s⟩ := p
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨?_, ih (fun q hq => hx q (List.mem_cons_of_mem _ hq))⟩
      have hs : s.occursIn x = false := hx (Y, s) (by simp)
      rw [ntm.subst_singleton, ntm.applyOne_of_not_occursIn s x u hs]

end Nominal
