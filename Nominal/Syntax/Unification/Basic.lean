import Nominal.Syntax.Problems.Basic
import Nominal.Syntax.Problems.Properties
import Nominal.Syntax.Substitution.Basic
import Nominal.Syntax.Substitution.Occurs
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


/-! ### Object-level permutation action on problems -/

/-- Object-level action on a constraint: `π · (a #? t) = π·a #? π·t` and
    `π · (s ≈? t) = π·s ≈? π·t`. -/
def UnifConstraint.permute (π : LPerm 𝔸) : UnifConstraint F X 𝔸 → UnifConstraint F X 𝔸
  | .fresh a t => .fresh (LPermApply π a) (t.permute π)
  | .unif s t  => .unif (s.permute π) (t.permute π)

def UnifProblem.permute (π : LPerm 𝔸) (Pr : UnifProblem F X 𝔸) : UnifProblem F X 𝔸 :=
  Pr.map (UnifConstraint.permute π)

lemma UnifConstraint.entails_permute (π : LPerm 𝔸) (Γ : Context 𝔸 X) (σ : Subst F X 𝔸)
    (c : UnifConstraint F X 𝔸) :
    ((c.permute π).applySubst σ).toConstraint.Entails Γ
      = (c.applySubst σ).toConstraint.Entails Γ := by
  cases c with
  | fresh a t =>
    simp only [UnifConstraint.permute, UnifConstraint.applySubst, UnifConstraint.toConstraint,
      Constraint.Entails, ntm.subst_permute]
    exact (fresh_equivariance Γ a (t.subst σ) π).symm
  | unif s t =>
    simp only [UnifConstraint.permute, UnifConstraint.applySubst, UnifConstraint.toConstraint,
      Constraint.Entails, ntm.subst_permute]
    exact (alphaEquiv_equivariance Γ (s.subst σ) (t.subst σ) π).symm

/-- **Solutions are invariant under the object-level action**: `𝒰(π · Pr) = 𝒰(Pr)`. The action
    is suspended on metavariables, so it does not change which substitutions solve a problem. -/
theorem UnifProblem.solutions_permute (π : LPerm 𝔸) (Pr : UnifProblem F X 𝔸) :
    (Pr.permute π).Solutions = Pr.Solutions := by
  ext ⟨Γ, σ⟩
  simp [UnifProblem.Solutions, Solution.Satisfies, Problem.Entails, UnifProblem.permute,
    UnifProblem.applySubst, UnifProblem.toConstraint, UnifConstraint.entails_permute]

end Nominal
