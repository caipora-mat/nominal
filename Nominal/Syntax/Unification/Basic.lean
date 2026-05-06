import Nominal.Syntax.Problems.Basic
import Nominal.Syntax.Problems.Properties
import Nominal.Syntax.Substitution.Basic
import Nominal.Syntax.AlphaEquiv

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

-- (Unification constraints and problems).

/-- A unification constraint is either a freshness question `a #? t` or a unification question `s ≫≈α? t`. -/
inductive UnifConstraint (F X 𝔸 : Type*) [DecidableEq F] [DecidableEq X] [Name 𝔸] where
  | fresh : 𝔸 → ntm F X 𝔸 → UnifConstraint F X 𝔸
  | unif  : ntm F X 𝔸 → ntm F X 𝔸 → UnifConstraint F X 𝔸

/-- A unification problem is a list of unification constraints. -/
abbrev UnifProblem (F X 𝔸 : Type*) [DecidableEq F] [DecidableEq X] [Name 𝔸] :=
  List (UnifConstraint F X 𝔸)

-- (Notation for unification constraint).

notation s " ≫≈α " t => UnifConstraint.unif s t

-- (Substitution on unification constraints).

/-- Apply a substitution to a unification constraint. -/
def UnifConstraint.applySubst : UnifConstraint F X 𝔸 → Subst F X 𝔸 → UnifConstraint F X 𝔸
  | .fresh a t, σ => .fresh a (t.subst σ)
  | .unif s t,  σ => .unif (s.subst σ) (t.subst σ)

/-- Apply a substitution to a unification problem. -/
def UnifProblem.applySubst (Pr : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) : UnifProblem F X 𝔸 :=
  Pr.map fun c => c.applySubst σ

-- (Conversion to regular problem).

/-- Convert a unification constraint to a regular constraint by treating unification as equality. -/
def UnifConstraint.toConstraint : UnifConstraint F X 𝔸 → Constraint F X 𝔸
  | .fresh a t => .fresh a t
  | .unif s t  => .alpha s t

/-- Convert a unification problem to a regular problem. -/
def UnifProblem.toConstraint (Pr : UnifProblem F X 𝔸) : Problem F X 𝔸 :=
  Pr.map UnifConstraint.toConstraint

-- (Idempotence).

/-- A substitution is idempotent if applying it twice gives the same result as applying it once. -/
def Subst.IsIdempotent (σ : Subst F X 𝔸) : Prop :=
  ∀ X : X, (ntm.mvar [] X).subst σ = ((ntm.mvar [] X).subst σ).subst σ

-- (Context entailment under substitution).

/-- A context Γ₂ entails another context Γ₁ under a substitution σ if for every freshness constraint
    `(a, Y) ∈ Γ₁`, we have `Γ₂ ⊢ a # Yσ`. -/
def Context.EntailsUnder (Γ₁ : Context 𝔸 X) (Γ₂ : Context 𝔸 X) (σ : Subst F X 𝔸) : Prop :=
  ∀ (a : 𝔸) (Y : X), (a, Y) ∈ Γ₁ → fresh Γ₂ a ((ntm.mvar [] Y).subst σ) = true

-- (Solution).

/-- A solution to a unification problem is a pair (Γ, σ) of a context and a substitution.
    Definition 27: A solution must satisfy:
    (1) Γ ⊢ 𝒫'σ where 𝒫' is obtained by converting unification constraints to equality constraints,
    (2) Xσ ≡ Xσσ for all X (idempotence). -/
structure Solution (F X 𝔸 : Type*) [DecidableEq F] [DecidableEq X] [Name 𝔸] where
  ctx : Context 𝔸 X
  subst : Subst F X 𝔸

/-- A solution satisfies a unification problem if the converted problem with applied substitution
    is entailed by the context. -/
def Solution.Satisfies (sol : Solution F X 𝔸) (Pr : UnifProblem F X 𝔸) : Prop :=
  Problem.Entails sol.ctx ((Pr.applySubst sol.subst).toConstraint)

/-- A solution is idempotent if its substitution is idempotent. -/
def Solution.IsIdempotent (sol : Solution F X 𝔸) : Prop :=
  sol.subst.IsIdempotent

/-- The set of solutions to a unification problem: pairs (Γ, σ) that satisfy both conditions of Definition 27. -/
def UnifProblem.Solutions (Pr : UnifProblem F X 𝔸) : Set (Solution F X 𝔸) :=
  { sol | sol.Satisfies Pr ∧ sol.IsIdempotent }

-- (Instantiation ordering).

/-- The instantiation ordering on solutions (Definition 28): (Γ₁, σ₁) ≤ (Γ₂, σ₂) if there exists
    a substitution σ' such that:
    - for all X, Γ₂ ⊢ Xσ₁σ' ≈α Xσ₂
    - Γ₂ ⊢ Γ₁σ' (Γ₁ is entailed by Γ₂ under σ'). -/
def Solution.Le (sol₁ sol₂ : Solution F X 𝔸) : Prop :=
  ∃ σ' : Subst F X 𝔸,
    (∀ Y : X, alphaEquiv sol₂.ctx
        ((ntm.mvar [] Y).subst sol₁.subst |>.subst σ')
        ((ntm.mvar [] Y).subst sol₂.subst) = true)
    ∧ sol₁.ctx.EntailsUnder sol₂.ctx σ'

instance : LE (Solution F X 𝔸) := ⟨Solution.Le⟩

-- (Principal solution).

/-- A principal (or most general) solution to a unification problem is a least element of the
    solutions set with respect to the instantiation ordering. Definition 30. -/
def UnifProblem.IsPrincipalSolution (Pr : UnifProblem F X 𝔸) (sol : Solution F X 𝔸) : Prop :=
  sol ∈ Pr.Solutions ∧ ∀ sol' ∈ Pr.Solutions, sol ≤ sol'

end Nominal
