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
    (1) Γ ⊢ Pr'σ where Pr' is obtained by converting unification constraints to equality constraints,
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

-- (Occurrence check and reduced constraints).

mutual
/-- Check if metavariable x occurs in term t. Used for the occurrence check in instantiation rules. -/
  def ntm.occursIn (x : X) : ntm F X 𝔸 → Bool
    | .atm _     => false
    | .mvar _ y  => x == y
    | .fapp _ ts => ntmListOccursIn x ts
    | .abs _ t   => t.occursIn x

  /-- Helper: check if x occurs in any term in a list. -/
  def ntmListOccursIn (x : X) : List (ntm F X 𝔸) → Bool
    | [] => false
    | t :: ts => t.occursIn x || ntmListOccursIn x ts
end

/-- A unification constraint is inconsistent (reduced in the sense of Definition 31) when
    no simplification or instantiation rule can be applied.
    Definition 31: u ≫≈α v is reduced when one of:
    1. u and v are distinct atoms.
    2. Precisely one is a moderated variable (mvar) and the other mentions that variable.
    3. Both are applications with different term-formers.
    4. They have different constructors at the root, and neither is a moderated variable. -/
def UnifConstraint.IsInconsistent : UnifConstraint F X 𝔸 → Bool
  | .fresh _ _ => false
  | .unif s t  =>
    match s, t with
    -- Condition 1: distinct atoms
    | .atm a, .atm b                 => a ≠ b
    -- Condition 2a: left is mvar, right is non-mvar containing left's variable
    | .mvar _ x, .fapp _ _           => t.occursIn x
    | .mvar _ x, .abs _ _            => t.occursIn x
    -- Condition 2b: right is mvar, left is non-mvar containing right's variable
    | .fapp _ _, .mvar _ x           => s.occursIn x
    | .abs _ _, .mvar _ x            => s.occursIn x
    -- Condition 3: both applications, different functors
    | .fapp f _, .fapp g _           => f ≠ g
    -- Condition 4: different constructors, neither is mvar
    | .atm _, .fapp _ _              => true
    | .atm _, .abs _ _               => true
    | .fapp _ _, .atm _              => true
    | .fapp _ _, .abs _ _            => true
    | .abs _ _, .atm _               => true
    | .abs _ _, .fapp _ _            => true
    -- Not reduced: both are mvars, or other combinations where rules apply
    | _, _ => false

/-- A unification problem is in normal form when all constraints are either freshness constraints
    or reduced (inconsistent) unification constraints. -/
def UnifProblem.IsNormalForm (Pr : UnifProblem F X 𝔸) : Prop :=
  ∀ c ∈ Pr, match c with
    | .fresh _ _ => true
    | .unif _ _ => c.IsInconsistent
    = true

end Nominal
