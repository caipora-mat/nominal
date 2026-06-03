import Nominal.Syntax.Problems.Basic
import Nominal.Syntax.Problems.Properties
import Nominal.Syntax.Substitution.Basic
import Nominal.Syntax.Substitution.Properties
import Nominal.Syntax.AlphaEquiv

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

-- (Definition 26: Unification constraints and problems).
-- A unification problem is like a problem (Definition 4 of Section 3),
-- but replacing equality constraints s ≈α t by unification constraints s ≈? t.

/-- A unification constraint is either a freshness constraint `a #? t`
    or a unification constraint `s ≈? t`. -/
inductive UnifConstraint (F X 𝔸 : Type*) [DecidableEq F] [DecidableEq X] [Name 𝔸] where
  | fresh : 𝔸 → ntm F X 𝔸 → UnifConstraint F X 𝔸
  | unif  : ntm F X 𝔸 → ntm F X 𝔸 → UnifConstraint F X 𝔸

/-- A unification problem is a list of unification constraints (Definition 26). -/
abbrev UnifProblem (F X 𝔸 : Type*) [DecidableEq F] [DecidableEq X] [Name 𝔸] :=
  List (UnifConstraint F X 𝔸)

-- (Substitution on unification constraints and problems).

/-- Apply a substitution to a unification constraint. -/
def UnifConstraint.applySubst (c : UnifConstraint F X 𝔸) (σ : Subst F X 𝔸) : UnifConstraint F X 𝔸 :=
  match c with
  | .fresh a t => .fresh a (t.subst σ)
  | .unif  s t => .unif  (s.subst σ) (t.subst σ)

/-- Apply a substitution to a unification problem. -/
def UnifProblem.applySubst (Pr : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) : UnifProblem F X 𝔸 :=
  Pr.map (·.applySubst σ)

@[simp] lemma UnifConstraint.applySubst_append (c : UnifConstraint F X 𝔸) (σ σ' : Subst F X 𝔸) :
    c.applySubst (σ ++ σ') = (c.applySubst σ).applySubst σ' := by
  cases c with
  | fresh a t => simp [UnifConstraint.applySubst]
  | unif s t  => simp [UnifConstraint.applySubst]

@[simp] lemma UnifProblem.applySubst_append (Pr : UnifProblem F X 𝔸) (σ σ' : Subst F X 𝔸) :
    Pr.applySubst (σ ++ σ') = (Pr.applySubst σ).applySubst σ' := by
  simp [UnifProblem.applySubst, List.map_map, Function.comp_def]

@[simp] lemma UnifConstraint.applySubst_nil (c : UnifConstraint F X 𝔸) :
    c.applySubst [] = c := by
  cases c <;> simp [UnifConstraint.applySubst]

@[simp] lemma UnifProblem.applySubst_nil (Pr : UnifProblem F X 𝔸) :
    Pr.applySubst [] = Pr := by
  simp [UnifProblem.applySubst]

-- (Conversion to regular problem: replace ≈? by ≈α).

/-- Convert a unification constraint to a regular constraint. -/
def UnifConstraint.toConstraint : UnifConstraint F X 𝔸 → Constraint F X 𝔸
  | .fresh a t => .fresh a t
  | .unif  s t => .alpha s t

/-- Convert a unification problem to a regular problem (Pr' in Definition 27). -/
def UnifProblem.toConstraint (Pr : UnifProblem F X 𝔸) : Problem F X 𝔸 :=
  Pr.map UnifConstraint.toConstraint

-- (Definition 27: Solution).

/-- A solution to a unification problem Pr is a pair (Γ, σ) satisfying (Definition 27):
    (1) Γ ⊢ Pr'σ, where Pr' replaces ≈? by ≈α, and Pr'σ applies σ to all terms;
    (2) Xσ ≡ Xσσ for all X (idempotence). -/
def Solution.Satisfies (Γ : Context 𝔸 X) (σ : Subst F X 𝔸) (Pr : UnifProblem F X 𝔸) : Prop :=
  Problem.Entails Γ (Pr.applySubst σ).toConstraint ∧ σ.IsIdempotent

/-- The set of solutions to Pr, written 𝒰(Pr) in the paper. -/
def UnifProblem.Solutions (Pr : UnifProblem F X 𝔸) : Set (Context 𝔸 X × Subst F X 𝔸) :=
  { p | Solution.Satisfies p.1 p.2 Pr }

-- (Definition 28: Instantiation ordering).

/-- Γ₂ entails context Γ₁ under substitution σ': for every (a, Y) ∈ Γ₁, Γ₂ ⊢ a # Yσ'. -/
def Context.EntailsUnder (Γ₁ : Context 𝔸 X) (Γ₂ : Context 𝔸 X) (σ : Subst F X 𝔸) : Bool :=
  decide (∀ p ∈ Γ₁, (Γ₂ ⊢ p.1 # (ntm.mvar (F := F) [] p.2).subst σ) = true)

/-- (Γ₁, σ₁) ≤ (Γ₂, σ₂) iff there exists σ' such that (Definition 28):
    - for all X, Γ₂ ⊢ Xσ₁σ' ≈α Xσ₂, and
    - Γ₂ ⊢ Γ₁σ' (Γ₁ is entailed by Γ₂ under σ'). -/
def SolutionLe (p₁ p₂ : Context 𝔸 X × Subst F X 𝔸) : Prop :=
  ∃ σ' : Subst F X 𝔸,
    (∀ x : X, (p₂.1 ⊢ ((ntm.mvar (F := F) [] x).subst p₁.2).subst σ' ≈α
                        (ntm.mvar (F := F) [] x).subst p₂.2) = true) ∧
    p₁.1.EntailsUnder p₂.1 σ' = true

-- (Definition 30: Principal solution).

/-- A principal (most general) solution is a least element of 𝒰(Pr) under the instantiation ordering (Definition 30). -/
def UnifProblem.IsPrincipalSolution (Pr : UnifProblem F X 𝔸)
    (p : Context 𝔸 X × Subst F X 𝔸) : Prop :=
  p ∈ Pr.Solutions ∧ ∀ q ∈ Pr.Solutions, SolutionLe p q

-- (Occurrence check — used in Definition 31 and instantiation rules).

mutual
  /-- True iff metavariable x occurs in term t. -/
  def ntm.occursIn (x : X) : ntm F X 𝔸 → Bool
    | .atm _     => false
    | .mvar _ y  => x == y
    | .fapp _ ts => ntmList.occursIn x ts
    | .abs _ t   => t.occursIn x

  /-- True iff x occurs in any term in the list. -/
  def ntmList.occursIn (x : X) : List (ntm F X 𝔸) → Bool
    | []      => false
    | t :: ts => t.occursIn x || ntmList.occursIn x ts
end

-- (Lemmas relating `occursIn` and substitution.)

mutual
  /-- If `x` doesn't occur in `t`, then substituting `s` for `x` is a no-op. -/
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

  /-- List version. -/
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

/-- If `x` doesn't occur in `u`, the singleton substitution `[(x, u)]` is idempotent. -/
lemma Subst.IsIdempotent.singleton_of_not_occursIn {x : X} {u : ntm F X 𝔸}
    (h : u.occursIn x = false) :
    Subst.IsIdempotent ([(x, u)] : Subst F X 𝔸) := by
  intro y
  simp only [ntm.subst_cons, ntm.subst_nil, ntm.applyOne]
  by_cases hxy : y = x
  · subst hxy
    rw [if_pos rfl, ntm.permute_nil, ntm.applyOne_of_not_occursIn u y u h]
  · simp [if_neg hxy, ntm.applyOne]

-- (Definition 31: Reduced / inconsistent unification constraints).
-- A unification constraint u ≈? v is reduced when one of the following holds:
-- (1) u and v are distinct atoms.
-- (2) Exactly one of u, v is a moderated variable and the other mentions that variable.
-- (3) u and v are applications with different term-formers.
-- (4) Different root constructors, and neither is a moderated variable.

/-- A unification constraint is reduced (inconsistent) if no rule can simplify it further. -/
def UnifConstraint.IsInconsistent : UnifConstraint F X 𝔸 → Bool
  | .fresh _ _ => false
  | .unif s t  =>
    match s, t with
    | .atm a,    .atm b    => decide (a ≠ b)                     -- (1)
    | .mvar _ x, .fapp _ _ => t.occursIn x                       -- (2a)
    | .mvar _ x, .abs _ _  => t.occursIn x                       -- (2a)
    | .fapp _ _, .mvar _ x => s.occursIn x                       -- (2b)
    | .abs _ _,  .mvar _ x => s.occursIn x                       -- (2b)
    | .fapp f _, .fapp g _ => decide (f ≠ g)                     -- (3)
    | .atm _,    .fapp _ _ => true                               -- (4)
    | .atm _,    .abs _ _  => true                               -- (4)
    | .fapp _ _, .atm _    => true                               -- (4)
    | .fapp _ _, .abs _ _  => true                               -- (4)
    | .abs _ _,  .atm _    => true                               -- (4)
    | .abs _ _,  .fapp _ _ => true                               -- (4)
    | _,         _         => false

end Nominal
