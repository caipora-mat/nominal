import Nominal.Syntax.Unification.Basic
import Nominal.Syntax.Problems.Basic

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

-- (Simplification for unification constraints).

mutual
/-- Simplify a unification constraint `s ≫≈α t` to a list of reduced constraints.
    Returns None if the constraint is inconsistent. -/
  def simplifyUnif : ntm F X 𝔸 → ntm F X 𝔸 → Option (UnifProblem F X 𝔸)
    | .atm a, .atm b =>
        if a = b then some [] else none
    | .mvar π x, .mvar π' y =>
        if x = y then some ((dsList π π').map fun n => .fresh n (.mvar [] x))
        else none
    | .fapp f ls, .fapp g ss =>
        if f = g then simplifyUnifList ls ss else none
    | .abs a l, .abs b s =>
        if a = b then simplifyUnif l s
        else
          match simplifyUnif (l.permute [(b, a)]) s, simplifyFresh b l with
          | some cs₁, some cs₂ =>
              some (cs₁ ++ (cs₂.map fun c =>
                match c with
                | .fresh a' t => UnifConstraint.fresh a' t
                | .alpha s t => UnifConstraint.unif s t))
          | _, _ => none
    | _, _ => none

  /-- Simplify a list of unification constraints. -/
  def simplifyUnifList : List (ntm F X 𝔸) → List (ntm F X 𝔸) → Option (UnifProblem F X 𝔸)
    | [], [] => some []
    | l :: ls, s :: ss =>
        match simplifyUnif l s, simplifyUnifList ls ss with
        | some cs₁, some cs₂ => some (cs₁ ++ cs₂)
        | _, _ => none
    | _, _ => none
end

-- (Termination measure: count variable occurrences).

/-- Collect all metavariables in a term. -/
def ntm.vars : ntm F X 𝔸 → List X
  | .atm _ => []
  | .mvar _ x => [x]
  | .fapp _ ts => ts.flatMap ntm.vars
  | .abs _ t => t.vars

/-- Count metavariable occurrences in a constraint. -/
def UnifConstraint.varCount : UnifConstraint F X 𝔸 → Nat
  | .fresh _ t => t.vars.length
  | .unif s t => s.vars.length + t.vars.length

/-- Count total metavariable occurrences in a problem. -/
def UnifProblem.varCount (Pr : UnifProblem F X 𝔸) : Nat :=
  Pr.foldl (fun acc c => acc + c.varCount) 0

-- (Instantiation rules).

/-- Apply instantiation rule: if `πX ≫≈α u` with X ∉ V(u), substitute [X ↦ π⁻¹u].
    Returns the substitution to apply and the remaining problem. -/
def UnifConstraint.tryInst : UnifConstraint F X 𝔸 → Option (X × ntm F X 𝔸)
  | .fresh _ _ => none
  | .unif (.mvar π x) u =>
      if !u.occursIn x then some (x, u.permute π.reverse) else none
  | .unif u (.mvar π x) =>
      if !u.occursIn x then some (x, u.permute π.reverse) else none
  | _ => none

/-- Apply a substitution [x ↦ t] to a unification problem. -/
def UnifProblem.applyInst (Pr : UnifProblem F X 𝔸) (x : X) (t : ntm F X 𝔸) : UnifProblem F X 𝔸 :=
  Pr.map fun c =>
    match c with
    | .fresh a u => UnifConstraint.fresh a (u.applyOne x t)
    | .unif s u => UnifConstraint.unif (s.applyOne x t) (u.applyOne x t)

-- (Full unification algorithm).

/-- Normalize a unification problem by first simplifying all constraints,
    then extracting and applying instantiations.
    Returns (reduced_problem, substitution) if solvable, or None if inconsistent. -/
def UnifProblem.normalize (Pr : UnifProblem F X 𝔸) : Option (UnifProblem F X 𝔸 × Subst F X 𝔸) :=
  -- Convert to regular problem and simplify using Problems.simplify
  match simplify (Pr.toConstraint) with
  | none => none  -- Inconsistent constraint found
  | some Pr_simple =>
    -- Convert back to unification problem
    let Pr_unif : UnifProblem F X 𝔸 := Pr_simple.map fun c =>
      match c with
      | .fresh a t => UnifConstraint.fresh a t
      | .alpha s t => UnifConstraint.unif s t
    -- Return simplified problem with empty substitution
    some (Pr_unif, [])

end Nominal
