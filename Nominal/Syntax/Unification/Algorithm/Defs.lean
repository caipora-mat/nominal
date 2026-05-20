import Nominal.Syntax.Unification.Basic
import Nominal.Syntax.Problems.Basic

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

-- (Convert a regular Constraint to a UnifConstraint).

def Constraint.toUnif : Constraint F X 𝔸 → UnifConstraint F X 𝔸
  | .fresh a t => .fresh a t
  | .alpha s t => .unif s t

-- (Step result).

inductive StepResult (F X 𝔸 : Type*) [DecidableEq F] [DecidableEq X] [Name 𝔸] where
  | fail : StepResult F X 𝔸
  | ctx  : 𝔸 → X → StepResult F X 𝔸
  | next : UnifProblem F X 𝔸 → Subst F X 𝔸 → StepResult F X 𝔸

-- (One step of the nominal unification algorithm).

def unifStep (c : UnifConstraint F X 𝔸) (rest : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) :
    StepResult F X 𝔸 :=
  match c with
  -- All mvar fresh constraints: `a #? (π·X)` becomes context entry `(π⁻¹·a, X)`.
  | .fresh b (.mvar π x) =>
      .ctx (LPermApply π.reverse b) x
  | .fresh a t =>
      match simplifyFresh a t with
      | none    => .fail
      | some cs => .next (rest ++ cs.map (·.toUnif)) σ
  | .unif s t =>
      match s, t with
      | .atm a, .atm b =>
          if a = b then .next rest σ else .fail
      | .mvar π x, .mvar π' y =>
          if x = y then
            .next (rest ++ (dsList π π').map (UnifConstraint.fresh · (.mvar [] x))) σ
          else
            let binding := (x, (ntm.mvar π' y : ntm F X 𝔸).permute π.reverse)
            .next (rest.applySubst [binding]) (σ ++ [binding])
      | .mvar π x, u =>
          if u.occursIn x then .fail
          else
            let binding := (x, u.permute π.reverse)
            .next (rest.applySubst [binding]) (σ ++ [binding])
      | u, .mvar π x =>
          if u.occursIn x then .fail
          else
            let binding := (x, u.permute π.reverse)
            .next (rest.applySubst [binding]) (σ ++ [binding])
      | .fapp f ss, .fapp g ts =>
          if f = g then
            if ss.length = ts.length then
              .next ((ss.zip ts).map (fun (s, t) => .unif s t) ++ rest) σ
            else .fail
          else .fail
      | .abs a s', .abs b t' =>
          if a = b then
            .next (.unif s' t' :: rest) σ
          else
            .next (.unif (s'.permute [(b, a)]) t' :: .fresh b s' :: rest) σ
      | _, _ => .fail

end Nominal
