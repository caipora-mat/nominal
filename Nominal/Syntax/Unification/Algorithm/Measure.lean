import Nominal.Syntax.Unification.Algorithm.Defs

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]


mutual
  def ntm.metavars : ntm F X 𝔸 → Finset X
    | .atm _     => ∅
    | .mvar _ x  => {x}
    | .fapp _ ts => ntmList.metavars ts
    | .abs _ t   => t.metavars

  def ntmList.metavars : List (ntm F X 𝔸) → Finset X
    | []      => ∅
    | t :: ts => t.metavars ∪ ntmList.metavars ts
end

mutual
  lemma ntm.permute_metavars (π : LPerm 𝔸) (t : ntm F X 𝔸) :
      (t.permute π).metavars = t.metavars := by
    match t with
    | .atm _    => simp [ntm.permute, ntm.metavars]
    | .mvar _ _ => simp [ntm.permute, ntm.metavars]
    | .fapp _ ts =>
      simp only [ntm.permute, ntm.metavars]
      exact ntmList.permute_metavars π ts
    | .abs _ t' =>
      simp only [ntm.permute, ntm.metavars]
      exact ntm.permute_metavars π t'

  lemma ntmList.permute_metavars (π : LPerm 𝔸) (ts : List (ntm F X 𝔸)) :
      ntmList.metavars (ts.map (·.permute π)) = ntmList.metavars ts := by
    match ts with
    | []       => simp [ntmList.metavars]
    | t :: ts' =>
      simp only [List.map_cons, ntmList.metavars]
      rw [ntm.permute_metavars π t, ntmList.permute_metavars π ts']
end


/-- Metavariables appearing only in unification constraints. -/
def UnifProblem.unifVars (Pr : UnifProblem F X 𝔸) : Finset X :=
  Pr.foldl (fun acc c => match c with
    | .fresh _ _ => acc
    | .unif s t  => acc ∪ s.metavars ∪ t.metavars) ∅

mutual
  def ntm.depth : ntm F X 𝔸 → ℕ
    | .atm _     => 0
    | .mvar _ _  => 0
    | .fapp _ ts => 1 + ntmList.maxDepth ts
    | .abs _ t   => 1 + t.depth

  def ntmList.maxDepth : List (ntm F X 𝔸) → ℕ
    | []      => 0
    | t :: ts => max t.depth (ntmList.maxDepth ts)
end

mutual
  lemma ntm.permute_depth (π : LPerm 𝔸) (t : ntm F X 𝔸) :
      (t.permute π).depth = t.depth := by
    match t with
    | .atm _ | .mvar _ _ => simp [ntm.permute, ntm.depth]
    | .fapp _ ts =>
      simp only [ntm.permute, ntm.depth]
      congr 1; exact ntmList.permute_maxDepth π ts
    | .abs _ t' =>
      simp only [ntm.permute, ntm.depth]
      rw [ntm.permute_depth π t']

  lemma ntmList.permute_maxDepth (π : LPerm 𝔸) (ts : List (ntm F X 𝔸)) :
      ntmList.maxDepth (ts.map (·.permute π)) = ntmList.maxDepth ts := by
    match ts with
    | []       => simp [ntmList.maxDepth]
    | t :: ts' =>
      simp only [List.map_cons, ntmList.maxDepth]
      rw [ntm.permute_depth π t, ntmList.permute_maxDepth π ts']
end

/-- Multiset of constraint weights (used as secondary termination measure).
    Fresh constraints have weight `t.depth + 1`; unification constraints have
    weight `max s.depth t.depth + 2`.  The +2 gap ensures that a unif constraint
    is always strictly heavier than any fresh constraint at the same depth, which
    is needed for the mvar-mvar-same rule's termination argument. -/
def UnifProblem.unifDepthMs (Pr : UnifProblem F X 𝔸) : Multiset ℕ :=
  (Pr.map fun c => match c with
    | .fresh _ t => t.depth + 1
    | .unif s t  => max s.depth t.depth + 2 : List ℕ)

end Nominal
