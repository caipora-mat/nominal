import Nominal.Core
import Nominal.Syntax.LPerm
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic

namespace Nominal

open Core

/-- Nominal terms over function symbols `F`, metavariables `X`, and atoms `𝔸`. -/
inductive ntm (F X 𝔸 : Type*) [DecidableEq F] [DecidableEq X] [Name 𝔸] where
  | atm : 𝔸 → ntm F X 𝔸
  | mvar : LPerm 𝔸 → X → ntm F X 𝔸
  | fapp : F → List (ntm F X 𝔸) → ntm F X 𝔸
  | abs : 𝔸 → ntm F X 𝔸 → ntm F X 𝔸

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

/-- Permutation action on nominal terms: applies `π` to all atoms in the term. -/
def ntm.permute (π : LPerm 𝔸) : ntm F X 𝔸 → ntm F X 𝔸
    | ntm.atm a       => ntm.atm (LPermApply π a)
    | ntm.mvar σ x    => ntm.mvar (σ ++ π) x
    | ntm.fapp f ts   => ntm.fapp f (ts.map (ntm.permute π))
    | ntm.abs a t     => ntm.abs (LPermApply π a) (ntm.permute π t)

/-- Size of a nominal term, used as a termination measure. -/
def ntmSize : ntm F X 𝔸 → ℕ
  | ntm.atm _      => 1
  | ntm.mvar _ _   => 1
  | ntm.fapp _ ts  => 1 + ntmSizeList ts
  | ntm.abs _ t    => 1 + ntmSize t
where
  ntmSizeList : List (ntm F X 𝔸) → ℕ
    | []      => 0
    | t :: ts => ntmSize t + ntmSizeList ts

/-- Elements of a list have size strictly less than the whole `fapp` term. -/
lemma ntmSize_lt_of_mem (t : ntm F X 𝔸) (ts : List (ntm F X 𝔸)) (h : t ∈ ts) :
    ntmSize t < 1 + ntmSize.ntmSizeList ts := by
  induction ts with
  | nil => exact absurd h (List.not_mem_nil)
  | cons hd tl ih =>
    simp only [ntmSize.ntmSizeList]
    rcases List.mem_cons.mp h with heq | hmem
    · subst heq; omega
    · have := ih hmem; omega

/-- The empty permutation acts as the identity on terms. -/
lemma ntm.permute_nil (t : ntm F X 𝔸) : ntm.permute [] t = t := by
  match t with
  | ntm.atm a => simp [ntm.permute]
  | .mvar π x => simp [ntm.permute]
  | .fapp f ts =>
    simp only [ntm.permute]
    congr 1
    conv_rhs => rw [show ts = ts.map id from (List.map_id ts).symm]
    apply List.map_congr_left
    intro t ht
    exact ntm.permute_nil t
  | .abs a t =>
    simp only [permute, LPermApply_nil, abs.injEq, true_and]
    exact ntm.permute_nil t
termination_by ntmSize t
decreasing_by
  · exact ntmSize_lt_of_mem _ _ ‹_›
  · simp [ntmSize]

/-- Permutation composition: permuting by `π` then `π'` equals permuting by `π ++ π'`. -/
lemma ntm.permute_append (u : ntm F X 𝔸) (π₁ π₂ : LPerm 𝔸) :
    ntm.permute π₂ (ntm.permute π₁ u) = ntm.permute (π₁ ++ π₂) u := by
  match u with
  | .atm a => simp [ntm.permute, LPermApply_append]
  | .mvar σ x => simp [ntm.permute, List.append_assoc]
  | .fapp f ts =>
    simp only [ntm.permute, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t ht
    exact ntm.permute_append t π₁ π₂
  | .abs a t =>
    simp only [ntm.permute, LPermApply_append]
    rw [ntm.permute_append t π₁ π₂]

end Nominal
