import Nominal.Syntax.Terms
import Nominal.Syntax.Ds

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

/-- Freshness context: a finite set of pairs `(a, X)` meaning atom `a` is fresh for metavariable `X`. -/
abbrev Context (𝔸 X : Type*) [Name 𝔸] [DecidableEq X] := Finset (𝔸 × X)

mutual
  /-- Decidable freshness: `fresh Γ a t` checks whether atom `a` is fresh for term `t` under context `Γ`. -/
  def fresh
    (Γ : Context 𝔸 X) (a : 𝔸) : ntm F X 𝔸 → Bool
    | ntm.atm b       => a ≠ b                            -- (#ab)
    | ntm.mvar π x    => (LPermApply π.reverse a, x) ∈ Γ  -- (#X)
    | ntm.fapp _ ts   => freshList Γ a ts                 -- (#f)/(#tup)
    | ntm.abs b t     => a = b ∨ fresh Γ a t              -- (#absa)/(#absb)

  /-- Auxiliary for `fresh`: checks freshness across a list of terms. -/
  def freshList
    (Γ : Context 𝔸 X) (a : 𝔸) : List (ntm F X 𝔸) → Bool
    | []      => true
    | t :: ts => fresh Γ a t ∧ freshList Γ a ts
end

/-- Freshness judgment: `Γ ⊢ a # t` means atom `a` is fresh for term `t` under context `Γ`. -/
notation Γ " ⊢ " a " # " t => fresh Γ a t

lemma fresh_atm (Γ : Context 𝔸 X) (a b : 𝔸) :
    (Γ ⊢ a # ntm.atm (F := F) b) = (a ≠ b) := by
  simp [fresh]

lemma fresh_abs_same (Γ : Context 𝔸 X) (a : 𝔸) (t : ntm F X 𝔸) :
    (Γ ⊢ a # ntm.abs a t) = true := by
  simp [fresh]

lemma fresh_mvar_id (Γ : Context 𝔸 X) (a : 𝔸) (x : X) :
    (Γ ⊢ a # ntm.mvar (F := F) [] x) = ((a, x) ∈ Γ) := by
  simp [fresh]

mutual
  /-- Freshness is equivariant: permuting both the atom and the term preserves freshness. -/
  theorem fresh_equivariance (Γ : Context 𝔸 X) (a : 𝔸)
  (t : ntm F X 𝔸) (π : LPerm 𝔸) :
  (Γ ⊢ a # t) = (Γ ⊢ LPermApply π a # t.permute π) := by
    match t with
    | ntm.atm b =>
      simp only [fresh, ntm.permute]
      have h := (LPermApply_injective π).eq_iff (a := a) (b := b)
      simp [h]

    | ntm.mvar σ x =>
      simp only [fresh, ntm.permute]
      simp only [List.reverse_append]
      simp only [LPermApply_append]
      simp only [LPermApply_reverse_left]
    | ntm.fapp f ts =>
      simp only [fresh, ntm.permute]
      exact freshList_equivariance Γ a ts π

    | ntm.abs b t =>
      simp only [fresh, ntm.permute]
      rw [fresh_equivariance Γ a t π]
      congr 1
      simp [(LPermApply_injective π).eq_iff]

  /-- Collects all atoms appearing in a list permutation. -/
  theorem freshList_equivariance (Γ : Context 𝔸 X) (a : 𝔸) (ts : List (ntm F X 𝔸)) (π : LPerm 𝔸) :
      freshList Γ a ts = freshList Γ (LPermApply π a) (ts.map (ntm.permute π)) := by
    match ts with
    | [] => simp [freshList]
    | t :: ts =>
      simp only [freshList, List.map_cons]
      rw [fresh_equivariance Γ a t π]
      rw [freshList_equivariance Γ a ts π]
end

mutual
/-- If `π` and `π'` agree on all atoms, permuting a term by either gives the same freshness
    judgement. -/
  theorem fresh_permute_ds_empty (Γ : Context 𝔸 X) (a : 𝔸) (s : ntm F X 𝔸) (π π' : LPerm 𝔸)
      (h : ds π π' = ∅) :
      (Γ ⊢ a # ntm.permute π s) = (Γ ⊢ a # ntm.permute π' s) := by
    match s with
    | ntm.atm b =>
      simp only [ntm.permute, fresh, ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_not,
        decide_eq_decide]
      rw [LPermApply_eq_of_ds_empty π π' h b]

    | ntm.mvar σ x =>
      simp only [ntm.permute, fresh, List.reverse_append, decide_eq_decide]
      rw [LPermApply_append, LPermApply_append, LPermApply_reverse_eq_of_ds_empty π π' h]

    | ntm.fapp f ts =>
      simp only [ntm.permute, fresh]
      exact freshList_permute_ds_empty Γ a ts π π' h

    | ntm.abs b t =>
      simp only [ntm.permute, fresh, Bool.decide_or, Bool.decide_eq_true]
      rw [LPermApply_eq_of_ds_empty π π' h, fresh_permute_ds_empty Γ a t π π' h]

  theorem freshList_permute_ds_empty (Γ : Context 𝔸 X) (a : 𝔸) (ts : List (ntm F X 𝔸))
      (π π' : LPerm 𝔸) (h : ds π π' = ∅) :
      freshList Γ a (ts.map (ntm.permute π)) = freshList Γ a (ts.map (ntm.permute π')) := by
    match ts with
    | [] => simp [freshList]
    | t :: ts' =>
      simp only [List.map_cons, freshList]
      rw [fresh_permute_ds_empty Γ a t π π' h,
          freshList_permute_ds_empty Γ a ts' π π' h]
end

end Nominal
