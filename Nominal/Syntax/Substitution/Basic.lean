import Nominal.Syntax.Terms

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

/-- A substitution is a list of bindings `[X₁ ↦ s₁, …, Xₙ ↦ sₙ]`, applied left-to-right -/
abbrev Subst (F X 𝔸 : Type*) [DecidableEq F] [DecidableEq X] [Name 𝔸] :=
  List (X × ntm F X 𝔸)

/-- The action of a single binding `[Y ↦ s]` on a term: every suspended occurrence
    `π·Y` becomes `π·s`; other variables are unchanged. -/
def ntm.applyOne : ntm F X 𝔸 → X → ntm F X 𝔸 → ntm F X 𝔸
  | .atm a,     _, _ => .atm a
  | .mvar π x,  Y, s => if x = Y then s.permute π else .mvar π x
  | .fapp f ts, Y, s => .fapp f (ts.map (fun t => t.applyOne Y s))
  | .abs a t,   Y, s => .abs a (t.applyOne Y s)

/-- The action of a substitution on a term: apply each binding from left to right. -/
def ntm.subst : ntm F X 𝔸 → Subst F X 𝔸 → ntm F X 𝔸
  | t, []          => t
  | t, (Y, s) :: σ => (t.applyOne Y s).subst σ

@[simp] lemma ntm.subst_nil (t : ntm F X 𝔸) : t.subst [] = t := rfl

@[simp] lemma ntm.subst_cons (t : ntm F X 𝔸) (Y : X) (s : ntm F X 𝔸) (σ : Subst F X 𝔸) :
    t.subst ((Y, s) :: σ) = (t.applyOne Y s).subst σ := rfl

/-- `[Y ↦ s]` and a permutation commute on terms. -/
lemma ntm.applyOne_permute (t : ntm F X 𝔸) (Y : X) (s : ntm F X 𝔸) (π : LPerm 𝔸) :
    (t.permute π).applyOne Y s = (t.applyOne Y s).permute π := by
  match t with
  | .atm a => simp [permute, applyOne]
  | .mvar σ x =>
    simp only [permute, applyOne]
    by_cases hx : x = Y
    · rw [if_pos hx, if_pos hx]
      exact (permute_append s σ π).symm
    · rw [if_neg hx, if_neg hx, permute]
  | .fapp f ts =>
    simp only [permute, applyOne, List.map_map]
    congr 1
    apply List.map_congr_left
    intro u hu
    exact ntm.applyOne_permute u Y s π
  | .abs a t' =>
    simp only [permute, applyOne]
    rw [ntm.applyOne_permute t' Y s π]

/-- Substitution and permutation commute, `π·(tσ) ≡ (π·t)σ`. -/
lemma ntm.subst_permute (t : ntm F X 𝔸) (π : LPerm 𝔸) (σ : Subst F X 𝔸) :
    (t.permute π).subst σ = (t.subst σ).permute π := by
  induction σ generalizing t with
  | nil => rfl
  | cons p σ' ih =>
    obtain ⟨Y, s⟩ := p
    simp only [subst_cons]
    rw [applyOne_permute, ih]

end Nominal
