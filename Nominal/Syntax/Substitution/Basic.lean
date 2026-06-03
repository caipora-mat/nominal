import Nominal.Syntax.Terms

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

-- (Definition 4: Substitution).
-- σ ::= Id | [X↦s]σ
-- Represented as a list: [] = Id, (Y, s) :: σ = [Y↦s]σ.

/-- A substitution is a list of variable-term bindings, applied left-to-right. -/
abbrev Subst (F X 𝔸 : Type*) [DecidableEq F] [DecidableEq X] [Name 𝔸] :=
  List (X × ntm F X 𝔸)

-- (Action of a single binding [Y↦s] on a term).

/-- `t[Y↦s]`: replace every suspended occurrence `π·Y` with `π·s`; leave all else unchanged. -/
def ntm.applyOne : ntm F X 𝔸 → X → ntm F X 𝔸 → ntm F X 𝔸
  | .atm a,     _, _ => .atm a
  | .mvar π x,  Y, s => if x = Y then s.permute π else .mvar π x
  | .fapp f ts, Y, s => .fapp f (ts.map fun t => t.applyOne Y s)
  | .abs a t,   Y, s => .abs a (t.applyOne Y s)

-- (σ acts elementwise: tId ≡ t, t[X↦s]σ ≡ (t[X↦s])σ).

/-- `tσ`: apply each binding in `σ` from left to right. -/
def ntm.subst : ntm F X 𝔸 → Subst F X 𝔸 → ntm F X 𝔸
  | t, []            => t
  | t, (Y, s) :: σ  => (t.applyOne Y s).subst σ

@[simp] lemma ntm.subst_nil (t : ntm F X 𝔸) : t.subst [] = t := rfl

@[simp] lemma ntm.subst_cons (t : ntm F X 𝔸) (Y : X) (s : ntm F X 𝔸) (σ : Subst F X 𝔸) :
    t.subst ((Y, s) :: σ) = (t.applyOne Y s).subst σ := rfl

-- (Lemma 5: π·(tσ) ≡ (π·t)σ).

/-- Single-step: `(π·t)[Y↦s] ≡ π·(t[Y↦s])`. -/
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

/-- Lemma 5: substitution and permutation commute: `π·(tσ) ≡ (π·t)σ`. -/
lemma ntm.subst_permute (t : ntm F X 𝔸) (π : LPerm 𝔸) (σ : Subst F X 𝔸) :
    (t.permute π).subst σ = (t.subst σ).permute π := by
  induction σ generalizing t with
  | nil => rfl
  | cons p σ' ih =>
    obtain ⟨Y, s⟩ := p
    simp only [subst_cons]
    rw [applyOne_permute, ih]

-- (Shape lemmas for subst on each constructor).

@[simp] lemma ntm.subst_atm (b : 𝔸) (σ : Subst F X 𝔸) :
    (ntm.atm (F := F) (X := X) b).subst σ = ntm.atm b := by
  induction σ with
  | nil => rfl
  | cons p σ' ih =>
    obtain ⟨_, _⟩ := p
    simp [ntm.subst_cons, ntm.applyOne, ih]

@[simp] lemma ntm.subst_fapp (f : F) (ts : List (ntm F X 𝔸)) (σ : Subst F X 𝔸) :
    (ntm.fapp f ts).subst σ = ntm.fapp f (ts.map (·.subst σ)) := by
  induction σ generalizing ts with
  | nil => simp
  | cons p σ' ih =>
    obtain ⟨Y, s⟩ := p
    simp only [ntm.subst_cons, ntm.applyOne]
    rw [ih]
    simp [List.map_map, Function.comp]

@[simp] lemma ntm.subst_abs (b : 𝔸) (t : ntm F X 𝔸) (σ : Subst F X 𝔸) :
    (ntm.abs b t).subst σ = ntm.abs b (t.subst σ) := by
  induction σ generalizing t with
  | nil => rfl
  | cons p σ' ih =>
    obtain ⟨Y, s⟩ := p
    simp only [ntm.subst_cons, ntm.applyOne]
    exact ih _

lemma ntm.subst_mvar (π : LPerm 𝔸) (y : X) (σ : Subst F X 𝔸) :
    (ntm.mvar π y).subst σ = ((ntm.mvar (F := F) [] y).subst σ).permute π := by
  have : ntm.mvar π y = ntm.permute π (ntm.mvar (F := F) [] y) := by simp [ntm.permute]
  rw [this]
  exact ntm.subst_permute _ _ _

-- (Idempotence — condition (2) of Definition 27).

/-- A substitution is idempotent: `Xσ ≡ Xσσ` for all `X`. -/
def Subst.IsIdempotent (σ : Subst F X 𝔸) : Prop :=
  ∀ x : X, (ntm.mvar (F := F) [] x).subst σ = ((ntm.mvar (F := F) [] x).subst σ).subst σ

-- (Domain of a substitution).

/-- The set of variables on the left-hand side of bindings in `σ`. -/
def Subst.dom (σ : Subst F X 𝔸) : Finset X :=
  (σ.map Prod.fst).toFinset

@[simp] lemma Subst.dom_nil : Subst.dom ([] : Subst F X 𝔸) = ∅ := by
  simp [Subst.dom]

@[simp] lemma Subst.dom_cons (x : X) (s : ntm F X 𝔸) (σ : Subst F X 𝔸) :
    Subst.dom ((x, s) :: σ) = insert x (Subst.dom σ) := by
  simp [Subst.dom]

@[simp] lemma Subst.dom_append (σ σ' : Subst F X 𝔸) :
    Subst.dom (σ ++ σ') = Subst.dom σ ∪ Subst.dom σ' := by
  simp [Subst.dom, List.toFinset_append]

@[simp] lemma Subst.dom_singleton (x : X) (s : ntm F X 𝔸) :
    Subst.dom ([(x, s)] : Subst F X 𝔸) = {x} := by
  simp [Subst.dom]

end Nominal
