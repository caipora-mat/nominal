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

-- (Simultaneous substitution.)

/-- Look up the term bound to `x` in `σ` (first match wins). -/
def Subst.lookup : Subst F X 𝔸 → X → Option (ntm F X 𝔸)
  | [],          _ => none
  | (Y, s) :: σ, x => if x = Y then some s else Subst.lookup σ x

@[simp] lemma Subst.lookup_nil (x : X) : Subst.lookup ([] : Subst F X 𝔸) x = none := rfl

@[simp] lemma Subst.lookup_cons (Y : X) (s : ntm F X 𝔸) (σ : Subst F X 𝔸) (x : X) :
    Subst.lookup ((Y, s) :: σ) x = if x = Y then some s else Subst.lookup σ x := rfl

/-- `tσ`: replace every suspended occurrence `π·x` by `π·(σ x)` in one pass. -/
def ntm.subst : ntm F X 𝔸 → Subst F X 𝔸 → ntm F X 𝔸
  | .atm a,     _ => .atm a
  | .mvar π x,  σ => match σ.lookup x with
                    | some s => s.permute π
                    | none   => .mvar π x
  | .fapp f ts, σ => .fapp f (ts.map fun t => t.subst σ)
  | .abs a t,   σ => .abs a (t.subst σ)

-- (Shape lemmas — now definitional.)

@[simp] lemma ntm.subst_atm (b : 𝔸) (σ : Subst F X 𝔸) :
    (ntm.atm (F := F) (X := X) b).subst σ = ntm.atm b := by
  simp only [ntm.subst]

@[simp] lemma ntm.subst_fapp (f : F) (ts : List (ntm F X 𝔸)) (σ : Subst F X 𝔸) :
    (ntm.fapp f ts).subst σ = ntm.fapp f (ts.map (·.subst σ)) := by
  simp only [ntm.subst]

@[simp] lemma ntm.subst_abs (b : 𝔸) (t : ntm F X 𝔸) (σ : Subst F X 𝔸) :
    (ntm.abs b t).subst σ = ntm.abs b (t.subst σ) := by
  simp only [ntm.subst]

/-- On a bare metavariable, `subst` is the raw lookup (or the variable itself). -/
lemma ntm.subst_mvar_nil (y : X) (σ : Subst F X 𝔸) :
    (ntm.mvar (F := F) [] y).subst σ = (Subst.lookup σ y).getD (ntm.mvar [] y) := by
  simp only [ntm.subst]; cases Subst.lookup σ y <;> simp [ntm.permute_nil]

/-- `mvar π y` under `σ`: apply `σ` to the bare mvar, then re-suspend `π`. -/
lemma ntm.subst_mvar (π : LPerm 𝔸) (y : X) (σ : Subst F X 𝔸) :
    (ntm.mvar π y).subst σ = ((ntm.mvar (F := F) [] y).subst σ).permute π := by
  simp only [ntm.subst]; cases σ.lookup y <;> simp [ntm.permute, ntm.permute_nil]

mutual
@[simp] lemma ntm.subst_nil : ∀ (t : ntm F X 𝔸), t.subst [] = t
  | .atm _ => by simp only [ntm.subst]
  | .mvar π x => by simp only [ntm.subst, Subst.lookup_nil]
  | .fapp f ts => by simp only [ntm.subst_fapp, ntm.substList_nil ts]
  | .abs a t => by simp only [ntm.subst_abs, ntm.subst_nil t]
lemma ntm.substList_nil : ∀ (ts : List (ntm F X 𝔸)), ts.map (·.subst []) = ts
  | [] => rfl
  | t :: ts' => by simp only [List.map_cons, ntm.subst_nil t, ntm.substList_nil ts']
end

-- (Single binding [Y↦s] on a term = subst by a singleton; still a useful shape.)

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
lemma ntm.subst_permute : ∀ (t : ntm F X 𝔸) (π : LPerm 𝔸) (σ : Subst F X 𝔸),
    (t.permute π).subst σ = (t.subst σ).permute π
  | .atm a, π, σ => by simp only [ntm.permute, ntm.subst]
  | .mvar ρ x, π, σ => by
      simp only [ntm.permute, ntm.subst]
      cases σ.lookup x <;> simp [ntm.permute, ntm.permute_append]
  | .fapp f ts, π, σ => by
      simp only [ntm.permute, ntm.subst_fapp, List.map_map]
      congr 1
      exact List.map_congr_left (fun t _ => ntm.subst_permute t π σ)
  | .abs a t, π, σ => by
      simp only [ntm.permute, ntm.subst_abs]
      rw [ntm.subst_permute t π σ]

-- (Composition of simultaneous substitutions.)
-- Under simultaneous substitution, `subst (σ ++ τ) ≠ (subst σ) ∘ subst τ` in
-- general (append prepends bindings, it does not compose them).  The correct
-- composition applies `τ` to the *range* of `σ` and then appends `τ`.

/-- Composition: `t.subst (σ.comp τ) = (t.subst σ).subst τ`.  Applies `τ` to each
    value of `σ`, then falls back to `τ` for variables outside `dom σ`. -/
def Subst.comp (σ τ : Subst F X 𝔸) : Subst F X 𝔸 :=
  σ.map (fun p => (p.1, p.2.subst τ)) ++ τ

lemma Subst.lookup_append (σ τ : Subst F X 𝔸) (x : X) :
    Subst.lookup (σ ++ τ) x = (Subst.lookup σ x).orElse (fun _ => Subst.lookup τ x) := by
  induction σ with
  | nil => rfl
  | cons p σ' ih =>
      obtain ⟨Y, s⟩ := p
      simp only [List.cons_append, Subst.lookup_cons]
      split <;> simp [ih]

lemma Subst.lookup_map_subst (σ τ : Subst F X 𝔸) (x : X) :
    Subst.lookup (σ.map (fun p => (p.1, p.2.subst τ))) x
      = (Subst.lookup σ x).map (·.subst τ) := by
  induction σ with
  | nil => rfl
  | cons p σ' ih =>
      obtain ⟨Y, s⟩ := p
      simp only [List.map_cons, Subst.lookup_cons, ih]
      split <;> rfl

/-- Composition law on a bare metavariable. -/
lemma ntm.subst_mvar_nil_comp (x : X) (σ τ : Subst F X 𝔸) :
    (ntm.mvar (F := F) [] x).subst (σ.comp τ)
      = ((ntm.mvar (F := F) [] x).subst σ).subst τ := by
  rw [Subst.comp, ntm.subst_mvar_nil, ntm.subst_mvar_nil, Subst.lookup_append,
      Subst.lookup_map_subst]
  cases Subst.lookup σ x with
  | some s => simp
  | none => simp [ntm.subst_mvar_nil]

/-- Composition law: `t.subst (σ.comp τ) = (t.subst σ).subst τ` for every term. -/
lemma ntm.subst_comp : ∀ (t : ntm F X 𝔸) (σ τ : Subst F X 𝔸),
    t.subst (σ.comp τ) = (t.subst σ).subst τ
  | .atm a, _, _ => by simp
  | .mvar π x, σ, τ => by
      rw [ntm.subst_mvar π x (σ.comp τ), ntm.subst_mvar_nil_comp,
          ntm.subst_mvar π x σ, ntm.subst_permute]
  | .fapp f ts, σ, τ => by
      simp only [ntm.subst_fapp, List.map_map]
      congr 1
      exact List.map_congr_left (fun t _ => ntm.subst_comp t σ τ)
  | .abs a t, σ, τ => by
      simp only [ntm.subst_abs]
      rw [ntm.subst_comp t σ τ]

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
