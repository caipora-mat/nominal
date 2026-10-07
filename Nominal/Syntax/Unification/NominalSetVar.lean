import Nominal.Syntax.Unification.NominalSet
import Nominal.Syntax.Unification.Metavars

/-!
# Nominal sets over metavariables

Renaming metavariables is a permutation action as well: terms, freshness contexts, substitutions
and problems form nominal sets over the metavariables, each element supported by the
metavariables occurring in it, and `UnifProblem.solve` is an equivariant function between them
(`UnifProblem.solve_isEquivariant_var`). This requires infinitely many metavariables (`Name X`).

`Nominal.Set` associates a single type of atoms to each carrier, and the syntax is already
nominal over the atoms `𝔸`. The instances for the action on metavariables are therefore declared
on the type synonym `ByVar`.
-/

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [Name X] [Name 𝔸]

/-- Type synonym carrying the nominal-set structure over metavariables. -/
def ByVar (α : Type*) : Type _ := α

/-! ### Action laws and supports -/

lemma ntm.renameVar_mul (τ τ' : Equiv.Perm X) (t : ntm F X 𝔸) :
    t.renameVar (τ * τ') = (t.renameVar τ').renameVar τ := by
  simpa using ntm.relabel_mul 1 1 τ τ' t

mutual
  /-- A renaming fixing every metavariable of a term leaves the term unchanged. -/
  lemma ntm.renameVar_eq_self (τ : Equiv.Perm X) (t : ntm F X 𝔸)
      (h : ∀ x ∈ t.metavars, τ x = x) : t.renameVar τ = t := by
    match t with
    | .atm a => simp
    | .mvar π x =>
      simp only [ntm.relabel_mvar, LPerm.rename_one, ntm.mvar.injEq, true_and]
      exact h x (by simp [ntm.metavars])
    | .fapp f ts =>
      simp only [ntm.relabel_fapp, ntm.fapp.injEq, true_and]
      exact ntmList.renameVar_eq_self τ ts fun x hx => h x (by simpa [ntm.metavars] using hx)
    | .abs a t =>
      simp only [ntm.relabel_abs, Equiv.Perm.coe_one, id_eq, ntm.abs.injEq, true_and]
      exact ntm.renameVar_eq_self τ t fun x hx => h x (by simpa [ntm.metavars] using hx)

  lemma ntmList.renameVar_eq_self (τ : Equiv.Perm X) (ts : List (ntm F X 𝔸))
      (h : ∀ x ∈ ntmList.metavars ts, τ x = x) : ts.map (ntm.renameVar τ) = ts := by
    match ts with
    | [] => rfl
    | t :: ts =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨ntm.renameVar_eq_self τ t fun x hx => h x (by simp [ntmList.metavars, hx]),
        ntmList.renameVar_eq_self τ ts fun x hx => h x (by simp [ntmList.metavars, hx])⟩
end

lemma Context.renameVar_one (Γ : Context 𝔸 X) : Context.renameVar 1 Γ = Γ := by
  ext p; simp [Context.relabel, Finset.mem_map_equiv]

lemma Context.renameVar_mul (τ τ' : Equiv.Perm X) (Γ : Context 𝔸 X) :
    Context.renameVar (τ * τ') Γ = Context.renameVar τ (Context.renameVar τ' Γ) := by
  ext ⟨a, x⟩; simp [Context.relabel, Finset.mem_map_equiv, Equiv.Perm.mul_def]

/-- Metavariables of a context: those occurring in some `a # X`. -/
def Context.metavars (Γ : Context 𝔸 X) : Finset X := Γ.image Prod.snd

lemma Context.renameVar_eq_self (τ : Equiv.Perm X) (Γ : Context 𝔸 X)
    (h : ∀ x ∈ Γ.metavars, τ x = x) : Context.renameVar τ Γ = Γ := by
  have hfix : ∀ a x, (a, x) ∈ Γ → τ x = x := fun a x hp =>
    h x (Finset.mem_image.mpr ⟨(a, x), hp, rfl⟩)
  ext ⟨a, x⟩
  simp only [Context.relabel, Finset.mem_map_equiv]
  simp only [Equiv.prodCongr_symm, Equiv.prodCongr_apply, Equiv.Perm.one_symm, Equiv.Perm.coe_one,
    Prod.map_apply, id_eq]
  constructor
  · intro hp
    have h1 := hfix a _ hp
    rw [Equiv.apply_symm_apply] at h1
    rwa [← h1] at hp
  · intro hp
    have h2 : τ.symm x = x := by rw [Equiv.symm_apply_eq]; exact (hfix a x hp).symm
    rwa [h2]

lemma Subst.renameVar_one (σ : Subst F X 𝔸) : Subst.renameVar 1 σ = σ := by
  simp [Subst.relabel, ntm.relabel_one]

lemma Subst.renameVar_mul (τ τ' : Equiv.Perm X) (σ : Subst F X 𝔸) :
    Subst.renameVar (τ * τ') σ = Subst.renameVar τ (Subst.renameVar τ' σ) := by
  simp [Subst.relabel, ntm.renameVar_mul, Function.comp_def]

/-- Metavariables of a substitution: those it binds and those of its bound terms. -/
def Subst.metavars (σ : Subst F X 𝔸) : Finset X :=
  σ.foldr (fun p acc => insert p.1 (p.2.metavars ∪ acc)) ∅

lemma Subst.renameVar_eq_self (τ : Equiv.Perm X) (σ : Subst F X 𝔸)
    (h : ∀ x ∈ σ.metavars, τ x = x) : Subst.renameVar τ σ = σ := by
  induction σ with
  | nil => rfl
  | cons p σ ih =>
    obtain ⟨x, t⟩ := p
    simp only [Subst.metavars, List.foldr_cons, Finset.mem_insert, Finset.mem_union] at h ih
    simp only [Subst.relabel_cons, List.cons.injEq, Prod.mk.injEq]
    exact ⟨⟨h x (Or.inl rfl), ntm.renameVar_eq_self τ t fun y hy => h y (Or.inr (Or.inl hy))⟩,
      ih fun y hy => h y (Or.inr (Or.inr hy))⟩

lemma UnifConstraint.renameVar_one (c : UnifConstraint F X 𝔸) : c.relabel 1 1 = c := by
  cases c <;> simp [UnifConstraint.relabel, ntm.relabel_one]

lemma UnifConstraint.renameVar_mul (τ τ' : Equiv.Perm X) (c : UnifConstraint F X 𝔸) :
    c.relabel 1 (τ * τ') = (c.relabel 1 τ').relabel 1 τ := by
  cases c <;> simp [UnifConstraint.relabel, ntm.renameVar_mul]

lemma UnifConstraint.renameVar_eq_self (τ : Equiv.Perm X) (c : UnifConstraint F X 𝔸)
    (h : ∀ x ∈ c.metavars, τ x = x) : c.relabel 1 τ = c := by
  cases c with
  | fresh a t =>
    simp only [UnifConstraint.relabel, Equiv.Perm.coe_one, id_eq, UnifConstraint.fresh.injEq,
      true_and]
    exact ntm.renameVar_eq_self τ t h
  | unif s t =>
    simp only [UnifConstraint.metavars, Finset.mem_union] at h
    simp only [UnifConstraint.relabel, UnifConstraint.unif.injEq]
    exact ⟨ntm.renameVar_eq_self τ s fun x hx => h x (Or.inl hx),
      ntm.renameVar_eq_self τ t fun x hx => h x (Or.inr hx)⟩

lemma UnifProblem.renameVar_one (Pr : UnifProblem F X 𝔸) : Pr.renameVar 1 = Pr := by
  induction Pr <;> simp_all [UnifConstraint.renameVar_one]

lemma UnifProblem.renameVar_mul (τ τ' : Equiv.Perm X) (Pr : UnifProblem F X 𝔸) :
    Pr.renameVar (τ * τ') = (Pr.renameVar τ').renameVar τ := by
  simp [UnifProblem.relabel, UnifConstraint.renameVar_mul, Function.comp_def]

lemma UnifProblem.renameVar_eq_self (τ : Equiv.Perm X) (Pr : UnifProblem F X 𝔸)
    (h : ∀ x ∈ UnifProblem.allMetavars Pr, τ x = x) : Pr.renameVar τ = Pr := by
  induction Pr with
  | nil => rfl
  | cons c Pr ih =>
    simp only [UnifProblem.allMetavars_cons, Finset.mem_union] at h
    simp only [UnifProblem.relabel_cons, List.cons.injEq]
    exact ⟨UnifConstraint.renameVar_eq_self τ c fun x hx => h x (Or.inl hx),
      ih fun x hx => h x (Or.inr hx)⟩

/-! ### Nominal-set instances -/

instance ntm.instPermTypeVar : Set.PermType X (ByVar (ntm F X 𝔸)) where
  smul π t := ntm.renameVar (π : Equiv.Perm X) t
  one_smul t := ntm.relabel_one t
  mul_smul π σ t := ntm.renameVar_mul (π : Equiv.Perm X) σ t

instance Context.instPermTypeVar : Set.PermType X (ByVar (Context 𝔸 X)) where
  smul π Γ := Context.renameVar (π : Equiv.Perm X) Γ
  one_smul Γ := Context.renameVar_one Γ
  mul_smul π σ Γ := Context.renameVar_mul (π : Equiv.Perm X) σ Γ

instance Subst.instPermTypeVar : Set.PermType X (ByVar (Subst F X 𝔸)) where
  smul π σ := Subst.renameVar (π : Equiv.Perm X) σ
  one_smul σ := Subst.renameVar_one σ
  mul_smul π τ σ := Subst.renameVar_mul (π : Equiv.Perm X) τ σ

instance UnifProblem.instPermTypeVar : Set.PermType X (ByVar (UnifProblem F X 𝔸)) where
  smul π Pr := UnifProblem.renameVar (π : Equiv.Perm X) Pr
  one_smul Pr := UnifProblem.renameVar_one Pr
  mul_smul π σ Pr := UnifProblem.renameVar_mul (π : Equiv.Perm X) σ Pr

lemma UnifProblem.smul_def_var (π : FinitePerm X) (Pr : ByVar (UnifProblem F X 𝔸)) :
    π • Pr = UnifProblem.renameVar (π : Equiv.Perm X) Pr := rfl

/-- **Nominal terms form a nominal set over metavariables**: each term is supported by its
    metavariables. -/
instance ntm.instNominalVar : Set.Nominal X (ByVar (ntm F X 𝔸)) where
  __ := ntm.instPermTypeVar
  finSupp t := ⟨ntm.metavars (F := F) (𝔸 := 𝔸) t, fun π hπ =>
    ntm.renameVar_eq_self _ t fun x hx => hπ (by simpa using hx)⟩

instance Context.instNominalVar : Set.Nominal X (ByVar (Context 𝔸 X)) where
  __ := Context.instPermTypeVar
  finSupp Γ := ⟨Context.metavars (𝔸 := 𝔸) Γ, fun π hπ =>
    Context.renameVar_eq_self _ Γ fun x hx => hπ (by simpa using hx)⟩

instance Subst.instNominalVar : Set.Nominal X (ByVar (Subst F X 𝔸)) where
  __ := Subst.instPermTypeVar
  finSupp σ := ⟨Subst.metavars (F := F) (𝔸 := 𝔸) σ, fun π hπ =>
    Subst.renameVar_eq_self _ σ fun x hx => hπ (by simpa using hx)⟩

instance UnifProblem.instNominalVar : Set.Nominal X (ByVar (UnifProblem F X 𝔸)) where
  __ := UnifProblem.instPermTypeVar
  finSupp Pr := ⟨UnifProblem.allMetavars (F := F) (𝔸 := 𝔸) Pr, fun π hπ =>
    UnifProblem.renameVar_eq_self _ Pr fun x hx => hπ (by simpa using hx)⟩

/-! ### The algorithm is a morphism of nominal sets over metavariables -/

/-- `solve`, between the carriers of the action on metavariables. -/
def UnifProblem.solveByVar (Pr : ByVar (UnifProblem F X 𝔸)) :
    Option (ByVar (Context 𝔸 X) × ByVar (Subst F X 𝔸)) :=
  UnifProblem.solve Pr

/-- **`solve` is equivariant in metavariables**, in the sense of `Nominal.Set`: a morphism of
    nominal sets over the metavariables. -/
theorem UnifProblem.solve_isEquivariant_var :
    Set.IsEquivariant X (UnifProblem.solveByVar (F := F) (X := X) (𝔸 := 𝔸)) where
  map_smul π Pr := by
    rw [UnifProblem.smul_def_var]
    unfold UnifProblem.solveByVar
    rw [UnifProblem.solve_renameVar]
    cases UnifProblem.solve Pr with
    | none => rfl
    | some r => rfl

end Nominal
