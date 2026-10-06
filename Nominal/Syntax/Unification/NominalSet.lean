import Nominal.Syntax.Unification.Equivariance
import Nominal.Syntax.TermsNominal
import Nominal.Set.Equivariant

/-!
# The unification algorithm as a morphism of nominal sets

Freshness contexts, substitutions, constraints and problems form nominal sets under the
meta-level renaming of atoms, and `UnifProblem.solve` is an equivariant function between them
(`UnifProblem.solve_isEquivariant`): a morphism of nominal sets. The solution relation is
equivariant as well (`UnifProblem.solutions_equivariantRel`).

The instances are declared on the abbreviations `Context`, `Subst` and `UnifProblem`, which
unfold to `Finset (𝔸 × X)` and lists. `Nominal.Set` has no generic instances for lists or for
finite sets of pairs, so they do not overlap with existing ones.
-/

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

/-! ### Action laws -/

lemma UnifConstraint.rename_one (c : UnifConstraint F X 𝔸) : c.rename 1 = c := by
  cases c <;> simp [UnifConstraint.rename, ntm.rename_one]

lemma UnifConstraint.rename_mul (ρ ρ' : Equiv.Perm 𝔸) (c : UnifConstraint F X 𝔸) :
    c.rename (ρ * ρ') = (c.rename ρ').rename ρ := by
  cases c <;> simp [UnifConstraint.rename, ntm.rename_mul]

lemma UnifProblem.rename_one (Pr : UnifProblem F X 𝔸) : Pr.rename 1 = Pr := by
  induction Pr <;> simp_all [UnifConstraint.rename_one]

lemma UnifProblem.rename_mul (ρ ρ' : Equiv.Perm 𝔸) (Pr : UnifProblem F X 𝔸) :
    Pr.rename (ρ * ρ') = (Pr.rename ρ').rename ρ := by
  simp [UnifProblem.rename, UnifConstraint.rename_mul, Function.comp_def]

/-! ### Permutation-type instances -/

instance UnifConstraint.instPermType : Set.PermType 𝔸 (UnifConstraint F X 𝔸) where
  smul π c := c.rename (π : Equiv.Perm 𝔸)
  one_smul c := UnifConstraint.rename_one c
  mul_smul π σ c := UnifConstraint.rename_mul (π : Equiv.Perm 𝔸) σ c

instance UnifProblem.instPermType : Set.PermType 𝔸 (UnifProblem F X 𝔸) where
  smul π Pr := Pr.rename (π : Equiv.Perm 𝔸)
  one_smul Pr := UnifProblem.rename_one Pr
  mul_smul π σ Pr := UnifProblem.rename_mul (π : Equiv.Perm 𝔸) σ Pr

lemma UnifProblem.smul_def (π : FinitePerm 𝔸) (Pr : UnifProblem F X 𝔸) :
    π • Pr = Pr.rename (π : Equiv.Perm 𝔸) := rfl

/-! ### Finite support -/

def UnifConstraint.atoms : UnifConstraint F X 𝔸 → Finset 𝔸
  | .fresh a t => insert a t.atoms
  | .unif s t  => s.atoms ∪ t.atoms

def UnifProblem.atoms (Pr : UnifProblem F X 𝔸) : Finset 𝔸 :=
  Pr.foldr (fun c acc => c.atoms ∪ acc) ∅

lemma UnifConstraint.rename_eq_self (ρ : Equiv.Perm 𝔸) (c : UnifConstraint F X 𝔸)
    (h : ∀ a ∈ c.atoms, ρ a = a) : c.rename ρ = c := by
  cases c with
  | fresh a t =>
    simp only [UnifConstraint.atoms, Finset.mem_insert] at h
    simp only [UnifConstraint.rename, UnifConstraint.fresh.injEq]
    exact ⟨h a (Or.inl rfl), ntm.rename_eq_self ρ t fun b hb => h b (Or.inr hb)⟩
  | unif s t =>
    simp only [UnifConstraint.atoms, Finset.mem_union] at h
    simp only [UnifConstraint.rename, UnifConstraint.unif.injEq]
    exact ⟨ntm.rename_eq_self ρ s fun b hb => h b (Or.inl hb),
      ntm.rename_eq_self ρ t fun b hb => h b (Or.inr hb)⟩

lemma UnifProblem.rename_eq_self (ρ : Equiv.Perm 𝔸) (Pr : UnifProblem F X 𝔸)
    (h : ∀ a ∈ Pr.atoms, ρ a = a) : Pr.rename ρ = Pr := by
  induction Pr with
  | nil => rfl
  | cons c Pr ih =>
    simp only [UnifProblem.atoms, List.foldr_cons, Finset.mem_union] at h ih
    simp only [UnifProblem.rename_cons, List.cons.injEq]
    exact ⟨UnifConstraint.rename_eq_self ρ c fun a ha => h a (Or.inl ha),
      ih fun a ha => h a (Or.inr ha)⟩

/-! ### Nominal-set instances -/

instance UnifConstraint.instNominal : Set.Nominal 𝔸 (UnifConstraint F X 𝔸) where
  __ := UnifConstraint.instPermType
  finSupp c := ⟨c.atoms, fun π hπ =>
    UnifConstraint.rename_eq_self _ c fun a ha => hπ (by simpa using ha)⟩

instance UnifProblem.instNominal : Set.Nominal 𝔸 (UnifProblem F X 𝔸) where
  __ := UnifProblem.instPermType
  finSupp Pr := ⟨Pr.atoms, fun π hπ =>
    UnifProblem.rename_eq_self _ Pr fun a ha => hπ (by simpa using ha)⟩

/-! ### The algorithm is a morphism of nominal sets -/

/-- **`solve` is equivariant**, in the sense of `Nominal.Set`: an equivariant function from
    problems to optional pairs of a context and a substitution. -/
theorem UnifProblem.solve_isEquivariant :
    Set.IsEquivariant 𝔸 (UnifProblem.solve (F := F) (X := X) (𝔸 := 𝔸)) where
  map_smul π Pr := by
    rw [UnifProblem.smul_def, UnifProblem.solve_rename]
    cases Pr.solve with
    | none => rfl
    | some r => rfl

/-- The solution relation `(Γ, σ) ∈ 𝒰(Pr)` is equivariant. -/
theorem UnifProblem.solutions_equivariantRel :
    Set.EquivariantRel 𝔸
      (fun (Pr : UnifProblem F X 𝔸) (p : Context 𝔸 X × Subst F X 𝔸) => p ∈ Pr.Solutions) where
  smul_iff π Pr p := by
    obtain ⟨Γ, σ⟩ := p
    exact UnifProblem.mem_solutions_rename (π : Equiv.Perm 𝔸) Pr Γ σ

end Nominal
