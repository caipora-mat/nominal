import Nominal.Syntax.Rename
import Nominal.Set.Nominal

/-!
# Nominal terms form a nominal set

Under the meta-level renaming of atoms (`ntm.rename`), finite permutations act on nominal
terms, and every term is supported by the finite set of atoms occurring in it. This connects
the syntax of the development with its nominal-sets layer (`Nominal.Set`).

The same holds for freshness contexts and substitutions. Their instances are declared on the
abbreviations `Context` and `Subst`, which unfold to `Finset (𝔸 × X)` and lists.
-/

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

mutual
  /-- Atoms occurring in a term, including those of suspended swaps. -/
  def ntm.atoms : ntm F X 𝔸 → Finset 𝔸
    | .atm a     => {a}
    | .mvar π _  => LPerm.atoms π
    | .fapp _ ts => ntmList.atoms ts
    | .abs a t   => insert a t.atoms

  def ntmList.atoms : List (ntm F X 𝔸) → Finset 𝔸
    | []      => ∅
    | t :: ts => t.atoms ∪ ntmList.atoms ts
end

lemma LPerm.rename_eq_self (ρ : Equiv.Perm 𝔸) (π : LPerm 𝔸)
    (h : ∀ a ∈ LPerm.atoms π, ρ a = a) : LPerm.rename ρ π = π := by
  induction π with
  | nil => rfl
  | cons s π ih =>
    obtain ⟨a, b⟩ := s
    simp only [LPerm.atoms, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h
    simp only [LPerm.rename_cons, h a (by simp), h b (by simp), List.cons.injEq, true_and]
    exact ih fun c hc => h c (Or.inr hc)

mutual
  /-- A renaming fixing every atom of a term leaves the term unchanged. -/
  lemma ntm.rename_eq_self (ρ : Equiv.Perm 𝔸) (t : ntm F X 𝔸)
      (h : ∀ a ∈ t.atoms, ρ a = a) : t.rename ρ = t := by
    match t with
    | .atm a => simp [h a (by simp [ntm.atoms])]
    | .mvar π x =>
      simp only [ntm.rename_mvar, ntm.mvar.injEq, and_true]
      exact LPerm.rename_eq_self ρ π fun a ha => h a ha
    | .fapp f ts =>
      simp only [ntm.rename_fapp, ntm.fapp.injEq, true_and]
      exact ntmList.rename_eq_self ρ ts fun a ha => h a (by simpa [ntm.atoms] using ha)
    | .abs a t =>
      simp only [ntm.rename_abs, ntm.abs.injEq]
      exact ⟨h a (by simp [ntm.atoms]),
        ntm.rename_eq_self ρ t fun b hb => h b (by simp [ntm.atoms, hb])⟩

  lemma ntmList.rename_eq_self (ρ : Equiv.Perm 𝔸) (ts : List (ntm F X 𝔸))
      (h : ∀ a ∈ ntmList.atoms ts, ρ a = a) : ts.map (ntm.rename ρ) = ts := by
    match ts with
    | [] => rfl
    | t :: ts =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨ntm.rename_eq_self ρ t fun a ha => h a (by simp [ntmList.atoms, ha]),
        ntmList.rename_eq_self ρ ts fun a ha => h a (by simp [ntmList.atoms, ha])⟩
end

/-- Finite permutations act on nominal terms by meta-level renaming. -/
instance ntm.instPermType : Set.PermType 𝔸 (ntm F X 𝔸) where
  smul π t := t.rename (π : Equiv.Perm 𝔸)
  one_smul t := ntm.rename_one t
  mul_smul π σ t := ntm.rename_mul (π : Equiv.Perm 𝔸) σ t

lemma ntm.smul_def (π : FinitePerm 𝔸) (t : ntm F X 𝔸) :
    π • t = t.rename (π : Equiv.Perm 𝔸) := rfl

/-- **Nominal terms form a nominal set**: each term is supported by its atoms. -/
instance ntm.instNominal : Set.Nominal 𝔸 (ntm F X 𝔸) where
  __ := ntm.instPermType
  finSupp t := ⟨t.atoms, fun π hπ => ntm.rename_eq_self _ t fun a ha => hπ (by simpa using ha)⟩

/-! ### Contexts and substitutions -/

lemma Context.rename_one (Γ : Context 𝔸 X) : Context.rename 1 Γ = Γ := by
  ext p; simp [Context.rename, Finset.mem_map_equiv]

lemma Context.rename_mul (ρ ρ' : Equiv.Perm 𝔸) (Γ : Context 𝔸 X) :
    Context.rename (ρ * ρ') Γ = Context.rename ρ (Context.rename ρ' Γ) := by
  ext ⟨a, x⟩; simp [Context.rename, Finset.mem_map_equiv, Equiv.Perm.mul_def]

lemma Subst.rename_one (σ : Subst F X 𝔸) : Subst.rename 1 σ = σ := by
  simp [Subst.rename, ntm.rename_one]

lemma Subst.rename_mul (ρ ρ' : Equiv.Perm 𝔸) (σ : Subst F X 𝔸) :
    Subst.rename (ρ * ρ') σ = Subst.rename ρ (Subst.rename ρ' σ) := by
  simp [Subst.rename, ntm.rename_mul, Function.comp_def]

instance Context.instPermType : Set.PermType 𝔸 (Context 𝔸 X) where
  smul π Γ := Context.rename (π : Equiv.Perm 𝔸) Γ
  one_smul Γ := Context.rename_one Γ
  mul_smul π σ Γ := Context.rename_mul (π : Equiv.Perm 𝔸) σ Γ

instance Subst.instPermType : Set.PermType 𝔸 (Subst F X 𝔸) where
  smul π σ := Subst.rename (π : Equiv.Perm 𝔸) σ
  one_smul σ := Subst.rename_one σ
  mul_smul π τ σ := Subst.rename_mul (π : Equiv.Perm 𝔸) τ σ

lemma Context.smul_def (π : FinitePerm 𝔸) (Γ : Context 𝔸 X) :
    π • Γ = Context.rename (π : Equiv.Perm 𝔸) Γ := rfl

lemma Subst.smul_def (π : FinitePerm 𝔸) (σ : Subst F X 𝔸) :
    π • σ = Subst.rename (π : Equiv.Perm 𝔸) σ := rfl

/-- Atoms of a context: those occurring in some `a # X`. -/
def Context.atoms (Γ : Context 𝔸 X) : Finset 𝔸 := Γ.image Prod.fst

/-- Atoms of a substitution: those of its bound terms. -/
def Subst.atoms (σ : Subst F X 𝔸) : Finset 𝔸 := σ.foldr (fun p acc => p.2.atoms ∪ acc) ∅

lemma Context.rename_eq_self (ρ : Equiv.Perm 𝔸) (Γ : Context 𝔸 X)
    (h : ∀ a ∈ Γ.atoms, ρ a = a) : Context.rename ρ Γ = Γ := by
  have hfix : ∀ a x, (a, x) ∈ Γ → ρ a = a := fun a x hp =>
    h a (Finset.mem_image.mpr ⟨(a, x), hp, rfl⟩)
  ext ⟨a, x⟩
  simp only [Context.rename, Finset.mem_map_equiv]
  simp only [Equiv.prodCongr_symm, Equiv.prodCongr_apply, Equiv.refl_symm, Equiv.coe_refl,
    Prod.map_apply, id_eq]
  constructor
  · intro hp
    have h1 := hfix _ x hp
    rw [Equiv.apply_symm_apply] at h1
    rwa [← h1] at hp
  · intro hp
    have h2 : ρ.symm a = a := by rw [Equiv.symm_apply_eq]; exact (hfix a x hp).symm
    rwa [h2]

lemma Subst.rename_eq_self (ρ : Equiv.Perm 𝔸) (σ : Subst F X 𝔸)
    (h : ∀ a ∈ σ.atoms, ρ a = a) : Subst.rename ρ σ = σ := by
  induction σ with
  | nil => rfl
  | cons p σ ih =>
    obtain ⟨x, t⟩ := p
    simp only [Subst.atoms, List.foldr_cons, Finset.mem_union] at h ih
    simp only [Subst.rename_cons, List.cons.injEq, Prod.mk.injEq, true_and]
    exact ⟨ntm.rename_eq_self ρ t fun a ha => h a (Or.inl ha),
      ih fun a ha => h a (Or.inr ha)⟩

instance Context.instNominal : Set.Nominal 𝔸 (Context 𝔸 X) where
  __ := Context.instPermType
  finSupp Γ := ⟨Γ.atoms, fun π hπ => Context.rename_eq_self _ Γ fun a ha => hπ (by simpa using ha)⟩

instance Subst.instNominal : Set.Nominal 𝔸 (Subst F X 𝔸) where
  __ := Subst.instPermType
  finSupp σ := ⟨σ.atoms, fun π hπ => Subst.rename_eq_self _ σ fun a ha => hπ (by simpa using ha)⟩

end Nominal
