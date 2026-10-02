import Nominal.Syntax.Rename
import Nominal.Set.Nominal

/-!
# Nominal terms form a nominal set

Under the meta-level renaming of atoms (`ntm.rename`), finite permutations act on nominal
terms, and every term is supported by the finite set of atoms occurring in it. This connects
the syntax of the development with its nominal-sets layer (`Nominal.Set`).
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

end Nominal
