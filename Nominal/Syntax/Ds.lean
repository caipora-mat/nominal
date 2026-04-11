import Nominal.Core
import Nominal.Syntax.LPerm
import Mathlib.Data.Finset.Basic

namespace Nominal

open Core

variable {𝔸 : Type*} [Name 𝔸]

def LPerm.atoms [Name 𝔸] : LPerm 𝔸 → Finset 𝔸
   | []           => ∅
   | (a, b) :: π  => {a, b} ∪ LPerm.atoms π

/-- Difference set: {n | π·n ≠ π'·n} -/
def ds [Name 𝔸] (π π' : LPerm 𝔸) : Finset 𝔸 :=
  (LPerm.atoms π ∪ LPerm.atoms π').filter fun n =>
    LPermApply π n ≠ LPermApply π' n

lemma ds_comm (π π' : LPerm 𝔸) : ds π π' = ds π' π := by
    ext n
    simp only [ds, Finset.mem_filter, Finset.mem_union, ne_eq]
    tauto

@[simp]
lemma LPermAtoms_append (π π' : LPerm 𝔸) :
    (π ++ π').atoms = π.atoms ∪ π'.atoms := by
  induction π with
  | nil => simp [LPerm.atoms]
  | cons s τ ih =>
    rcases s with ⟨a, b⟩
    simp only [List.cons_append, LPerm.atoms, Finset.insert_union, Finset.singleton_union]
    rw [<- ih]

@[simp]
lemma LPermAtoms_reverse (π : LPerm 𝔸) :
    LPerm.atoms (π.reverse) = π.atoms := by
  induction π with
  | nil => simp
  | cons s τ ih =>
    rcases s with ⟨a, b⟩
    simp only [List.reverse_cons, LPermAtoms_append]
    rw [ih]
    simp [LPerm.atoms]

/-- A permutation fixes any atom not in its atom set. -/
lemma LPermApply_not_mem_atoms (π : LPerm 𝔸) (a : 𝔸) (h : a ∉ LPerm.atoms π) :
    LPermApply π a = a := by
  induction π with
  | nil => simp [LPermApply]
  | cons s ps ih =>
    rcases s with ⟨x, y⟩
    simp only [LPerm.atoms, Finset.mem_union] at h
    push_neg at h
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
    rw [LPermApply_cons]
    rcases h with ⟨⟨hax, hay⟩, h⟩
    rw [swapApply_other]
    · exact ih h
    · exact hax
    · exact hay

lemma ds_perm_swap (σ σ' π : LPerm 𝔸) :
    ds (σ ++ π) σ' = ds σ (σ' ++ π.reverse) := by
  ext n
  simp only [ds, Finset.mem_filter, Finset.mem_union, ne_eq,
             LPermAtoms_append, LPermAtoms_reverse, LPermApply_append]
  constructor
  · rintro ⟨hmem, hne⟩
    refine ⟨?_, fun heq => hne ?_⟩
    · rcases hmem with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    · rw [heq, LPermApply_reverse_right]
  · rintro ⟨hmem, hne⟩
    refine ⟨?_, fun heq => hne ?_⟩
    · rcases hmem with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
      · exact Or.inl (Or.inr h)
    · rw [← heq, LPermApply_reverse_left]

lemma ds_trans (π₁ π₂ π₃ : LPerm 𝔸) :
    ∀ n, n ∈ ds π₁ π₃ → n ∈ ds π₁ π₂ ∨ n ∈ ds π₂ π₃ := by
  intro n hn
  simp only [ds, Finset.mem_filter, Finset.mem_union, ne_eq] at hn ⊢
  obtain ⟨hmem, hne⟩ := hn
  by_cases hc : LPermApply π₁ n = LPermApply π₂ n
  · right
    refine ⟨?_, fun heq => hne (hc.trans heq)⟩
    by_cases h2 : n ∈ π₂.atoms
    · exact Or.inl h2
    · right
      by_contra h3
      apply hne
      rw [hc, LPermApply_not_mem_atoms π₂ n h2, LPermApply_not_mem_atoms π₃ n h3]
  · left
    refine ⟨?_, hc⟩
    by_cases h1 : n ∈ π₁.atoms
    · exact Or.inl h1
    · right
      by_contra h2
      apply hc
      rw [LPermApply_not_mem_atoms π₁ n h1, LPermApply_not_mem_atoms π₂ n h2]

lemma ds_append (σ σ' π : LPerm 𝔸) :
    ds σ σ' = ds (σ ++ π) (σ' ++ π) := by
  ext n
  simp only [ds, Finset.mem_filter, Finset.mem_union, LPermAtoms_append,
             LPermApply_append, ne_eq]
  constructor
  · rintro ⟨hmem, hne⟩
    refine ⟨?_, fun h => hne (LPermApply_injective π h)⟩
    rcases hmem with (h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
  · rintro ⟨hmem, hne⟩
    replace hne : LPermApply σ n ≠ LPermApply σ' n := fun h => hne (by rw [h])
    rcases hmem with (h | h) | h
    · exact ⟨Or.inl h, hne⟩
    · refine ⟨?_, hne⟩
      by_contra hnot
      push_neg at hnot
      apply hne
      rw [LPermApply_not_mem_atoms σ n hnot.1, LPermApply_not_mem_atoms σ' n hnot.2]
    · rcases h with h | h
      · exact ⟨Or.inr h, hne⟩
      · refine ⟨?_, hne⟩
        by_contra hnot
        push_neg at hnot
        apply hne
        rw [LPermApply_not_mem_atoms σ n hnot.1,
            LPermApply_not_mem_atoms σ' n hnot.2]

/-- Swap-conjugation at the LPerm level: `[(b,a)] ++ π` and `π ++ [(π b, π a)]` apply
    identically to every atom, so their difference set is empty. -/
lemma ds_swap_conjugate (π : LPerm 𝔸) (a b : 𝔸) :
    ds ([(b, a)] ++ π) (π ++ [(LPermApply π b, LPermApply π a)]) = ∅ := by
  have hpw : ∀ n, LPermApply ([(b, a)] ++ π) n
      = LPermApply (π ++ [(LPermApply π b, LPermApply π a)]) n := by
    intro n
    rw [LPermApply_append, LPermApply_append]
    simp only [LPermApply_cons, LPermApply_nil]
    exact LPermApply_swap_conjugate π a b n
  ext n
  simp only [ds, Finset.mem_filter, Finset.mem_union, ne_eq, Finset.notMem_empty, iff_false,
             not_and, not_not]
  intro _
  exact hpw n

/-- Key consequence of `ds π π' = ∅`: the two permutations act identically on every atom. -/
lemma LPermApply_eq_of_ds_empty (π π' : LPerm 𝔸) (h : ds π π' = ∅) (a : 𝔸) :
    LPermApply π a = LPermApply π' a := by
  by_contra hne
  have : a ∈ ds π π' := by
    simp only [ds, Finset.mem_filter, Finset.mem_union, ne_eq]
    refine ⟨?_, hne⟩
    by_contra hnot
    push_neg at hnot
    apply hne
    rw [LPermApply_not_mem_atoms π a hnot.1, LPermApply_not_mem_atoms π' a hnot.2]
  rw [h] at this
  simp only [Finset.notMem_empty] at this

lemma LPermApply_reverse_eq_of_ds_empty (π π' : LPerm 𝔸) (h : ds π π' = ∅) (a : 𝔸) :
    LPermApply π.reverse a = LPermApply π'.reverse a := by
  have h1 := LPermApply_eq_of_ds_empty π π' h (LPermApply π.reverse a)
  rw [LPermApply_reverse_right] at h1
  have h2 := congrArg (LPermApply π'.reverse) h1
  rw [LPermApply_reverse_left] at h2
  exact h2.symm

lemma ds_append_eq_of_ds_empty (σ τ π π' : LPerm 𝔸) (h : ds π π' = ∅) :
    ds (σ ++ π) τ = ds (σ ++ π') τ := by
  ext n
  simp only [ds, Finset.mem_filter, Finset.mem_union, ne_eq,
             LPermAtoms_append, LPermApply_append]
  have hpw : LPermApply π (LPermApply σ n) = LPermApply π' (LPermApply σ n) :=
    LPermApply_eq_of_ds_empty π π' h _
  rw [hpw]
  refine and_congr_left fun hne => ?_
  constructor
  · rintro ((hσ | hπ) | hτ)
    · exact Or.inl (Or.inl hσ)
    · by_cases hπ' : n ∈ π'.atoms
      · exact Or.inl (Or.inr hπ')
      · by_cases hσ' : n ∈ σ.atoms
        · exact Or.inl (Or.inl hσ')
        · by_cases hτ' : n ∈ τ.atoms
          · exact Or.inr hτ'
          · exfalso; apply hne
            rw [LPermApply_not_mem_atoms σ n hσ',
                LPermApply_not_mem_atoms π' n hπ',
                LPermApply_not_mem_atoms τ n hτ']
    · exact Or.inr hτ
  · rintro ((hσ | hπ') | hτ)
    · exact Or.inl (Or.inl hσ)
    · by_cases hπ : n ∈ π.atoms
      · exact Or.inl (Or.inr hπ)
      · by_cases hσ' : n ∈ σ.atoms
        · exact Or.inl (Or.inl hσ')
        · by_cases hτ' : n ∈ τ.atoms
          · exact Or.inr hτ'
          · exfalso; apply hne
            rw [LPermApply_not_mem_atoms σ n hσ',
                LPermApply_not_mem_atoms π n hπ,
                LPermApply_not_mem_atoms τ n hτ'] at *
            exact hpw.symm
    · exact Or.inr hτ

lemma ds_reverse_nil (π : LPerm 𝔸) : ds (π ++ π.reverse) [] = ∅ := by
  simp [ds]
  intro n hn
  simp [LPermApply_append, LPermApply_reverse_left]

lemma ds_swap_symm (a b : 𝔸) : ds [(a,b)] [(b,a)] = ∅ := by
  simp [ds]
  intro n hn
  simp [swapApply_symm]

lemma Lperm_not_in_ds (a : 𝔸) (π π' : LPerm 𝔸) :
    LPermApply π a = LPermApply π' a ↔ a ∉ ds π π' := by
  constructor
  · intro h
    simp [ds]
    intro hmem
    exact h
  · intro h
    simp [ds] at h
    by_cases ha : a ∈ π.atoms ∨ a ∈ π'.atoms
    · exact h ha                                                                                                                                    
    · push_neg at ha
      rw [LPermApply_not_mem_atoms _ _ ha.1, LPermApply_not_mem_atoms _ _ ha.2]

lemma ds_append_swap_sub (π π' : LPerm 𝔸) (b : 𝔸) (a : 𝔸) (hab : a ≠ b) :
    a ∈ ds (π ++ [(LPermApply π' b, LPermApply π b)]) π' → a ∈ ds π π' := by
  simp only [ds, LPermAtoms_append, Finset.union_assoc, Finset.mem_filter, Finset.mem_union, and_imp]
  intro h h'
  constructor
  · have hmem : a ∈ (π ++ [(LPermApply π' b, LPermApply π b)]).atoms ∨ a ∈ π'.atoms := by
      by_contra hnot
      push_neg at hnot
      exact h' (by rw [LPermApply_not_mem_atoms _ _ hnot.1, LPermApply_not_mem_atoms _ _ hnot.2])
    by_contra hnot
    push_neg at hnot
    apply h'
    rw [LPermApply_append, LPermApply_not_mem_atoms _ _ hnot.1, LPermApply_not_mem_atoms _ _ hnot.2]
    simp only [LPermApply_cons, LPermApply_nil]
    rw [swapApply_other]
    · intro heq; exact hab (by
        rw [← LPermApply_reverse_left π' b, ← heq,
            LPermApply_not_mem_atoms _ _ (LPermAtoms_reverse π' ▸ hnot.2)])
    · intro heq; exact hab (by
        rw [← LPermApply_reverse_left π b, ← heq,
            LPermApply_not_mem_atoms _ _ (LPermAtoms_reverse π ▸ hnot.1)]) 
  · intro heq
    apply h'
    rw [LPermApply_append, heq]
    simp only [LPermApply_cons, LPermApply_nil]
    rw [swapApply_other]
    · intro h; exact hab (LPermApply_injective π' h) 
    · intro h; exact hab (LPermApply_injective π (h.symm ▸ heq))

end Nominal
