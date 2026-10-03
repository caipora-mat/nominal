import Nominal.Syntax.Problems.Basic
import Nominal.Syntax.Problems.Properties

/-!
# Meta-level renaming of atoms

Nominal terms carry two permutation actions. `ntm.permute` is the *object-level* action:
it is suspended on metavariables (`π · X`), so it never changes which substitutions solve a
problem. This file defines the *meta-level* action: a bijection `ρ : Equiv.Perm 𝔸` renames
every atom occurring in the syntax, including those inside the swaps of a suspension
(by conjugation), in freshness contexts and in substitutions.

Every operation of the development commutes with renaming; freshness and α-equivalence are
invariant under it. These facts are the building blocks for the equivariance of the
unification algorithm (`Nominal.Syntax.Unification.Equivariance`).
-/

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

/-! ### Permutations -/

/-- Rename the atoms of every swap: `(a b) ↦ (ρ a  ρ b)`. -/
def LPerm.rename (ρ : Equiv.Perm 𝔸) (π : LPerm 𝔸) : LPerm 𝔸 :=
  π.map fun s => (ρ s.1, ρ s.2)

omit [Name 𝔸] in
@[simp] lemma LPerm.rename_nil (ρ : Equiv.Perm 𝔸) : LPerm.rename ρ [] = [] := rfl

omit [Name 𝔸] in
@[simp] lemma LPerm.rename_cons (ρ : Equiv.Perm 𝔸) (a b : 𝔸) (π : LPerm 𝔸) :
    LPerm.rename ρ ((a, b) :: π) = (ρ a, ρ b) :: LPerm.rename ρ π := rfl

omit [Name 𝔸] in
@[simp] lemma LPerm.rename_append (ρ : Equiv.Perm 𝔸) (π π' : LPerm 𝔸) :
    LPerm.rename ρ (π ++ π') = LPerm.rename ρ π ++ LPerm.rename ρ π' := by
  simp [LPerm.rename]

omit [Name 𝔸] in
@[simp] lemma LPerm.rename_reverse (ρ : Equiv.Perm 𝔸) (π : LPerm 𝔸) :
    (LPerm.rename ρ π).reverse = LPerm.rename ρ π.reverse := by
  simp [LPerm.rename, List.map_reverse]

omit [Name 𝔸] in
@[simp] lemma LPerm.rename_eq_nil_iff (ρ : Equiv.Perm 𝔸) (π : LPerm 𝔸) :
    LPerm.rename ρ π = [] ↔ π = [] := by
  simp [LPerm.rename]

omit [Name 𝔸] in
lemma LPerm.rename_one (π : LPerm 𝔸) : LPerm.rename 1 π = π := by
  simp [LPerm.rename]

omit [Name 𝔸] in
lemma LPerm.rename_mul (ρ ρ' : Equiv.Perm 𝔸) (π : LPerm 𝔸) :
    LPerm.rename (ρ * ρ') π = LPerm.rename ρ (LPerm.rename ρ' π) := by
  simp [LPerm.rename, Function.comp_def]

/-- A renamed swap acts on renamed atoms as the conjugate of the original swap. -/
lemma swapApply_rename (ρ : Equiv.Perm 𝔸) (a b c : 𝔸) :
    swapApply (ρ a, ρ b) (ρ c) = ρ (swapApply (a, b) c) := by
  simp only [swapApply, EmbeddingLike.apply_eq_iff_eq]
  split_ifs <;> rfl

lemma LPermApply_rename (ρ : Equiv.Perm 𝔸) (π : LPerm 𝔸) (c : 𝔸) :
    LPermApply (LPerm.rename ρ π) (ρ c) = ρ (LPermApply π c) := by
  induction π generalizing c with
  | nil => rfl
  | cons s π ih =>
    obtain ⟨a, b⟩ := s
    simp only [LPerm.rename_cons, LPermApply_cons, swapApply_rename, ih]

/-- The renamed permutation is the conjugate of the original one, so the renaming of a
    suspension is `(γ · X)ρ ≡ (ρ γ ρ⁻¹) · X`. -/
lemma LPermApply_rename_eq_conj (ρ : Equiv.Perm 𝔸) (π : LPerm 𝔸) :
    LPermApply (LPerm.rename ρ π) = ρ ∘ LPermApply π ∘ ρ.symm := by
  funext d
  simpa using LPermApply_rename ρ π (ρ.symm d)

omit [Name 𝔸] in
lemma LPerm.atomsList_rename (ρ : Equiv.Perm 𝔸) (π : LPerm 𝔸) :
    LPerm.atomsList (LPerm.rename ρ π) = (LPerm.atomsList π).map ρ := by
  induction π with
  | nil => rfl
  | cons s π ih =>
    obtain ⟨a, b⟩ := s
    simp [LPerm.atomsList, ih]

lemma dsList_rename (ρ : Equiv.Perm 𝔸) (π π' : LPerm 𝔸) :
    dsList (LPerm.rename ρ π) (LPerm.rename ρ π') = (dsList π π').map ρ := by
  simp only [dsList, LPerm.atomsList_rename, ← List.map_append, List.filter_map]
  congr 1
  apply List.filter_congr
  intro n _
  simp [LPermApply_rename]

lemma LPerm.atoms_rename (ρ : Equiv.Perm 𝔸) (π : LPerm 𝔸) :
    LPerm.atoms (LPerm.rename ρ π) = (LPerm.atoms π).map ρ.toEmbedding := by
  induction π with
  | nil => rfl
  | cons s π ih =>
    obtain ⟨a, b⟩ := s
    simp [LPerm.atoms, ih, Finset.map_insert]

lemma ds_rename (ρ : Equiv.Perm 𝔸) (π π' : LPerm 𝔸) :
    ds (LPerm.rename ρ π) (LPerm.rename ρ π') = (ds π π').map ρ.toEmbedding := by
  simp only [ds, LPerm.atoms_rename, ← Finset.map_union, Finset.filter_map]
  congr 1
  apply Finset.filter_congr
  intro n _
  simp [LPermApply_rename]

/-! ### Terms -/

/-- Meta-level renaming of the atoms of a term. -/
def ntm.rename (ρ : Equiv.Perm 𝔸) : ntm F X 𝔸 → ntm F X 𝔸
  | .atm a     => .atm (ρ a)
  | .mvar π x  => .mvar (LPerm.rename ρ π) x
  | .fapp f ts => .fapp f (ts.map (ntm.rename ρ))
  | .abs a t   => .abs (ρ a) (ntm.rename ρ t)

@[simp] lemma ntm.rename_atm (ρ : Equiv.Perm 𝔸) (a : 𝔸) :
    (ntm.atm a : ntm F X 𝔸).rename ρ = .atm (ρ a) := by simp [ntm.rename]

@[simp] lemma ntm.rename_mvar (ρ : Equiv.Perm 𝔸) (π : LPerm 𝔸) (x : X) :
    (ntm.mvar π x : ntm F X 𝔸).rename ρ = .mvar (LPerm.rename ρ π) x := by simp [ntm.rename]

@[simp] lemma ntm.rename_fapp (ρ : Equiv.Perm 𝔸) (f : F) (ts : List (ntm F X 𝔸)) :
    (ntm.fapp f ts).rename ρ = .fapp f (ts.map (ntm.rename ρ)) := by simp [ntm.rename]

@[simp] lemma ntm.rename_abs (ρ : Equiv.Perm 𝔸) (a : 𝔸) (t : ntm F X 𝔸) :
    (ntm.abs a t).rename ρ = .abs (ρ a) (t.rename ρ) := by simp [ntm.rename]

lemma ntm.rename_one (t : ntm F X 𝔸) : t.rename 1 = t := by
  match t with
  | .atm a => simp
  | .mvar π x => simp [LPerm.rename_one]
  | .fapp f ts =>
    simp only [ntm.rename_fapp, ntm.fapp.injEq, true_and]
    conv_rhs => rw [← List.map_id ts]
    exact List.map_congr_left fun t _ => ntm.rename_one t
  | .abs a t => simp [ntm.rename_one t]
termination_by ntmSize t
decreasing_by
  · exact ntmSize_lt_of_mem _ _ ‹_›
  · simp [ntmSize]

lemma ntm.rename_mul (ρ ρ' : Equiv.Perm 𝔸) (t : ntm F X 𝔸) :
    t.rename (ρ * ρ') = (t.rename ρ').rename ρ := by
  match t with
  | .atm a => simp
  | .mvar π x => simp [LPerm.rename_mul]
  | .fapp f ts =>
    simp only [ntm.rename_fapp, List.map_map, ntm.fapp.injEq, true_and]
    exact List.map_congr_left fun t _ => ntm.rename_mul ρ ρ' t
  | .abs a t => simp [ntm.rename_mul ρ ρ' t]
termination_by ntmSize t
decreasing_by
  · exact ntmSize_lt_of_mem _ _ ‹_›
  · simp [ntmSize]

lemma ntm.rename_injective (ρ : Equiv.Perm 𝔸) :
    Function.Injective (ntm.rename (F := F) (X := X) ρ) := by
  intro s t h
  have := congrArg (ntm.rename ρ⁻¹) h
  simpa [← ntm.rename_mul, ntm.rename_one] using this

/-- Renaming commutes with the object-level permutation action, the permutation being
    renamed as well. -/
lemma ntm.rename_permute (ρ : Equiv.Perm 𝔸) (π : LPerm 𝔸) (t : ntm F X 𝔸) :
    (t.permute π).rename ρ = (t.rename ρ).permute (LPerm.rename ρ π) := by
  match t with
  | .atm a => simp [ntm.permute, LPermApply_rename]
  | .mvar σ x => simp [ntm.permute]
  | .fapp f ts =>
    simp only [ntm.permute, ntm.rename_fapp, List.map_map, ntm.fapp.injEq, true_and]
    exact List.map_congr_left fun t _ => ntm.rename_permute ρ π t
  | .abs a t => simp [ntm.permute, LPermApply_rename, ntm.rename_permute ρ π t]
termination_by ntmSize t
decreasing_by
  · exact ntmSize_lt_of_mem _ _ ‹_›
  · simp [ntmSize]

/-! ### Contexts -/

/-- Renaming of a freshness context: `a # X ↦ ρ a # X`. -/
def Context.rename (ρ : Equiv.Perm 𝔸) (Γ : Context 𝔸 X) : Context 𝔸 X :=
  Γ.map (ρ.prodCongr (Equiv.refl X)).toEmbedding

@[simp] lemma Context.mem_rename (ρ : Equiv.Perm 𝔸) (Γ : Context 𝔸 X) (a : 𝔸) (x : X) :
    (ρ a, x) ∈ Context.rename ρ Γ ↔ (a, x) ∈ Γ := by
  simp [Context.rename, Finset.mem_map_equiv]

@[simp] lemma Context.rename_empty (ρ : Equiv.Perm 𝔸) :
    Context.rename ρ (∅ : Context 𝔸 X) = ∅ := rfl

@[simp] lemma Context.rename_insert (ρ : Equiv.Perm 𝔸) (Γ : Context 𝔸 X) (a : 𝔸) (x : X) :
    Context.rename ρ (insert (a, x) Γ) = insert (ρ a, x) (Context.rename ρ Γ) := by
  simp [Context.rename, Finset.map_insert]

/-! ### Freshness and α-equivalence are invariant -/

mutual
  theorem fresh_rename (ρ : Equiv.Perm 𝔸) (Γ : Context 𝔸 X) (a : 𝔸) (t : ntm F X 𝔸) :
      (Context.rename ρ Γ ⊢ ρ a # t.rename ρ) = (Γ ⊢ a # t) := by
    match t with
    | .atm b => simp [fresh]
    | .mvar π x =>
      simp only [ntm.rename_mvar, fresh, LPerm.rename_reverse, LPermApply_rename,
        Context.mem_rename]
    | .fapp f ts =>
      simp only [ntm.rename_fapp, fresh]
      exact freshList_rename ρ Γ a ts
    | .abs b t =>
      simp only [ntm.rename_abs, fresh, EmbeddingLike.apply_eq_iff_eq, fresh_rename ρ Γ a t]

  theorem freshList_rename (ρ : Equiv.Perm 𝔸) (Γ : Context 𝔸 X) (a : 𝔸)
      (ts : List (ntm F X 𝔸)) :
      freshList (Context.rename ρ Γ) (ρ a) (ts.map (ntm.rename ρ)) = freshList Γ a ts := by
    match ts with
    | [] => simp [freshList]
    | t :: ts =>
      simp only [List.map_cons, freshList, fresh_rename ρ Γ a t, freshList_rename ρ Γ a ts]
end

mutual
  theorem alphaEquiv_rename (ρ : Equiv.Perm 𝔸) (Γ : Context 𝔸 X) (s t : ntm F X 𝔸) :
      (Context.rename ρ Γ ⊢ s.rename ρ ≈α t.rename ρ) = (Γ ⊢ s ≈α t) := by
    match s, t with
    | .atm a, .atm b => simp [alphaEquiv]
    | .mvar π x, .mvar π' y =>
      simp only [ntm.rename_mvar, alphaEquiv, ds_rename, Finset.forall_mem_map,
        Equiv.coe_toEmbedding, Context.mem_rename]
    | .fapp f ss, .fapp g ts =>
      simp only [ntm.rename_fapp, alphaEquiv, alphaEquivList_rename ρ Γ ss ts]
    | .abs a s, .abs b t =>
      simp only [ntm.rename_abs, alphaEquiv, EmbeddingLike.apply_eq_iff_eq]
      split_ifs with hab
      · exact alphaEquiv_rename ρ Γ s t
      · have hp : (s.rename ρ).permute [(ρ b, ρ a)] = (s.permute [(b, a)]).rename ρ := by
          rw [ntm.rename_permute]; rfl
        rw [hp, alphaEquiv_rename ρ Γ (s.permute [(b, a)]) t, fresh_rename]
    | .atm _, .mvar _ _ | .atm _, .fapp _ _ | .atm _, .abs _ _
    | .mvar _ _, .atm _ | .mvar _ _, .fapp _ _ | .mvar _ _, .abs _ _
    | .fapp _ _, .atm _ | .fapp _ _, .mvar _ _ | .fapp _ _, .abs _ _
    | .abs _ _, .atm _ | .abs _ _, .mvar _ _ | .abs _ _, .fapp _ _ => simp [alphaEquiv]
  termination_by ntmSize s
  decreasing_by
    all_goals simp [ntmSize, ntmPermSize]

  theorem alphaEquivList_rename (ρ : Equiv.Perm 𝔸) (Γ : Context 𝔸 X)
      (ss ts : List (ntm F X 𝔸)) :
      alphaEquivList (Context.rename ρ Γ) (ss.map (ntm.rename ρ)) (ts.map (ntm.rename ρ))
        = alphaEquivList Γ ss ts := by
    match ss, ts with
    | [], [] => simp [alphaEquivList]
    | s :: ss, t :: ts =>
      simp only [List.map_cons, alphaEquivList, alphaEquiv_rename ρ Γ s t,
        alphaEquivList_rename ρ Γ ss ts]
    | [], _ :: _ | _ :: _, [] => simp [alphaEquivList]
  termination_by ntmSize.ntmSizeList ss
  decreasing_by
    all_goals simp [ntmSize.ntmSizeList]
    all_goals omega
end

/-! ### Substitutions -/

/-- Renaming of a substitution: rename the atoms of every bound term. -/
def Subst.rename (ρ : Equiv.Perm 𝔸) (σ : Subst F X 𝔸) : Subst F X 𝔸 :=
  σ.map fun p => (p.1, p.2.rename ρ)

@[simp] lemma Subst.rename_nil (ρ : Equiv.Perm 𝔸) : Subst.rename ρ ([] : Subst F X 𝔸) = [] := rfl

@[simp] lemma Subst.rename_cons (ρ : Equiv.Perm 𝔸) (x : X) (t : ntm F X 𝔸) (σ : Subst F X 𝔸) :
    Subst.rename ρ ((x, t) :: σ) = (x, t.rename ρ) :: Subst.rename ρ σ := rfl

lemma Subst.lookup_rename (ρ : Equiv.Perm 𝔸) (σ : Subst F X 𝔸) (x : X) :
    (Subst.rename ρ σ).lookup x = (σ.lookup x).map (ntm.rename ρ) := by
  induction σ with
  | nil => rfl
  | cons p σ ih =>
    obtain ⟨Y, s⟩ := p
    simp only [Subst.rename_cons, Subst.lookup_cons]
    split_ifs <;> simp [ih]

/-- Renaming commutes with substitution application. -/
lemma ntm.rename_subst (ρ : Equiv.Perm 𝔸) (σ : Subst F X 𝔸) (t : ntm F X 𝔸) :
    (t.subst σ).rename ρ = (t.rename ρ).subst (Subst.rename ρ σ) := by
  match t with
  | .atm a => simp
  | .mvar π x =>
    simp only [ntm.subst, ntm.rename_mvar, Subst.lookup_rename]
    cases σ.lookup x <;> simp [ntm.rename_permute]
  | .fapp f ts =>
    simp only [ntm.subst_fapp, ntm.rename_fapp, List.map_map, ntm.fapp.injEq, true_and]
    exact List.map_congr_left fun t _ => ntm.rename_subst ρ σ t
  | .abs a t => simp [ntm.rename_subst ρ σ t]
termination_by ntmSize t
decreasing_by
  · exact ntmSize_lt_of_mem _ _ ‹_›
  · simp [ntmSize]

lemma Subst.rename_comp (ρ : Equiv.Perm 𝔸) (σ τ : Subst F X 𝔸) :
    Subst.rename ρ (σ.comp τ) = (Subst.rename ρ σ).comp (Subst.rename ρ τ) := by
  simp [Subst.comp, Subst.rename, Function.comp_def, ntm.rename_subst]

/-- A bare metavariable is unaffected by renaming, so its image is the renamed image. -/
lemma ntm.subst_mvar_nil_rename (ρ : Equiv.Perm 𝔸) (σ : Subst F X 𝔸) (x : X) :
    (ntm.mvar (F := F) [] x).subst (Subst.rename ρ σ) = ((ntm.mvar [] x).subst σ).rename ρ := by
  simpa using (ntm.rename_subst ρ σ (.mvar [] x)).symm

lemma Subst.isIdempotent_rename_iff (ρ : Equiv.Perm 𝔸) (σ : Subst F X 𝔸) :
    (Subst.rename ρ σ).IsIdempotent ↔ σ.IsIdempotent := by
  have h : ∀ t : ntm F X 𝔸, (t.rename ρ).subst (Subst.rename ρ σ) = (t.subst σ).rename ρ :=
    fun t => (ntm.rename_subst ρ σ t).symm
  simp only [Subst.IsIdempotent, ntm.subst_mvar_nil_rename, h, (ntm.rename_injective ρ).eq_iff]

/-! ### Constraints and problems -/

def Constraint.rename (ρ : Equiv.Perm 𝔸) : Constraint F X 𝔸 → Constraint F X 𝔸
  | .fresh a t => .fresh (ρ a) (t.rename ρ)
  | .alpha s t => .alpha (s.rename ρ) (t.rename ρ)

def Problem.rename (ρ : Equiv.Perm 𝔸) (P : Problem F X 𝔸) : Problem F X 𝔸 :=
  P.map (Constraint.rename ρ)

mutual
  theorem simplifyFresh_rename (ρ : Equiv.Perm 𝔸) (a : 𝔸) (t : ntm F X 𝔸) :
      simplifyFresh (ρ a) (t.rename ρ) = (simplifyFresh a t).map (Problem.rename ρ) := by
    match t with
    | .atm b =>
      simp only [ntm.rename_atm, simplifyFresh, EmbeddingLike.apply_eq_iff_eq]
      split_ifs <;> rfl
    | .abs b t =>
      simp only [ntm.rename_abs, simplifyFresh, EmbeddingLike.apply_eq_iff_eq]
      split_ifs
      · rfl
      · exact simplifyFresh_rename ρ a t
    | .mvar π x =>
      simp [simplifyFresh, Problem.rename, Constraint.rename, LPermApply_rename]
    | .fapp f ts =>
      simp only [ntm.rename_fapp, simplifyFresh]
      exact simplifyFreshList_rename ρ a ts

  theorem simplifyFreshList_rename (ρ : Equiv.Perm 𝔸) (a : 𝔸) (ts : List (ntm F X 𝔸)) :
      simplifyFreshList (ρ a) (ts.map (ntm.rename ρ))
        = (simplifyFreshList a ts).map (Problem.rename ρ) := by
    match ts with
    | [] => rfl
    | t :: ts =>
      simp only [List.map_cons, simplifyFreshList, simplifyFresh_rename ρ a t,
        simplifyFreshList_rename ρ a ts]
      cases simplifyFresh a t <;> cases simplifyFreshList a ts <;> simp [Problem.rename]
end

lemma Constraint.entails_rename (ρ : Equiv.Perm 𝔸) (Γ : Context 𝔸 X) (c : Constraint F X 𝔸) :
    (c.rename ρ).Entails (Context.rename ρ Γ) = c.Entails Γ := by
  cases c <;> simp [Constraint.rename, Constraint.Entails, fresh_rename, alphaEquiv_rename]

lemma Problem.entails_rename (ρ : Equiv.Perm 𝔸) (Γ : Context 𝔸 X) (P : Problem F X 𝔸) :
    Problem.Entails (Context.rename ρ Γ) (Problem.rename ρ P) ↔ Problem.Entails Γ P := by
  simp [Problem.Entails, Problem.rename, Constraint.entails_rename]

end Nominal
