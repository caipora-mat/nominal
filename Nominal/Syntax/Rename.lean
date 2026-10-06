import Nominal.Syntax.Problems.Basic
import Nominal.Syntax.Problems.Properties

/-!
# Meta-level renaming of atoms and metavariables

Nominal terms carry two permutation actions. `ntm.permute` is the *object-level* action:
it is suspended on metavariables (`π · X`), so it never changes which substitutions solve a
problem. This file defines the *meta-level* action `relabel ρ τ`: a bijection
`ρ : Equiv.Perm 𝔸` renames every atom occurring in the syntax, including those inside the
swaps of a suspension (by conjugation), and a bijection `τ : Equiv.Perm X` renames every
metavariable, in suspensions, in freshness contexts and in the domain and range of
substitutions.

Every operation of the development commutes with relabelling; freshness and α-equivalence are
invariant under it. These facts are the building blocks for the equivariance of the
unification algorithm (`Nominal.Syntax.Unification.Equivariance`).

`rename ρ` and `renameVar τ` are the special cases `relabel ρ 1` and `relabel 1 τ`.
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

/-- Meta-level renaming of the atoms (by `ρ`) and metavariables (by `τ`) of a term. -/
def ntm.relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) : ntm F X 𝔸 → ntm F X 𝔸
  | .atm a     => .atm (ρ a)
  | .mvar π x  => .mvar (LPerm.rename ρ π) (τ x)
  | .fapp f ts => .fapp f (ts.map (ntm.relabel ρ τ))
  | .abs a t   => .abs (ρ a) (ntm.relabel ρ τ t)

@[simp] lemma ntm.relabel_atm (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (a : 𝔸) :
    (ntm.atm a : ntm F X 𝔸).relabel ρ τ = .atm (ρ a) := by simp [ntm.relabel]

@[simp] lemma ntm.relabel_mvar (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (π : LPerm 𝔸) (x : X) :
    (ntm.mvar π x : ntm F X 𝔸).relabel ρ τ = .mvar (LPerm.rename ρ π) (τ x) := by
  simp [ntm.relabel]

@[simp] lemma ntm.relabel_fapp (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (f : F)
    (ts : List (ntm F X 𝔸)) :
    (ntm.fapp f ts).relabel ρ τ = .fapp f (ts.map (ntm.relabel ρ τ)) := by simp [ntm.relabel]

@[simp] lemma ntm.relabel_abs (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (a : 𝔸) (t : ntm F X 𝔸) :
    (ntm.abs a t).relabel ρ τ = .abs (ρ a) (t.relabel ρ τ) := by simp [ntm.relabel]

lemma ntm.relabel_one (t : ntm F X 𝔸) : t.relabel 1 1 = t := by
  match t with
  | .atm a => simp
  | .mvar π x => simp [LPerm.rename_one]
  | .fapp f ts =>
    simp only [ntm.relabel_fapp, ntm.fapp.injEq, true_and]
    conv_rhs => rw [← List.map_id ts]
    exact List.map_congr_left fun t _ => ntm.relabel_one t
  | .abs a t => simp [ntm.relabel_one t]
termination_by ntmSize t
decreasing_by
  · exact ntmSize_lt_of_mem _ _ ‹_›
  · simp [ntmSize]

lemma ntm.relabel_mul (ρ ρ' : Equiv.Perm 𝔸) (τ τ' : Equiv.Perm X) (t : ntm F X 𝔸) :
    t.relabel (ρ * ρ') (τ * τ') = (t.relabel ρ' τ').relabel ρ τ := by
  match t with
  | .atm a => simp
  | .mvar π x => simp [LPerm.rename_mul]
  | .fapp f ts =>
    simp only [ntm.relabel_fapp, List.map_map, ntm.fapp.injEq, true_and]
    exact List.map_congr_left fun t _ => ntm.relabel_mul ρ ρ' τ τ' t
  | .abs a t => simp [ntm.relabel_mul ρ ρ' τ τ' t]
termination_by ntmSize t
decreasing_by
  · exact ntmSize_lt_of_mem _ _ ‹_›
  · simp [ntmSize]

lemma ntm.relabel_injective (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) :
    Function.Injective (ntm.relabel (F := F) ρ τ) := by
  intro s t h
  have := congrArg (ntm.relabel ρ⁻¹ τ⁻¹) h
  simpa [← ntm.relabel_mul, ntm.relabel_one] using this

/-- Relabelling commutes with the object-level permutation action, the permutation being
    renamed as well. -/
lemma ntm.relabel_permute (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (π : LPerm 𝔸)
    (t : ntm F X 𝔸) :
    (t.permute π).relabel ρ τ = (t.relabel ρ τ).permute (LPerm.rename ρ π) := by
  match t with
  | .atm a => simp [ntm.permute, LPermApply_rename]
  | .mvar σ x => simp [ntm.permute]
  | .fapp f ts =>
    simp only [ntm.permute, ntm.relabel_fapp, List.map_map, ntm.fapp.injEq, true_and]
    exact List.map_congr_left fun t _ => ntm.relabel_permute ρ τ π t
  | .abs a t => simp [ntm.permute, LPermApply_rename, ntm.relabel_permute ρ τ π t]
termination_by ntmSize t
decreasing_by
  · exact ntmSize_lt_of_mem _ _ ‹_›
  · simp [ntmSize]

/-! ### Contexts -/

/-- Relabelling of a freshness context: `a # X ↦ ρ a # τ X`. -/
def Context.relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (Γ : Context 𝔸 X) : Context 𝔸 X :=
  Γ.map (ρ.prodCongr τ).toEmbedding

@[simp] lemma Context.mem_relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (Γ : Context 𝔸 X)
    (a : 𝔸) (x : X) :
    (ρ a, τ x) ∈ Context.relabel ρ τ Γ ↔ (a, x) ∈ Γ := by
  simp [Context.relabel, Finset.mem_map_equiv]

@[simp] lemma Context.relabel_empty (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) :
    Context.relabel ρ τ (∅ : Context 𝔸 X) = ∅ := rfl

@[simp] lemma Context.relabel_insert (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (Γ : Context 𝔸 X)
    (a : 𝔸) (x : X) :
    Context.relabel ρ τ (insert (a, x) Γ) = insert (ρ a, τ x) (Context.relabel ρ τ Γ) := by
  simp [Context.relabel, Finset.map_insert]

/-! ### Freshness and α-equivalence are invariant -/

mutual
  theorem fresh_relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (Γ : Context 𝔸 X) (a : 𝔸)
      (t : ntm F X 𝔸) :
      (Context.relabel ρ τ Γ ⊢ ρ a # t.relabel ρ τ) = (Γ ⊢ a # t) := by
    match t with
    | .atm b => simp [fresh]
    | .mvar π x =>
      simp only [ntm.relabel_mvar, fresh, LPerm.rename_reverse, LPermApply_rename,
        Context.mem_relabel]
    | .fapp f ts =>
      simp only [ntm.relabel_fapp, fresh]
      exact freshList_relabel ρ τ Γ a ts
    | .abs b t =>
      simp only [ntm.relabel_abs, fresh, EmbeddingLike.apply_eq_iff_eq,
        fresh_relabel ρ τ Γ a t]

  theorem freshList_relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (Γ : Context 𝔸 X) (a : 𝔸)
      (ts : List (ntm F X 𝔸)) :
      freshList (Context.relabel ρ τ Γ) (ρ a) (ts.map (ntm.relabel ρ τ)) = freshList Γ a ts := by
    match ts with
    | [] => simp [freshList]
    | t :: ts =>
      simp only [List.map_cons, freshList, fresh_relabel ρ τ Γ a t,
        freshList_relabel ρ τ Γ a ts]
end

mutual
  theorem alphaEquiv_relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (Γ : Context 𝔸 X)
      (s t : ntm F X 𝔸) :
      (Context.relabel ρ τ Γ ⊢ s.relabel ρ τ ≈α t.relabel ρ τ) = (Γ ⊢ s ≈α t) := by
    match s, t with
    | .atm a, .atm b => simp [alphaEquiv]
    | .mvar π x, .mvar π' y =>
      simp only [ntm.relabel_mvar, alphaEquiv, ds_rename, Finset.forall_mem_map,
        Equiv.coe_toEmbedding, EmbeddingLike.apply_eq_iff_eq, Context.mem_relabel]
    | .fapp f ss, .fapp g ts =>
      simp only [ntm.relabel_fapp, alphaEquiv, alphaEquivList_relabel ρ τ Γ ss ts]
    | .abs a s, .abs b t =>
      simp only [ntm.relabel_abs, alphaEquiv, EmbeddingLike.apply_eq_iff_eq]
      split_ifs with hab
      · exact alphaEquiv_relabel ρ τ Γ s t
      · have hp : (s.relabel ρ τ).permute [(ρ b, ρ a)] = (s.permute [(b, a)]).relabel ρ τ := by
          rw [ntm.relabel_permute]; rfl
        rw [hp, alphaEquiv_relabel ρ τ Γ (s.permute [(b, a)]) t, fresh_relabel]
    | .atm _, .mvar _ _ | .atm _, .fapp _ _ | .atm _, .abs _ _
    | .mvar _ _, .atm _ | .mvar _ _, .fapp _ _ | .mvar _ _, .abs _ _
    | .fapp _ _, .atm _ | .fapp _ _, .mvar _ _ | .fapp _ _, .abs _ _
    | .abs _ _, .atm _ | .abs _ _, .mvar _ _ | .abs _ _, .fapp _ _ => simp [alphaEquiv]
  termination_by ntmSize s
  decreasing_by
    all_goals simp [ntmSize, ntmPermSize]

  theorem alphaEquivList_relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (Γ : Context 𝔸 X)
      (ss ts : List (ntm F X 𝔸)) :
      alphaEquivList (Context.relabel ρ τ Γ) (ss.map (ntm.relabel ρ τ))
          (ts.map (ntm.relabel ρ τ))
        = alphaEquivList Γ ss ts := by
    match ss, ts with
    | [], [] => simp [alphaEquivList]
    | s :: ss, t :: ts =>
      simp only [List.map_cons, alphaEquivList, alphaEquiv_relabel ρ τ Γ s t,
        alphaEquivList_relabel ρ τ Γ ss ts]
    | [], _ :: _ | _ :: _, [] => simp [alphaEquivList]
  termination_by ntmSize.ntmSizeList ss
  decreasing_by
    all_goals simp [ntmSize.ntmSizeList]
    all_goals omega
end

/-! ### Substitutions -/

/-- Relabelling of a substitution: relabel both the bound metavariable and the bound term. -/
def Subst.relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (σ : Subst F X 𝔸) : Subst F X 𝔸 :=
  σ.map fun p => (τ p.1, p.2.relabel ρ τ)

@[simp] lemma Subst.relabel_nil (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) :
    Subst.relabel ρ τ ([] : Subst F X 𝔸) = [] := rfl

@[simp] lemma Subst.relabel_cons (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (x : X)
    (t : ntm F X 𝔸) (σ : Subst F X 𝔸) :
    Subst.relabel ρ τ ((x, t) :: σ) = (τ x, t.relabel ρ τ) :: Subst.relabel ρ τ σ := rfl

lemma Subst.lookup_relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (σ : Subst F X 𝔸) (x : X) :
    (Subst.relabel ρ τ σ).lookup (τ x) = (σ.lookup x).map (ntm.relabel ρ τ) := by
  induction σ with
  | nil => rfl
  | cons p σ ih =>
    obtain ⟨Y, s⟩ := p
    simp only [Subst.relabel_cons, Subst.lookup_cons, EmbeddingLike.apply_eq_iff_eq]
    split_ifs <;> simp [ih]

/-- Relabelling commutes with substitution application. -/
lemma ntm.relabel_subst (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (σ : Subst F X 𝔸)
    (t : ntm F X 𝔸) :
    (t.subst σ).relabel ρ τ = (t.relabel ρ τ).subst (Subst.relabel ρ τ σ) := by
  match t with
  | .atm a => simp
  | .mvar π x =>
    simp only [ntm.subst, ntm.relabel_mvar, Subst.lookup_relabel]
    cases σ.lookup x <;> simp [ntm.relabel_permute]
  | .fapp f ts =>
    simp only [ntm.subst_fapp, ntm.relabel_fapp, List.map_map, ntm.fapp.injEq, true_and]
    exact List.map_congr_left fun t _ => ntm.relabel_subst ρ τ σ t
  | .abs a t => simp [ntm.relabel_subst ρ τ σ t]
termination_by ntmSize t
decreasing_by
  · exact ntmSize_lt_of_mem _ _ ‹_›
  · simp [ntmSize]

lemma Subst.relabel_comp (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (σ σ' : Subst F X 𝔸) :
    Subst.relabel ρ τ (σ.comp σ') = (Subst.relabel ρ τ σ).comp (Subst.relabel ρ τ σ') := by
  simp [Subst.comp, Subst.relabel, Function.comp_def, ntm.relabel_subst]

/-- The image of a relabelled bare metavariable is the relabelled image. -/
lemma ntm.subst_mvar_nil_relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (σ : Subst F X 𝔸)
    (x : X) :
    (ntm.mvar (F := F) [] (τ x)).subst (Subst.relabel ρ τ σ)
      = ((ntm.mvar [] x).subst σ).relabel ρ τ := by
  simpa using (ntm.relabel_subst ρ τ σ (.mvar [] x)).symm

lemma Subst.isIdempotent_relabel_iff (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (σ : Subst F X 𝔸) :
    (Subst.relabel ρ τ σ).IsIdempotent ↔ σ.IsIdempotent := by
  have h : ∀ t : ntm F X 𝔸, (t.relabel ρ τ).subst (Subst.relabel ρ τ σ)
      = (t.subst σ).relabel ρ τ := fun t => (ntm.relabel_subst ρ τ σ t).symm
  simp only [Subst.IsIdempotent]
  rw [τ.surjective.forall]
  simp only [ntm.subst_mvar_nil_relabel, h, (ntm.relabel_injective ρ τ).eq_iff]

/-! ### Constraints and problems -/

def Constraint.relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) :
    Constraint F X 𝔸 → Constraint F X 𝔸
  | .fresh a t => .fresh (ρ a) (t.relabel ρ τ)
  | .alpha s t => .alpha (s.relabel ρ τ) (t.relabel ρ τ)

def Problem.relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (P : Problem F X 𝔸) :
    Problem F X 𝔸 :=
  P.map (Constraint.relabel ρ τ)

mutual
  theorem simplifyFresh_relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (a : 𝔸)
      (t : ntm F X 𝔸) :
      simplifyFresh (ρ a) (t.relabel ρ τ) = (simplifyFresh a t).map (Problem.relabel ρ τ) := by
    match t with
    | .atm b =>
      simp only [ntm.relabel_atm, simplifyFresh, EmbeddingLike.apply_eq_iff_eq]
      split_ifs <;> rfl
    | .abs b t =>
      simp only [ntm.relabel_abs, simplifyFresh, EmbeddingLike.apply_eq_iff_eq]
      split_ifs
      · rfl
      · exact simplifyFresh_relabel ρ τ a t
    | .mvar π x =>
      simp [simplifyFresh, Problem.relabel, Constraint.relabel, LPermApply_rename]
    | .fapp f ts =>
      simp only [ntm.relabel_fapp, simplifyFresh]
      exact simplifyFreshList_relabel ρ τ a ts

  theorem simplifyFreshList_relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (a : 𝔸)
      (ts : List (ntm F X 𝔸)) :
      simplifyFreshList (ρ a) (ts.map (ntm.relabel ρ τ))
        = (simplifyFreshList a ts).map (Problem.relabel ρ τ) := by
    match ts with
    | [] => rfl
    | t :: ts =>
      simp only [List.map_cons, simplifyFreshList, simplifyFresh_relabel ρ τ a t,
        simplifyFreshList_relabel ρ τ a ts]
      cases simplifyFresh a t <;> cases simplifyFreshList a ts <;> simp [Problem.relabel]
end

lemma Constraint.entails_relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (Γ : Context 𝔸 X)
    (c : Constraint F X 𝔸) :
    (c.relabel ρ τ).Entails (Context.relabel ρ τ Γ) = c.Entails Γ := by
  cases c <;> simp [Constraint.relabel, Constraint.Entails, fresh_relabel, alphaEquiv_relabel]

lemma Problem.entails_relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (Γ : Context 𝔸 X)
    (P : Problem F X 𝔸) :
    Problem.Entails (Context.relabel ρ τ Γ) (Problem.relabel ρ τ P) ↔ Problem.Entails Γ P := by
  simp [Problem.Entails, Problem.relabel, Constraint.entails_relabel]

/-! ### Renaming atoms only, or metavariables only -/

/-- Meta-level renaming of the atoms of a term. -/
abbrev ntm.rename (ρ : Equiv.Perm 𝔸) : ntm F X 𝔸 → ntm F X 𝔸 := ntm.relabel ρ 1

/-- Renaming of the metavariables of a term. -/
abbrev ntm.renameVar (τ : Equiv.Perm X) : ntm F X 𝔸 → ntm F X 𝔸 := ntm.relabel 1 τ

/-- Renaming of a freshness context: `a # X ↦ ρ a # X`. -/
abbrev Context.rename (ρ : Equiv.Perm 𝔸) : Context 𝔸 X → Context 𝔸 X := Context.relabel ρ 1

/-- Renaming of a freshness context: `a # X ↦ a # τ X`. -/
abbrev Context.renameVar (τ : Equiv.Perm X) : Context 𝔸 X → Context 𝔸 X := Context.relabel 1 τ

/-- Renaming of a substitution: rename the atoms of every bound term. -/
abbrev Subst.rename (ρ : Equiv.Perm 𝔸) : Subst F X 𝔸 → Subst F X 𝔸 := Subst.relabel ρ 1

/-- Renaming of a substitution: rename both the bound metavariable and the bound term. -/
abbrev Subst.renameVar (τ : Equiv.Perm X) : Subst F X 𝔸 → Subst F X 𝔸 := Subst.relabel 1 τ

lemma ntm.rename_mul (ρ ρ' : Equiv.Perm 𝔸) (t : ntm F X 𝔸) :
    t.rename (ρ * ρ') = (t.rename ρ').rename ρ := by
  simpa using ntm.relabel_mul ρ ρ' 1 1 t

end Nominal
