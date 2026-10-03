import Nominal.Syntax.Problems.Basic
import Nominal.Syntax.Problems.Properties

/-!
# Renaming of metavariables

A bijection `τ : Equiv.Perm X` renames every metavariable occurring in the syntax: in
suspensions, in freshness contexts, and in the domain and range of substitutions. This is the
counterpart, for unknowns, of the meta-level renaming of atoms (`Nominal.Syntax.Rename`).

Every operation of the development commutes with this renaming, and freshness and
α-equivalence are invariant under it.
-/

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

/-! ### Terms -/

/-- Rename the metavariables of a term. -/
def ntm.renameVar (τ : Equiv.Perm X) : ntm F X 𝔸 → ntm F X 𝔸
  | .atm a     => .atm a
  | .mvar π x  => .mvar π (τ x)
  | .fapp f ts => .fapp f (ts.map (ntm.renameVar τ))
  | .abs a t   => .abs a (ntm.renameVar τ t)

@[simp] lemma ntm.renameVar_atm (τ : Equiv.Perm X) (a : 𝔸) :
    (ntm.atm a : ntm F X 𝔸).renameVar τ = .atm a := by simp [ntm.renameVar]

@[simp] lemma ntm.renameVar_mvar (τ : Equiv.Perm X) (π : LPerm 𝔸) (x : X) :
    (ntm.mvar π x : ntm F X 𝔸).renameVar τ = .mvar π (τ x) := by simp [ntm.renameVar]

@[simp] lemma ntm.renameVar_fapp (τ : Equiv.Perm X) (f : F) (ts : List (ntm F X 𝔸)) :
    (ntm.fapp f ts).renameVar τ = .fapp f (ts.map (ntm.renameVar τ)) := by simp [ntm.renameVar]

@[simp] lemma ntm.renameVar_abs (τ : Equiv.Perm X) (a : 𝔸) (t : ntm F X 𝔸) :
    (ntm.abs a t).renameVar τ = .abs a (t.renameVar τ) := by simp [ntm.renameVar]

lemma ntm.renameVar_one (t : ntm F X 𝔸) : t.renameVar 1 = t := by
  match t with
  | .atm a => simp
  | .mvar π x => simp
  | .fapp f ts =>
    simp only [ntm.renameVar_fapp, ntm.fapp.injEq, true_and]
    conv_rhs => rw [← List.map_id ts]
    exact List.map_congr_left fun t _ => ntm.renameVar_one t
  | .abs a t => simp [ntm.renameVar_one t]
termination_by ntmSize t
decreasing_by
  · exact ntmSize_lt_of_mem _ _ ‹_›
  · simp [ntmSize]

lemma ntm.renameVar_mul (τ τ' : Equiv.Perm X) (t : ntm F X 𝔸) :
    t.renameVar (τ * τ') = (t.renameVar τ').renameVar τ := by
  match t with
  | .atm a => simp
  | .mvar π x => simp
  | .fapp f ts =>
    simp only [ntm.renameVar_fapp, List.map_map, ntm.fapp.injEq, true_and]
    exact List.map_congr_left fun t _ => ntm.renameVar_mul τ τ' t
  | .abs a t => simp [ntm.renameVar_mul τ τ' t]
termination_by ntmSize t
decreasing_by
  · exact ntmSize_lt_of_mem _ _ ‹_›
  · simp [ntmSize]

lemma ntm.renameVar_injective (τ : Equiv.Perm X) :
    Function.Injective (ntm.renameVar (F := F) (𝔸 := 𝔸) τ) := by
  intro s t h
  have := congrArg (ntm.renameVar τ⁻¹) h
  simpa [← ntm.renameVar_mul, ntm.renameVar_one] using this

/-- Renaming metavariables commutes with the object-level permutation action. -/
lemma ntm.renameVar_permute (τ : Equiv.Perm X) (π : LPerm 𝔸) (t : ntm F X 𝔸) :
    (t.permute π).renameVar τ = (t.renameVar τ).permute π := by
  match t with
  | .atm a => simp [ntm.permute]
  | .mvar σ x => simp [ntm.permute]
  | .fapp f ts =>
    simp only [ntm.permute, ntm.renameVar_fapp, List.map_map, ntm.fapp.injEq, true_and]
    exact List.map_congr_left fun t _ => ntm.renameVar_permute τ π t
  | .abs a t => simp [ntm.permute, ntm.renameVar_permute τ π t]
termination_by ntmSize t
decreasing_by
  · exact ntmSize_lt_of_mem _ _ ‹_›
  · simp [ntmSize]

/-! ### Contexts -/

/-- Renaming of a freshness context: `a # X ↦ a # τ X`. -/
def Context.renameVar (τ : Equiv.Perm X) (Γ : Context 𝔸 X) : Context 𝔸 X :=
  Γ.map ((Equiv.refl 𝔸).prodCongr τ).toEmbedding

@[simp] lemma Context.mem_renameVar (τ : Equiv.Perm X) (Γ : Context 𝔸 X) (a : 𝔸) (x : X) :
    (a, τ x) ∈ Context.renameVar τ Γ ↔ (a, x) ∈ Γ := by
  simp [Context.renameVar, Finset.mem_map_equiv]

@[simp] lemma Context.renameVar_empty (τ : Equiv.Perm X) :
    Context.renameVar τ (∅ : Context 𝔸 X) = ∅ := rfl

@[simp] lemma Context.renameVar_insert (τ : Equiv.Perm X) (Γ : Context 𝔸 X) (a : 𝔸) (x : X) :
    Context.renameVar τ (insert (a, x) Γ) = insert (a, τ x) (Context.renameVar τ Γ) := by
  simp [Context.renameVar, Finset.map_insert]

/-! ### Freshness and α-equivalence are invariant -/

mutual
  theorem fresh_renameVar (τ : Equiv.Perm X) (Γ : Context 𝔸 X) (a : 𝔸) (t : ntm F X 𝔸) :
      (Context.renameVar τ Γ ⊢ a # t.renameVar τ) = (Γ ⊢ a # t) := by
    match t with
    | .atm b => simp [fresh]
    | .mvar π x => simp only [ntm.renameVar_mvar, fresh, Context.mem_renameVar]
    | .fapp f ts =>
      simp only [ntm.renameVar_fapp, fresh]
      exact freshList_renameVar τ Γ a ts
    | .abs b t =>
      simp only [ntm.renameVar_abs, fresh, fresh_renameVar τ Γ a t]

  theorem freshList_renameVar (τ : Equiv.Perm X) (Γ : Context 𝔸 X) (a : 𝔸)
      (ts : List (ntm F X 𝔸)) :
      freshList (Context.renameVar τ Γ) a (ts.map (ntm.renameVar τ)) = freshList Γ a ts := by
    match ts with
    | [] => simp [freshList]
    | t :: ts =>
      simp only [List.map_cons, freshList, fresh_renameVar τ Γ a t, freshList_renameVar τ Γ a ts]
end

mutual
  theorem alphaEquiv_renameVar (τ : Equiv.Perm X) (Γ : Context 𝔸 X) (s t : ntm F X 𝔸) :
      (Context.renameVar τ Γ ⊢ s.renameVar τ ≈α t.renameVar τ) = (Γ ⊢ s ≈α t) := by
    match s, t with
    | .atm a, .atm b => simp [alphaEquiv]
    | .mvar π x, .mvar π' y =>
      simp only [ntm.renameVar_mvar, alphaEquiv, EmbeddingLike.apply_eq_iff_eq,
        Context.mem_renameVar]
    | .fapp f ss, .fapp g ts =>
      simp only [ntm.renameVar_fapp, alphaEquiv, alphaEquivList_renameVar τ Γ ss ts]
    | .abs a s, .abs b t =>
      simp only [ntm.renameVar_abs, alphaEquiv]
      split_ifs with hab
      · exact alphaEquiv_renameVar τ Γ s t
      · rw [← ntm.renameVar_permute, alphaEquiv_renameVar τ Γ (s.permute [(b, a)]) t,
          fresh_renameVar]
    | .atm _, .mvar _ _ | .atm _, .fapp _ _ | .atm _, .abs _ _
    | .mvar _ _, .atm _ | .mvar _ _, .fapp _ _ | .mvar _ _, .abs _ _
    | .fapp _ _, .atm _ | .fapp _ _, .mvar _ _ | .fapp _ _, .abs _ _
    | .abs _ _, .atm _ | .abs _ _, .mvar _ _ | .abs _ _, .fapp _ _ => simp [alphaEquiv]
  termination_by ntmSize s
  decreasing_by
    all_goals simp [ntmSize, ntmPermSize]

  theorem alphaEquivList_renameVar (τ : Equiv.Perm X) (Γ : Context 𝔸 X)
      (ss ts : List (ntm F X 𝔸)) :
      alphaEquivList (Context.renameVar τ Γ) (ss.map (ntm.renameVar τ))
          (ts.map (ntm.renameVar τ))
        = alphaEquivList Γ ss ts := by
    match ss, ts with
    | [], [] => simp [alphaEquivList]
    | s :: ss, t :: ts =>
      simp only [List.map_cons, alphaEquivList, alphaEquiv_renameVar τ Γ s t,
        alphaEquivList_renameVar τ Γ ss ts]
    | [], _ :: _ | _ :: _, [] => simp [alphaEquivList]
  termination_by ntmSize.ntmSizeList ss
  decreasing_by
    all_goals simp [ntmSize.ntmSizeList]
    all_goals omega
end

/-! ### Substitutions -/

/-- Renaming of a substitution: rename both the bound metavariable and the bound term. -/
def Subst.renameVar (τ : Equiv.Perm X) (σ : Subst F X 𝔸) : Subst F X 𝔸 :=
  σ.map fun p => (τ p.1, p.2.renameVar τ)

@[simp] lemma Subst.renameVar_nil (τ : Equiv.Perm X) :
    Subst.renameVar τ ([] : Subst F X 𝔸) = [] := rfl

@[simp] lemma Subst.renameVar_cons (τ : Equiv.Perm X) (x : X) (t : ntm F X 𝔸)
    (σ : Subst F X 𝔸) :
    Subst.renameVar τ ((x, t) :: σ) = (τ x, t.renameVar τ) :: Subst.renameVar τ σ := rfl

lemma Subst.lookup_renameVar (τ : Equiv.Perm X) (σ : Subst F X 𝔸) (x : X) :
    (Subst.renameVar τ σ).lookup (τ x) = (σ.lookup x).map (ntm.renameVar τ) := by
  induction σ with
  | nil => rfl
  | cons p σ ih =>
    obtain ⟨Y, s⟩ := p
    simp only [Subst.renameVar_cons, Subst.lookup_cons, EmbeddingLike.apply_eq_iff_eq]
    split_ifs <;> simp [ih]

/-- Renaming metavariables commutes with substitution application. -/
lemma ntm.renameVar_subst (τ : Equiv.Perm X) (σ : Subst F X 𝔸) (t : ntm F X 𝔸) :
    (t.subst σ).renameVar τ = (t.renameVar τ).subst (Subst.renameVar τ σ) := by
  match t with
  | .atm a => simp
  | .mvar π x =>
    simp only [ntm.subst, ntm.renameVar_mvar, Subst.lookup_renameVar]
    cases σ.lookup x <;> simp [ntm.renameVar_permute]
  | .fapp f ts =>
    simp only [ntm.subst_fapp, ntm.renameVar_fapp, List.map_map, ntm.fapp.injEq, true_and]
    exact List.map_congr_left fun t _ => ntm.renameVar_subst τ σ t
  | .abs a t => simp [ntm.renameVar_subst τ σ t]
termination_by ntmSize t
decreasing_by
  · exact ntmSize_lt_of_mem _ _ ‹_›
  · simp [ntmSize]

lemma Subst.renameVar_comp (τ : Equiv.Perm X) (σ σ' : Subst F X 𝔸) :
    Subst.renameVar τ (σ.comp σ') = (Subst.renameVar τ σ).comp (Subst.renameVar τ σ') := by
  simp [Subst.comp, Subst.renameVar, Function.comp_def, ntm.renameVar_subst]

lemma ntm.subst_mvar_nil_renameVar (τ : Equiv.Perm X) (σ : Subst F X 𝔸) (x : X) :
    (ntm.mvar (F := F) [] (τ x)).subst (Subst.renameVar τ σ)
      = ((ntm.mvar [] x).subst σ).renameVar τ := by
  simpa using (ntm.renameVar_subst τ σ (.mvar [] x)).symm

lemma Subst.isIdempotent_renameVar_iff (τ : Equiv.Perm X) (σ : Subst F X 𝔸) :
    (Subst.renameVar τ σ).IsIdempotent ↔ σ.IsIdempotent := by
  have h : ∀ t : ntm F X 𝔸, (t.renameVar τ).subst (Subst.renameVar τ σ)
      = (t.subst σ).renameVar τ := fun t => (ntm.renameVar_subst τ σ t).symm
  simp only [Subst.IsIdempotent]
  rw [τ.surjective.forall]
  simp only [ntm.subst_mvar_nil_renameVar, h, (ntm.renameVar_injective τ).eq_iff]

/-! ### Constraints and problems -/

def Constraint.renameVar (τ : Equiv.Perm X) : Constraint F X 𝔸 → Constraint F X 𝔸
  | .fresh a t => .fresh a (t.renameVar τ)
  | .alpha s t => .alpha (s.renameVar τ) (t.renameVar τ)

def Problem.renameVar (τ : Equiv.Perm X) (P : Problem F X 𝔸) : Problem F X 𝔸 :=
  P.map (Constraint.renameVar τ)

mutual
  theorem simplifyFresh_renameVar (τ : Equiv.Perm X) (a : 𝔸) (t : ntm F X 𝔸) :
      simplifyFresh a (t.renameVar τ) = (simplifyFresh a t).map (Problem.renameVar τ) := by
    match t with
    | .atm b =>
      simp only [ntm.renameVar_atm, simplifyFresh]
      split_ifs <;> rfl
    | .abs b t =>
      simp only [ntm.renameVar_abs, simplifyFresh]
      split_ifs
      · rfl
      · exact simplifyFresh_renameVar τ a t
    | .mvar π x =>
      simp [simplifyFresh, Problem.renameVar, Constraint.renameVar]
    | .fapp f ts =>
      simp only [ntm.renameVar_fapp, simplifyFresh]
      exact simplifyFreshList_renameVar τ a ts

  theorem simplifyFreshList_renameVar (τ : Equiv.Perm X) (a : 𝔸) (ts : List (ntm F X 𝔸)) :
      simplifyFreshList a (ts.map (ntm.renameVar τ))
        = (simplifyFreshList a ts).map (Problem.renameVar τ) := by
    match ts with
    | [] => rfl
    | t :: ts =>
      simp only [List.map_cons, simplifyFreshList, simplifyFresh_renameVar τ a t,
        simplifyFreshList_renameVar τ a ts]
      cases simplifyFresh a t <;> cases simplifyFreshList a ts <;> simp [Problem.renameVar]
end

lemma Constraint.entails_renameVar (τ : Equiv.Perm X) (Γ : Context 𝔸 X) (c : Constraint F X 𝔸) :
    (c.renameVar τ).Entails (Context.renameVar τ Γ) = c.Entails Γ := by
  cases c <;> simp [Constraint.renameVar, Constraint.Entails, fresh_renameVar,
    alphaEquiv_renameVar]

lemma Problem.entails_renameVar (τ : Equiv.Perm X) (Γ : Context 𝔸 X) (P : Problem F X 𝔸) :
    Problem.Entails (Context.renameVar τ Γ) (Problem.renameVar τ P) ↔ Problem.Entails Γ P := by
  simp [Problem.Entails, Problem.renameVar, Constraint.entails_renameVar]

end Nominal
