import Instances.LambdaCalculus.ReductionInduction

/-!
# Parallel reduction and capture-avoiding substitution

`Term.Parallel.subst` substitutes related replacements into related subjects.
All terms are alpha quotients; the substitution variable and the free atoms of
the subjects and replacements are unrestricted. `subst_left` and `subst_right`
specialize this result using parallel reflexivity.

Fresh rule induction carries the variable and both replacements in its nominal
context. Its binder cases therefore permit substitution beneath lambdas. In the
contraction case both premise induction hypotheses are used, and `subst_subst`
identifies the contracted substituted body with the substituted original result.
The induction principle already transports binders using `subst_rename` and
freshness preservation; no further binder convention is assumed here.
-/

namespace LambdaCalculus

open Nominal.Core Nominal.Set

universe u
variable {α : Type u} [Name α]

namespace Term.Parallel

/-- Simultaneous compatibility with capture-avoiding substitution: both the
subject and the replacement may reduce. Freshness is local to rule induction,
so the public statement applies to arbitrary open terms and any variable. -/
theorem subst {t t' s s' : Term α} (ht : t ⇉ t') (hs : s ⇉ s') (x : α) :
    t[x := s] ⇉ t'[x := s'] := by
  apply strong_ind
    (P := fun t t' (p : α × Term α × Term α) =>
      p.2.1 ⇉ p.2.2 → t[p.1 := p.2.1] ⇉ t'[p.1 := p.2.2])
    (hVar := by
      rintro a ⟨x, r, r'⟩ hr
      by_cases hax : a = x
      · simpa only [subst_var, ite_eq_left hax] using hr
      · simpa only [subst_var, ite_eq_right hax] using Parallel.var a)
    (hApp := by
      rintro t t' s s' ⟨x, r, r'⟩ _ _ iht ihs hr
      simpa only [subst_app] using Parallel.app (iht (x, r, r') hr) (ihs (x, r, r') hr))
    (hLam := by
      rintro a t t' ⟨x, r, r'⟩ _ ha ih hr
      obtain ⟨hax, har, har'⟩ := (fresh_prod_right.mp ha).imp_right fresh_prod_right.mp
      rw [subst_lam a t x r (fresh_prod_right.mpr ⟨hax, har⟩),
        subst_lam a t' x r' (fresh_prod_right.mpr ⟨hax, har'⟩)]
      exact Parallel.lam a (ih (x, r, r') hr))
    (hBeta := by
      rintro a t t' s s' ⟨x, r, r'⟩ _ _ ha _ _ iht ihs hr
      obtain ⟨hax, har, har'⟩ := (fresh_prod_right.mp ha).imp_right fresh_prod_right.mp
      -- Composition is used with the contraction binder first:
      -- (t'[a := s'])[x := r'] = (t'[x := r'])[a := s'[x := r']].
      -- Its hypotheses are a ≠ x and a # r', both supplied by the context.
      rw [subst_app, subst_lam a t x r (fresh_prod_right.mpr ⟨hax, har⟩),
        subst_subst a x t' s' r' ((fresh_atoms a x).mp hax) har']
      exact Parallel.beta a (iht (x, r, r') hr) (ihs (x, r, r') hr))
    ht (x, s, s') hs

/-- Substitution of a fixed replacement preserves parallel reduction of the subject. -/
theorem subst_left {t t' : Term α} (ht : t ⇉ t') (x : α) (s : Term α) :
    t[x := s] ⇉ t'[x := s] :=
  ht.subst (Parallel.refl s) x

/-- Reducing the replacement preserves parallel reduction after substitution
into any fixed subject, including subjects with multiple occurrences of `x`. -/
theorem subst_right {s s' : Term α} (hs : s ⇉ s') (t : Term α) (x : α) :
    t[x := s] ⇉ t[x := s'] :=
  (Parallel.refl t).subst hs x

end Term.Parallel

end LambdaCalculus
