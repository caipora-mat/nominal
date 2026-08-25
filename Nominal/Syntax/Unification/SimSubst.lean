import Nominal.Syntax.Unification.Basic

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

-- ===========================================================================
-- One-shot lookup and normalisation, used to reason about `Subst.reduce`.
--
-- `Subst.lookupSim` is a `find?`-based lookup (first binding for `x`, or the
-- bare metavariable).  Since substitution is simultaneous, it agrees with `subst`
-- on a bare metavariable (`lookup_getD_eq_lookupSim` in `Mgu.lean`).
-- `Subst.normalize` replaces each value by its full image, and
-- `lookupSim_normalize` looks each variable up to that image.  Both feed
-- `Subst.reduce` (the solved-form reduction of a solution) via `lookupSim_reduce`.
-- ===========================================================================

/-- Look up `x` in `σ`, returning the (first) bound value or the bare `mvar` if
    unbound. -/
def Subst.lookupSim (σ : Subst F X 𝔸) (x : X) : ntm F X 𝔸 :=
  (σ.find? (fun p => p.1 == x)).elim (ntm.mvar [] x) Prod.snd

/-- Normalisation: send each domain variable to its full image under `σ`. -/
def Subst.normalize (σ : Subst F X 𝔸) : Subst F X 𝔸 :=
  σ.map (fun p => (p.1, (ntm.mvar (F := F) [] p.1).subst σ))

@[simp] lemma Subst.dom_normalize (σ : Subst F X 𝔸) :
    (σ.normalize).dom = σ.dom := by
  simp only [Subst.normalize, Subst.dom, List.map_map]
  congr 1

/-- Looking up `x` in `normalize σ` returns exactly `x`'s image `(mvar [] x).subst σ`.
    For `x ∈ dom σ` the mapped binding carries that image; for `x ∉ dom σ`, `σ`
    fixes `x`, so both sides are `x`. -/
lemma Subst.lookupSim_normalize (σ : Subst F X 𝔸) (x : X) :
    (σ.normalize).lookupSim x = (ntm.mvar (F := F) [] x).subst σ := by
  unfold Subst.lookupSim Subst.normalize
  rw [List.find?_map]
  simp only [Function.comp_def]
  cases hf : σ.find? (fun p => p.1 == x) with
  | none =>
      simp only [Option.map_none, Option.elim_none]
      have hnd : x ∉ σ.dom := by
        rw [Subst.dom, List.mem_toFinset, List.mem_map]
        rintro ⟨p, hp, hpx⟩
        have := List.find?_eq_none.mp hf p hp
        simp only [beq_iff_eq] at this
        exact this hpx
      exact (ntm.subst_mvar_nil_of_not_mem_dom hnd).symm
  | some p =>
      simp only [Option.map_some, Option.elim_some]
      have hpx : p.1 = x := by
        have := List.find?_some hf
        simpa using this
      rw [hpx]

end Nominal
