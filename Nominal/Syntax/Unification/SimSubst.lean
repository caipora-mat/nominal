import Nominal.Syntax.Unification.Basic

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

-- ===========================================================================
-- Simultaneous substitution, and its agreement with the sequential one.
--
-- The substitution `ntm.subst` used by the algorithm is *sequential*: it folds
-- `applyOne` left-to-right, so a binding can act on the result of an earlier
-- one (`[X ↦ Y, Y ↦ a]` sends `X` to `a`).  This is non-standard — the usual
-- notion of substitution is *simultaneous*: walk the term once and replace each
-- domain variable by its value, without re-scanning (`substSim`, below).
--
-- The two disagree on a raw substitution (`[X ↦ Y, Y ↦ a]` sends `X` to `Y`
-- simultaneously), but they agree once we *normalise*: replacing each domain
-- variable's value by its full sequential image gives a simultaneous
-- substitution `normalize σ` with `t.subst σ = t.substSim (normalize σ)` for
-- every term.  This justifies the sequential definition: it computes exactly the
-- standard simultaneous action of `normalize σ`.  (No hypothesis on `σ` needed.)
-- ===========================================================================

/-- Look up `x` in `σ`, returning the (first) bound value or the bare `mvar` if
    unbound.  The one-shot lookup underlying simultaneous substitution. -/
def Subst.lookupSim (σ : Subst F X 𝔸) (x : X) : ntm F X 𝔸 :=
  (σ.find? (fun p => p.1 == x)).elim (ntm.mvar [] x) Prod.snd

/-- Simultaneous substitution: replace each metavariable by its `lookupSim`
    value in a single structural pass (no re-scanning of results). -/
def ntm.substSim : ntm F X 𝔸 → Subst F X 𝔸 → ntm F X 𝔸
  | .atm a,     _ => .atm a
  | .mvar π x,  σ => (σ.lookupSim x).permute π
  | .fapp f ts, σ => .fapp f (ts.map (·.substSim σ))
  | .abs a t,   σ => .abs a (t.substSim σ)

/-- Normalisation: send each domain variable to its *full* sequential image
    under `σ`.  The result is a simultaneous substitution with the same domain. -/
def Subst.normalize (σ : Subst F X 𝔸) : Subst F X 𝔸 :=
  σ.map (fun p => (p.1, (ntm.mvar (F := F) [] p.1).subst σ))

@[simp] lemma Subst.dom_normalize (σ : Subst F X 𝔸) :
    (σ.normalize).dom = σ.dom := by
  simp only [Subst.normalize, Subst.dom, List.map_map]
  congr 1

/-- Key lemma: looking up `x` in `normalize σ` returns exactly `x`'s full
    sequential image `(mvar [] x).subst σ`.  For `x ∈ dom σ` the mapped binding
    carries that image; for `x ∉ dom σ`, `σ` fixes `x`, so both sides are `x`. -/
lemma Subst.lookupSim_normalize (σ : Subst F X 𝔸) (x : X) :
    (σ.normalize).lookupSim x = (ntm.mvar (F := F) [] x).subst σ := by
  unfold Subst.lookupSim Subst.normalize
  rw [List.find?_map]
  simp only [Function.comp_def]
  cases hf : σ.find? (fun p => p.1 == x) with
  | none =>
      simp only [Option.map_none, Option.elim_none]
      -- x ∉ dom σ, so σ fixes the bare mvar.
      have hnd : x ∉ σ.dom := by
        rw [Subst.dom, List.mem_toFinset, List.mem_map]
        rintro ⟨p, hp, hpx⟩
        have := List.find?_eq_none.mp hf p hp
        simp only [beq_iff_eq] at this
        exact this hpx
      exact (ntm.subst_mvar_nil_of_not_mem_dom hnd).symm
  | some p =>
      simp only [Option.map_some, Option.elim_some]
      -- The found binding has `p.1 = x`.
      have hpx : p.1 = x := by
        have := List.find?_some hf
        simpa using this
      rw [hpx]

/-- Sequential and simultaneous substitution agree after normalisation:
    `t.subst σ = t.substSim (normalize σ)` for every term `t` and every `σ`. -/
theorem ntm.subst_eq_substSim_normalize (σ : Subst F X 𝔸) :
    ∀ t : ntm F X 𝔸, t.subst σ = t.substSim σ.normalize
  | .atm a => by simp [ntm.substSim, ntm.subst_atm]
  | .mvar π x => by
      rw [ntm.substSim, Subst.lookupSim_normalize, ntm.subst_mvar]
  | .fapp f ts => by
      rw [ntm.substSim, ntm.subst_fapp]
      congr 1
      exact List.map_congr_left (fun t _ => ntm.subst_eq_substSim_normalize σ t)
  | .abs a t => by
      rw [ntm.substSim, ntm.subst_abs, ntm.subst_eq_substSim_normalize σ t]

end Nominal
