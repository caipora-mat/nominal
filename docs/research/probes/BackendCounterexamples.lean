import Instances.LambdaCalculus.Substitution

/-!
Research counterexamples, 2026-10-05, Lean 4.34.1.
Run: `lake env lean docs/research/probes/BackendCounterexamples.lean`.
These refute fixed-substitution equivariance and the unguarded representative
equation for mapping arbitrary supported functions under name abstraction.
They do not assert that supported abstraction mapping itself is impossible.
-/

open Nominal.Core Nominal.Set LambdaCalculus
universe u
namespace BackendCounterexamples
variable {α : Type u} [Name α]

theorem fixed_subst_not_equivariant (a b : α) (hne : a ≠ b) :
    ¬ IsEquivariant α (fun t : Term α => Term.subst t a (Term.var b)) := by
  intro h
  have heq := h.map_smul (swap a b) (Term.var a)
  simp [Term.smul_var, Term.subst_var,
    Ne.symm hne] at heq

theorem no_unconditional_const_abs_map {β : Type} [Name β] (c : β) :
    letI := Nominal.instUnit (α := β)
    ¬ ∃ F : NameAbs β Unit → NameAbs β β, ∀ a, F (abs a ()) = abs a c := by
  let _ : Nominal β Unit := Nominal.instUnit
  rintro ⟨F, hF⟩
  obtain ⟨b, hbc⟩ := exists_ne c
  have hin : abs c () = abs b () := NameAbs.abs_rename (fresh_unit c) (fresh_unit b)
  have hout : abs c c = abs b c := (hF c).symm.trans ((congrArg F hin).trans (hF b))
  have hc : c # c := (NameAbs.abs_eq_iff_of_ne hbc.symm).mp hout |>.1
  simp at hc

#print axioms fixed_subst_not_equivariant
#print axioms no_unconditional_const_abs_map
end BackendCounterexamples
