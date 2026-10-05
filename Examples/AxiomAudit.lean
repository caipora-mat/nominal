/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Nominal
import Instances
import Lean.Util.CollectAxioms

/-!
# Supported-library axiom audit

`lake build Examples` runs this audit when this module or its imports change.
Use `lake env lean Examples/AxiomAudit.lean` to rerun it explicitly, including
when Lake can reuse the compiled module. The traversal includes public and
private declarations originating in both supported libraries, including root
and `Equiv.Perm` declarations. It does not scan every imported Mathlib
declaration. Unexpected dependencies fail the command.
-/

open Lean Elab Command

#print axioms Nominal.Set.supp_supports
#print axioms Nominal.Set.someAny
#print axioms Nominal.Set.supp_quotient_eq_sInter
#print axioms Nominal.Set.NameAbs.supp_abs
#print axioms Nominal.Set.NameAbs.liftFCB_abs
#print axioms Nominal.Set.NameAbs.liftFreshParam_unique
#print axioms Nominal.Set.NFun.curry_uncurry
#print axioms LambdaCalculus.Term.strong_ind
#print axioms LambdaCalculus.Term.recNoContext_lam
#print axioms LambdaCalculus.Term.recNoContext_unique
#print axioms LambdaCalculus.Term.recNoContext_independent
#print axioms LambdaCalculus.Term.recNoContext_supports
#print axioms LambdaCalculus.Term.supp_recNoContextNFun_le
#print axioms LambdaCalculus.Term.subst_subst
#print axioms LambdaCalculus.Term.Beta.strong_ind
#print axioms LambdaCalculus.Term.Parallel.strong_ind
#print axioms LambdaCalculus.Term.Parallel.subst
#print axioms LambdaCalculus.Term.Parallel.diamond
#print axioms LambdaCalculus.Term.betaStar_iff_parallelStar
#print axioms LambdaCalculus.Term.BetaStar.confluent
#print axioms LambdaCalculus.Term.BetaEq.church_rosser
#print axioms LambdaCalculus.Term.BetaEq.normal_unique

set_option maxHeartbeats 0 in
-- Only the inspection traversal has an unlimited heartbeat budget. Library
-- proofs retain their normal checking and elaboration settings.
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!.toString
    if origin == "Nominal" || origin == "Instances" ||
        origin.startsWith "Nominal." || origin.startsWith "Instances." then
      count := count + 1
      let axioms ← collectAxioms name
      let unexpected := axioms.filter fun ax =>
        ax != `propext && ax != `Classical.choice && ax != `Quot.sound
      unless unexpected.isEmpty do
        throwError "{name}: unexpected axioms {unexpected}"
  unless count > 0 do
    throwError "No project declarations found; check imports and module filters"
  logInfo m!"Checked {count} project declarations; no axioms beyond propext, Classical.choice, Quot.sound"
