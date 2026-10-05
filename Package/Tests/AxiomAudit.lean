/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Package
import Lean.Util.CollectAxioms

/-!
# Package axiom audit

Audit imported production declarations by module origin, including private/generated names.
Run this file directly to repeat the audit when Lake reuses its compiled artifact.
-/

open Lean Elab Command

private def unexpectedAxioms (xs : Array Name) : Array Name :=
  xs.filter fun ax => ax != `propext && ax != `Classical.choice && ax != `Quot.sound

private def checkCount (production : Nat) : Except String Unit := do
  if production == 0 then throw "No Package production declarations found"

-- These are names supplied to the validator, not declarations of axioms.
run_cmd do
  unless (unexpectedAxioms #[`propext, `Classical.choice, `Quot.sound]).isEmpty do
    throwError "The audit rejected standard axioms"
  unless unexpectedAxioms #[`sorryAx] == #[`sorryAx] do
    throwError "The audit failed to reject sorryAx"
  unless unexpectedAxioms #[`PackageAuditProbe.unapproved] == #[`PackageAuditProbe.unapproved] do
    throwError "The audit failed to reject an unapproved axiom name"
  unless (match checkCount 0 with | .error _ => true | .ok _ => false) do
    throwError "The audit accepted empty production coverage"
  unless (match checkCount 1 with | .ok _ => true | .error _ => false) do
    throwError "The audit rejected nonempty production coverage"

#print axioms NominalPackage.Perm.moved_conj
#print axioms NominalPackage.Perm.conj_swap
#print axioms NominalPackage.Perm.smul_atom
#print axioms NominalPackage.Discrete.smul_val
#print axioms NominalPackage.Equivariant.comp

set_option maxHeartbeats 0 in
-- This budget applies only to the inspection traversal, not mathematical proofs.
run_cmd do
  let env ← getEnv
  let mut production := 0
  let mut productionModules : Array String := #[]
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!.toString
    unless origin == "Package" || origin.startsWith "Package." do continue
    unless origin == "Package" || origin.startsWith "Package.Foundations." do
      throwError "Unexpected non-production Package import: {origin}"
    let bad := unexpectedAxioms (← collectAxioms name)
    unless bad.isEmpty do
      throwError "{name} ({origin}): unexpected axioms {bad}"
    production := production + 1
    unless productionModules.contains origin do
      productionModules := productionModules.push origin
  match checkCount production with
  | .error message => throwError "{message}; check imports and module-origin filters"
  | .ok () => pure ()
  logInfo m!"Package production: {production} declarations from {productionModules.size} modules"
  logInfo "No axioms beyond propext, Classical.choice, Quot.sound"
