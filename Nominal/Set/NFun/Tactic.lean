import Nominal.Set.NFun.Basic

/-!
# NFun construction tactics and experimental macro

* `supports_nfun [rules] from c₁ ... cₙ` — prove capture-support inclusions,
  derive fixpoint facts, and discharge the action equation with proved simp rules.
  Implements a certified form of the free-variables heuristic.

* `nfun` is an experimental syntax-only macro. Simple projections, identity, and
  captures have examples below. Automatic capture mode rejects `let`, `match`,
  nested functions, and multiple binders; global identifiers remain unsupported.
  Use `NFun.equivariant`, `NFun.ofSupports`, or
  `NFun.ofCaptures` with explicit support evidence for reliable construction.
-/

namespace Nominal.Set

open Core

/-! ### Explicit support certificates

`supports_nfun [rules] from c₁ ... cₙ` proves a `supports S (PFun.mk f)`
goal. Each capture must have its least support contained in `S`; unions may be
reordered or reassociated, atoms may use singleton supports, and local inclusion
or support hypotheses are accepted. The optional rules use ordinary simp-lemma
syntax, including `← hf.map_smul` to move actions into an equivariant operation
before simplifying fixed captures.
The tactic is transactional and either closes the goal or reports the remaining
obligation. Use `rw [supports_pfun_iff]` for a fully explicit proof.
-/

attribute [nfun_simp] PFun.coe_mk PFun.coe_apply
  PermType.prod_smul PermType.prod_smul_fst PermType.prod_smul_snd
  NFun.smul_apply_smul NFun.id_apply NFun.const_apply NFun.comp_apply
  NFun.prod_apply NFun.eval_apply NFun.map_apply NFun.comap_apply
  NFun.curry_apply_apply NFun.uncurry_apply NFun.fromParam_apply
  NFun.smul_const NFun.smul_comp NFun.smul_prod NFun.smul_map NFun.smul_comap
  NFun.smul_curry NFun.smul_uncurry NFun.smul_fromParam smul_ite

private theorem support_product {α X Y : Type*} [Name α]
    [Nominal α X] [Nominal α Y] (p : X × Y) :
    supp p = supp p.1 ∪ supp p.2 := supp_prod p.1 p.2

private theorem fixed_nfun_apply {α X Y : Type*} [Name α]
    [Nominal α X] [Nominal α Y] (π : FinitePerm α) (f : NFun α X Y)
    (hf : π • f = f) (x : X) : f (π • x) = π • f x := by
  simpa only [hf] using NFun.smul_apply_smul π f x

private theorem fixed_eq_iff {α X : Type*} [Name α] [Nominal α X]
    (π : FinitePerm α) (c : X) (hc : π • c = c) (x : X) :
    π • x = c ↔ x = c := by
  simpa only [hc] using (PermType.smul_eq_smul_iff_eq π (x := x) (y := c))

private theorem fixed_eq_iff_left {α X : Type*} [Name α] [Nominal α X]
    (π : FinitePerm α) (c : X) (hc : π • c = c) (x : X) :
    c = π • x ↔ c = x := by
  simpa only [eq_comm] using fixed_eq_iff π c hc x

syntax "supports_nfun" (" [" Lean.Parser.Tactic.simpLemma,* "]")?
  (" from " (colGt term:max)+)? : tactic

open Lean Meta Elab Elab.Tactic in
elab_rules : tactic
  | `(tactic| supports_nfun $[[$rules,*]]? $[from $cs:term*]?) => focus <| withMainContext do
    let saved ← saveState
    try
      let target ← getMainTarget
      unless target.isAppOf ``supports do
        throwError "supports_nfun: expected a supports S (PFun.mk f) goal"
      let support ← Term.exprToSyntax target.getAppArgs[target.getAppArgs.size - 2]!
      -- Resolve captures before introducing any new locals. `exprToSyntax` retains
      -- expression identities, including shadowed locals and compound captures.
      let captures ← (cs.getD #[]).mapM fun c => do
        let e ← Term.elabTerm c none
        Term.synthesizeSyntheticMVarsNoPostponing
        return (c, ← Term.exprToSyntax (← instantiateMVars e))
      let rules := rules.map (·.getElems) |>.getD #[]
      let pi := mkIdent (← mkFreshUserName `π)
      let hp := mkIdent (← mkFreshUserName `hπ)
      let input := mkIdent (← mkFreshUserName `x)
      evalTactic (← `(tactic| rw [supports_pfun_iff]))
      evalTactic (← `(tactic| intro $pi $hp $input))
      let mut facts : Array (TSyntax `term) := #[]
      for (source, c) in captures do
        let hf := mkIdent (← mkFreshUserName `capture_fixed)
        try
          withoutRecover <| evalTactic (← `(tactic|
            have $hf : $pi • $c = $c := by
              apply supp_supports $c $pi
              intro a ha
              refine $hp ?_
              have inclusion : supp $c ⊆ $support := by
                first
                | assumption
                | exact Finset.Subset.refl _
                | exact supp_le (by assumption)
                | intro b hb
                  simp only [supp_atom, support_product, Finset.mem_union,
                    Finset.mem_singleton] at hb ⊢
                  tauto
              exact inclusion ha))
        catch _ =>
          throwError "supports_nfun: cannot prove the support of capture {source} is contained in the supplied set; provide a local inclusion or support hypothesis"
        facts := facts.push (← `($hf))
        facts := facts.push (← `(fixed_eq_iff $pi $c $hf))
        facts := facts.push (← `(fixed_eq_iff_left $pi $c $hf))
        let cExpr ← Term.elabTerm c none
        let cType ← whnf (← inferType cExpr)
        if cType.isAppOf ``NFun then
          facts := facts.push (← `(fixed_nfun_apply $pi $c $hf))
      let factRules ← facts.mapM fun r => `(Parser.Tactic.simpLemma| $r:term)
      let allRules := factRules ++ rules
      evalTactic (← `(tactic| simp -failIfUnchanged only [nfun_simp, $allRules,*]))
      unless (← getUnsolvedGoals).isEmpty do
        let remaining ← withMainContext do
          return (← ppExpr (← getMainTarget)).pretty
        throwError "supports_nfun: remaining action equation; supply proved rules in [rules], or use `rw [supports_pfun_iff]` for an explicit proof\n{remaining}"
    catch ex =>
      saved.restore
      throw ex

/-! ### Experimental `nfun` macro — free variable collection

`nfun fun x => body` builds an `NFun` by:
1. Collecting free names in `body` (excluding lambda-bound names).
2. Building the support set as `supp v₁ ∪ supp v₂ ∪ ...`.
3. Emitting `NFun.ofCaptures ⟨fun x => body⟩ S (by supports_nfun from v₁ v₂ ...)`.
-/

open Lean in
/-- Collect all bound variable names from a function binder pattern.
    Handles simple binders (`fun x => ...`), product patterns (`fun (a, b) => ...`),
    and wildcard (`fun _ => ...`). -/
private partial def collectBinderNames (stx : Syntax) : Array Name :=
  match stx with
  | .ident _ _ n _   => #[n]
  | .node _ kind args =>
    -- `_` (hole) — no name to bind
    if kind == `Lean.Parser.Term.hole then #[]
    -- Product pattern: `(a, b)` or similar tuple patterns
    else if kind == `Lean.Parser.Term.paren then
      args.foldl (fun acc a => acc ++ collectBinderNames a) #[]
    else
      args.foldl (fun acc a => acc ++ collectBinderNames a) #[]
  | _ => #[]

open Lean in
/-- Prototype syntax traversal for identifiers outside `bound`.
    This is not elaborated free-variable analysis: globals and lexical scopes
    (`let`, `match`, nested functions) are not handled reliably. -/
private partial def collectFreeNames (stx : Syntax) (bound : Std.HashSet Name) : Array Name :=
  match stx with
  | .ident _ _ n _ =>
    -- All identifiers outside `bound` are included, including globals.
    -- There is no subsequent elaboration-based capture filtering.
    if bound.contains n || n.isAnonymous then #[] else #[n]
  | .node _ kind args =>
    -- For `fun` binders: add parameters to bound set before traversing body
    if kind == `Lean.Parser.Term.fun then
      -- Structure: `fun` <binders> `=>` <body>
      -- args typically: [funBinder*, `=>`, body]
      -- The binders are in args[1] (the matchAlts or funBinder), body is the last arg
      let binderNames := args[:args.size - 1].foldl (fun acc a => acc ++ collectBinderNames a) #[]
      let innerBound := binderNames.foldl (fun s n => s.insert n) bound
      if args.size > 0 then
        collectFreeNames args.back! innerBound
      else #[]
    -- For `let` expressions: add the bound name
    else if kind == `Lean.Parser.Term.letDecl || kind == `Lean.Parser.Term.let then
      let binderNames := args[:1].foldl (fun r a => r ++ collectBinderNames a) #[]
      let innerBound := binderNames.foldl (fun s n => s.insert n) bound
      args.foldl (fun r a => r ++ collectFreeNames a innerBound) #[]
    else
      -- General case: recurse into all children
      args.foldl (fun r a => r ++ collectFreeNames a bound) #[]
  | .atom .. => #[]
  | .missing => #[]

open Lean in
/-- Parsed result of a `fun` term: binder names, individual binder syntaxes, and body.

    Syntax structure:
    ```
    (Term.fun "fun" (Term.basicFun [binder₁ binder₂ ...] [] "=>" body))
    ```
    - `Term.fun` has children: `"fun"`, `Term.basicFun`
    - `Term.basicFun` has children: `[binders]`, `[]`, `"=>"`, `body`
    - The binders node is a null node containing individual binder syntaxes -/
private structure ParsedFun where
  binderNames : Array Name
  binderStxs  : Array Syntax  -- individual binder syntaxes (for counting/rewriting)
  body        : Syntax

open Lean in
/-- Extract the binder names, individual binder syntaxes, and body from a `fun` term. -/
private def parseFunTerm (fnStx : Syntax) : Option ParsedFun := do
  guard (fnStx.getKind == `Lean.Parser.Term.fun)
  let funArgs := fnStx.getArgs
  guard (funArgs.size >= 2)
  let basicFun := funArgs[1]!
  guard (basicFun.getKind == `Lean.Parser.Term.basicFun)
  let bfArgs := basicFun.getArgs
  guard (bfArgs.size >= 4)
  -- bfArgs[0] = binder patterns (null node with idents/typed binders)
  let binderNode := bfArgs[0]!
  let body := bfArgs[3]!
  let binderStxs := binderNode.getArgs
  let binderNames := collectBinderNames binderNode
  some { binderNames, binderStxs, body }

open Lean in
/-- Given a function term, collect the free nominal variables (names that appear
    in the body but are not bound by the lambda). Returns deduplicated names. -/
private def collectCaptureSyntax (fnStx : Syntax) : Array Name :=
  match parseFunTerm fnStx with
  | some pf =>
    let bound : Std.HashSet Name := pf.binderNames.foldl (fun s n => s.insert n) {}
    let freeNames := collectFreeNames pf.body bound
    -- Deduplicate while preserving order
    freeNames.foldl (fun (acc : Array Name × Std.HashSet Name) n =>
      if acc.2.contains n then acc
      else (acc.1.push n, acc.2.insert n)) (#[], {}) |>.1
  | none => #[]

/-- Experimental syntax-only macro for constructing an `NFun` from candidate
captures and a generated support proof. Automatic capture mode rejects `let`,
`match`, nested functions, and multiple binders. Globals are not distinguished
from captures by this syntax-only prototype. Explicit captures skip the scope
guards, but still require the generated support certificate to succeed.

Syntax variants:
- `nfun fun x => body` — automatic capture detection
- `nfun [capturing a b c] fun x => body` — explicit nonempty identifier list

There is no `(capturing S)` support-set form or `(bind a)` annotation. Use
`NFun.ofCaptures` for an explicit support set (including empty support), or
`NFun.equivariant` for a function with an equivariance proof.

See Urban, *Nominal Techniques in Isabelle/HOL*, JAR 2008, Section 5. -/
-- Syntax:
-- `nfun fun x => body`                    — automatic capture detection
-- `nfun [capturing a b c] fun x => body`   — explicit capture list
syntax "nfun " (atomic("[" "capturing " ident+ "]"))? term : term

open Lean in
/-- Core logic for the `nfun` macro: given capture idents and a function term,
    build the `NFun.ofCaptures` expression. -/
private def mkNFunSyntax (captureIdents : Array Lean.Ident) (fn : TSyntax `term)
    : MacroM (TSyntax `term) := do
  if captureIdents.isEmpty then
    `(NFun.ofCaptures ⟨$fn⟩ ∅ (by supports_nfun))
  else
    let firstIdent := captureIdents[0]!
    let initTerm ← `(Nominal.Set.supp $firstIdent)
    let rest : Array (TSyntax `term) := captureIdents[1:].toArray.map (⟨·.raw⟩)
    let unionTerm ← rest.foldlM (init := initTerm) fun acc id => do
      `($acc ∪ Nominal.Set.supp $id)
    let fromArgs : Array (TSyntax `term) := captureIdents.map (⟨·.raw⟩)
    `(NFun.ofCaptures ⟨$fn⟩ $unionTerm (by supports_nfun from $fromArgs*))

open Lean in
/-- Typed groups `(x y : X)` elaborate to several arguments, unlike one tuple pattern. -/
private def binderArity (binder : Syntax) : Nat :=
  if binder.isOfKind ``Lean.Parser.Term.typeAscription then
    let pattern := binder[1]
    if pattern.isOfKind ``Lean.Parser.Term.app then
      1 + pattern[1].getArgs.size
    else 1
  else 1

open Lean in
/-- Reject lexical scopes that the prototype's name collection cannot model.
Explicit capture lists skip this check and still require a support certificate. -/
private partial def hasUnsupportedScope (stx : Syntax) : Bool :=
  stx.getKind == ``Lean.Parser.Term.let ||
  stx.getKind == ``Lean.Parser.Term.letDecl ||
  stx.getKind == ``Lean.Parser.Term.match ||
  stx.getKind == ``Lean.Parser.Term.fun ||
  stx.getArgs.any hasUnsupportedScope

open Lean in
macro_rules
  | `(nfun $[[capturing $caps*]]? $fn:term) => do
    match caps with
    | some cs =>
      mkNFunSyntax cs fn
    | none =>
      if let some pf := parseFunTerm fn.raw then
        if pf.binderStxs.foldl (fun n binder => n + binderArity binder) 0 != 1 then
          Macro.throwError "nfun: automatic construction accepts one binder; use NFun.curry for curried nominal functions"
        if hasUnsupportedScope pf.body then
          Macro.throwError "nfun: automatic captures do not support let, match, or nested functions; use explicit [capturing ...] or NFun.ofCaptures with a proof"
      else
        Macro.throwError "nfun: automatic construction expects a single lambda; use NFun.ofCaptures with a proof"
      let freeNames := collectCaptureSyntax fn.raw
      let captureIdents := freeNames.map (fun n => mkIdent n)
      mkNFunSyntax captureIdents fn

/-! ### Tests -/

noncomputable section TEST
set_option linter.unusedVariables false

variable {α : Type*} [Name α] {X Y : Type*} [Nominal α X] [Nominal α Y]

-- Test: equivariant NFun (empty support)
private def testEquivariant : NFun α (X × X) X :=
  NFun.ofCaptures (PFun.mk fun p => p.1) ∅ (by supports_nfun)

-- Test: single capture (supp c) — using `from` clause
private def testSingleCapture (c : X) : NFun α X X :=
  NFun.ofCaptures (PFun.mk fun _ => c) (supp c) (by supports_nfun from c)

-- Test: union capture (supp a ∪ supp c) — using `from` clause
private def testUnionCapture₂ (a : X) (c : X) : NFun α X X :=
  NFun.ofCaptures (PFun.mk fun _ => c) (supp a ∪ supp c) (by supports_nfun from a c)

-- Test: three captures (supp a ∪ supp b ∪ supp c)
private def testTripleCapture (a b c : X) : NFun α X X :=
  NFun.ofCaptures (PFun.mk fun _ => c) (supp a ∪ supp b ∪ supp c) (by supports_nfun from a b c)

-- Test: pair output (products), two captures
private def testPairOutput (c d : X) : NFun α X (X × X) :=
  NFun.ofCaptures (PFun.mk fun _ => (c, d)) (supp c ∪ supp d) (by supports_nfun from c d)

-- Test: three captures (supp a ∪ supp b ∪ supp c), function uses all
private def testTripleUse (a b c : X) : NFun α X (X × X × X) :=
  NFun.ofCaptures (PFun.mk fun _ => (a, b, c)) (supp a ∪ supp b ∪ supp c) (by supports_nfun from a b c)

-- Test: equivariant with product pattern (like substFa)
private def testEquivariantProd : NFun α (X × X) X :=
  NFun.ofCaptures (PFun.mk fun p => p.2) ∅ (by supports_nfun)

-- Test: equivariant with the `equivariant` constructor
private def testEquivariantCtor : NFun α (X × X) X :=
  NFun.equivariant (fun p => p.1) (by intro π p; simp)

-- Test: NFun capturing another NFun (curried / higher-order)
private def testNFunCapture (f : NFun α X Y) (c : X) : NFun α X (Y × X) :=
  NFun.ofCaptures (PFun.mk fun x => (f x, c)) (supp f ∪ supp c) (by supports_nfun from f c)

-- Test: atom capture — constant function returning an atom
private def testAtomConst (a : α) : NFun α α α :=
  NFun.ofCaptures (PFun.mk fun _ => a) (supp a) (by supports_nfun from a)

-- Test: atom capture with conditional — body ignores input
private def testAtomConditional (x : α) (s : X) : NFun α α X :=
  NFun.ofCaptures (PFun.mk fun _ => s) (supp x ∪ supp s) (by supports_nfun from x s)

-- Test: two atom captures — non-conditional body
private def testTwoAtoms (a b : α) : NFun α α (α × α) :=
  NFun.ofCaptures (PFun.mk fun _ => (a, b)) (supp a ∪ supp b) (by supports_nfun from a b)

-- Test: atom + nominal mixed capture
private def testAtomAndNominal (a : α) (c : X) : NFun α α X :=
  NFun.ofCaptures (PFun.mk fun _ => c) (supp a ∪ supp c) (by supports_nfun from a c)

-- Test: three atoms
private def testThreeAtoms (a b c : α) : NFun α α (α × α × α) :=
  NFun.ofCaptures (PFun.mk fun _ => (a, b, c)) (supp a ∪ supp b ∪ supp c) (by supports_nfun from a b c)

-- Test: atom identity (equivariant)
private def testAtomId : NFun α α α :=
  NFun.ofCaptures (PFun.mk fun x => x) ∅ (by supports_nfun)

/-! #### Experimental `nfun` macro examples -/

-- Test: nfun equivariant (no captures)
private def testNfunEquiv : X × X ⟶ₙ X :=
  nfun fun p => p.1

-- Test: nfun single capture
private def testNfunCapture (c : X) : X ⟶ₙ X :=
  nfun fun _ => c

-- Test: nfun two captures
private def testNfunTwoCaptures (a b : X) : X ⟶ₙ X × X :=
  nfun fun _ => (a, b)

-- Test: nfun atom capture
private def testNfunAtom (a : α) : α ⟶ₙ α :=
  nfun fun _ => a

-- Test: nfun mixed atom and nominal
private def testNfunMixed (a : α) (c : X) : α ⟶ₙ X :=
  nfun fun _ => c

-- Test: nfun NFun capture (higher-order)
private def testNfunHigherOrder (f : X ⟶ₙ Y) (c : X) : X ⟶ₙ Y × X :=
  nfun fun x => (f x, c)

-- Test: nfun with explicit capturing override
private def testNfunCapturing (a : α) (c : X) : α ⟶ₙ X :=
  nfun [capturing a c] fun _ => c


-- Test: nfun identity (equivariant)
private def testNfunId : X ⟶ₙ X :=
  nfun fun x => x

-- Test: nfun product pattern (equivariant, like substFa)
private def testNfunProdPattern : X × X ⟶ₙ X :=
  nfun fun (a, _) => a

-- Test: nfun product pattern with capture
private def testNfunProdCapture (c : X) : X × X ⟶ₙ X × X :=
  nfun fun (a, _) => (a, c)

end TEST

end Nominal.Set
