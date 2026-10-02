import Nominal.Set.NFun.Basic

/-!
# NFun construction tactics and experimental macro

* `supports_nfun` — discharge `supports S (PFun.mk f)` goals by parsing the support set `S`,
  auto-deriving fixpoint facts `π • cᵢ = cᵢ` for each component, and finishing with `simp`.
  Implements Urban's "free variables heuristic" (JAR 2008, Section 5).

* `nfun` is an experimental syntax-only macro. Simple projections, identity, and
  captures have examples below; global identifiers and `let`/`match`/nested-function
  scopes have known failures. Use `NFun.equivariant`, `NFun.ofSupports`, or
  `NFun.ofCaptures` with explicit support evidence for reliable construction.
-/

namespace Nominal.Set

open Core

/-! ### `supports_nfun` tactic

The tactic works via `supports_pfun_iff` + auto-derived fixpoint facts + `simp_all`.

Two modes:
* `supports_nfun` — just does `rw [supports_pfun_iff]; intro π hπ x; simp only [PFun.coe_mk]; simp_all [PermType.atoms_smul]`
* `supports_nfun from x₁ x₂ ...` — additionally derives `π • xᵢ = xᵢ` for each `xᵢ`
  via `supp_supports` (for nominal values) before the final `simp_all`.

The `from` clause uses the same membership-path construction as `choose_fresh`
(see `Nominal/Set/Freshness/Tactic.lean`).
-/

/-- `supports_nfun` discharges goals of the form `supports S (PFun.mk f)`.

Without arguments, it rewrites via `supports_pfun_iff`, introduces `π`, `hπ`, `x`,
and closes with `simp_all [PermType.atoms_smul]`.

With `supports_nfun from c₁ c₂ ...`, it additionally derives `π • cᵢ = cᵢ` for each
captured nominal value, making them available for the final `simp_all`. The support set
must be of the form `supp c₁ ∪ supp c₂ ∪ ... ∪ {a₁} ∪ ...` for the derivation to work.

See Urban, *Nominal Techniques in Isabelle/HOL*, JAR 2008, Section 5. -/
syntax "supports_nfun" (" from " (colGt term:max)+)? : tactic

open Lean Meta Elab Elab.Tactic in
/-- Build a membership path for index `i` in a left-associated union of `n` elements.
    Same algorithm as `choose_fresh` in `Freshness/Tactic.lean`. -/
private def mkMembershipPath (hmemId : TSyntax `ident) (i n : Nat) : MacroM (TSyntax `term) := do
  let mut directions : Array Bool := #[]
  let mut remaining := n
  while remaining > 1 do
    if i == remaining - 1 then
      directions := directions.push true
      remaining := 1
    else
      directions := directions.push false
      remaining := remaining - 1
  let mut proof : TSyntax `term := ⟨hmemId.raw⟩
  for dir in directions.reverse do
    if dir then
      proof ← `(Finset.mem_union_right _ $proof)
    else
      proof ← `(Finset.mem_union_left _ $proof)
  return proof

open Lean Meta Elab Elab.Tactic in
/-- Emit fixpoint facts for a list of captured nominal values.
    For each `cᵢ` in `cs`, emits:
    `have _hfix_i : π • cᵢ = cᵢ := supp_supports cᵢ π (fun _a _ha => hπ (path _ha))`
    where `path` embeds `_ha : _a ∈ supp cᵢ` into `_a ∈ S` (the full support set).

    Additionally, for FunLike-typed captures (e.g., `NFun`), derives the application form:
    `have _hfix_app_i : ∀ y, cᵢ (π • y) = π • cᵢ y`
    This is needed because `simp_all` can't automatically derive this from `π • cᵢ = cᵢ`. -/
private def emitFixpointFacts (cs : Array (TSyntax `term)) : TacticM Unit := do
  let n := cs.size
  for h : i in [:n] do
    let c := cs[i]
    let hfixId := mkIdent <| Name.mkSimple s!"_hfix_{i + 1}"
    let haId : TSyntax `ident := ⟨← withFreshMacroScope `(_ha_supp)⟩
    let hmemId : TSyntax `ident := ⟨← withFreshMacroScope `(_hmem_supp)⟩
    let pathProof ← liftMacroM <| mkMembershipPath hmemId i n
    evalTactic (← `(tactic|
      have $hfixId : π • $c = $c :=
        Nominal.Set.supp_supports $c π (fun $haId $hmemId ↦ hπ ($pathProof))))
    -- For FunLike-typed captures, also derive the application form
    let hfixAppId := mkIdent <| Name.mkSimple s!"_hfix_app_{i + 1}"
    try
      evalTactic (← `(tactic|
        have $hfixAppId : ∀ y, $c (π • y) = π • $c y := fun y => by
          have := congrArg (· (π • y)) $hfixId
          simp [NFun.smul_apply_smul] at this
          exact this.symm))
    catch _ => pure ()  -- Not FunLike — skip silently

open Lean Meta Elab Elab.Tactic in
elab_rules : tactic
  | `(tactic| supports_nfun $[from $cs:term*]?) => do
    -- Phase 1: Rewrite and introduce
    evalTactic (← `(tactic| rw [supports_pfun_iff]))
    evalTactic (← `(tactic| intro π hπ x))
    evalTactic (← `(tactic| simp only [PFun.coe_mk]))
    -- Phase 2: Derive fixpoint facts if captures provided
    if let some cs := cs then
      if cs.size > 0 then
        emitFixpointFacts cs
    -- Phase 3: Close the goal (if not already closed by simp only [PFun.coe_mk]).
    let goals ← Tactic.getUnsolvedGoals
    if !goals.isEmpty then
      evalTactic (← `(tactic| simp_all [PermType.atoms_smul, NFun.smul_apply_smul]))

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
captures and a generated support proof. Capture detection has known failures for
globals, `let`, `match`, and nested functions; ordinary multiple binders do not
automatically become a curried `NFun`.

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
macro_rules
  | `(nfun $[[capturing $caps*]]? $fn:term) => do
    match caps with
    | some cs =>
      mkNFunSyntax cs fn
    | none =>
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
