import Lean

/-!
# Statement measure for the reduction descent gate

`ledger/ledger.py` refuses a frontier-restructuring reduction unless every
unproven child strictly descends below its target in a fixed, agent-independent
statement measure. This module computes that measure. See
`docs/ADMISSION.md` (Reduction descent gate) for the governing contract.

The measure of a `def ... : Prop` body is taken relative to a signature Σ:

* Σ contains every constant that does not live in the `MathlibPlus` package
  (the pinned Mathlib/core signature agents cannot change), plus the project
  constants transitively used by the *target* statement (its phrasing is fixed
  by an earlier gated or externally reviewed admission). There is no mutable
  extension mechanism.
* Every other constant — anything the agent introduced — is δ-unfolded away
  before measuring. A non-Σ constant that cannot be unfolded (agent-minted
  inductive, axiom, opaque) makes the statement unmeasurable and the
  reduction inadmissible.

On the normalized term we report:

* `u`/`e`: minimal prenex Π/Σ levels, computed compositionally with polarity
  over `∀`/`∃`/`→`/`∧`/`∨`/`¬`/`↔`. Binders with non-`Prop` domains count as
  quantifiers (including higher-order and instance binders); `Prop` domains
  are implications. Everything else is an atom of rank 0. `rank = min u e`.
* `sexpr`/`size`: a serialized tree of the normalized quantifier-free matrix
  (∀/∃ binders erased after rank computation; implication and connectives
  retained; proof subterms collapsed by proof irrelevance) for the
  homeomorphic-embedding tie-break computed in `ledger/descent_gate.py`.
  Bound-variable indices and literal values collapse to finite labels, so the
  fixed signature gives the finite label alphabet required by Kruskal's theorem.

Output: one `GATE-MEASURE {json}` line per requested declaration. Per-decl
failures are reported as `ok := false` rows; the process itself succeeds so
the gate can distinguish unmeasurable statements from infrastructure errors.
-/

namespace MathlibPlus.Meta.StatementMeasure

open Lean Meta

/-- Marker wrapping collapsed proof subterms. Serialized as `(proof <type>)`
with the proof argument dropped; never unfolded by normalization. -/
theorem proofMark (α : Prop) (h : α) : α := h

/-- Unfold budget per measured statement; exceeding it means unmeasurable. -/
def maxUnfolds : Nat := 20000

/-- Serialized-tree node budget per statement; exceeding it means unmeasurable. -/
def maxNodes : Nat := 100000

/-- Constants owned by this package or the submission file itself: everything
agents can introduce. Anything else is pinned signature. -/
def isProjectConst (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
    match env.header.moduleNames[idx.toNat]? with
    | some m => m.getRoot == `MathlibPlus
    | none => true
  | none => true

/-- Project constants transitively reachable from the listed declarations
(through both types and bodies). These are the target's own phrasing and stay
in Σ for the comparison. -/
partial def projectClosure (env : Environment) (roots : List Name) : NameSet :=
  go roots {}
where
  go : List Name → NameSet → NameSet
    | [], acc => acc
    | n :: rest, acc =>
      if acc.contains n then go rest acc
      else
        let acc := acc.insert n
        match env.find? n with
        | none => go rest acc
        | some ci =>
          let used := ci.type.getUsedConstants
            ++ (ci.value?.map Expr.getUsedConstants).getD #[]
          let next := used.toList.filter fun c =>
            isProjectConst env c && !acc.contains c
          go (next ++ rest) acc

structure Ctx where
  closure : NameSet

def mustUnfold (ctx : Ctx) (env : Environment) (n : Name) : Bool :=
  isProjectConst env n && !ctx.closure.contains n && n != ``proofMark

/-- Normalize a statement body: ζ-reduce lets, β-reduce, strip metadata,
δ-unfold every non-Σ constant everywhere (including inside atoms), and
collapse proof subterms to `proofMark`. Throws when a non-Σ constant cannot
be unfolded or the unfold budget is exhausted. -/
partial def norm (ctx : Ctx) (fuel : IO.Ref Nat) (e : Expr) : MetaM Expr := do
  let e := e.headBeta
  match e with
  | .mdata _ b => norm ctx fuel b
  | .letE _ _ v b _ => norm ctx fuel (b.instantiate1 v)
  | .forallE n t b bi => do
    let t' ← norm ctx fuel t
    withLocalDecl n bi t' fun x => do
      let b' ← norm ctx fuel (b.instantiate1 x)
      mkForallFVars #[x] b'
  | .lam n t b bi => do
    let t' ← norm ctx fuel t
    withLocalDecl n bi t' fun x => do
      let b' ← norm ctx fuel (b.instantiate1 x)
      mkLambdaFVars #[x] b'
  | _ => do
    if ← isProof e then
      let α ← instantiateMVars (← inferType e)
      let α' ← norm ctx fuel α
      return mkApp2 (mkConst ``proofMark) α' e
    let f := e.getAppFn
    match f with
    | .const n _ =>
      let env ← getEnv
      if mustUnfold ctx env n then
        let remaining ← fuel.get
        if remaining == 0 then
          throwError "unmeasurable: unfold budget exhausted while eliminating agent-introduced constants"
        fuel.set (remaining - 1)
        match ← withTransparency .all (unfoldDefinition? e) with
        | some e' => norm ctx fuel e'
        | none =>
          throwError "unmeasurable: agent-introduced constant '{n}' cannot be unfolded (inductive/axiom/opaque); rephrase over the fixed target signature"
      else
        let args ← e.getAppArgs.mapM (norm ctx fuel)
        return mkAppN f args
    | .proj s i b => do
      let b' ← norm ctx fuel b
      let args ← e.getAppArgs.mapM (norm ctx fuel)
      return mkAppN (.proj s i b') args
    | _ =>
      let f' ← if f.isApp || f.isLet || f.isMData || f.isLambda then norm ctx fuel f else pure f
      let args ← e.getAppArgs.mapM (norm ctx fuel)
      return mkAppN f' args

/-- Minimal prenex (Π-level, Σ-level) of a normalized proposition, computed
compositionally with polarity. -/
partial def rankOf (e : Expr) : MetaM (Nat × Nat) := do
  let e := e.headBeta
  match e with
  | .mdata _ b => rankOf b
  | .forallE n t b bi =>
    if ← isProp t then do
      let (u₁, e₁) ← rankOf t
      withLocalDecl n bi t fun x => do
        let (u₂, e₂) ← rankOf (b.instantiate1 x)
        return (max e₁ u₂, max u₁ e₂)
    else
      withLocalDecl n bi t fun x => do
        let (u₁, _) ← rankOf (b.instantiate1 x)
        let u := max 1 u₁
        return (u, u + 1)
  | _ =>
    if let some (_, p) := e.app2? ``Exists then
      let go (body : Expr) : MetaM (Nat × Nat) := do
        let (_, e₁) ← rankOf body
        let el := max 1 e₁
        return (el + 1, el)
      match p with
      | .lam n t b bi =>
        withLocalDecl n bi t fun x => go (b.instantiate1 x)
      | _ =>
        -- η-contracted predicate: introduce an argument of its actual domain.
        match ← whnf (← inferType p) with
        | .forallE n t _ bi =>
          withLocalDecl n bi t fun x => go (mkApp p x)
        | _ => throwError "unmeasurable: Exists predicate is not a function"
    else if let some (a, b) := e.app2? ``And then combine a b
    else if let some (a, b) := e.app2? ``Or then combine a b
    else if let some (a, b) := e.app2? ``Iff then do
      let (u₁, e₁) ← rankOf a
      let (u₂, e₂) ← rankOf b
      let u := max (max e₁ u₂) (max e₂ u₁)
      let v := max (max u₁ e₂) (max u₂ e₁)
      return (u, v)
    else if let some a := e.app1? ``Not then do
      let (u₁, e₁) ← rankOf a
      return (e₁, u₁)
    else
      return (0, 0)
where
  combine (a b : Expr) : MetaM (Nat × Nat) := do
    let (u₁, e₁) ← rankOf a
    let (u₂, e₂) ← rankOf b
    return (max u₁ u₂, max e₁ e₂)

/-- Serialize the normalized closed term as a labeled tree for the embedding
tie-break. Proof arguments under `proofMark` are dropped; bound-variable
indices and literal values collapse to finite labels, making the tree
α-invariant and preserving a finite label alphabet. -/
partial def serialize (budget : IO.Ref Nat) (e : Expr) : MetaM String := do
  let remaining ← budget.get
  if remaining == 0 then
    throwError "unmeasurable: serialized statement exceeds {maxNodes} nodes"
  budget.set (remaining - 1)
  match e with
  | .mdata _ b => serialize budget b
  | .bvar _ => return "bvar"
  | .fvar _ => return "fvar"
  | .mvar _ => return "mvar"
  | .sort _ => return "sort"
  | .const n _ => return n.toString
  | .lit (.natVal _) => return "natLit"
  | .lit (.strVal _) => return "strLit"
  | .forallE _ t b _ =>
    return s!"(all {← serialize budget t} {← serialize budget b})"
  | .lam _ t b _ =>
    return s!"(lam {← serialize budget t} {← serialize budget b})"
  | .letE _ t v b _ =>
    return s!"(let {← serialize budget t} {← serialize budget v} {← serialize budget b})"
  | .proj s i b =>
    return s!"(proj:{s}:{i} {← serialize budget b})"
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if f.isConstOf ``proofMark && args.size == 2 then
      return s!"(proof {← serialize budget args[0]!})"
    let mut out := s!"(@ {← serialize budget f}"
    for a in args do
      out := out ++ " " ++ (← serialize budget a)
    return out ++ ")"

structure Measure where
  u : Nat
  e : Nat
  size : Nat
  sexpr : String

/-- Serialize the quantifier-free matrix: erase ∀/∃ binders, retain logical
connectives (including implication polarity), and serialize atoms normally. -/
partial def serializeMatrix (budget : IO.Ref Nat) (e : Expr) : MetaM String := do
  let tick : MetaM Unit := do
    let remaining ← budget.get
    if remaining == 0 then
      throwError "unmeasurable: serialized statement exceeds {maxNodes} nodes"
    budget.set (remaining - 1)
  let e := e.headBeta
  match e with
  | .mdata _ b => serializeMatrix budget b
  | .forallE n t b bi =>
    if ← isProp t then do
      tick
      let left ← serializeMatrix budget t
      withLocalDecl n bi t fun x => do
        let right ← serializeMatrix budget (b.instantiate1 x)
        return s!"(imp {left} {right})"
    else
      withLocalDecl n bi t fun x =>
        serializeMatrix budget (b.instantiate1 x)
  | _ =>
    if let some (_, p) := e.app2? ``Exists then
      match p with
      | .lam n t b bi =>
        withLocalDecl n bi t fun x =>
          serializeMatrix budget (b.instantiate1 x)
      | _ =>
        match ← whnf (← inferType p) with
        | .forallE n t _ bi =>
          withLocalDecl n bi t fun x => serializeMatrix budget (mkApp p x)
        | _ => throwError "unmeasurable: Exists predicate is not a function"
    else if let some (a, b) := e.app2? ``And then binary "and" a b tick
    else if let some (a, b) := e.app2? ``Or then binary "or" a b tick
    else if let some (a, b) := e.app2? ``Iff then binary "iff" a b tick
    else if let some a := e.app1? ``Not then do
      tick
      return s!"(not {← serializeMatrix budget a})"
    else
      serialize budget e
where
  binary (tag : String) (a b : Expr) (tick : MetaM Unit) : MetaM String := do
    tick
    return s!"({tag} {← serializeMatrix budget a} {← serializeMatrix budget b})"

def measureValue (ctx : Ctx) (v : Expr) : MetaM Measure := do
  let fuel ← IO.mkRef maxUnfolds
  let v' ← norm ctx fuel v
  let (u, e) ← rankOf v'
  let budget ← IO.mkRef maxNodes
  let s ← serializeMatrix budget v'
  return { u, e, size := maxNodes - (← budget.get), sexpr := s }

def measureDecl (ctx : Ctx) (d : Name) : MetaM Json := do
  try
    let ci ← getConstInfo d
    let v ←
      if ci.type.isProp then
        match ci.value? with
        | some body => pure body
        | none => throwError "unmeasurable: {d} is declared `Prop` but has no body"
      else if ← isProp ci.type then
        -- Externally fixed theorem signatures are represented as scratch
        -- axioms; measure the proposition type, never the proof value.
        pure ci.type
      else
        throwError "unmeasurable: {d} is not a proposition declaration"
    let m ← measureValue ctx v
    return Json.mkObj
      [("decl", toJson d.toString), ("ok", toJson true), ("u", toJson m.u),
       ("e", toJson m.e), ("rank", toJson (min m.u m.e)),
       ("size", toJson m.size), ("sexpr", toJson m.sexpr)]
  catch ex =>
    return Json.mkObj
      [("decl", toJson d.toString), ("ok", toJson false),
       ("reason", toJson (← ex.toMessageData.toString))]

/-- Entry point used by `ledger/descent_gate.py`. Measures the target and each
child relative to the target's Σ and prints one `GATE-MEASURE` JSON line per
declaration. -/
def gate (target : Name) (children : List Name) : MetaM Unit := do
  let env ← getEnv
  let ctx : Ctx := { closure := projectClosure env [target] }
  for d in target :: children do
    let json ← measureDecl ctx d
    IO.println s!"GATE-MEASURE {json.compress}"

end MathlibPlus.Meta.StatementMeasure
