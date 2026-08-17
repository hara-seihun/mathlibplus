import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim1705

noncomputable section

/-- The selected row tuple for the partition `(n,3)`. -/
def thirdStripRows (d n : ℕ) : Fin d → ℕ :=
  fun i =>
    if i.1 < d - 2 then i.1
    else if i.1 = d - 2 then d + 1
    else d + n - 1

/-- The principal row tuple. -/
def principalRows (d : ℕ) : Fin d → ℕ := fun i => i.1

/-- The arithmetic Newton order attached to a flagged-array row index. -/
def newtonOrder (r : ℕ) : ℕ := r + 1

/-- The common principal block removed before comparing the two final orders. -/
def commonPrincipalBlock (d : ℕ) : List ℕ := List.range (d - 2)

/-- The complete selected row tuple written as a list. -/
def selectedRowList (d n : ℕ) : List ℕ :=
  List.ofFn (thirdStripRows d n)

/-- The two target Newton orders after the common principal block is removed. -/
def targetOrders (d n : ℕ) : List ℕ :=
  (selectedRowList d n).drop (d - 2) |>.map newtonOrder

/-- The two final principal Newton orders after the same block is removed. -/
def finalPrincipalOrders (d : ℕ) : List ℕ :=
  (List.ofFn (principalRows d)).drop (d - 2) |>.map newtonOrder

/-- Claim 1705: the neighboring row tuple and both two-entry Newton-order
lists, with the common principal block made explicit. -/
def claim1705_neighboringRowSetAndNewtonOrders : Prop :=
  ∀ (d n : ℕ),
    max n 4 ≤ d →
      selectedRowList d n = commonPrincipalBlock d ++ [d + 1, d + n - 1] ∧
        targetOrders d n = [d + 2, d + n] ∧
        finalPrincipalOrders d = [d - 1, d]

end

end MathlibPlus.Open.ResearchFormalization.Claim1705
