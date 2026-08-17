import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0848

noncomputable section
open Classical

/-- The leaf number of a finite labelled graph. -/
def leafNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  (Finset.univ.filter (fun v => (G.neighborSet v).ncard = 1)).card

/-- A labelled tree on the label set `Fin n`. -/
abbrev LabelledTree (n : ℕ) := {T : SimpleGraph (Fin n) // T.IsTree}

/-- A labelled card together with the missing label. -/
abbrev CardWithMissing (n : ℕ) :=
  Σ missing : Fin n,
    {C : SimpleGraph {x : Fin n // x ≠ missing} // C.IsTree}

/-- The labelled trees and cards retained by a leaf prefix. -/
abbrev TreePrefix (n L : ℕ) :=
  {T : LabelledTree n // leafNumber T.1 ≤ L}

abbrev RowBase (n k : ℕ) := CardWithMissing n × Fin k

def rowCardWithMissing {n k : ℕ} (r : RowBase n k) : CardWithMissing n :=
  let p : CardWithMissing n × Fin k := r
  p.1

def rowMissing {n k : ℕ} (r : RowBase n k) : Fin n :=
  (rowCardWithMissing r).1

def rowGraph {n k : ℕ} (r : RowBase n k) :
    SimpleGraph {x : Fin n // x ≠ rowMissing r} :=
  (rowCardWithMissing r).2.1

def rowChannel {n k : ℕ} (r : RowBase n k) : Fin k :=
  let p : CardWithMissing n × Fin k := r
  p.2

abbrev RowPrefix (n L k : ℕ) :=
  {r : RowBase n k // leafNumber (rowGraph r) ≤ L}

def deleteCard {n : ℕ} (T : SimpleGraph (Fin n)) (missing : Fin n) :
    SimpleGraph {x : Fin n // x ≠ missing} :=
  T.induce {x : Fin n | x ≠ missing}

def treeGraph {n L : ℕ} (T : TreePrefix n L) : SimpleGraph (Fin n) :=
  T.1.1

def cardDegree {V : Type*} [Fintype V] (C : SimpleGraph V) (v : V) : ℕ :=
  (C.neighborSet v).ncard

/-- The exact neighbour-load statistic on a card. -/
def neighborLoad {V : Type*} [Fintype V] (C : SimpleGraph V) (v : V) : ℕ :=
  ∑ u : V, if C.Adj v u then cardDegree C u - 1 else 0

/-- Constant and degree are the two retained channels. -/
def twoChannelWeight {V : Type*} [Fintype V] (c : Fin 2)
    (C : SimpleGraph V) (v : V) : ℕ :=
  if c.val = 0 then 1 else cardDegree C v

/-- The constant, degree, and neighbour-load channels. -/
def threeChannelWeight {V : Type*} [Fintype V] (c : Fin 3)
    (C : SimpleGraph V) (v : V) : ℕ :=
  if c.val = 0 then 1 else
    if c.val = 1 then cardDegree C v else neighborLoad C v

def twoChannelEntry {n L : ℕ} (r : RowPrefix n L 2)
    (T : TreePrefix n L) : ℚ :=
  if deleteCard (treeGraph T) (rowMissing r.1) = rowGraph r.1 then
    ∑ v : {x : Fin n // x ≠ rowMissing r.1},
      if (treeGraph T).Adj (rowMissing r.1) v.1 then
        (twoChannelWeight (rowChannel r.1) (rowGraph r.1) v : ℚ)
      else 0
  else 0

def threeChannelEntry {n L : ℕ} (r : RowPrefix n L 3)
    (T : TreePrefix n L) : ℚ :=
  if deleteCard (treeGraph T) (rowMissing r.1) = rowGraph r.1 then
    ∑ v : {x : Fin n // x ≠ rowMissing r.1},
      if (treeGraph T).Adj (rowMissing r.1) v.1 then
        (threeChannelWeight (rowChannel r.1) (rowGraph r.1) v : ℚ)
      else 0
  else 0

/-- The exact labelled three-channel leaf-prefix attachment matrix. -/
noncomputable def threeChannelLeafPrefixAttachmentMatrix (n L : ℕ) :
    Matrix (RowPrefix n L 3) (TreePrefix n L) ℚ :=
  fun r T => threeChannelEntry r T

/-- Deleting the neighbour-load row channel gives the two-channel matrix. -/
noncomputable def twoChannelLeafPrefixAttachmentMatrix (n L : ℕ) :
    Matrix (RowPrefix n L 2) (TreePrefix n L) ℚ :=
  fun r T => twoChannelEntry r T

noncomputable def twoChannelPrefixCorank (n L : ℕ) : ℕ :=
  letI : Fintype (TreePrefix n L) := Fintype.ofFinite _
  Fintype.card (TreePrefix n L) -
    Matrix.rank (twoChannelLeafPrefixAttachmentMatrix n L)

noncomputable def threeChannelPrefixCorank (n L : ℕ) : ℕ :=
  letI : Fintype (TreePrefix n L) := Fintype.ofFinite _
  Fintype.card (TreePrefix n L) -
    Matrix.rank (threeChannelLeafPrefixAttachmentMatrix n L)

/-- Claim 25281: the constant/degree order-six prefixes have corank 100,
forty dimensions beyond the sixty-dimensional Hamiltonian path kernel. -/
def claim25281 : Prop :=
  ∀ L : ℕ, 3 ≤ L ∧ L ≤ 5 →
    twoChannelPrefixCorank 6 L = 100 ∧
      threeChannelPrefixCorank 6 L = 60 ∧
      twoChannelPrefixCorank 6 L = threeChannelPrefixCorank 6 L + 40

/-- Claim 25282: the constant/degree order-seven prefixes have the extra
840-dimensional kernel while the three-channel prefixes are injective. -/
def claim25282 : Prop :=
  ∀ L : ℕ, 3 ≤ L ∧ L ≤ 6 →
    twoChannelPrefixCorank 7 L = 840 ∧
      threeChannelPrefixCorank 7 L = 0 ∧
      twoChannelPrefixCorank 7 L = threeChannelPrefixCorank 7 L + 840

/-- Claim 25283: the neighbour-load channel is nonredundant in both first
nontrivial filtered extensions. -/
def claim25283 : Prop :=
  (∀ L : ℕ, 3 ≤ L ∧ L ≤ 5 →
    twoChannelPrefixCorank 6 L = threeChannelPrefixCorank 6 L + 40) ∧
  (∀ L : ℕ, 3 ≤ L ∧ L ≤ 6 →
    twoChannelPrefixCorank 7 L = threeChannelPrefixCorank 7 L + 840)

end
end MathlibPlus.Open.ResearchFormalization.R0848
