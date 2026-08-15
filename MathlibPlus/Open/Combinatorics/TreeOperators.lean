import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics

attribute [local instance] Classical.propDecidable

def graphIsoRel {n : ℕ} (g h : SimpleGraph (Fin n)) : Prop :=
  Nonempty (g ≃g h)

instance graphSetoid (n : ℕ) : Setoid (SimpleGraph (Fin n)) where
  r := graphIsoRel
  iseqv := by
    constructor
    · intro g
      exact ⟨SimpleGraph.Iso.refl⟩
    · intro g h ⟨e⟩
      exact ⟨e.symm⟩
    · intro g h k ⟨e⟩ ⟨f⟩
      exact ⟨e.trans f⟩

abbrev GraphClass (n : ℕ) := Quotient (graphSetoid n)

def graphClass {n : ℕ} (g : SimpleGraph (Fin n)) : GraphClass n := Quotient.mk _ g

def graphRep {n : ℕ} (q : GraphClass n) : SimpleGraph (Fin n) := Quotient.out q

def graftGraph {n : ℕ} (g : SimpleGraph (Fin n)) (v : Fin n) :
    SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.fromRel (fun a b =>
    (∃ i j, a = i.castSucc ∧ b = j.castSucc ∧ g.Adj i j) ∨
      (a = v.castSucc ∧ b = Fin.last n))

def deleteGraph {n : ℕ} (g : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1)) :
    SimpleGraph (Fin n) :=
  SimpleGraph.comap (Fin.succAbove v) g

def isLeaf {n : ℕ} (g : SimpleGraph (Fin n)) (v : Fin n) : Prop :=
  letI : Fintype (g.neighborSet v) := Fintype.ofFinite _
  g.degree v = 1

def subdivideGraph {n : ℕ} (g : SimpleGraph (Fin n)) (e : Sym2 (Fin n)) :
    SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.fromRel (fun a b =>
    (∃ i j, a = i.castSucc ∧ b = j.castSucc ∧ g.Adj i j ∧ s(i, j) ≠ e) ∨
      (∃ i j, e = s(i, j) ∧ g.Adj i j ∧
        ((a = i.castSucc ∧ b = Fin.last n) ∨
          (a = j.castSucc ∧ b = Fin.last n))))

def graphGraft {n : ℕ} (q : GraphClass n) (v : Fin n) : GraphClass (n + 1) :=
  graphClass (graftGraph (graphRep q) v)

def graphDelete {n : ℕ} (q : GraphClass (n + 1)) (v : Fin (n + 1)) : GraphClass n :=
  graphClass (deleteGraph (graphRep q) v)

def graphSubdivide {n : ℕ} (q : GraphClass n) (e : Sym2 (Fin n)) : GraphClass (n + 1) :=
  graphClass (subdivideGraph (graphRep q) e)

abbrev GraphSpace (n : ℕ) := GraphClass n →₀ ℚ

def treeSupported {n : ℕ} (x : GraphSpace n) : Prop :=
  ∀ q, ¬(graphRep q).IsTree → x q = 0

def treeSpace (n : ℕ) : Submodule ℚ (GraphSpace n) where
  carrier := {x | treeSupported x}
  zero_mem' := by
    intro q hq
    simp
  add_mem' := by
    intro x y hx hy q hq
    change treeSupported x at hx
    change treeSupported y at hy
    change (x + y) q = 0
    simp [hx q hq, hy q hq]
  smul_mem' := by
    intro c x hx q hq
    change treeSupported x at hx
    change (c • x) q = 0
    simp [hx q hq]

def extendBasis {α β : Type} (f : α → (β →₀ ℚ)) :
    (α →₀ ℚ) →ₗ[ℚ] (β →₀ ℚ) :=
  (Finsupp.lsum ℚ) (fun a => (LinearMap.id : ℚ →ₗ[ℚ] ℚ).smulRight (f a))

def graftBasis {n : ℕ} (q : GraphClass n) : GraphSpace (n + 1) :=
  ∑ v : Fin n, Finsupp.single (graphGraft q v) 1

def deleteBasis {n : ℕ} (q : GraphClass (n + 1)) : GraphSpace n :=
  ∑ v ∈ (Finset.univ.filter (fun v : Fin (n + 1) => isLeaf (graphRep q) v)),
    Finsupp.single (graphDelete q v) 1

def subdivideBasis {n : ℕ} (q : GraphClass n) : GraphSpace (n + 1) :=
  letI : Fintype ((graphRep q).edgeSet) := Fintype.ofFinite _
  ∑ e ∈ (graphRep q).edgeFinset, Finsupp.single (graphSubdivide q e) 1

def degreeGraftBasis {n : ℕ} (q : GraphClass n) : GraphSpace (n + 1) :=
  ∑ v : Fin n,
    letI : Fintype ((graphRep q).neighborSet v) := Fintype.ofFinite _
    ((graphRep q).degree v : ℚ) • Finsupp.single (graphGraft q v) 1

def G (n : ℕ) : GraphSpace n →ₗ[ℚ] GraphSpace (n + 1) :=
  extendBasis graftBasis

def L (n : ℕ) : GraphSpace (n + 1) →ₗ[ℚ] GraphSpace n :=
  extendBasis deleteBasis

def S (n : ℕ) : GraphSpace n →ₗ[ℚ] GraphSpace (n + 1) :=
  extendBasis subdivideBasis

def Gdeg (n : ℕ) : GraphSpace n →ₗ[ℚ] GraphSpace (n + 1) :=
  extendBasis degreeGraftBasis

def R (n : ℕ) : GraphSpace n →ₗ[ℚ] GraphSpace (n + 1) :=
  (2 * (n : ℚ) - 2) • G n - (n : ℚ) • Gdeg n + (n : ℚ) • S n

def correctedRaisingOperatorPreservesLeafKernel : Prop :=
  ∀ n : ℕ, ∀ x : GraphSpace (n + 1), x ∈ treeSpace (n + 1) →
    (L (n + 1) (R (n + 1) x) - R n (L n x) =
        (2 • G n (L n x) -
          Gdeg n (L n x) +
          S n (L n x)) ∧
      (L n x = 0 → R (n + 1) x ∈ treeSpace (n + 2) ∧
        L (n + 1) (R (n + 1) x) = 0))

end MathlibPlus.Open.Combinatorics
