import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0516Claim26072

noncomputable section

noncomputable def classicalIte {α : Sort*} (p : Prop) (a b : α) : α :=
  @ite α p (Classical.propDecidable p) a b

noncomputable def classicalFilter {α : Type*} (s : Finset α)
    (p : α → Prop) : Finset α :=
  @Finset.filter α p (Classical.decPred p) s

noncomputable def edgeFinset {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : Finset (Sym2 V) :=
  letI : Fintype T.edgeSet := Fintype.ofFinite _
  T.edgeFinset

abbrev ColorVar (q : ℕ) := Sum (Fin q) (Sum (Fin q) Unit)

def xVar (q : ℕ) (i : Fin q) : ColorVar q :=
  Sum.inl i

def zVar (q : ℕ) (i : Fin q) : ColorVar q :=
  Sum.inr (Sum.inl i)

def yVar (q : ℕ) : ColorVar q :=
  Sum.inr (Sum.inr ())

/-- A color is constant on an unordered host edge. -/
def monochromaticOn {V : Type*} (c : V → Fin 3)
    (e : Sym2 V) (i : Fin 3) : Prop :=
  ∀ v, v ∈ e → c v = i

def edgeWeight {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → Fin 3) (e : Sym2 V) : MvPolynomial (ColorVar 3) ℤ :=
  classicalIte (monochromaticOn c e 0)
    (MvPolynomial.X (zVar 3 0))
    (classicalIte (monochromaticOn c e 1)
      (MvPolynomial.X (zVar 3 1))
      (classicalIte (monochromaticOn c e 2)
        (MvPolynomial.X (zVar 3 2))
        (MvPolynomial.X (yVar 3))))

/-- The literal finite-color order-two generalized-degree monomial. -/
def gDegreeTwoMonomial {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (c : V → Fin 3) :
    MvPolynomial (ColorVar 3) ℤ :=
  (∏ v : V, MvPolynomial.X (xVar 3 (c v))) *
    (∏ e ∈ edgeFinset T, edgeWeight c e)

/-- The literal finite-color order-two generalized-degree polynomial. -/
def gDegreeTwo {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : MvPolynomial (ColorVar 3) ℤ :=
  ∑ c : V → Fin 3, gDegreeTwoMonomial T c

def colorOneVertexCount {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → Fin 3) : ℕ :=
  (classicalFilter Finset.univ (fun v => c v = (1 : Fin 3))).card

def colorOneMonochromaticEdgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (c : V → Fin 3) : ℕ :=
  (classicalFilter (edgeFinset T) (fun e => monochromaticOn c e 1)).card

/-- This is the `x₁^k z₁^(k-1)` filter on the coloring summands of `G_T^(2)`. -/
def gDegreeTwoCoefficientFilter {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (k : ℕ) (c : V → Fin 3) : Prop :=
  colorOneVertexCount c = k ∧
    colorOneMonochromaticEdgeCount T c = k - 1

def supportOfColor {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → Fin 3) : Finset V :=
  classicalFilter Finset.univ (fun v => c v = (1 : Fin 3))

/-- Connectivity in the induced host graph on a finite support. -/
def inducedConnected {V : Type*} [DecidableEq V]
    (T : SimpleGraph V) (S : Finset V) : Prop :=
  S.Nonempty ∧
    ∀ u, u ∈ S → ∀ v, v ∈ S →
      Relation.ReflTransGen
        (fun x y => T.Adj x y ∧ x ∈ S ∧ y ∈ S) u v

/-- A binary coloring of the complement, extended by color zero on the
support so that the complement coloring has no duplicate padding choices. -/
def ComplementBinaryColoring (V : Type*) (S : Finset V) :=
  {b : V → Fin 2 // ∀ v, v ∈ S → b v = 0}

def supportComplementData {V : Type*} [DecidableEq V]
    (T : SimpleGraph V) (k : ℕ) (S : Finset V)
    (b : V → Fin 2) : Prop :=
  S.card = k ∧ inducedConnected T S ∧
    ∀ v, v ∈ S → b v = 0

def binaryColorOnComplement {V : Type*} [DecidableEq V]
    (c : V → Fin 3) : V → Fin 2 :=
  fun v => if c v = (1 : Fin 3) then 0 else
    if c v = (0 : Fin 3) then 0 else 1

def rebuildTernaryColor {V : Type*} [DecidableEq V]
    (S : Finset V) (b : V → Fin 2) : V → Fin 3 :=
  fun v => if v ∈ S then 1 else if b v = (0 : Fin 2) then 0 else 2

def edgeInside {V : Type*} [DecidableEq V]
    (S : Finset V) (e : Sym2 V) : Prop :=
  ∀ v, v ∈ e → v ∈ S

def edgeOutside {V : Type*} [DecidableEq V]
    (S : Finset V) (e : Sym2 V) : Prop :=
  ∀ v, v ∈ e → v ∉ S

def residualVertexCount {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (c : V → Fin 3) (i : Fin 3) : ℕ :=
  (classicalFilter Finset.univ (fun v => v ∉ S ∧ c v = i)).card

def complementVertexCount {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (b : V → Fin 2) (i : Fin 2) : ℕ :=
  (classicalFilter Finset.univ (fun v => v ∉ S ∧ b v = i)).card

def residualMonochromaticEdgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (S : Finset V) (c : V → Fin 3) (i : Fin 3) : ℕ :=
  (classicalFilter (edgeFinset T) (fun e =>
    edgeOutside S e ∧ monochromaticOn c e i)).card

def complementMonochromaticEdgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (S : Finset V) (b : V → Fin 2) (i : Fin 2) : ℕ :=
  (classicalFilter (edgeFinset T) (fun e =>
    edgeOutside S e ∧ ∀ v, v ∈ e → b v = i)).card

def residualUnequalEdgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (S : Finset V) (c : V → Fin 3) : ℕ :=
  (classicalFilter (edgeFinset T) (fun e =>
    edgeOutside S e ∧ ∃ u, u ∈ e ∧ ∃ v, v ∈ e ∧ c u ≠ c v)).card

def complementUnequalEdgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (S : Finset V) (b : V → Fin 2) : ℕ :=
  (classicalFilter (edgeFinset T) (fun e =>
    edgeOutside S e ∧ ∃ u, u ∈ e ∧ ∃ v, v ∈ e ∧ b u ≠ b v)).card

/-- The residual vertex and edge statistics retained after deleting the
selected color-one support. -/
def residualStatisticsPreserved {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (S : Finset V) (c : V → Fin 3)
    (b : V → Fin 2) (k : ℕ) : Prop :=
  residualVertexCount S c 0 = complementVertexCount S b 0 ∧
    residualVertexCount S c 2 = complementVertexCount S b 1 ∧
    residualMonochromaticEdgeCount T S c 0 =
      complementMonochromaticEdgeCount T S b 0 ∧
    residualMonochromaticEdgeCount T S c 2 =
      complementMonochromaticEdgeCount T S b 1 ∧
    residualUnequalEdgeCount T S c = complementUnequalEdgeCount T S b ∧
    colorOneVertexCount c = k ∧
    (classicalFilter (edgeFinset T) (fun e => monochromaticOn c e 1)).card = k - 1

/-- Claim 26072: the exact `x₁^k z₁^(k-1)` coloring filter of the literal
finite-color `G_T^(2)` is in bijection with connected support plus a binary
coloring of the induced complement, with all residual statistics retained. -/
def claim_26072 : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (T : SimpleGraph V),
    T.IsTree →
      ∀ k : ℕ, 1 ≤ k →
        (∀ c : V → Fin 3,
          gDegreeTwoCoefficientFilter T k c →
            let S := supportOfColor c
            let b := binaryColorOnComplement c
            supportComplementData T k S b ∧
              (∀ v, rebuildTernaryColor S b v = c v) ∧
              residualStatisticsPreserved T S c b k) ∧
        (∀ (S : Finset V) (b : V → Fin 2),
          supportComplementData T k S b →
            gDegreeTwoCoefficientFilter T k (rebuildTernaryColor S b) ∧
              supportOfColor (rebuildTernaryColor S b) = S ∧
              (∀ v, binaryColorOnComplement
                (rebuildTernaryColor S b) v = b v) ∧
              residualStatisticsPreserved T S
                (rebuildTernaryColor S b) b k)

end

end MathlibPlus.Open.ResearchFormalization.R0516Claim26072
