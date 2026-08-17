import Mathlib

namespace MathlibPlus.Open.Research.FormalizationR0314

noncomputable section

open Classical
open scoped BigOperators

abbrev PottsPoly (m : ℕ) :=
  MvPolynomial (Fin m ⊕ (Fin m ⊕ Unit)) ℤ

abbrev PottsRat (m : ℕ) := FractionRing (PottsPoly m)

private def pottsX {m : ℕ} (i : Fin m) : PottsPoly m :=
  MvPolynomial.X (Sum.inl i)

private def pottsZ {m : ℕ} (i : Fin m) : PottsPoly m :=
  MvPolynomial.X (Sum.inr (Sum.inl i))

private def pottsY {m : ℕ} : PottsPoly m :=
  MvPolynomial.X (Sum.inr (Sum.inr ()))

private def pottsStateZ {m : ℕ} (s : Fin (m + 1)) : PottsPoly m :=
  if h : s = 0 then 1 else pottsZ ⟨s.val - 1, by omega⟩

private def pottsInteraction {m : ℕ}
    (s t : Fin (m + 1)) : PottsPoly m :=
  if s = 0 ∧ t = 0 then 1
  else if s = t then pottsStateZ s
  else pottsY

private def pottsInteractionMatrix (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) (PottsPoly m) :=
  fun s t => pottsInteraction s t

private def pottsLambda {m : ℕ} (s : Fin (m + 1)) : PottsPoly m :=
  if h : s = 0 then
    1 + pottsY * (∑ i : Fin m, pottsX i)
  else
    let i : Fin m := ⟨s.val - 1, by omega⟩
    pottsY + pottsX i * pottsZ i +
      pottsY *
        Finset.sum ((Finset.univ : Finset (Fin m)).erase i) pottsX

private def positiveStateIndex {m : ℕ}
    (s : Fin (m + 1)) (hs : s ≠ 0) : Fin m :=
  ⟨s.val - 1, by omega⟩

private def pottsStateWeight {m : ℕ} (s : Fin (m + 1)) : PottsPoly m :=
  if h : s = 0 then 1 else pottsX ⟨s.val - 1, by omega⟩

private def pottsEdgePairs {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset (Sym2 V) :=
  G.edgeSet.toFinite.toFinset

private def pottsEdgeInteraction {V : Type} [Fintype V] [DecidableEq V]
    {m : ℕ} (σ : V → Fin (m + 1)) (e : Sym2 V) : PottsPoly m :=
  Sym2.lift
    ⟨(fun a b => pottsInteraction (σ a) (σ b)), by
      intro a b
      by_cases hs : σ a = 0 <;>
        by_cases ht : σ b = 0 <;>
          by_cases he : σ a = σ b <;>
            simp [pottsInteraction, hs, ht, he] <;> aesop⟩ e

private def pottsAssignmentWeight
    {V : Type} [Fintype V] [DecidableEq V]
    {m : ℕ} (G : SimpleGraph V) (σ : V → Fin (m + 1)) : PottsPoly m :=
  Finset.prod (Finset.univ : Finset V) (fun v => pottsStateWeight (σ v)) *
    Finset.prod (pottsEdgePairs G) (pottsEdgeInteraction σ)

private def pottsMessage
    {V : Type} [Fintype V] [DecidableEq V]
    (m : ℕ) (G : SimpleGraph V) (r : V) (s : Fin (m + 1)) : PottsPoly m :=
  Finset.sum (Finset.univ : Finset (V → Fin (m + 1))) (fun σ =>
    if σ r = s then pottsAssignmentWeight G σ else 0)

private def pottsPhi
    {V : Type} [Fintype V] [DecidableEq V]
    (m : ℕ) (G : SimpleGraph V) (r : V) (s : Fin (m + 1)) : PottsPoly m :=
  Finset.sum (Finset.univ : Finset (Fin (m + 1)))
    (fun t => pottsInteraction s t * pottsMessage m G r t)

private def pottsOrdinary
    {V : Type} [Fintype V] [DecidableEq V]
    (m : ℕ) (G : SimpleGraph V) (r : V) : PottsPoly m :=
  Finset.sum (Finset.univ : Finset (Fin (m + 1))) (pottsMessage m G r)

private def attachLeaves
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) (k : ℕ) :
    SimpleGraph (Sum V (Fin k)) :=
  SimpleGraph.fromRel (fun a b =>
    match a, b with
    | Sum.inl v, Sum.inl w => G.Adj v w
    | Sum.inl v, Sum.inr _ => v = r
    | Sum.inr _, Sum.inl v => v = r
    | Sum.inr _, Sum.inr _ => False)

private def leafAugmentationTuple
    {V : Type} [Fintype V] [DecidableEq V]
    (m : ℕ) (G : SimpleGraph V) (r : V) :
    Fin (m + 1) → PottsPoly m :=
  fun k => pottsOrdinary m (attachLeaves G r k.val) (Sum.inl r)

private def rootedGraphIso
    {V W : Type} (G : SimpleGraph V) (r : V)
    (H : SimpleGraph W) (s : W) : Prop :=
  ∃ f : G ≃g H, f.toEquiv r = s

private def pottsMomentOverField {m : ℕ}
    (a : Fin (m + 1) → PottsPoly m) (k : Fin (m + 1)) : PottsRat m :=
  ∑ s : Fin (m + 1),
    algebraMap (PottsPoly m) (PottsRat m)
      (a s * pottsLambda s ^ k.val)

private def pottsVandermonde (m : ℕ) : PottsPoly m :=
  ∏ s : Fin (m + 1),
    ∏ t ∈ (Finset.univ : Finset (Fin (m + 1))).filter (fun t => s < t),
      (pottsLambda t - pottsLambda s)

private def stateOne {m : ℕ} (hm : 1 ≤ m) : Fin (m + 1) :=
  ⟨1, by omega⟩

/-- Claim 19704: the state-one message and the state-zero pinned factor both
have degree equal to the order of the finite rooted tree; hence unequal-order
rooted trees cannot collide under either invariant. -/
def treeOrderDetectedByDegree19704 : Prop :=
  (∀ {V : Type} [Fintype V] [DecidableEq V]
    (m : ℕ) (hm : 1 ≤ m)
    (G : SimpleGraph V) (r : V),
    G.IsTree →
    (MvPolynomial.degreeOf (Sum.inl (⟨0, by omega⟩))
        (pottsPhi m G r 0) = Fintype.card V ∧
      MvPolynomial.degreeOf (Sum.inl (⟨0, by omega⟩))
        (pottsMessage m G r (stateOne hm)) = Fintype.card V)) ∧
  (∀ {V W : Type} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (m : ℕ) (hm : 1 ≤ m)
    (G : SimpleGraph V) (r : V)
    (H : SimpleGraph W) (s : W),
    G.IsTree →
    H.IsTree →
    Fintype.card V ≠ Fintype.card W →
      pottsPhi m G r 0 ≠ pottsPhi m H s 0 ∧
      pottsMessage m G r (stateOne hm) ≠
        pottsMessage m H s (stateOne hm))

/-- Claim 19705: attaching `k` ordinary leaves at the specified root gives the
lambda-power moment expansion of the ordinary Potts invariant. -/
def leafAugmentationMomentFormula19705 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V]
    (m : ℕ) (G : SimpleGraph V) (r : V) (k : ℕ),
    1 ≤ m →
    G.IsTree →
    pottsOrdinary m (attachLeaves G r k) (Sum.inl r) =
      ∑ s : Fin (m + 1),
        pottsMessage m G r s * pottsLambda s ^ k

/-- Claim 19706: the displayed formal lambda differences and the associated
Vandermonde determinant are nonzero in the independent-variable polynomial
ring. -/
def augmentationVandermondeNonsingular19706 : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    (∀ s : Fin (m + 1), ∀ hs : s ≠ 0,
      pottsLambda s - pottsLambda 0 =
        (pottsY - 1) +
          pottsX (positiveStateIndex s hs) *
            (pottsZ (positiveStateIndex s hs) - pottsY) ∧
      pottsLambda s - pottsLambda 0 ≠ 0) ∧
    (∀ s t : Fin (m + 1), ∀ hs : s ≠ 0, ∀ ht : t ≠ 0,
      s ≠ t →
        pottsLambda s - pottsLambda t =
          pottsX (positiveStateIndex s hs) *
              (pottsZ (positiveStateIndex s hs) - pottsY) -
            pottsX (positiveStateIndex t ht) *
              (pottsZ (positiveStateIndex t ht) - pottsY) ∧
        pottsLambda s - pottsLambda t ≠ 0) ∧
    Matrix.det (fun s t : Fin (m + 1) =>
        pottsLambda t ^ s.val) = pottsVandermonde m ∧
      pottsVandermonde m ≠ 0

/-- Claim 19707: the `m+1` augmentation moments recover the full message
vector over the rational-function field and determine rooted trees of any
orders, not only equal-order trees. -/
def completeRootedAugmentationInvariant19707 : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    (∀ a b : Fin (m + 1) → PottsPoly m,
      (∀ k : Fin (m + 1),
        pottsMomentOverField a k = pottsMomentOverField b k) →
        ∀ s : Fin (m + 1),
          algebraMap (PottsPoly m) (PottsRat m) (a s) =
            algebraMap (PottsPoly m) (PottsRat m) (b s)) ∧
    (∀ {V W : Type} [Fintype V] [DecidableEq V]
      [Fintype W] [DecidableEq W]
      (G : SimpleGraph V) (r : V)
      (H : SimpleGraph W) (s : W),
      G.IsTree →
      H.IsTree →
      leafAugmentationTuple m G r = leafAugmentationTuple m H s →
      rootedGraphIso G r H s)

end

end MathlibPlus.Open.Research.FormalizationR0314
