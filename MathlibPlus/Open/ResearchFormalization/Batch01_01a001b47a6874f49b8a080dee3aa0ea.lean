import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch01

/-! Exact finite-forest U-polynomial construction. -/

noncomputable def componentSizeOfSelectedEdges {V : Type*} [Fintype V]
    (A : Finset (Sym2 V))
    (C : (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))).ConnectedComponent) : ℕ :=
  letI : Fintype (C : Set V) := Fintype.ofFinite _
  Fintype.card (C : Set V)

noncomputable def uPolynomial {V : Type*} [Fintype V]
    (F : SimpleGraph V) (x : ℕ → MvPolynomial ℕ ℕ) : MvPolynomial ℕ ℕ := by
  classical
  letI : Fintype F.edgeSet := Fintype.ofFinite _
  exact (∑ A ∈ F.edgeFinset.powerset,
    ∏ C : (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))).ConnectedComponent,
      x (componentSizeOfSelectedEdges A C))

noncomputable def uPolynomialOfFiniteForest {V : Type*} [Fintype V]
    (F : SimpleGraph V) (_hF : F.IsAcyclic)
    (x : ℕ → MvPolynomial ℕ ℕ) : MvPolynomial ℕ ℕ :=
  uPolynomial F x

noncomputable def deleteVertices {V : Type*}
    (T : SimpleGraph V) (S : Finset V) : SimpleGraph {v // v ∉ S} :=
  T.induce {v | v ∉ S}

noncomputable def deletedUPolynomial {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V)
    (x : ℕ → MvPolynomial ℕ ℕ) : MvPolynomial ℕ ℕ := by
  classical
  letI : Fintype {v // v ∉ S} := Fintype.ofFinite _
  exact uPolynomial (deleteVertices T S) x

noncomputable def vertexDeletionAggregate {V : Type*} [Fintype V]
    (T : SimpleGraph V) (x : ℕ → MvPolynomial ℕ ℕ) (r : ℕ) :
    MvPolynomial ℕ ℕ :=
  if r = 0 then
    uPolynomial T x
  else
    ∑ S ∈ (Finset.univ : Finset V).powerset.filter (fun S => S.card = r),
      deletedUPolynomial T S x

noncomputable def completeVertexDeletionTower {V : Type*} [Fintype V]
    (T : SimpleGraph V) (_hT : T.IsTree)
    (x : ℕ → MvPolynomial ℕ ℕ) :
    Fin (Fintype.card V + 1) → MvPolynomial ℕ ℕ :=
  fun r => vertexDeletionAggregate T x (r : ℕ)

/-! The zero layer and the complete symmetric deletion tower. -/

/- The tree hypothesis is carried by the tower's domain; the exact aggregate
   is supplied by `vertexDeletionAggregate` for every allowed Fin index. -/

/-! Strict directed descent data and its post-entry reachability gate. -/

def strictHostDescentGraph {V Λ : Type*} [Fintype V] [Preorder Λ]
    (E : V → V → Prop) (S_ent _X_rk1 : Set V) (mu : V → Λ) : Prop :=
  S_ent.Nonempty ∧
    (∀ ⦃v w : V⦄, E v w → mu w < mu v)

def strictHostPostEntryGate {V Λ : Type*} [Preorder Λ]
    (E : V → V → Prop) (S_ent X_rk1 : Set V) (x : V) : Prop :=
  x ∈ X_rk1 ∧
    ∃ s : V, s ∈ S_ent ∧ Relation.ReflTransGen E s x

/-! Explicit lifted central-plane permutation. -/

abbrev CentralPlaneVertex (r : ℕ) :=
  (Fin 2 → ZMod 3) × ((Fin 3 → ZMod 3) × (Fin (r - 5) → ZMod 3))

def liftedCentralPlaneMap (r : ℕ) (v : CentralPlaneVertex r) :
    CentralPlaneVertex r :=
  let d := v.1
  let q := v.2.1
  let w := v.2.2
  let d' := Function.update d (0 : Fin 2)
    (d 0 + q 2 * q 0 + (q 2)^2 * q 1)
  let q' := Function.update q (0 : Fin 3) (q 0 + q 1 * q 2)
  (d', (q', w))

def claim57139 : Prop :=
  ∀ r : ℕ, (r = 6 ∨ r = 7) →
    Function.Bijective (liftedCentralPlaneMap r) ∧
      liftedCentralPlaneMap r 0 = 0

/-! Double-broom graph relation and independence-polynomial conclusion. -/

abbrev DoubleBroomVertex (r s d : ℕ) :=
  (Fin (d + 1)) ⊕ (Fin r ⊕ Fin s)

def doubleBroomAdjacent (r s d : ℕ) :
    DoubleBroomVertex r s d → DoubleBroomVertex r s d → Prop
  | Sum.inl i, Sum.inl j => i.val + 1 = j.val ∨ j.val + 1 = i.val
  | Sum.inl i, Sum.inr (Sum.inl _) => i.val = 0
  | Sum.inr (Sum.inl _), Sum.inl i => i.val = 0
  | Sum.inl i, Sum.inr (Sum.inr _) => i.val = d
  | Sum.inr (Sum.inr _), Sum.inl i => i.val = d
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inr _) => False
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inl _) => False
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inl _) => False
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _) => False

def doubleBroomIndependentSet (r s d : ℕ)
    (I : Finset (DoubleBroomVertex r s d)) : Prop :=
  ∀ v ∈ I, ∀ w ∈ I, ¬ doubleBroomAdjacent r s d v w

noncomputable def doubleBroomIndependencePolynomial
    (r s d : ℕ) : Polynomial ℕ := by
  classical
  exact (∑ I ∈ (Finset.univ : Finset (DoubleBroomVertex r s d)).powerset.filter
      (doubleBroomIndependentSet r s d),
    Polynomial.X ^ I.card)

def logConcaveNoInternalZeros (p : Polynomial ℕ) : Prop :=
  (∀ n : ℕ, 0 < n →
      p.coeff n ^ 2 ≥ p.coeff (n - 1) * p.coeff (n + 1)) ∧
    (∀ i j k : ℕ, i ≤ j → j ≤ k →
      p.coeff i ≠ 0 → p.coeff k ≠ 0 → p.coeff j ≠ 0)

def claim57347 : Prop :=
  ∀ r s d : ℕ, 0 ≤ r → 0 ≤ s → 1 ≤ d →
    logConcaveNoInternalZeros (doubleBroomIndependencePolynomial r s d)

/-! Literal balanced incidence matrix and its deletion heredity. -/

def groundPoints {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Finset α :=
  F.biUnion (fun A => A)

def balancedIncidenceMatrixOn {α : Type*} [DecidableEq α]
    (rows : Finset α) (cols : Finset (Finset α)) : Prop :=
  ∀ (rows' : Finset α) (cols' : Finset (Finset α)),
    rows' ⊆ rows → cols' ⊆ cols → rows'.card = cols'.card →
    Odd rows'.card →
    ¬ ((∀ x ∈ rows', (cols'.filter (fun A => x ∈ A)).card = 2) ∧
      (∀ A ∈ cols', (rows'.filter (fun x => x ∈ A)).card = 2))

def balancedLiteralIncidenceMatrix {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  balancedIncidenceMatrixOn (groundPoints F) F

def nUniformFamily {α : Type*} [DecidableEq α]
    (n : ℕ) (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, A.card = n

def balancedIncidenceMatrixHereditary {α : Type*} [DecidableEq α] : Prop :=
  ∀ (rows rows' : Finset α) (cols cols' : Finset (Finset α)),
    rows' ⊆ rows → cols' ⊆ cols →
    balancedIncidenceMatrixOn rows cols →
    balancedIncidenceMatrixOn rows' cols'

/-! Balanced sunflower-free bound, matching number, and sharpness. -/

def pairwiseDisjointFamily {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) : Prop :=
  ∀ ⦃A⦄, A ∈ G → ∀ ⦃B⦄, B ∈ G → A ≠ B → (A ∩ B).card = 0

noncomputable def matchingNumber {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : ℕ := by
  classical
  exact (F.powerset.filter (fun G => pairwiseDisjointFamily G)).sup Finset.card

def containsKSunflower {α : Type*} [DecidableEq α]
    (k : ℕ) (F : Finset (Finset α)) : Prop :=
  ∃ (C : Finset (Finset α)) (core : Finset α),
    C ⊆ F ∧ C.card = k ∧
      (∀ x : α, x ∈ core ↔ ∀ A ∈ C, x ∈ A) ∧
      (∀ ⦃A B⦄, A ∈ C → B ∈ C → A ≠ B → A ∩ B = core)

def kSunflowerFree {α : Type*} [DecidableEq α]
    (k : ℕ) (F : Finset (Finset α)) : Prop :=
  ¬ containsKSunflower k F

def claim58909 : Prop :=
  ∀ (k n : ℕ), 3 ≤ k →
    let q := k - 1
    (∀ {α : Type*} [DecidableEq α] (F : Finset (Finset α)),
      nUniformFamily n F → kSunflowerFree k F →
      balancedLiteralIncidenceMatrix F →
      F.card ≤ matchingNumber F * q ^ (n - 1) ∧
        matchingNumber F * q ^ (n - 1) ≤ q ^ n) ∧
    (∀ s : ℕ, 1 ≤ s → s ≤ q →
      ∃ F : Finset (Finset ℕ),
        nUniformFamily n F ∧ kSunflowerFree k F ∧
        balancedLiteralIncidenceMatrix F ∧ matchingNumber F = s ∧
        F.card = s * q ^ (n - 1))

end MathlibPlus.Open.ResearchFormalization.Batch01
