import Mathlib


namespace MathlibPlus.Open.ResearchFormalizationBatch

open scoped BigOperators
open Set

noncomputable section

/-! Exact finite-sequence formalization of the Poisson graph-energy estimate. -/

def poissonWeight (x : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-x) * x ^ n / (n.factorial : ℝ)

def mZero (x : ℝ) (u : ℕ → ℂ) : ℝ :=
  Real.sqrt (∑' n : ℕ, poissonWeight x n * ‖u n‖ ^ 2)

def mOne (x : ℝ) (u : ℕ → ℂ) : ℝ :=
  Real.sqrt (∑' n : ℕ, poissonWeight x n * ‖u (n + 1)‖ ^ 2)

def graphFinite (x : ℝ) (u : ℕ → ℂ) : Prop :=
  Summable (fun n : ℕ => poissonWeight x n * ‖u n‖ ^ 2) ∧
    Summable (fun n : ℕ => poissonWeight x n * ‖u (n + 1)‖ ^ 2)

def bilinearForm (x : ℝ) (u v : ℕ → ℂ) : ℂ :=
  ∑' n : ℕ,
    (poissonWeight x n : ℂ) *
      (u n * v (n + 2) - u (n + 1) * v (n + 1))

def claim4229 : Prop :=
  ∀ (x : ℝ) (u v : ℕ → ℂ),
    0 < x → graphFinite x u → graphFinite x v →
      Summable (fun n : ℕ =>
        ‖(poissonWeight x n : ℂ) *
          (u n * v (n + 2) - u (n + 1) * v (n + 1))‖) ∧
      ‖bilinearForm x u v‖ ≤
        (1 + Real.sqrt 2) * mOne x u * mOne x v +
          (Real.sqrt x)⁻¹ * mZero x u * mOne x v

/-! Simple edges and the card coboundary carriers. -/

def SimpleEdge (V : Type*) [DecidableEq V] := {e : Finset V // e.card = 2}

def mapSimpleEdge {V : Type*} [DecidableEq V]
    (p : Equiv.Perm V) (e : SimpleEdge V) : SimpleEdge V :=
  ⟨e.1.image p, by
    calc
      (e.1.image p).card = e.1.card :=
        Finset.card_image_iff.mpr (by
          intro a ha b hb hab
          exact p.injective hab)
      _ = 2 := e.2⟩

def cardCompatibility {V A : Type*} [DecidableEq V] [AddGroup A]
    (π : V → Equiv.Perm V) (left right : SimpleEdge V → A) : Prop :=
  ∀ (i : V) (e : SimpleEdge V), i ∉ e.1 →
    left e = right (mapSimpleEdge (π i) e)

def cardCoboundaryZero {V A : Type*} [DecidableEq V] [AddGroup A]
    (π : V → Equiv.Perm V) (left right : SimpleEdge V → A) : Prop :=
  ∀ (i : V) (e : SimpleEdge V), i ∉ e.1 →
    left e - right (mapSimpleEdge (π i) e) = 0

def claim4443 : Prop :=
  ∀ {V A : Type*} [DecidableEq V] [AddGroup A]
    (π : V → Equiv.Perm V) (left right : SimpleEdge V → A),
    cardCompatibility π left right ↔ cardCoboundaryZero π left right

def constraintMultiplicity {V : Type*} [Fintype V] [DecidableEq V]
    (π : V → Equiv.Perm V) (e f : SimpleEdge V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i : V =>
    i ∉ e.1 ∧ mapSimpleEdge (π i) e = f)).card

def avoidedCount {V : Type*} [Fintype V] [DecidableEq V]
    (e : SimpleEdge V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i : V => i ∉ e.1)).card

def closedConstraintComponent {V : Type*} [Fintype V] [DecidableEq V]
    (π : V → Equiv.Perm V) (A B : Finset (SimpleEdge V)) : Prop :=
  (∀ e ∈ A, ∀ i : V, i ∉ e.1 → mapSimpleEdge (π i) e ∈ B) ∧
    (∀ f ∈ B, ∀ i : V, i ∉ f.1 →
      mapSimpleEdge (π i).symm f ∈ A)

def claim4448 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (π : V → Equiv.Perm V),
    (∀ i : V, π i i = i) →
      ∀ (A B : Finset (SimpleEdge V)),
        closedConstraintComponent π A B →
          ∀ f : SimpleEdge V, f ∈ B →
            ((Finset.sum A (fun e => constraintMultiplicity π e f)) = Fintype.card V - 2) ∧
              ((Finset.sum A (fun e => constraintMultiplicity π e f)) = avoidedCount f)

/-! The monomial Poisson--Charlier operator and its value. -/

def poissonCharlierSeed (n : ℕ) : Polynomial ℝ :=
  Polynomial.C ((n.factorial : ℝ)⁻¹) * Polynomial.X ^ n

def poissonCharlierOperator (p : Polynomial ℝ) : Polynomial ℝ :=
  p.derivative - p

def poissonCharlierIterate : ℕ → Polynomial ℝ → Polynomial ℝ
  | 0, p => p
  | r + 1, p => poissonCharlierIterate r (poissonCharlierOperator p)

def poissonCharlierPolynomial : ℕ → ℕ → Polynomial ℝ
  | n, 0 => poissonCharlierSeed n
  | n, r + 1 => poissonCharlierOperator (poissonCharlierPolynomial n r)

def claim4456 : Prop :=
  ∀ (n r : ℕ) (x : ℝ),
    poissonCharlierPolynomial n r =
        poissonCharlierIterate r (poissonCharlierSeed n) ∧
      (poissonCharlierPolynomial n r).eval x =
        (poissonCharlierIterate r (poissonCharlierSeed n)).eval x

/-! Connected spanning edge-subsets in the finite simple-graph carrier. -/

def connectedSpanningGraphs {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Finset (SimpleGraph V) := by
  classical
  exact Finset.univ.filter (fun H => H ≤ G ∧ H.Connected)

def graphEdgeCount {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ := by
  classical
  letI : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
  exact G.edgeFinset.card

def alphaPlus {V : Type*} [Fintype V]
    (k : ℕ) (G : SimpleGraph V) : ℚ := by
  classical
  exact if Fintype.card V = k then
    Finset.sum (connectedSpanningGraphs G) (fun _ => 1) else 0

def alphaMinus {V : Type*} [Fintype V]
    (k : ℕ) (G : SimpleGraph V) : ℚ := by
  classical
  exact if Fintype.card V = k then
    Finset.sum (connectedSpanningGraphs G)
      (fun H => (-1 : ℚ) ^ graphEdgeCount H) else 0

def emptyGraphIndicator {V : Type*} [Fintype V] (_G : SimpleGraph V) : ℚ :=
  if Fintype.card V = 0 then 1 else 0

def claim5746 : Prop :=
  ∀ (k : ℕ), 1 ≤ k →
    (∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
      0 < Fintype.card V → ¬ G.Connected →
        alphaPlus k G = 0 ∧ alphaMinus k G = 0) ∧
    (∀ {V W : Type*} [Fintype V] [Fintype W]
      (G : SimpleGraph V) (H : SimpleGraph W),
      alphaPlus k (G.sum H) =
          alphaPlus k G * emptyGraphIndicator H +
            emptyGraphIndicator G * alphaPlus k H ∧
        alphaMinus k (G.sum H) =
          alphaMinus k G * emptyGraphIndicator H +
            emptyGraphIndicator G * alphaMinus k H)

/-! The power-sum carrier for the chromatic symmetric-function identities. -/

def powerSumGenerator (k : ℕ) : MvPolynomial ℕ ℚ :=
  MvPolynomial.X k

def componentPowerProduct {V : Type*} [Fintype V]
    (G : SimpleGraph V) : MvPolynomial ℕ ℚ :=
  ∏ c : G.ConnectedComponent, powerSumGenerator c.supp.ncard

def spanningGraphs {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Finset (SimpleGraph V) := by
  classical
  exact Finset.univ.filter (fun H => H ≤ G)

def chromaticPowerSum {V : Type*} [Fintype V]
    (G : SimpleGraph V) : MvPolynomial ℕ ℚ := by
  classical
  exact Finset.sum (spanningGraphs G) (fun H =>
    MvPolynomial.C ((-1 : ℚ) ^ graphEdgeCount H) * componentPowerProduct H)

def connectedSubtreeSets {V : Type*} [Fintype V]
    (T : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (fun S : Finset V =>
    S.Nonempty ∧ (T.induce (↑S : Set V)).Connected)

def treeSubtreeContribution {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) : MvPolynomial ℕ ℚ := by
  classical
  let complement : Set V := (↑S : Set V)ᶜ
  letI : Fintype complement := Fintype.ofFinite _
  exact MvPolynomial.C ((-1 : ℚ) ^ (S.card - 1)) *
    powerSumGenerator S.card *
      chromaticPowerSum (T.induce complement)

def treeRecoveryRightHandSide {V : Type*} [Fintype V]
    (T : SimpleGraph V) : MvPolynomial ℕ ℚ := by
  classical
  exact MvPolynomial.C ((Fintype.card V : ℚ)⁻¹) *
    Finset.sum (connectedSubtreeSets T) (fun S =>
      MvPolynomial.C (S.card : ℚ) * treeSubtreeContribution T S)

def claim5759 : Prop :=
  ∀ {V : Type*} [Fintype V] (T : SimpleGraph V),
    T.Connected → T.IsAcyclic → 0 < Fintype.card V →
      chromaticPowerSum T = treeRecoveryRightHandSide T ∧
        treeSubtreeContribution T (Finset.univ : Finset V) =
          MvPolynomial.C ((-1 : ℚ) ^ (Fintype.card V - 1)) *
            powerSumGenerator (Fintype.card V)

/-! A marked fused regular pair, with the exact orbital and coordinate carriers. -/

def regularSubgroup {Ω : Type*}
    (P : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃! p : P, (p : Equiv.Perm Ω) x = y

def generatedPQ {Ω : Type*}
    (P Q : Subgroup (Equiv.Perm Ω)) : Subgroup (Equiv.Perm Ω) :=
  Subgroup.closure ((P : Set (Equiv.Perm Ω)) ∪ (Q : Set (Equiv.Perm Ω)))

def orbitalInvariant {Ω : Type*}
    (K : Subgroup (Equiv.Perm Ω)) (E : Ω → Ω → Prop) : Prop :=
  ∀ k : K, ∀ x y : Ω,
    E x y ↔ E ((k : Equiv.Perm Ω) x) ((k : Equiv.Perm Ω) y)

structure MarkedFusedRegularPair (H Ω : Type*) [Group H] [Fintype H] [Fintype Ω] where
  omega : Ω
  sourceSubgroup : Subgroup (Equiv.Perm Ω)
  targetSubgroup : Subgroup (Equiv.Perm Ω)
  iotaP : H ≃* ↥(sourceSubgroup)
  iotaQ : H ≃* ↥(targetSubgroup)
  E : Ω → Ω → Prop
  regularP : regularSubgroup sourceSubgroup
  regularQ : regularSubgroup targetSubgroup
  irreflexiveE : ∀ x : Ω, ¬ E x x
  symmetricE : ∀ {x y : Ω}, E x y → E y x
  orbitalE : orbitalInvariant (generatedPQ sourceSubgroup targetSubgroup) E

def relationPreserved {Ω : Type*} (E : Ω → Ω → Prop)
    (p : Equiv.Perm Ω) : Prop :=
  ∀ x y : Ω, E x y ↔ E (p x) (p y)

def claim5793 : Prop :=
  ∀ {H Ω : Type*} [Group H] [Fintype H] [Fintype Ω]
    (pair : MarkedFusedRegularPair H Ω),
    (∀ x : Ω, ¬ pair.E x x) ∧
      (∀ {x y : Ω}, pair.E x y → pair.E y x) ∧
      (∀ p : pair.sourceSubgroup, relationPreserved pair.E (p : Equiv.Perm Ω)) ∧
      (∀ q : pair.targetSubgroup, relationPreserved pair.E (q : Equiv.Perm Ω)) ∧
      (∀ (E : Ω → Ω → Prop),
        (∀ x, ¬ E x x) →
        (∀ {x y}, E x y → E y x) →
        orbitalInvariant (generatedPQ pair.sourceSubgroup pair.targetSubgroup) E →
          (∀ p : pair.sourceSubgroup, relationPreserved E (p : Equiv.Perm Ω)) ∧
            (∀ q : pair.targetSubgroup, relationPreserved E (q : Equiv.Perm Ω)))

def thetaP {H Ω : Type*} [Group H] [Fintype H] [Fintype Ω]
    (pair : MarkedFusedRegularPair H Ω) (h : H) : Ω :=
  ((pair.iotaP h : Equiv.Perm Ω) pair.omega)

def thetaQ {H Ω : Type*} [Group H] [Fintype H] [Fintype Ω]
    (pair : MarkedFusedRegularPair H Ω) (h : H) : Ω :=
  ((pair.iotaQ h : Equiv.Perm Ω) pair.omega)

def claim5794 : Prop :=
  ∀ {H Ω : Type*} [Group H] [Fintype H] [Fintype Ω]
    (pair : MarkedFusedRegularPair H Ω),
    Function.Bijective (thetaP pair) ∧ Function.Bijective (thetaQ pair)

def connectionSetP {H Ω : Type*} [Group H] [Fintype H] [Fintype Ω]
    (pair : MarkedFusedRegularPair H Ω) : Set H :=
  {c | c ≠ 1 ∧ pair.E pair.omega (thetaP pair c)}

def connectionSetQ {H Ω : Type*} [Group H] [Fintype H] [Fintype Ω]
    (pair : MarkedFusedRegularPair H Ω) : Set H :=
  {c | c ≠ 1 ∧ pair.E pair.omega (thetaQ pair c)}

def inverseClosed {H : Type*} [Group H] (S : Set H) : Prop :=
  ∀ c : H, c ∈ S ↔ c⁻¹ ∈ S

def claim5795 : Prop :=
  ∀ {H Ω : Type*} [Group H] [Fintype H] [Fintype Ω]
    (pair : MarkedFusedRegularPair H Ω),
    inverseClosed (connectionSetP pair) ∧ inverseClosed (connectionSetQ pair)

end
end MathlibPlus.Open.ResearchFormalizationBatch
