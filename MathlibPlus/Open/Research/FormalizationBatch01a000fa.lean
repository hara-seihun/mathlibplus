import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research.FormalizationBatch

/-! The finite carriers used for the weighted trace claims. -/

def kSunflower {α : Type} [DecidableEq α] (k : ℕ)
    (G : Finset (Finset α)) : Prop :=
  G.card = k ∧
    ∃ core : Finset α,
      (∀ A ∈ G, core ⊆ A) ∧
        (∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = core)

def uniformFamily {α : Type} [DecidableEq α] (s : ℕ)
    (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, A.card = s

def pairwiseIntersecting {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).Nonempty

def kSunflowerFree {α : Type} [DecidableEq α] (k : ℕ)
    (F : Finset (Finset α)) : Prop :=
  ∀ G : Finset (Finset α), G ⊆ F → ¬ kSunflower k G

def traceWeight {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) (Y T : Finset α) : ℕ :=
  (F.filter (fun A => A ∩ Y = T)).card

def occupiedTraces {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) (Y : Finset α) : Finset (Finset α) :=
  F.image (fun A => A ∩ Y)

def sourceDegree {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) (Y : Finset α) (y : α) : ℕ :=
  ∑ T ∈ occupiedTraces F Y, if y ∈ T then traceWeight F Y T else 0

def occupiedTraceCount {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) (Y : Finset α) (y : α) : ℕ :=
  (occupiedTraces F Y).filter (fun T => y ∈ T) |>.card

def collisionEnergy {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) (Y : Finset α) : ℕ :=
  ∑ y ∈ Y, sourceDegree F Y y * occupiedTraceCount F Y y

def totalTraceWeight {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) (Y : Finset α) : ℕ :=
  ∑ T ∈ occupiedTraces F Y, traceWeight F Y T

def traceSystem {α : Type} [DecidableEq α]
    (k r p : ℕ) (F : Finset (Finset α)) (Y : Finset α) : Prop :=
  3 ≤ k ∧ 1 ≤ p ∧
    uniformFamily r F ∧
      (∀ A ∈ F, (A ∩ Y).card = p) ∧
        pairwiseIntersecting F ∧ kSunflowerFree k F

def traceMatching {α : Type} [DecidableEq α]
    (occupied M : Finset (Finset α)) : Prop :=
  M ⊆ occupied ∧
    ∀ T ∈ M, ∀ U ∈ M, T ≠ U → T ∩ U = ∅

def matchingWeight {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) (Y : Finset α)
    (M : Finset (Finset α)) : ℕ :=
  ∑ T ∈ M, traceWeight F Y T

def traceDegreeSum {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) (Y T : Finset α) : ℕ :=
  ∑ y ∈ T, sourceDegree F Y y

def transformedMember {α : Type} [DecidableEq α]
    (A Y T : Finset α) : Finset (Sum α (Finset α)) :=
  (A \ Y).image Sum.inl ∪ {Sum.inr T}

def selectedFamily {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) (Y : Finset α) (M : Finset (Finset α)) :
    Finset (Finset α) :=
  F.filter (fun A => A ∩ Y ∈ M)

def transformedFamily {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) (Y : Finset α) (M : Finset (Finset α)) :
    Finset (Finset (Sum α (Finset α))) :=
  (selectedFamily F Y M).image (fun A => transformedMember A Y (A ∩ Y))

/-- Exact multiplicities, source degrees, and collision energy. -/
def claim_40385 : Prop :=
  ∀ (k r p : ℕ) (α : Type) [DecidableEq α]
    (F : Finset (Finset α)) (Y : Finset α),
    traceSystem k r p F Y →
      totalTraceWeight F Y = F.card ∧
        collisionEnergy F Y ≤ ∑ y ∈ Y, (sourceDegree F Y y) ^ 2

/-- The weighted matching bound and the resulting Cauchy--Schwarz inequality. -/
def claim_40386 : Prop :=
  ∀ (k r p : ℕ) (α : Type) [DecidableEq α]
    (F : Finset (Finset α)) (Y : Finset α),
    traceSystem k r p F Y →
      ∃ ν : ℚ,
        (∃ M : Finset (Finset α),
            traceMatching (occupiedTraces F Y) M ∧
              ν = (matchingWeight F Y M : ℚ)) ∧
          (∀ M : Finset (Finset α),
            traceMatching (occupiedTraces F Y) M →
              (matchingWeight F Y M : ℚ) ≤ ν) ∧
            ν ≥
              ∑ T ∈ occupiedTraces F Y,
                (traceWeight F Y T : ℚ) ^ 2 /
                  (traceDegreeSum F Y T : ℚ) ∧
              (F.card : ℚ) ^ 2 ≤ ν * (collisionEnergy F Y : ℚ)

/-- Deleting the literal coordinates and adding one fresh label per selected trace. -/
def claim_40387 : Prop :=
  ∀ (k r p : ℕ) (α : Type) [DecidableEq α]
    (F : Finset (Finset α)) (Y : Finset α)
    (M : Finset (Finset α)),
    traceSystem k r p F Y →
      traceMatching (occupiedTraces F Y) M →
        let G := transformedFamily F Y M
        G.card = matchingWeight F Y M ∧
          uniformFamily (r - p + 1) G ∧
            pairwiseIntersecting G ∧ kSunflowerFree k G

noncomputable def sunflowerExtremalSize (k s : ℕ) : ℕ :=
  sSup {n : ℕ |
    ∃ (α : Type) (inst : DecidableEq α),
      letI : DecidableEq α := inst
      ∃ F : Finset (Finset α),
        F.card = n ∧ uniformFamily s F ∧
          pairwiseIntersecting F ∧ kSunflowerFree k F}

/-- Extremal collision-energy transfer and its K-power consequence. -/
noncomputable def claim_40388 : Prop :=
  ∀ (k r p : ℕ) (α : Type) [DecidableEq α]
    (F : Finset (Finset α)) (Y : Finset α),
    traceSystem k r p F Y →
      let I := sunflowerExtremalSize k (r - p + 1)
      (∀ M : Finset (Finset α),
          traceMatching (occupiedTraces F Y) M →
            matchingWeight F Y M ≤ I) ∧
        (F.card : ℚ) ^ 2 ≤
          (I : ℚ) * (collisionEnergy F Y : ℚ) ∧
        (∀ K : ℝ,
          (collisionEnergy F Y : ℝ) ≤ K ^ p * (F.card : ℝ) →
            (F.card : ℝ) ≤ K ^ p * (I : ℝ))

/-! The explicit sheared integer lattice carriers. -/

def shearQuadratic (rho : ℝ) (d : ℤ × ℤ) : ℝ :=
  (d.1 : ℝ) ^ 2 + (d.2 : ℝ) ^ 2 +
    2 * rho * (d.1 : ℝ) * (d.2 : ℝ)

def indexDifference (u v : ℤ × ℤ) : ℤ × ℤ :=
  (u.1 - v.1, u.2 - v.2)

def coordinateStep (d : ℤ × ℤ) : Prop :=
  ((d.1 = 1 ∨ d.1 = -1) ∧ d.2 = 0) ∨
    (d.1 = 0 ∧ (d.2 = 1 ∨ d.2 = -1))

def unitAdjacent (rho : ℝ) (u v : ℤ × ℤ) : Prop :=
  shearQuadratic rho (indexDifference u v) = 1

def unitSeparated (rho : ℝ) (S : Finset (ℤ × ℤ)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
    1 ≤ shearQuadratic rho (indexDifference u v)

def parityBipartite (rho : ℝ) (S : Finset (ℤ × ℤ)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, unitAdjacent rho u v →
    (Even (u.1 + u.2) ∧ Odd (v.1 + v.2)) ∨
      (Odd (u.1 + u.2) ∧ Even (v.1 + v.2))

def triangleFreeUnitGraph (rho : ℝ) (S : Finset (ℤ × ℤ)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ∀ w ∈ S,
    u ≠ v → v ≠ w → u ≠ w →
      ¬ (unitAdjacent rho u v ∧ unitAdjacent rho v w ∧
        unitAdjacent rho w u)

def unitGraphConnected (rho : ℝ) (S : Finset (ℤ × ℤ)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S,
    Relation.ReflTransGen
      (fun a b => a ∈ S ∧ b ∈ S ∧ unitAdjacent rho a b) u v

noncomputable def endpointPositive : ℝ := (1 : ℝ) / 2
noncomputable def endpointNegative : ℝ := -(1 : ℝ) / 2

noncomputable def squaredDiameter (rho : ℝ)
    (S : Finset (ℤ × ℤ)) : ℝ :=
  if h : S.Nonempty then
    ((S.product S).image
      (fun uv => shearQuadratic rho (indexDifference uv.1 uv.2))).max'
      (by simpa using h.product h)
  else 0

noncomputable def maximumDistanceSquared (rho : ℝ)
    (z : ℤ × ℤ) (S : Finset (ℤ × ℤ)) : ℝ :=
  if h : S.Nonempty then
    (S.image (fun u => shearQuadratic rho (indexDifference z u))).max'
      (by simpa using h)
  else 0

def unitTriangle (rho : ℝ) (a b c : ℤ × ℤ) : Prop :=
  a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
    unitAdjacent rho a b ∧ unitAdjacent rho b c ∧ unitAdjacent rho c a

noncomputable def hexagonNorm (d : ℤ × ℤ) : ℕ :=
  max (max d.1.natAbs d.2.natAbs) (d.1 + d.2).natAbs

noncomputable def hexagonalCore (r : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(r : ℤ)) (r : ℤ)).product
      (Finset.Icc (-(r : ℤ)) (r : ℤ)) |>.filter
    (fun p => hexagonNorm p ≤ r)

def axialTail (r k : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc 1 k).image (fun t => (((r + t : ℕ) : ℤ), 0))

noncomputable def shearedAxialSource (r k : ℕ) : Finset (ℤ × ℤ) :=
  hexagonalCore r ∪ axialTail r k

noncomputable def shearParameter (r : ℕ) : ℝ :=
  endpointPositive - 1 / (16 * (r : ℝ))

def triangularTail (r k : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc 1 k).image
    (fun t => (((r + t : ℕ) : ℤ), -(t : ℤ)))

noncomputable def reindexedBoundarySource (r k : ℕ) : Finset (ℤ × ℤ) :=
  hexagonalCore r ∪ triangularTail r k

/-- Endpoint unit separation and the open-shear coordinate-step graph. -/
noncomputable def claim_40418 : Prop :=
  (∀ rho : ℝ, rho ∈ Set.Icc endpointNegative endpointPositive →
    ∀ a b : ℤ, (a, b) ≠ (0, 0) →
      (a * b ≥ 0 →
        shearQuadratic rho (a, b) ≥ (a : ℝ) ^ 2 + (b : ℝ) ^ 2 ∧
          1 ≤ (a : ℝ) ^ 2 + (b : ℝ) ^ 2) ∧
      (a * b < 0 →
        shearQuadratic rho (a, b) ≥ (a.natAbs : ℝ) ^ 2 +
            (b.natAbs : ℝ) ^ 2 - (a.natAbs : ℝ) * (b.natAbs : ℝ) ∧
          1 ≤ (a.natAbs : ℝ) ^ 2 + (b.natAbs : ℝ) ^ 2 -
            (a.natAbs : ℝ) * (b.natAbs : ℝ)) ∧
      1 ≤ shearQuadratic rho (a, b)) ∧
  (∀ rho : ℝ, rho ∈ Set.Ioo endpointNegative endpointPositive →
    (∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      1 < shearQuadratic rho (a, b)) ∧
    (∀ u v : ℤ × ℤ, unitAdjacent rho u v →
      coordinateStep (indexDifference u v))) ∧
  (∀ rho : ℝ, rho ∈ Set.Ioo endpointNegative endpointPositive →
    (∀ u v : ℤ × ℤ, unitAdjacent rho u v →
      (Even (u.1 + u.2) ∧ Odd (v.1 + v.2)) ∨
        (Odd (u.1 + u.2) ∧ Even (v.1 + v.2))) ∧
      (∀ u v w : ℤ × ℤ,
        u ≠ v → v ≠ w → u ≠ w →
          ¬ (unitAdjacent rho u v ∧ unitAdjacent rho v w ∧
            unitAdjacent rho w u)))

/-- An endpoint negative-product diameter witness excludes the indicated open shears. -/
noncomputable def claim_40419 : Prop :=
  (∀ (S : Finset (ℤ × ℤ)) (a b : ℤ),
    (∃ u ∈ S, ∃ v ∈ S, indexDifference u v = (a, b)) ∧
      (∀ u ∈ S, ∀ v ∈ S,
        shearQuadratic endpointPositive (indexDifference u v) ≤
          shearQuadratic endpointPositive (a, b)) ∧
      a * b < 0 →
        unitSeparated endpointPositive S ∧
          (∀ rho : ℝ, rho < endpointPositive →
            squaredDiameter rho S > squaredDiameter endpointPositive S)) ∧
  (∀ (S : Finset (ℤ × ℤ)) (a b : ℤ),
    (∃ u ∈ S, ∃ v ∈ S, indexDifference u v = (a, b)) ∧
      (∀ u ∈ S, ∀ v ∈ S,
        shearQuadratic endpointNegative (indexDifference u v) ≤
          shearQuadratic endpointNegative (a, b)) ∧
      a * b > 0 →
        unitSeparated endpointNegative S ∧
          (∀ rho : ℝ, endpointNegative < rho →
            squaredDiameter rho S > squaredDiameter endpointNegative S))

/-- The exposure margin gives strict whole-set endpoint descent. -/
noncomputable def claim_40421 : Prop :=
  ∀ (S C : Finset (ℤ × ℤ)) (a b : ℤ),
    C ⊆ S →
      (∃ u ∈ C, ∃ v ∈ C, indexDifference u v = (a, b)) →
      (∀ u ∈ C, ∀ v ∈ C,
        shearQuadratic endpointPositive (indexDifference u v) ≤
          shearQuadratic endpointPositive (a, b)) →
      a * b < 0 →
        ∀ delta : ℝ, 0 < delta →
          squaredDiameter endpointPositive S - squaredDiameter endpointPositive C <
              2 * delta * (a * b).natAbs →
            squaredDiameter (endpointPositive - delta) S >
              squaredDiameter endpointPositive S

/-- The one-point axial-tail screen and its exact diameter equalities. -/
noncomputable def claim_40422 : Prop :=
  ∀ r : ℕ, 1 ≤ r →
    let H := hexagonalCore r
    let S := H ∪ {(((r + 1 : ℕ) : ℤ), 0)}
    let rho := shearParameter r
    H.card = 1 + 3 * r * (r + 1) ∧
      S.card = 3 * r ^ 2 + 3 * r + 2 ∧
      squaredDiameter endpointPositive H = 4 * (r : ℝ) ^ 2 ∧
      squaredDiameter rho H = 4 * (r : ℝ) ^ 2 + (r : ℝ) / 2 ∧
      shearQuadratic rho
          (indexDifference (((r + 1 : ℕ) : ℤ), 0) (-(r : ℤ), 0)) =
        ((2 * r + 1 : ℕ) : ℝ) ^ 2 ∧
      squaredDiameter endpointPositive S = ((2 * r + 1 : ℕ) : ℝ) ^ 2 ∧
      squaredDiameter rho S = squaredDiameter endpointPositive S ∧
      unitTriangle endpointPositive (0, 0) (1, 0) (1, -1)

/-! The source embedding and the boundary reindexing. -/

noncomputable def shearVector (rho : ℝ) (a b : ℤ) : ℝ × ℝ :=
  ((a : ℝ) + rho * (b : ℝ), Real.sqrt (1 - rho ^ 2) * (b : ℝ))

def dotTwo (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2

def normSquaredTwo (u : ℝ × ℝ) : ℝ := dotTwo u u

def embeddedIndices (rho : ℝ) (S : Finset (ℤ × ℤ)) : Set (ℝ × ℝ) :=
  {v | ∃ p ∈ S, v = shearVector rho p.1 p.2}

def triangularLattice : Set (ℝ × ℝ) :=
  Set.range (fun p : ℤ × ℤ => shearVector endpointPositive p.1 p.2)

noncomputable def claim_40557 : Prop :=
  ∀ r k : ℕ, 1 ≤ r → 1 ≤ k →
    let rho := shearParameter r
    let S := shearedAxialSource r k
    endpointNegative < rho ∧ rho < endpointPositive ∧
      (normSquaredTwo (shearVector rho 1 0) = 1 ∧
        normSquaredTwo (shearVector rho 0 1) = 1 ∧
        dotTwo (shearVector rho 1 0) (shearVector rho 0 1) = rho) ∧
      (∀ a b : ℤ,
        normSquaredTwo (shearVector rho a b) = shearQuadratic rho (a, b)) ∧
      unitSeparated rho S ∧ unitGraphConnected rho S ∧
        parityBipartite rho S ∧ triangleFreeUnitGraph rho S

def hexagonVertices (r : ℕ) : Finset (ℤ × ℤ) :=
  {((r : ℤ), 0), ((r : ℤ), -(r : ℤ)), (0, -(r : ℤ)),
    (-(r : ℤ), 0), (-(r : ℤ), (r : ℤ)), (0, (r : ℤ))}

noncomputable def claim_40558 : Prop :=
  ∀ r k : ℕ, 1 ≤ r → 1 ≤ k →
    let rho := shearParameter r
    let H := hexagonalCore r
    let S := shearedAxialSource r k
    (squaredDiameter rho H = 4 * (r : ℝ) ^ 2 + (r : ℝ) / 2) ∧
      (∀ t ∈ Finset.Icc 1 k,
        maximumDistanceSquared rho (((r + t : ℕ) : ℤ), 0) H =
          maximumDistanceSquared rho (((r + t : ℕ) : ℤ), 0)
            (hexagonVertices r)) ∧
      (∀ t ∈ Finset.Icc 1 k,
        shearQuadratic rho
            (indexDifference (((r + t : ℕ) : ℤ), 0) (-(r : ℤ), 0)) =
          ((2 * r + t : ℕ) : ℝ) ^ 2) ∧
      (∀ t ∈ Finset.Icc 1 k,
        shearQuadratic rho
            (indexDifference (((r + t : ℕ) : ℤ), 0)
              (-(r : ℤ), (r : ℤ))) =
          3 * (r : ℝ) ^ 2 + 3 * (r : ℝ) * (t : ℝ) +
            (t : ℝ) ^ 2 + (2 * (r : ℝ) + (t : ℝ)) / 8 ∧
        shearQuadratic rho
            (indexDifference (((r + t : ℕ) : ℤ), 0) (-(r : ℤ), 0)) >
          shearQuadratic rho
            (indexDifference (((r + t : ℕ) : ℤ), 0)
              (-(r : ℤ), (r : ℤ)))) ∧
      squaredDiameter rho S = ((2 * r + k : ℕ) : ℝ) ^ 2

def claim_40559 : Prop :=
  ∀ r k : ℕ, 1 ≤ r → 1 ≤ k →
    let S := reindexedBoundarySource r k
    embeddedIndices endpointPositive S ⊆ triangularLattice ∧
      unitSeparated endpointPositive S ∧
      unitTriangle endpointPositive
        (((r : ℕ) : ℤ), 0) (((r : ℕ) : ℤ), -1)
        (((r + 1 : ℕ) : ℤ), -1)

end MathlibPlus.Open.Research.FormalizationBatch
