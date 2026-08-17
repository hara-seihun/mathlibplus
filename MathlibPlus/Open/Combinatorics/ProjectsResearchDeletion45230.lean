import MathlibPlus.Open.Combinatorics.ProjectsResearchAlternatingPopulation45229

open scoped BigOperators
open Classical
noncomputable section

namespace MathlibPlus.Open.ProjectsResearch

/-- The multiplicity of a mass-`q - ell` table after deleting an unordered
`ell`-subset from a table `x`: choose the surviving entries cell by cell. -/
def deletionMultiplicity45230
    (q ell : ℕ) (x y : Fin 6 → ℕ) : ℕ :=
  if massTable45229 (q - ell) y ∧ (∀ c : Fin 6, y c ≤ x c) then
    ∏ c : Fin 6, Nat.choose (x c) (y c)
  else 0

def deletionProfilePlus45230
    (q ell : ℕ) (y : Fin 6 → ℕ) : ℕ :=
  ∑ k ∈ (Finset.range (q + 1)).filter (fun k => Even k),
    Nat.choose q k *
      deletionMultiplicity45230 q ell (lineTable45229 q k) y

def deletionProfileMinus45230
    (q ell : ℕ) (y : Fin 6 → ℕ) : ℕ :=
  ∑ k ∈ (Finset.range (q + 1)).filter (fun k => Odd k),
    Nat.choose q k *
      deletionMultiplicity45230 q ell (lineTable45229 q k) y

def signedDeletionCoefficient45230
    (q ell : ℕ) (y : Fin 6 → ℕ) : ℤ :=
  (deletionProfilePlus45230 q ell y : ℤ) -
    (deletionProfileMinus45230 q ell y : ℤ)

def otherCellInvolved45230 (y : Fin 6 → ℕ) : Prop :=
  y cell445229 ≠ 0 ∨
    y cell1245229 ≠ 0 ∨
    y cell1345229 ≠ 0 ∨
    y cell2345229 ≠ 0

def alternatingBinomialSum45230 (ell : ℕ) : ℤ :=
  ∑ r ∈ Finset.range (ell + 1),
    (-1 : ℤ) ^ r * (Nat.choose ell r : ℤ)

def lineCoefficient45230 (q ell i : ℕ) : ℤ :=
  ∑ r ∈ Finset.range (ell + 1),
    (-1 : ℤ) ^ (i + r) * (Nat.choose q (i + r) : ℤ) *
      (Nat.choose (i + r) i : ℤ) *
      (Nat.choose (q - i - r) (q - ell - i) : ℤ)

def closedLineCoefficient45230 (q ell i : ℕ) : ℤ :=
  (-1 : ℤ) ^ i * (Nat.choose q i : ℤ) *
    (Nat.choose (q - i) ell : ℤ) * alternatingBinomialSum45230 ell

/-- The six residual-cell margins in the exact order from the admitted model. -/
def sixCellMargins45230 (x : Fin 6 → ℕ) : Fin 6 → ℕ :=
  fun c =>
    if c = 0 then x cell145229 + x cell1245229 + x cell1345229
    else if c = 1 then x cell245229 + x cell1245229 + x cell2345229
    else if c = 2 then x cell445229 + x cell1345229 + x cell2345229
    else if c = 3 then x cell1245229
    else if c = 4 then x cell1345229
    else x cell2345229

def sixCellMarginsInjective45230 : Prop :=
  ∀ x y : Fin 6 → ℕ,
    sixCellMargins45230 x = sixCellMargins45230 y → x = y

def marginPopulationPlus45230
    (q : ℕ) (m : Fin 6 → ℕ) : ℕ :=
  ∑ k ∈ (Finset.range (q + 1)).filter (fun k => Even k),
    if m = sixCellMargins45230 (lineTable45229 q k) then
      Nat.choose q k
    else 0

def marginPopulationMinus45230
    (q : ℕ) (m : Fin 6 → ℕ) : ℕ :=
  ∑ k ∈ (Finset.range (q + 1)).filter (fun k => Odd k),
    if m = sixCellMargins45230 (lineTable45229 q k) then
      Nat.choose q k
    else 0

/-- The complete profile data at all proper depths, indexed by `Fin q` so
that its entries are precisely depths `1, ..., q`. -/
def properDeletionDataPlus45230
    (q : ℕ) : (Fin q → (Fin 6 → ℕ) → ℕ) :=
  fun ell y => deletionProfilePlus45230 q (ell.val + 1) y

def properDeletionDataMinus45230
    (q : ℕ) : (Fin q → (Fin 6 → ℕ) → ℕ) :=
  fun ell y => deletionProfileMinus45230 q (ell.val + 1) y

def noProfileInversion45230 (q : ℕ) : Prop :=
  ¬ ∃ I :
      (Fin q → (Fin 6 → ℕ) → ℕ) → ((Fin 6 → ℕ) → ℕ),
      I (properDeletionDataPlus45230 q) = marginPopulationPlus45230 q ∧
        I (properDeletionDataMinus45230 q) = marginPopulationMinus45230 q

/-- Claim R-2816.3. The deletion profiles agree at every proper depth,
while the alternating populations and their induced six-margin populations
differ; the displayed cancellation is retained on the line and all other
four-cell outputs have zero signed coefficient. -/
def claim45230 : Prop :=
  ∀ q : ℕ, 1 ≤ q →
    (∀ ell : ℕ, 1 ≤ ell → ell ≤ q →
      deletionProfilePlus45230 q ell = deletionProfileMinus45230 q ell) ∧
    populationPlus45229 q ≠ populationMinus45229 q ∧
    (∀ ell : ℕ, 1 ≤ ell → ell ≤ q →
      ∀ i : ℕ, i ≤ q - ell →
        signedDeletionCoefficient45230 q ell
            (lineTable45229 (q - ell) i) = lineCoefficient45230 q ell i ∧
          lineCoefficient45230 q ell i = closedLineCoefficient45230 q ell i ∧
          closedLineCoefficient45230 q ell i = 0) ∧
    (∀ ell : ℕ, 1 ≤ ell → ell ≤ q →
      ∀ y : Fin 6 → ℕ, otherCellInvolved45230 y →
        signedDeletionCoefficient45230 q ell y = 0) ∧
    sixCellMarginsInjective45230 ∧
    marginPopulationPlus45230 q ≠ marginPopulationMinus45230 q ∧
    noProfileInversion45230 q

end MathlibPlus.Open.ProjectsResearch
