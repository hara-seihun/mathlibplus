import MathlibPlus.Open.ResearchFormalization.Claim37034

namespace MathlibPlus.Open.ResearchFormalization.R2105Claim37027

open Filter
open MathlibPlus.Open.ResearchFormalization

noncomputable section

/-- The side-one regular odd-polygon data for each shell. -/
def regularSideOneOddPolygon (q : ℕ) : Prop :=
  Odd q ∧
    polygonRadius q = 1 / (2 * Real.sin (Real.pi / (q : ℝ))) ∧
    polygonInradius q = polygonRadius q * Real.cos (Real.pi / (q : ℝ)) ∧
    polygonDiameter q = 1 / (2 * Real.sin (Real.pi / (2 * (q : ℝ))))

/-- The outer regular side-one shell in the admitted planar carrier. -/
def regularOuterDiameterShell (m : ℕ) : Prop :=
  regularSideOneOddPolygon m ∧
    diameter (polygonVertices m) = polygonDiameter m

/-- The second concentric shell is the explicit regular polygon at `M=m-8`.
Its inclusion in the constructed family is recorded without introducing a new
point-set carrier. -/
def secondConcentricShell (m : ℕ) : Prop :=
  let M := m - 8
  regularSideOneOddPolygon M ∧
    polygonVertices M ⊆ nestedShell m ∧
    polygonVertices M = regularPolygon M

/-- The explicit sheared lattice vectors have the prescribed inner product and
bulk cutoff. -/
def nearTriangularLatticeBulk (M : ℕ) : Prop :=
  (latticeU M).1 * (latticeV M).1 +
      (latticeU M).2 * (latticeV M).2 =
    (1 / 2 : ℝ) - 1 / (M : ℝ) ^ 2 ∧
    latticeBulk M = latticeSet M ∩ euclideanBall (polygonRadius M - 2)

/-- Claim 37027: the explicit nested regular-shell and sheared-lattice family
is eventually a finite, unit-separated, triangle-free planar local minimum of
diameter ratio.  The declaration contains no global-minimum predicate. -/
def claim37027 : Prop :=
  ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → Odd m →
    let M := m - 8
    let X := polygonVertices m ∪ polygonVertices M ∪ latticeBulk M
    X = nestedShell m ∧
      X.Finite ∧
      unitSeparated X ∧
      triangleFree X ∧
      localRatioMinimum X ∧
      regularOuterDiameterShell m ∧
      secondConcentricShell m ∧
      nearTriangularLatticeBulk M

end
end MathlibPlus.Open.ResearchFormalization.R2105Claim37027
