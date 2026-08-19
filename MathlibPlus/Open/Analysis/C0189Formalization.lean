import Mathlib
import MathlibPlus.Open.Analysis.ExactRectangleRootCount

open Filter Set Topology
open scoped BigOperators

namespace MathlibPlus.Open.Analysis.C0189

noncomputable section

/-- The completed xi factor used by the saved shifted-Euler profile. -/
noncomputable def savedXi (s : ℂ) : ℂ :=
  (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2

/-- The forty nonconstant coefficients in the saved exact degree-forty state. -/
noncomputable def degreeFortyCoefficients : Fin 40 → ℝ := ![
  -0.8824739608624199,
  2.816598275979663,
  0,
  0,
  0,
  0,
  -0.291823441775511462704736925086,
  0.123027643379614215971149239916,
  -0.0207839545323778109243242278602,
  0.00175879823818437519844298958496,
  -0.0000745504928632908194611477445219,
  0.00000126611934386230650140945434773,
  -0.0000962868733179478142677130943071,
  0.0000558820202091420720825640386391,
  -0.0000139100370967417958365512517721,
  0.00000192498664927043176019189284646,
  -0.000000159947632046118214705947726983,
  0.00000000797918354852525141626009891496,
  -0.000000000221269934128117632858199186827,
  0.00000000000263110981640649324429400415442,
  -0.262485879293138696811453529258,
  0.479716993631056309733933684874,
  -0.412317825008294986447372578989,
  0.221649380148222154137010815745,
  -0.083586889068693743723503946004,
  0.0235049819103489560947393814009,
  -0.00511320399627730015582218838717,
  0.000880851274057917271986307776983,
  -0.000121984286127458368916292340705,
  0.0000137036370303364838670906898647,
  -0.00000125430795873661068934771059503,
  0.0000000935650762420777506259166938557,
  -0.00000000566591059162563393058893662904,
  0.000000000276151243918824774719168393892,
  -0.0000000000106769934473835092877646951221,
  0.000000000000320064050447796786137014932,
  -0.00000000000000717438851590558343652515247,
  0.000000000000000113194965167557381640221,
  -0.0000000000000000011214364678142967064466,
  0.00000000000000000000524910514987955377867]

/-- The saved state has constant coefficient one and the displayed list at
powers one through forty. -/
noncomputable def degreeFortyProfile : Polynomial ℝ :=
  1 + ∑ j : Fin 40,
    Polynomial.C (degreeFortyCoefficients j) *
      Polynomial.X ^ ((j : ℕ) + 1)

/-- The exact order-two shifted-Euler superheat-shadow plus center-carrier
leading-Dini model from the admitted C-0189 state. -/
noncomputable def degreeFortyModel (t : ℂ) : ℂ :=
  savedXi ((1 / 2 : ℂ) + Complex.I * t) /
      (2 * (Real.pi : ℂ)) *
    Complex.exp (-(0.015169226266280162 : ℂ) * t ^ 4) *
      (Polynomial.map (algebraMap ℝ ℂ) degreeFortyProfile).eval
        (t ^ 2 / (Real.sqrt 40 : ℂ)) -
    (690.225171612913413810019847006 : ℂ) /
      (2 * Complex.exp (100 : ℂ)) *
      (t * Complex.sin (40 * t) - (1 / 2 : ℂ) * Complex.cos (40 * t)) /
        (t ^ 2 + 1 / 4)

noncomputable def degreeFortyRectangle : Set ℂ :=
  rectangleClosed 0.01 20 (-0.499) 0.499

noncomputable def degreeFortyBoundary : Set ℂ :=
  rectangleBoundary 0.01 20 (-0.499) 0.499

noncomputable def degreeFortyBoundaryPath (s : ℝ) : ℂ :=
  rectangleBoundaryPath 0.01 20 (-0.499) 0.499 s

noncomputable def strictRealSignChange (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  (f a < 0 ∧ 0 < f b) ∨ (0 < f a ∧ f b < 0)

/-- A finite exact zero set with its analytic orders.  The order, rather
than an unconstrained multiplicity label, is used for the count. -/
def exactZeroMultiplicityData
    (F : ℂ → ℂ) (R : Set ℂ) (S : Finset ℂ) (mult : ℂ → ℕ) : Prop :=
  letI : DecidableEq ℂ := Classical.decEq ℂ
  AnalyticOnNhd ℂ F R ∧
    (∀ z : ℂ, z ∈ S ↔ z ∈ R ∧ F z = 0) ∧
    (∀ z : ℂ, z ∈ S →
      analyticOrderAt F z ≠ ⊤ ∧ mult z = analyticOrderNatAt F z) ∧
    (∀ z : ℂ, z ∉ S → mult z = 0)

/-- At least k distinct real zeros in a specified complex region. -/
def hasDistinctRealZeros
    (F : ℂ → ℂ) (R : Set ℂ) (k : ℕ) : Prop :=
  ∃ z : Fin k → ℝ,
    (∀ i : Fin k, (z i : ℂ) ∈ R ∧ F (z i : ℂ) = 0) ∧
    (∀ i : Fin k, (z i : ℂ).im = 0) ∧
    (∀ i j : Fin k, i ≠ j → z i ≠ z j)

/-- A subdivision trace records the actual finite boundary partition, its
refinement depths, and the set of endpoint evaluations.  Its half-plane
condition is the mathematical acceptance condition for each segment. -/
def boundarySubdivisionTrace
    (F : ℂ → ℂ) (a b c d : ℝ) (bound : ℝ)
    (segmentCount maximumDepth pointEvaluationCount : ℕ) : Prop :=
  let γ : ℝ → ℂ := rectangleBoundaryPath a b c d
  ∃ vertices : Fin (segmentCount + 1) → ℝ,
    ∃ depths : Fin segmentCount → ℕ,
      ∃ evaluated : Finset ℂ,
        vertices 0 = 0 ∧ vertices (Fin.last segmentCount) = 1 ∧
          (∀ i : Fin segmentCount,
            0 ≤ vertices i.castSucc ∧
              vertices i.succ ≤ 1 ∧
              vertices i.castSucc < vertices i.succ ∧
              depths i ≤ maximumDepth ∧
              (∀ s ∈ Icc (vertices i.castSucc) (vertices i.succ),
                bound < ‖F (γ s)‖) ∧
              ((∃ u : ℂ,
                  u ≠ 0 ∧
                    ∀ s ∈ Icc (vertices i.castSucc) (vertices i.succ),
                      0 < (u * F (γ s)).im) ∨
                (∃ u : ℂ,
                  u ≠ 0 ∧
                    ∀ s ∈ Icc (vertices i.castSucc) (vertices i.succ),
                      (u * F (γ s)).im < 0))) ∧
          (∃ i : Fin segmentCount, depths i = maximumDepth) ∧
          (∀ z : ℂ, z ∈ evaluated ↔
            ∃ i : Fin segmentCount,
              z = γ (vertices i.castSucc) ∨ z = γ (vertices i.succ)) ∧
          evaluated.card = pointEvaluationCount

/-- Claim 2795: the named degree-forty profile has the certified winding,
strict boundary margin, and saved certificate statistics. -/
def certifiedWindingCount_claim2795 : Prop :=
  (∀ z : ℂ, z ∈ degreeFortyBoundary → degreeFortyModel z ≠ 0) ∧
    MathlibPlus.Open.hasWindingNumber
      (degreeFortyModel ∘ degreeFortyBoundaryPath) 159 ∧
    (∀ z : ℂ, z ∈ degreeFortyBoundary →
      5.8065 * Real.rpow (10 : ℝ) (-43 : ℝ) <
        ‖degreeFortyModel z‖) ∧
    boundarySubdivisionTrace degreeFortyModel
      0.01 20 (-0.499) 0.499
      (5.8065 * Real.rpow (10 : ℝ) (-43 : ℝ))
      14933 3 14933

/-- Claim 2796: the certified disjoint strict sign changes and the resulting
155 distinct real zeros on the physical interval. -/
def certifiedRealSignChanges_claim2796 : Prop :=
  ∃ intervals : Fin 155 → ℝ × ℝ,
    ∃ zeros : Fin 155 → ℝ,
      (∀ i : Fin 155,
        0.01 ≤ (intervals i).1 ∧
          (intervals i).2 ≤ 20 ∧
          (intervals i).1 < (intervals i).2 ∧
          strictRealSignChange
            (fun x : ℝ => (degreeFortyModel (x : ℂ)).re)
            (intervals i).1 (intervals i).2 ∧
          zeros i ∈ Icc (intervals i).1 (intervals i).2 ∧
          (zeros i : ℂ) ∈ degreeFortyRectangle ∧
          degreeFortyModel (zeros i : ℂ) = 0) ∧
      (∀ i j : Fin 155, i ≠ j →
        Disjoint (Icc (intervals i).1 (intervals i).2)
          (Icc (intervals j).1 (intervals j).2)) ∧
      (∀ i j : Fin 155, i ≠ j → zeros i ≠ zeros j)

/-- The zeros left after deleting a specified family of M distinct simple
real zeros, counted with their exact analytic orders. -/
def remainingZerosAtMost
    (S : Finset ℂ) (mult : ℂ → ℕ) (N M : ℕ) : Prop :=
  letI : DecidableEq ℂ := Classical.decEq ℂ
  ∀ z : Fin M → ℂ,
    (∀ i : Fin M, z i ∈ S ∧ (z i).im = 0 ∧ mult (z i) = 1) →
      (∀ i j : Fin M, i ≠ j → z i ≠ z j) →
        (∑ w ∈ S.filter (fun w : ℂ => ∀ i : Fin M, w ≠ z i), mult w) ≤ N - M

/-- Conjugation symmetry of a set and of a complex-valued function. -/
def conjugationSymmetricSet (R : Set ℂ) : Prop :=
  ∀ z : ℂ, z ∈ R ↔ star z ∈ R

def conjugationSymmetricFunction (F : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, F (star z) = star (F z)

def realOnRealAxis (F : ℂ → ℂ) : Prop :=
  ∀ x : ℝ, (F (x : ℂ)).im = 0

/-- The exact notion of a family of simple real sign changes used by the
excess-count principle. -/
def simpleRealSignChangeFamily
    (F : ℂ → ℂ) (a b : ℝ) (M : ℕ) : Prop :=
  ∃ intervals : Fin M → ℝ × ℝ,
    ∃ zeros : Fin M → ℝ,
      (∀ i : Fin M,
        a ≤ (intervals i).1 ∧
          (intervals i).2 ≤ b ∧
          (intervals i).1 < (intervals i).2 ∧
          strictRealSignChange
            (fun x : ℝ => (F (x : ℂ)).re)
            (intervals i).1 (intervals i).2 ∧
          zeros i ∈ Icc (intervals i).1 (intervals i).2 ∧
          F (zeros i : ℂ) = 0 ∧
          deriv F (zeros i : ℂ) ≠ 0) ∧
      (∀ i j : Fin M, i ≠ j →
        Disjoint (Icc (intervals i).1 (intervals i).2)
          (Icc (intervals j).1 (intervals j).2)) ∧
      (∀ i j : Fin M, i ≠ j → zeros i ≠ zeros j)

/-- An independent isolation of q simple nonreal conjugate pairs. -/
def isolatedNonrealConjugatePairs
    (F : ℂ → ℂ) (R : Set ℂ) (S : Finset ℂ) (mult : ℂ → ℕ)
    (q : ℕ) : Prop :=
  ∃ representatives : Fin q → ℂ,
    (∀ i : Fin q,
      0 < (representatives i).im ∧
        representatives i ∈ R ∧
        F (representatives i) = 0 ∧
        F (star (representatives i)) = 0 ∧
        deriv F (representatives i) ≠ 0 ∧
        deriv F (star (representatives i)) ≠ 0 ∧
        mult (representatives i) = 1 ∧
        mult (star (representatives i)) = 1) ∧
    (∀ i j : Fin q, i ≠ j → representatives i ≠ representatives j) ∧
    (∀ z : ℂ, z ∈ S → z.im ≠ 0 →
      (∃ i : Fin q, z = representatives i ∨
        z = star (representatives i)))

/-- Claim 2797: the exact 159-zero count, the real count, and the two
nonreal conjugate pairs for the same named profile. -/
def exactlyTwoNonrealConjugatePairs_claim2797 : Prop :=
  let F : ℂ → ℂ := degreeFortyModel
  let R : Set ℂ := degreeFortyRectangle
  letI : DecidableEq ℂ := Classical.decEq ℂ
  letI : DecidablePred (fun z : ℂ => z.im ≠ 0) := Classical.decPred _
  ∃ S : Finset ℂ,
    ∃ mult : ℂ → ℕ,
      exactZeroMultiplicityData F R S mult ∧
        (∑ z ∈ S, mult z) = 159 ∧
        (∑ z ∈ S.filter (fun z : ℂ => z.im ≠ 0), mult z) = 4 ∧
        hasDistinctRealZeros F R 155 ∧
        realOnRealAxis F ∧
        conjugationSymmetricFunction F ∧
        ∃ z₁ z₂ : ℂ,
          0 < z₁.im ∧
            0 < z₂.im ∧
            z₁ ≠ z₂ ∧
            z₁ ∈ R ∧
            z₂ ∈ R ∧
            star z₁ ∈ R ∧
            star z₂ ∈ R ∧
            F z₁ = 0 ∧
            F (star z₁) = 0 ∧
            F z₂ = 0 ∧
            F (star z₂) = 0 ∧
            (∀ z : ℂ, z ∈ R → F z = 0 → z.im ≠ 0 →
              z = z₁ ∨ z = star z₁ ∨ z = z₂ ∨ z = star z₂)

/-- Claim 2799: the global excess-count implication, including the exact
analytic count and the independent-isolation-to-pair-count clause. -/
def globalExcessCountPrinciple_claim2799 : Prop :=
  ∀ (F : ℂ → ℂ) (R : Set ℂ) (a b c d : ℝ) (N M : ℕ),
    R = rectangleClosed a b c d →
    a < b →
    c < d →
    conjugationSymmetricSet R →
    conjugationSymmetricFunction F →
    AnalyticOnNhd ℂ F R →
    (∀ z : ℂ, z ∈ rectangleBoundary a b c d → F z ≠ 0) →
    MathlibPlus.Open.hasWindingNumber
      (fun s : ℝ => F (rectangleBoundaryPath a b c d s)) (N : ℤ) →
    simpleRealSignChangeFamily F a b M →
    ∃ S : Finset ℂ,
      ∃ mult : ℂ → ℕ,
        exactZeroMultiplicityData F R S mult ∧
          (∑ z ∈ S, mult z) = N ∧
          M ≤ N ∧
          remainingZerosAtMost S mult N M ∧
          (∑ z ∈ S.filter (fun z : ℂ => z.im ≠ 0), mult z) ≤ N - M ∧
          ((∃ q : ℕ,
              isolatedNonrealConjugatePairs F R S mult q ∧
                (∑ z ∈ S.filter (fun z : ℂ => z.im ≠ 0), mult z) =
                  N - M) →
            ∃ q : ℕ,
              isolatedNonrealConjugatePairs F R S mult q ∧
                2 * q = N - M ∧
                q = (N - M) / 2)

end

end MathlibPlus.Open.Analysis.C0189
