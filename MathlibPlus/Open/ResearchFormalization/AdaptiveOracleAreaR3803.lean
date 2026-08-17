import MathlibPlus.Open.OracleAreaOccupation

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaR3803

open MathlibPlus.Open.OracleAreaOccupation

abbrev Driver (n : ℕ) := Configuration n → Sign
abbrev BooleanLaw (n : ℕ) := List (Driver n × ℝ)

/-- The real-valued table represented by a Boolean driver. -/
def driverValue (H : Driver n) : Configuration n → ℝ :=
  fun ω => signValue (H ω)

/-- A policy is complete: it chooses a fresh coordinate at every proper state,
so its full continuation is retained by `policyCost`. -/
def policyArea (d : DeterministicPolicy n) (g : Configuration n → ℝ) : ℝ :=
  policyCost g (deterministicKernel d)

/-- The transcript reached after `m` queries of a deterministic complete policy. -/
def policyState (d : DeterministicPolicy n) (ω : Configuration n) : ℕ → TranscriptState n
  | 0 => rootState
  | m + 1 =>
      let s := policyState d ω m
      if hs : s.1.card < n then
        let a := d ⟨s, hs⟩
        child s a.1 a.2 (ω a.1)
      else s

/-- A driver is determined at a transcript when all compatible outcomes give
it the same Boolean value. -/
def driverDetermined (H : Driver n) (s : TranscriptState n) : Prop :=
  ∀ ω ω', Consistent s ω → Consistent s ω' →
    driverValue H ω = driverValue H ω'

/-- The first determination time, expressed as the infimum over the finite
full-policy run. -/
noncomputable def stoppingTime (H : Driver n) (d : DeterministicPolicy n)
    (ω : Configuration n) : ℕ :=
  sInf {m : ℕ | driverDetermined H (policyState d ω m)}

/-- Uniform expected cost of the stopped prefix computing `H`. -/
noncomputable def expectedStoppingCost (H : Driver n) (d : DeterministicPolicy n) : ℝ :=
  (Fintype.card (Configuration n) : ℝ)⁻¹ *
    ∑ ω : Configuration n, (stoppingTime H d ω : ℝ)

/-- The minimum expected query cost of a Boolean driver. -/
noncomputable def qCost (H : Driver n) : ℝ :=
  sInf (Set.range (fun d : DeterministicPolicy n => expectedStoppingCost H d))

def qOptimal (H : Driver n) (d : DeterministicPolicy n) : Prop :=
  expectedStoppingCost H d = qCost H

/-- The constrained value obtained by retaining every full completion after a
q-optimal stopped prefix for `H`. -/
noncomputable def constrainedValue (H : Driver n) (g : Configuration n → ℝ) : ℝ :=
  sInf {z : ℝ | ∃ d : DeterministicPolicy n,
    qOptimal H d ∧ z = policyArea d g}

def activePolicy (H : Driver n) (g : Configuration n → ℝ)
    (d : DeterministicPolicy n) : Prop :=
  qOptimal H d ∧ policyArea d g = constrainedValue H g

/-- Polarization of the complete-policy posterior-variance quadratic. -/
def policyBilinear (d : DeterministicPolicy n)
    (f g : Configuration n → ℝ) : ℝ :=
  (policyArea d (fun ω => f ω + g ω) - policyArea d f - policyArea d g) / 2

/-- The active directional derivative used at a lower-envelope switch. -/
def directionalActive (K h : Driver n) (u : Configuration n → ℝ)
    (d : DeterministicPolicy n) : Prop :=
  activePolicy K u d ∧
    ∀ d' : DeterministicPolicy n, activePolicy K u d' →
      2 * policyBilinear d u (driverValue h) - policyArea d u - qCost K ≤
        2 * policyBilinear d' u (driverValue h) - policyArea d' u - qCost K

noncomputable def directionalMinimum (K h : Driver n)
    (u : Configuration n → ℝ) : ℝ :=
  sInf {z : ℝ | ∃ d : DeterministicPolicy n,
    activePolicy K u d ∧
      z = 2 * policyBilinear d u (driverValue h) - policyArea d u - qCost K}

def defect (H : Driver n) (g : Configuration n → ℝ) : ℝ :=
  constrainedValue H g - qCost H

noncomputable def lawWeightSum (law : BooleanLaw n) : ℝ :=
  (law.map Prod.snd).sum

def lawNonnegative (law : BooleanLaw n) : Prop :=
  ∀ entry ∈ law, 0 ≤ entry.2

def isProbabilityLaw (law : BooleanLaw n) : Prop :=
  lawNonnegative law ∧ lawWeightSum law = 1

noncomputable def lawBarycentre (law : BooleanLaw n) : Configuration n → ℝ :=
  fun ω =>
    (law.map (fun entry => entry.2 * driverValue entry.1 ω)).sum

noncomputable def lawExpectation (law : BooleanLaw n)
    (f : Driver n → ℝ) : ℝ :=
  (law.map (fun entry => entry.2 * f entry.1)).sum

noncomputable def lawPairExpectation (law : BooleanLaw n)
    (f : Driver n → Driver n → ℝ) : ℝ :=
  (law.map (fun entry =>
    (law.map (fun entry' => entry.2 * entry'.2 * f entry.1 entry'.1)).sum)).sum

noncomputable def score (law : BooleanLaw n) (h : Driver n) : ℝ :=
  let u := lawBarycentre law
  defect h u + lawExpectation law (fun K => directionalMinimum K h u)

noncomputable def residualX (law : BooleanLaw n) (h : Driver n)
    (rho : DeterministicPolicy n)
    (pi : Driver n → DeterministicPolicy n) : ℝ :=
  lawExpectation law (fun K =>
    policyArea rho (driverValue K) - qCost h +
      policyArea (pi K) (driverValue h) - qCost K)

noncomputable def residualPairDisagreement (law : BooleanLaw n)
    (rho : DeterministicPolicy n) : ℝ :=
  lawPairExpectation law (fun K L =>
    policyArea rho (fun ω => driverValue K ω - driverValue L ω))

noncomputable def directionDisagreement (law : BooleanLaw n) (h : Driver n)
    (pi : Driver n → DeterministicPolicy n) : ℝ :=
  lawExpectation law (fun K =>
    policyArea (pi K) (fun ω => driverValue h ω - lawBarycentre law ω))

noncomputable def residualY (law : BooleanLaw n) (h : Driver n)
    (rho : DeterministicPolicy n)
    (pi : Driver n → DeterministicPolicy n) : ℝ :=
  (1 / 2 : ℝ) * residualPairDisagreement law rho +
    directionDisagreement law h pi

/-- Claim 51641: the arbitrary-residual score is exactly the difference of the
active cross-policy term and the two full disagreement terms.  The displayed
inequality is recorded as the equivalent sign obligation, rather than hiding
it in a pointwise or packet surrogate. -/
def claim51641 : Prop :=
  ∀ (n : ℕ) (law : BooleanLaw n) (h : Driver n)
    (rho : DeterministicPolicy n)
    (pi : Driver n → DeterministicPolicy n),
    isProbabilityLaw law →
    activePolicy h (lawBarycentre law) rho →
    (∀ entry ∈ law,
      directionalActive entry.1 h (lawBarycentre law) (pi entry.1)) →
    score law h = residualX law h rho pi - residualY law h rho pi ∧
      (score law h ≤ 0 ↔ residualX law h rho pi ≤ residualY law h rho pi)

/-- Laws representing a prescribed barycentre. -/
def lawRepresents (law : BooleanLaw n) (u : Configuration n → ℝ) : Prop :=
  isProbabilityLaw law ∧ lawBarycentre law = u

def representable (u : Configuration n → ℝ) : Prop :=
  ∃ law : BooleanLaw n, lawRepresents law u

noncomputable def lawMinimum (c : Driver n → ℝ)
    (u : Configuration n → ℝ) : ℝ :=
  sInf {z : ℝ | ∃ law : BooleanLaw n,
    lawRepresents law u ∧ z = lawExpectation law c}

noncomputable def worstScore (h : Driver n) (u : Configuration n → ℝ) : ℝ :=
  sSup {z : ℝ | ∃ law : BooleanLaw n,
    lawRepresents law u ∧ z = score law h}

abbrev AffineForm (n : ℕ) := ℝ × (Configuration n → ℝ)

def affineValue (a : AffineForm n) (f : Configuration n → ℝ) : ℝ :=
  a.1 + ∑ ω : Configuration n, a.2 ω * f ω

def affineMinorant (c : Driver n → ℝ) (a : AffineForm n) : Prop :=
  ∀ K : Driver n, affineValue a (driverValue K) ≤ c K

noncomputable def affineDual (c : Driver n → ℝ)
    (u : Configuration n → ℝ) : ℝ :=
  sSup {z : ℝ | ∃ a : AffineForm n,
    affineMinorant c a ∧ z = affineValue a u}

def dualAttained (c : Driver n → ℝ) (u : Configuration n → ℝ) : Prop :=
  ∃ a : AffineForm n,
    affineMinorant c a ∧ affineValue a u = affineDual c u

noncomputable def residualCoefficient (u : Configuration n → ℝ)
    (h : Driver n) (K : Driver n) : ℝ :=
  qCost K - sInf {z : ℝ | ∃ d : DeterministicPolicy n,
    activePolicy K u d ∧
      z = 2 * policyBilinear d u (driverValue h) - constrainedValue K u}

noncomputable def modifiedRoofObligation (u : Configuration n → ℝ)
    (h : Driver n) : Prop :=
  lawMinimum (residualCoefficient u h) u ≥ defect h u

noncomputable def policyTangent (d : DeterministicPolicy n)
    (u : Configuration n → ℝ) (K : Driver n) : ℝ :=
  2 * policyBilinear d u (driverValue K) - policyArea d u

noncomputable def gaugedCost (c : Driver n → ℝ)
    (d : DeterministicPolicy n) (u : Configuration n → ℝ) : Driver n → ℝ :=
  fun K => c K + policyTangent d u K

/-- The eight truth-table rows use the bit-index order: coordinate zero is the
fastest-changing sign. -/
def bitSign (b : Bool) : Sign :=
  if b then negativeSign else positiveSign

def orderedConfiguration (r : Fin 8) : Configuration 3 :=
  fun i => bitSign (Nat.testBit r.1 i.1)

def signProduct (a b : Sign) : Sign :=
  if signValue a * signValue b = 1 then positiveSign else negativeSign

def targetH85 : Driver 3 :=
  fun ω => ω 0

def targetH195 : Driver 3 :=
  fun ω => signProduct (ω 1) (ω 2)

def targetLaw : BooleanLaw 3 :=
  [(targetH85, (5 / 9 : ℝ)), (targetH195, (4 / 9 : ℝ))]

noncomputable def targetU : Configuration 3 → ℝ :=
  lawBarycentre targetLaw

def targetCoefficients : Fin 9 → ℝ :=
  ![(-3 / 2 : ℝ), (17 / 36 : ℝ), (-3 / 8 : ℝ), (-7 / 36 : ℝ),
    (-17 / 36 : ℝ), (-1 / 8 : ℝ), (-17 / 36 : ℝ), (17 / 36 : ℝ),
    (-28 / 81 : ℝ)]

noncomputable def targetAffineValue (f : Configuration 3 → ℝ) : ℝ :=
  targetCoefficients 0 +
    ∑ r : Fin 8, targetCoefficients r.succ * f (orderedConfiguration r)

noncomputable def targetAffineMinorant : Prop :=
  ∀ K : Driver 3,
    targetAffineValue (driverValue K) ≤ residualCoefficient targetU targetH85 K

noncomputable def targetAffineTight : Prop :=
  ∃ K : Driver 3,
    targetAffineValue (driverValue K) = residualCoefficient targetU targetH85 K

noncomputable def targetCertificate : Prop :=
  worstScore targetH85 targetU = (-388 / 729 : ℝ) ∧
    defect targetH85 targetU = (-8 / 81 : ℝ) ∧
    lawMinimum (residualCoefficient targetU targetH85) targetU = (316 / 729 : ℝ) ∧
    targetAffineMinorant ∧
    targetAffineTight ∧
    targetAffineValue targetU = (316 / 729 : ℝ)

/-- Claim 51643: fixed-barycentre signed roofs have the stated affine dual,
policy-tangent gauge invariance, and the exact R-3874 three-bit certificate. -/
def claim51643 : Prop :=
  (∀ (n : ℕ) (h : Driver n) (u : Configuration n → ℝ),
    representable u →
      worstScore h u =
        defect h u - lawMinimum (residualCoefficient u h) u ∧
      (worstScore h u ≤ 0 ↔ modifiedRoofObligation u h)) ∧
  (∀ (n : ℕ) (c : Driver n → ℝ) (u : Configuration n → ℝ),
    representable u →
      lawMinimum c u = affineDual c u ∧ dualAttained c u) ∧
  (∀ (n : ℕ) (c : Driver n → ℝ) (u : Configuration n → ℝ)
      (d : DeterministicPolicy n),
    representable u →
      lawMinimum (gaugedCost c d u) u = lawMinimum c u + policyArea d u) ∧
  targetCertificate

end MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaR3803
