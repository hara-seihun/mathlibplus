import MathlibPlus.Open.Research.OracleQueryTrees

open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaDerivativeLog

noncomputable section

open MathlibPlus.Open.Research

abbrev Cube (n : ℕ) := Fin n → Bool

def signValue : Bool → ℝ
  | false => -1
  | true => 1

def setCoordinate (x : Cube n) (i : Fin n) (b : Bool) : Cube n :=
  Function.update x i b

/-- The one-coordinate discrete derivative in the sign convention of the
source. -/
def derivative (i : Fin n) (f : Cube n → ℝ) (x : Cube n) : ℝ :=
  (f (setCoordinate x i true) - f (setCoordinate x i false)) / 2

/-- Iterated coordinate derivatives, in the canonical list order of a
finite coordinate set. -/
def iteratedDerivative (U : Finset (Fin n)) (f : Cube n → ℝ) : Cube n → ℝ :=
  U.toList.foldl (fun g i => derivative i g) f

def cubeExpectation (f : Cube n → ℝ) : ℝ :=
  (Fintype.card (Cube n) : ℝ)⁻¹ * ∑ x, f x

def cubeMean (f : Cube n → ℝ) : ℝ :=
  cubeExpectation f

def cubeVariance (f : Cube n → ℝ) : ℝ :=
  cubeExpectation (fun x => (f x - cubeMean f) ^ 2)

/-- The all-orders derivative mass `J_t`. -/
def derivativeMass (t : ℝ) (f : Cube n → ℝ) : ℝ :=
  ∑ U ∈ (Finset.univ.filter (fun U : Finset (Fin n) => U.Nonempty)),
    t ^ U.card * cubeExpectation (fun x => |iteratedDerivative U f x|)

/-- The logarithmic derivative potential for positive `t`. -/
def logarithmicPotential (t : ℝ) (f : Cube n → ℝ) : ℝ :=
  Real.log (1 + derivativeMass t f) / Real.log (1 + t)

/-- The endpoint potential at `t=0`. -/
def endpointPotential (f : Cube n → ℝ) : ℝ :=
  ∑ i : Fin n, cubeExpectation (fun x => |derivative i f x|)

def hierarchyPotential (t : ℝ) (f : Cube n → ℝ) : ℝ :=
  if t = 0 then endpointPotential f else logarithmicPotential t f

def restrictCoordinate (f : Cube n → ℝ) (i : Fin n) (b : Bool) : Cube n → ℝ :=
  fun x => f (setCoordinate x i b)

def logarithmicBellmanDefect
    (t : ℝ) (f : Cube n → ℝ) (i : Fin n) : ℝ :=
  cubeVariance f +
      (logarithmicPotential t (restrictCoordinate f i false) +
        logarithmicPotential t (restrictCoordinate f i true)) / 2 -
    logarithmicPotential t f

def hierarchyBellmanDefect
    (t : ℝ) (f : Cube n → ℝ) (i : Fin n) : ℝ :=
  cubeVariance f +
      (hierarchyPotential t (restrictCoordinate f i false) +
        hierarchyPotential t (restrictCoordinate f i true)) / 2 -
    hierarchyPotential t f

def mixtureMean
    (T : Finset (BinaryQueryTree n Bool))
    (p : BinaryQueryTree n Bool → ℝ) : Cube n → ℝ :=
  fun x => ∑ h ∈ T, p h * signValue (BinaryQueryTree.run h x)

def probabilityWeights
    (T : Finset (BinaryQueryTree n Bool))
    (p : BinaryQueryTree n Bool → ℝ) : Prop :=
  (∀ h ∈ T, 0 ≤ p h) ∧ ∑ h ∈ T, p h = 1

def mixtureDepthAtMost
    (k : ℕ) (T : Finset (BinaryQueryTree n Bool)) : Prop :=
  ∀ h ∈ T, BinaryQueryTree.height h ≤ k

def literalTree {n : ℕ} (i : Fin n) : BinaryQueryTree n Bool :=
  BinaryQueryTree.query i (BinaryQueryTree.leaf true)
    (BinaryQueryTree.leaf false)

def uniformLiteralMixture (n : ℕ) : Cube n → ℝ :=
  fun x =>
    ∑ i : Fin n,
      (1 / (n : ℝ)) *
        signValue (BinaryQueryTree.run (literalTree i) x)

def averageSigns (n : ℕ) : Cube n → ℝ :=
  fun x => (1 / (n : ℝ)) * ∑ i : Fin n, signValue (x i)

def majorityBit (x : Cube 3) : Bool :=
  decide (2 ≤ (Finset.univ.filter (fun i : Fin 3 => x i)).card)

def majorityFunction : Cube 3 → ℝ :=
  fun x => signValue (majorityBit x)

def depthCapAt (t : ℝ) : Prop :=
  ∀ (n k : ℕ) (T : Finset (BinaryQueryTree n Bool))
    (p : BinaryQueryTree n Bool → ℝ),
    probabilityWeights T p →
      mixtureDepthAtMost k T →
        hierarchyPotential t (mixtureMean T p) ≤ k

def bellmanSupersolutionAt (t : ℝ) : Prop :=
  ∀ (n k : ℕ) (T : Finset (BinaryQueryTree n Bool))
    (p : BinaryQueryTree n Bool → ℝ),
    probabilityWeights T p →
      mixtureDepthAtMost k T →
        ∀ i : Fin n,
          hierarchyBellmanDefect t (mixtureMean T p) i ≤ 0

def universalSharpCapBellman (t : ℝ) : Prop :=
  depthCapAt t ∧ bellmanSupersolutionAt t

/-- Claim 61065: the logarithmic all-orders derivative hierarchy has the
formal depth cap, but no fixed parameter is a Bellman supersolution. -/
def derivativeLogObstruction_claim61065 : Prop :=
  (∀ (t : ℝ), 0 < t →
    (∀ (n : ℕ) (k : ℕ) (T : Finset (BinaryQueryTree n Bool))
      (p : BinaryQueryTree n Bool → ℝ),
      probabilityWeights T p →
        mixtureDepthAtMost k T →
          logarithmicPotential t (mixtureMean T p) ≤ k)) ∧
  (∀ (n : ℕ) (t : ℝ) (f : Cube n → ℝ) (c : ℝ),
    0 < t → (∀ x, f x = c) → logarithmicPotential t f = 0) ∧
  (∀ (n : ℕ) (f : Cube n → ℝ),
    Filter.Tendsto
      (fun t : ℝ => logarithmicPotential t f)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (endpointPotential f))) ∧
  (∀ (n : ℕ), 2 ≤ n →
    (∀ i : Fin n,
      BinaryQueryTree.height (literalTree i) ≤ 1) ∧
      (∀ x : Cube n, averageSigns n x = uniformLiteralMixture n x) ∧
      cubeVariance (averageSigns n) = 1 / (n : ℝ) ∧
      (∀ t : ℝ, 0 < t → ∀ i : Fin n,
        logarithmicBellmanDefect t (averageSigns n) i =
            1 / (n : ℝ) +
              Real.log (1 + t * (1 - 1 / (n : ℝ))) /
                Real.log (1 + t) - 1 ∧
          0 < logarithmicBellmanDefect t (averageSigns n) i)) ∧
  (∃ h : BinaryQueryTree 3 Bool,
    BinaryQueryTree.height h = 3 ∧
      (∀ x : Cube 3,
        signValue (BinaryQueryTree.run h x) = majorityFunction x)) ∧
  endpointPotential majorityFunction = 3 / 2 ∧
    cubeVariance majorityFunction = 1 ∧
    (∀ i : Fin 3, ∀ s : Bool,
      endpointPotential (restrictCoordinate majorityFunction i s) = 1 ∧
        hierarchyBellmanDefect 0 majorityFunction i = 1 / 2) ∧
    (¬ ∃ t : ℝ, 0 ≤ t ∧ universalSharpCapBellman t)

end

end MathlibPlus.Open.ResearchFormalization.OracleAreaDerivativeLog
