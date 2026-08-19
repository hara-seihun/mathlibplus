import MathlibPlus.Open.DecisionTree.Cost

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Claim61272

noncomputable section

open MathlibPlus.Open.DecisionTree.Cost

abbrev Cube := Fin 3 → Sign

/-- The little-endian row of the three-sign cube indexed by `r`. -/
def rowConfiguration (r : Fin 8) : Cube :=
  fun i => if Nat.testBit r.1 i.1 then .pos else .neg

/-- The sign table selected by an eight-bit mask. -/
def hMask (m : ℕ) : Atom 3 :=
  fun x => if Nat.testBit m (truthIndex 3 x).1 then .pos else .neg

/-- The real value of a sign-valued table. -/
def tableValue (b : Atom 3) : Cube → ℝ :=
  fun x => (signValue (b x) : ℝ)

/-- Uniform expectation on a finite sign cube. -/
def uniformAverageN {n : ℕ} (f : (Fin n → Sign) → ℝ) : ℝ :=
  (∑ x : Fin n → Sign, f x) / (Fintype.card (Fin n → Sign) : ℝ)

/-- Uniform variance on a finite sign cube. -/
def varianceN {n : ℕ} (f : (Fin n → Sign) → ℝ) : ℝ :=
  uniformAverageN (fun x => (f x - uniformAverageN f) ^ 2)

/-- Uniform expectation on the eight-point Rademacher cube. -/
def cubeAverage (f : Cube → ℝ) : ℝ :=
  uniformAverageN f

/-- Uniform variance on the eight-point Rademacher cube. -/
def cubeVariance (f : Cube → ℝ) : ℝ :=
  varianceN f

/-- The displayed target mixture. -/
def target (x : Cube) : ℝ :=
  (1 / 45 : ℝ) * tableValue (hMask 48) x +
    (12 / 45 : ℝ) * tableValue (hMask 15) x +
      (32 / 45 : ℝ) * tableValue (hMask 87) x

/-- The displayed little-endian target table. -/
def targetRows : Fin 8 → ℝ :=
  fun r => target (rowConfiguration r)

def displayedTargetRows : Fin 8 → ℝ :=
  ![(43 / 45 : ℝ), 43 / 45, 43 / 45, -7 / 15,
    7 / 15, -43 / 45, 19 / 45, -1]

/-- The three component tables and the three adversary tables. -/
def components : Fin 3 → Atom 3 :=
  ![hMask 48, hMask 15, hMask 87]

def adversaries : Fin 3 → Atom 3 :=
  ![hMask 15, hMask 71, hMask 87]

def adversaryWeights : Fin 3 → ℝ :=
  ![(1 / 5 : ℝ), 2 / 5, 2 / 5]

/-- Fresh-coordinate deterministic query trees over the sign cube. -/
inductive QueryTree (n : ℕ) where
  | leaf (value : Sign) : QueryTree n
  | query (coordinate : Fin n) (negative positive : QueryTree n) : QueryTree n

def QueryTree.evaluate : QueryTree n → (Fin n → Sign) → Sign
  | .leaf value, _ => value
  | .query coordinate negative positive, x =>
      if x coordinate = .pos then positive.evaluate x else negative.evaluate x

def QueryTree.depth : QueryTree n → ℕ
  | .leaf _ => 0
  | .query _ negative positive =>
      1 + max negative.depth positive.depth

def QueryTree.noRepeatFrom (seen : Finset (Fin n)) : QueryTree n → Prop
  | .leaf _ => True
  | .query coordinate negative positive =>
      coordinate ∉ seen ∧
        noRepeatFrom (insert coordinate seen) negative ∧
          noRepeatFrom (insert coordinate seen) positive

def QueryTree.legal (tree : QueryTree n) : Prop :=
  QueryTree.noRepeatFrom ∅ tree

def QueryTree.represents (tree : QueryTree n) (b : Atom n) : Prop :=
  ∀ x, tree.evaluate x = b x

noncomputable def minimumWorstDepth (b : Atom 3) : ℕ :=
  sInf {d : ℕ |
    ∃ tree : QueryTree 3,
      QueryTree.legal tree ∧ QueryTree.depth tree = d ∧
        QueryTree.represents tree b}

/-- The cost of a forced first coordinate, in the notation `q_i`. -/
def q (b : Atom 3) : ℝ :=
  (queryCost 3 b : ℝ)

def forcedRootCost (b : Atom 3) (i : Fin 3) : ℝ :=
  1 +
    ((queryCost 2 (restrict b i .neg) : ℝ) +
      (queryCost 2 (restrict b i .pos) : ℝ)) / 2

def regret (b : Atom 3) (i : Fin 3) : ℝ :=
  forcedRootCost b i - q b

/-- The right-hand side of the randomized-root system. -/
def rmRightSide (b : Atom 3) : ℝ :=
  1 - cubeVariance (tableValue b) +
    cubeVariance (fun x => tableValue b x - target x)

def probabilityVector (alpha : Fin 3 → ℝ) : Prop :=
  (∀ i, 0 ≤ alpha i) ∧ ∑ i, alpha i = 1

def nonconstant (b : Atom 3) : Prop :=
  ¬ IsConstant b

def rootSystemValid (alpha : Fin 3 → ℝ) : Prop :=
  ∀ b : Atom 3, nonconstant b →
    ∑ i : Fin 3, alpha i * regret b i ≤ rmRightSide b

def weightedRegret (i : Fin 3) : ℝ :=
  ∑ r : Fin 3, adversaryWeights r * regret (adversaries r) i

def weightedRightSide : ℝ :=
  ∑ r : Fin 3, adversaryWeights r * rmRightSide (adversaries r)

def weightedRootSystemLeft (alpha : Fin 3 → ℝ) : ℝ :=
  ∑ r : Fin 3, adversaryWeights r *
    (∑ i : Fin 3, alpha i * regret (adversaries r) i)

/-- Restriction of a real target after fixing one sign. -/
def targetRestrict (u : (Fin (n + 1) → Sign) → ℝ)
    (i : Fin (n + 1)) (s : Sign) : (Fin n → Sign) → ℝ :=
  fun x => u (insertAt i s x)

/-- Root-inclusive Bellman posterior-variance area. -/
noncomputable def bellmanArea : (n : ℕ) → ((Fin n → Sign) → ℝ) → ℝ
  | 0, u => varianceN u
  | n + 1, u =>
      varianceN u +
        sInf {a : ℝ |
          ∃ i : Fin (n + 1),
            a =
              (bellmanArea n (targetRestrict u i .neg) +
                bellmanArea n (targetRestrict u i .pos)) / 2}

def representationAverageQueryCost : ℝ :=
  ((1 : ℝ) / 45) * q (hMask 48) +
    ((12 : ℝ) / 45) * q (hMask 15) +
      ((32 : ℝ) / 45) * q (hMask 87)

/--
The exact three-adversary infeasibility certificate for the randomized-root
system.  All numerical assertions are retained over the explicit finite
little-endian sign cube; the final area and query-cost assertions record the
scope boundary, so this is not a counterexample to the adaptive oracle-area
statement.
-/
def claim61272 : Prop :=
  (∀ r : Fin 8,
    truthIndex 3 (rowConfiguration r) = r) ∧
  targetRows = displayedTargetRows ∧
  (minimumWorstDepth (components 0) = 2 ∧
    minimumWorstDepth (components 1) = 1 ∧
      minimumWorstDepth (components 2) = 3) ∧
  (∀ i : Fin 3,
    regret (adversaries 0) i = ![(1 : ℝ), 1, 0] i) ∧
  (∀ i : Fin 3,
    regret (adversaries 1) i = ![(1 / 2 : ℝ), 0, 1 / 2] i) ∧
  (∀ i : Fin 3,
    regret (adversaries 2) i = ![(0 : ℝ), 1 / 2, 1 / 2] i) ∧
  (rmRightSide (adversaries 0) = 6187 / 8100 ∧
    rmRightSide (adversaries 1) = 2587 / 8100 ∧
      rmRightSide (adversaries 2) = 343 / 2025) ∧
  (∀ i : Fin 3, weightedRegret i = 2 / 5) ∧
  weightedRightSide = 2821 / 8100 ∧
  (∀ alpha : Fin 3 → ℝ,
    probabilityVector alpha → weightedRootSystemLeft alpha = 2 / 5) ∧
  (2 / 5 : ℝ) = 3240 / 8100 ∧
  (2 / 5 : ℝ) > 2821 / 8100 ∧
  (2 / 5 : ℝ) - 2821 / 8100 = 419 / 8100 ∧
  (¬ ∃ alpha : Fin 3 → ℝ,
    probabilityVector alpha ∧ rootSystemValid alpha) ∧
  cubeVariance target = 5107 / 8100 ∧
  bellmanArea 3 target = 2234 / 2025 ∧
  bellmanArea 3 target < 3 ∧
  representationAverageQueryCost = 139 / 90

end

end MathlibPlus.Open.ResearchFormalization.Claim61272
