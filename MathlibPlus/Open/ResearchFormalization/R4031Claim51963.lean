import MathlibPlus.Open.Research.R4031Claim51988

namespace MathlibPlus.Open.ResearchFormalization.R4031Claim51963

open MathlibPlus.Open.Research.R4031Claim51988

noncomputable section

abbrev BooleanLaw := List (Atom 3 × ℝ)

def cubeIndex (x : Cube 3) : ℕ :=
  (x (0 : Fin 3)).toNat +
    2 * (x (1 : Fin 3)).toNat +
    4 * (x (2 : Fin 3)).toNat

def maskAtom (m : ℕ) : Atom 3 :=
  fun x => Nat.testBit m (cubeIndex x)

def lawBarycentre (mu : BooleanLaw) : Table 3 :=
  fun x => (mu.map (fun entry => entry.2 * atomValue entry.1 x)).sum

def lawExpectation (mu : BooleanLaw) (f : Atom 3 → ℝ) : ℝ :=
  (mu.map (fun entry => entry.2 * f entry.1)).sum

def rootHistory : History 3 := fun _ => none

def covariance (v : Table 3) (h : Atom 3) : ℝ :=
  conditionalCovariance v (atomValue h) rootHistory

def variance (v : Table 3) : ℝ :=
  conditionalCovariance v v rootHistory

def forcedQueryCost (i : Fin 3) (j : Atom 3) : ℝ :=
  1 +
    (queryCost (fixAtom j i false) + queryCost (fixAtom j i true)) / 2

def forcedLoss (i : Fin 3) (j : Atom 3) (v : Table 3) : ℝ :=
  variance v +
    (constrainedLoss (fixAtom j i false) (fixTable v i false) +
      constrainedLoss (fixAtom j i true) (fixTable v i true)) / 2

def endpointSlack (mu : BooleanLaw) (h : Atom 3) : ℝ :=
  let v := lawBarycentre mu
  2 * queryCost h -
      (2 * unrestrictedPairing v h - unrestrictedLoss v) -
    lawExpectation mu (fun K => constrainedLoss K v - queryCost K)

def restrictLaw (mu : BooleanLaw) (i : Fin 3) (side : Spin) : BooleanLaw :=
  mu.map (fun entry => (fixAtom entry.1 i side, entry.2))

def rootCorrection (mu : BooleanLaw) (h : Atom 3) (i : Fin 3) : ℝ :=
  let v := lawBarycentre mu
  3 - 2 * covariance v h -
      2 * (forcedQueryCost i h - queryCost h) +
    lawExpectation mu (fun K =>
      forcedLoss i K v - constrainedLoss K v -
        (forcedQueryCost i K - queryCost K))

def supportLaw51963 : BooleanLaw :=
  [(maskAtom 87, (17 / 56 : ℝ)),
    (maskAtom 83, (15 / 56 : ℝ)),
    (maskAtom 176, (3 / 7 : ℝ))]

def insertedAtom51963 : Atom 3 := maskAtom 80

def activeRootWitness51963 (mu : BooleanLaw) (h : Atom 3)
    (i : Fin 3) (rho : QueryTree 3) : Prop :=
  unrestrictedActive (lawBarycentre mu) rho ∧
    policyPair rho (lawBarycentre mu) (atomValue h) rootHistory =
      unrestrictedPairing (lawBarycentre mu) h ∧
    QueryTree.root rho = some i

def claim51963_threeBitRootRecursion : Prop :=
  let mu := supportLaw51963
  let h := insertedAtom51963
  let i := (1 : Fin 3)
  (∃ rho : QueryTree 3, activeRootWitness51963 mu h i rho) ∧
    covariance (lawBarycentre mu) h = 135 / 448 ∧
    forcedQueryCost i h - queryCost h = 1 ∧
    lawExpectation mu (fun K =>
      forcedLoss i K (lawBarycentre mu) -
        constrainedLoss K (lawBarycentre mu)) = -1633 / 87808 ∧
    lawExpectation mu (fun K => forcedQueryCost i K - queryCost K) = 1 / 2 ∧
    rootCorrection mu h i = -10649 / 87808 ∧
    rootCorrection mu h i < 0 ∧
    endpointSlack (restrictLaw mu i false) (fixAtom h i false) = 1069 / 343 ∧
    endpointSlack (restrictLaw mu i true) (fixAtom h i true) = 2895 / 784 ∧
    (endpointSlack (restrictLaw mu i false) (fixAtom h i false) +
      endpointSlack (restrictLaw mu i true) (fixAtom h i true)) / 2 =
        37369 / 10976 ∧
    endpointSlack mu h =
      (endpointSlack (restrictLaw mu i false) (fixAtom h i false) +
        endpointSlack (restrictLaw mu i true) (fixAtom h i true)) / 2 +
        rootCorrection mu h i ∧
    endpointSlack mu h = 288303 / 87808

end
end MathlibPlus.Open.ResearchFormalization.R4031Claim51963
