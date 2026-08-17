import MathlibPlus.Open.Combinatorics.Claim5457

namespace MathlibPlus.Open.Combinatorics.Claim5451

noncomputable section

/-- The three path classes: endpoint, distance one from an endpoint, and
 deep interior.  The arithmetic form avoids choosing labelled trees beyond
 the reviewed `Fin k` path carrier. -/
def pathClass (k : ℕ) (v : Fin k) : Fin 3 :=
  if v.val = 0 ∨ v.val + 1 = k then 0
  else if v.val = 1 ∨ v.val + 2 = k then 1
  else 2

/-- The four reviewed second-jet moments on the path. -/
def pathFourMoments (k : ℕ) : Fin 4 → Fin k → ℚ :=
  ![MathlibPlus.Open.Combinatorics.Claim5457.constantMoment k,
    MathlibPlus.Open.Combinatorics.Claim5457.degreeMoment k,
    MathlibPlus.Open.Combinatorics.Claim5457.secondDegreeMoment k,
    MathlibPlus.Open.Combinatorics.Claim5457.secondJetMoment k]

/-- The joint four-feature profile has exactly the three displayed path
value classes. -/
def pathThreeValueClasses (k : ℕ) : Prop :=
  Function.Surjective (pathClass k) ∧
    ∀ u v : Fin k,
      (pathClass k u = pathClass k v ↔
        ∀ i : Fin 4, pathFourMoments k i u = pathFourMoments k i v)

/-- For every `k ≥ 7`, the four fixed path moments have the three displayed
value classes and their automorphism-coinvariant span has rank three. -/
def rankThreePathMomentSpace_claim5451 : Prop :=
  ∀ k : ℕ, 7 ≤ k →
    pathThreeValueClasses k ∧
      Module.finrank ℚ
        (MathlibPlus.Open.Combinatorics.Claim5457.pathMomentSubspace k) = 3

end

end MathlibPlus.Open.Combinatorics.Claim5451
