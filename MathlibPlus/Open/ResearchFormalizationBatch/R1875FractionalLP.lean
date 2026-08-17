import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch.R1875

noncomputable section

open scoped BigOperators

private def supportUniverse (m : ℕ) : Finset (Finset (Fin m)) :=
  (Finset.univ : Finset (Finset (Fin m))).filter Finset.Nonempty

private def tripleUniverse (m : ℕ) : Finset (Finset (Fin m)) :=
  (Finset.univ : Finset (Finset (Fin m))).filter (fun I => I.card = 3)

private def pairUniverse (m : ℕ) : Finset (Finset (Fin m)) :=
  (Finset.univ : Finset (Finset (Fin m))).filter (fun I => I.card = 2)

private def supportLoad (m : ℕ)
    (z : Finset (Fin m) → ℝ) (i : Fin m) : ℝ :=
  ∑ S ∈ supportUniverse m, if i ∈ S then z S else 0

private def tripleCoverWeight (m : ℕ)
    (z : Finset (Fin m) → ℝ) (I : Finset (Fin m)) : ℝ :=
  ∑ S ∈ supportUniverse m,
    if (S ∩ I).card = 2 then z S else 0

private def pairSeparationWeight (m : ℕ)
    (z : Finset (Fin m) → ℝ) (I : Finset (Fin m)) : ℝ :=
  ∑ S ∈ supportUniverse m,
    if (S ∩ I).card = 1 then z S else 0

private def fractionalSupportFeasible (m : ℕ)
    (z : Finset (Fin m) → ℝ) : Prop :=
  (∀ S ∈ supportUniverse m, 0 ≤ z S) ∧
    (∀ I ∈ tripleUniverse m, 1 ≤ tripleCoverWeight m z I) ∧
    (∀ I ∈ pairUniverse m, 1 ≤ pairSeparationWeight m z I)

private def maximumLoad (m : ℕ)
    (z : Finset (Fin m) → ℝ) : ℝ :=
  sSup (Set.range (supportLoad m z))

private def lpValue (m : ℕ) : ℝ :=
  sInf {L : ℝ | ∃ z, fractionalSupportFeasible m z ∧ maximumLoad m z ≤ L}

private def balancedSupportSize (m : ℕ) : ℕ :=
  1 + (m - 1) / 2

private def balancedSupportWeight (m : ℕ) : ℝ :=
  1 / (3 * (Nat.choose (m - 3) (balancedSupportSize m - 2) : ℝ))

private def balancedWeights (m : ℕ)
    (S : Finset (Fin m)) : ℝ :=
  if S.card = balancedSupportSize m then balancedSupportWeight m else 0

/-- Claim 34586: the exact real support-cover LP has the stated minimum and
converges to 4/3, so it is not bounded below by a positive multiple of log m.
All supports, cover/separation constraints, and loads use the reviewed
support definitions. -/
def exactFractionalSupportCoverOptimum_claim34586 : Prop :=
  (∀ m : ℕ, 3 ≤ m →
    IsLeast
      {L : ℝ | ∃ z, fractionalSupportFeasible m z ∧ maximumLoad m z ≤ L}
      (lpValue m) ∧
      lpValue m =
        ((m - 1 : ℝ) * (m - 2 : ℝ)) /
          (3 * ((m - 1) ^ 2 / 4 : ℕ) : ℝ)) ∧
  Filter.Tendsto lpValue Filter.atTop (nhds (4 / 3 : ℝ)) ∧
  ¬∃ c : ℝ, 0 < c ∧
    ∀ᶠ m : ℕ in Filter.atTop,
      c * Real.log (m : ℝ) ≤ lpValue m

/-- Claim 34587: the exact support-size count and q bound yield the complete
triple-summing lower-certificate chain. -/
def lowerCertificateForFractionalOptimum_claim34587 : Prop :=
  ∀ (m : ℕ) (z : Finset (Fin m) → ℝ) (L : ℝ),
    3 ≤ m →
    fractionalSupportFeasible m z →
    (∀ i : Fin m, supportLoad m z i ≤ L) →
    let q : ℕ := (m - 1) ^ 2 / 4
    (∀ S ∈ supportUniverse m,
      ((tripleUniverse m).filter
          (fun I => (S ∩ I).card = 2)).card =
        Nat.choose S.card 2 * (m - S.card) ∧
        (S.card - 1) * (m - S.card) ≤ q) ∧
      (Nat.choose m 3 : ℝ) ≤
          (q : ℝ) / 2 *
            (∑ S ∈ supportUniverse m, z S * S.card) ∧
      (∑ S ∈ supportUniverse m, z S * S.card) =
        ∑ i : Fin m, supportLoad m z i ∧
      (∑ i : Fin m, supportLoad m z i) ≤ (m : ℝ) * L ∧
      (Nat.choose m 3 : ℝ) ≤ (q : ℝ) / 2 * (m : ℝ) * L ∧
      L ≥ ((m - 1 : ℝ) * (m - 2 : ℝ)) /
        (3 * (q : ℝ))

/-- Claim 34588: the balanced s-support weights are a feasible matching
certificate with unit triple covers, the exact pair-separation value, and the
stated uniform load. -/
def balancedSupportMatchingCertificate_claim34588 : Prop :=
  ∀ m : ℕ, 3 ≤ m →
    let s := balancedSupportSize m
    let α := balancedSupportWeight m
    let q : ℕ := (m - 1) ^ 2 / 4
    let z := balancedWeights m
    (s - 1) * (m - s) = q ∧
      fractionalSupportFeasible m z ∧
      (∀ I ∈ tripleUniverse m, tripleCoverWeight m z I = 1) ∧
      (∀ I ∈ pairUniverse m,
        pairSeparationWeight m z I =
          2 * (Nat.choose (m - 2) (s - 1) : ℝ) * α ∧
          1 ≤ 2 * (Nat.choose (m - 2) (s - 1) : ℝ) * α ∧
          2 * (Nat.choose (m - 2) (s - 1) : ℝ) * α =
            2 * (m - 2 : ℝ) / (3 * (s - 1 : ℝ))) ∧
      (∀ i : Fin m,
        supportLoad m z i =
          (Nat.choose (m - 1) (s - 1) : ℝ) * α ∧
          supportLoad m z i =
            (m - 1 : ℝ) * (m - 2 : ℝ) /
              (3 * (s - 1 : ℝ) * (m - s : ℝ)))

end

end MathlibPlus.Open.ResearchFormalizationBatch.R1875
