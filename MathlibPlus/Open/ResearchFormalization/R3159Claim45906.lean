import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R3159Claim45906

noncomputable section

open scoped BigOperators

/-- Claim 45906: the width-two tribes table is tied to the exact uniform
short-circuit policy family, and the scaling formulas give the width-twelve
coefficient obstruction. -/
def tribesLocalPivotCertificate_claim45906 : Prop :=
  let coord : Fin 2 → Fin 2 → Fin 4 :=
    fun j k => Fin.ofNat 4 (2 * j.val + k.val)
  let tribes : (Fin 4 → Bool) → Bool := fun x =>
    (x (coord 0 0) && x (coord 0 1)) ||
      (x (coord 1 0) && x (coord 1 1))
  let tribe : (Fin 4 → Bool) → Fin 2 → Bool := fun x j =>
    x (coord j 0) && x (coord j 1)
  let pathFor : (Fin 4 → Bool) → Fin 2 → Equiv.Perm (Fin 2) → Finset (Fin 4) :=
    fun x j order =>
      {coord j (order 0)} ∪
        (if x (coord j (order 0)) then
          {coord j (order 1)} else ∅)
  let execute : (Fin 4 → Bool) → Equiv.Perm (Fin 2) →
      (Fin 2 → Equiv.Perm (Fin 2)) → Bool × Finset (Fin 4) :=
    fun x tribeOrder bitOrders =>
      let j0 := tribeOrder 0
      let j1 := tribeOrder 1
      let p0 := pathFor x j0 (bitOrders j0)
      if tribe x j0 then
        (true, p0)
      else
        let p1 := pathFor x j1 (bitOrders j1)
        (tribe x j1, p0 ∪ p1)
  let sign : Bool → ℚ := fun b => if b then 1 else -1
  let rademacher : Bool → ℚ := fun b => if b then 1 else -1
  let cubeCount : ℚ := Fintype.card (Fin 4 → Bool)
  let policyCount : ℚ :=
    Fintype.card
      (Equiv.Perm (Fin 2) × (Fin 2 → Equiv.Perm (Fin 2)))
  let mean : ℚ :=
    (∑ x : Fin 4 → Bool, sign (tribes x)) / cubeCount
  let variance : ℚ :=
    (∑ x : Fin 4 → Bool, (sign (tribes x) - mean) ^ 2) / cubeCount
  let revealment : Fin 4 → ℚ := fun i =>
    (∑ tribeOrder : Equiv.Perm (Fin 2),
      ∑ bitOrders : Fin 2 → Equiv.Perm (Fin 2),
        ∑ x : Fin 4 → Bool,
          if i ∈ (execute x tribeOrder bitOrders).2 then 1 else 0) /
      (policyCount * cubeCount)
  let singletonCoefficient : Fin 4 → ℚ := fun i =>
    (∑ x : Fin 4 → Bool,
      sign (tribes x) * rademacher (x i)) / cubeCount
  let delta : Fin 4 → ℚ := fun i => singletonCoefficient i ^ 2
  let widthParameters : ℕ → ℚ × ℚ × ℚ × ℚ := fun w =>
    let p := 1 / (2 : ℚ) ^ w
    let q := (1 - p) ^ (2 ^ (w - 1))
    let V := 4 * q * (1 - q)
    let r := 4 * (1 - p) * (1 - q) / (w : ℚ)
    let D := (2 * p * q / (1 - p)) ^ 2
    (V, r, D, (V - r) / D)
  policyCount = 8 ∧
    cubeCount = 16 ∧
    (∀ tribeOrder : Equiv.Perm (Fin 2),
      ∀ bitOrders : Fin 2 → Equiv.Perm (Fin 2),
        ∀ x : Fin 4 → Bool,
          (execute x tribeOrder bitOrders).1 = tribes x ∧
            (execute x tribeOrder bitOrders).2.card ≤ 4 ∧
              ∃ y : Fin 4 → Bool,
                (execute y tribeOrder bitOrders).2.card = 4) ∧
    (∀ i : Fin 4, revealment i = 21 / 32) ∧
      variance = 63 / 64 ∧
        (∀ i : Fin 4, singletonCoefficient i = 3 / 8 ∧
          delta i = 9 / 64) ∧
          variance - revealment 0 - 2 * delta 0 = 3 / 64 ∧
            (variance - revealment 0) / delta 0 = 7 / 3 ∧
              (∀ w : ℕ, 2 ≤ w →
                let parameters := widthParameters w
                parameters.1 =
                    4 * (1 - (1 - 1 / (2 : ℚ) ^ w) ^ (2 ^ (w - 1))) *
                      (1 - 1 / (2 : ℚ) ^ w) ^ (2 ^ (w - 1)) ∧
                  (w = 12 → parameters.2.2.2 > 10 ^ 6))

end

end MathlibPlus.Open.ResearchFormalization.R3159Claim45906
