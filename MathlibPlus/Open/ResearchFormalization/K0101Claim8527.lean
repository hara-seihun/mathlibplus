import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.K0101Claim8527

noncomputable section

private def squareRootLiftR {n : ℕ}
    (q : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun k => Real.sqrt (q k)

private def squareRootLiftS {n : ℕ}
    (q : Fin (n + 1) → ℝ) (β : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cases 0 (fun i => β i / Real.sqrt (q i.castSucc))

private def jacobiCholeskyPivotContext (n : ℕ)
    (J L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (α q : Fin (n + 1) → ℝ) (β : Fin n → ℝ) : Prop :=
  (∀ i j, J i j = J j i) ∧
    (∀ i : Fin n, 0 < β i) ∧
      (∀ i : Fin n,
        J i.castSucc i.succ = β i ∧
          J i.succ i.castSucc = β i) ∧
        (∀ i j : Fin (n + 1), i.val + 1 < j.val → J i j = 0) ∧
          (∀ v : Fin (n + 1) → ℝ, v ≠ 0 →
            0 < ∑ i : Fin (n + 1),
              ∑ j : Fin (n + 1), v i * J i j * v j) ∧
            (∀ i j : Fin (n + 1), i.val + 1 < j.val → L i j = 0) ∧
              (∀ i : Fin (n + 1), 0 < L i i) ∧
                J = L * L.transpose ∧
                  (∀ i : Fin (n + 1), q i = (L i i) ^ 2) ∧
                    (∀ i : Fin (n + 1), α i = J i i) ∧
                      (∀ i : Fin n,
                        β i = L i.succ i.castSucc * L i.castSucc i.castSucc) ∧
                        q 0 = α 0 ∧
                          (∀ i : Fin n,
                            q i.succ =
                              α i.succ - β i ^ 2 / q i.castSucc)

def squareRootLiftCoefficientsFromPivots_claim8527 : Prop :=
  ∀ (n : ℕ) (J L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (α q : Fin (n + 1) → ℝ) (β : Fin n → ℝ),
    jacobiCholeskyPivotContext n J L α q β →
      (∀ i : Fin (n + 1), 0 < q i) →
        let r := squareRootLiftR q
        let s := squareRootLiftS q β
        (α 0 = r 0 ^ 2 + s 0 ^ 2 ∧
            (∀ i : Fin n,
              α i.succ = r i.succ ^ 2 + s i.succ ^ 2)) ∧
          (∀ i : Fin n,
            β i = r i.castSucc * s i.succ)

end

end MathlibPlus.Open.ResearchFormalization.K0101Claim8527
