import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Quadratic

noncomputable section

/-- The first five coordinates embedded into `Fin n`, for `n ≥ 5`. -/
def fin5ToFinN {n : ℕ} (hn : 5 ≤ n) (i : Fin 5) : Fin n :=
  Fin.castLE hn i

def rankFiveX {p n : ℕ} (hn : 5 ≤ n) (q : Fin n → ZMod p) : Fin n → ZMod p :=
  Function.update
    (Function.update q (fin5ToFinN hn 2)
      (q (fin5ToFinN hn 2) + q (fin5ToFinN hn 0)))
    (fin5ToFinN hn 3)
      (q (fin5ToFinN hn 3) + q (fin5ToFinN hn 1))

def rankFiveY {p n : ℕ} (hn : 5 ≤ n) (q : Fin n → ZMod p) : Fin n → ZMod p :=
  Function.update
    (Function.update q (fin5ToFinN hn 3)
      (q (fin5ToFinN hn 3) + q (fin5ToFinN hn 0)))
    (fin5ToFinN hn 4)
      (q (fin5ToFinN hn 4) + q (fin5ToFinN hn 1))

def rankFiveG {p n : ℕ} (hn : 5 ≤ n) (q : Fin n → ZMod p) : Fin n → ZMod p :=
  Function.update
    (Function.update
      (Function.update q (fin5ToFinN hn 2)
        (q (fin5ToFinN hn 2) +
          q (fin5ToFinN hn 0) * (q (fin5ToFinN hn 0) - 1)))
      (fin5ToFinN hn 3)
        (q (fin5ToFinN hn 3) +
          (2 * q (fin5ToFinN hn 0) - 1) * q (fin5ToFinN hn 1)))
    (fin5ToFinN hn 4)
      (q (fin5ToFinN hn 4) + q (fin5ToFinN hn 1) ^ 2)

def outsideFirstFive {n : ℕ} (hn : 5 ≤ n) (k : Fin n) : Prop :=
  ∀ i : Fin 5, k ≠ fin5ToFinN hn i

/-- The quadratic rank-five maps have the stated formulas and fix every remaining coordinate. -/
def claim5994 : Prop :=
  ∀ (p n : ℕ), (hp : Nat.Prime p) → (hn : 5 ≤ n) →
    ∀ q : Fin n → ZMod p,
      let i := q (fin5ToFinN hn 0)
      let j := q (fin5ToFinN hn 1)
      let a := q (fin5ToFinN hn 2)
      let b := q (fin5ToFinN hn 3)
      let c := q (fin5ToFinN hn 4)
      rankFiveX hn q (fin5ToFinN hn 0) = i ∧
      rankFiveX hn q (fin5ToFinN hn 1) = j ∧
      rankFiveX hn q (fin5ToFinN hn 2) = a + i ∧
      rankFiveX hn q (fin5ToFinN hn 3) = b + j ∧
      rankFiveX hn q (fin5ToFinN hn 4) = c ∧
      rankFiveY hn q (fin5ToFinN hn 0) = i ∧
      rankFiveY hn q (fin5ToFinN hn 1) = j ∧
      rankFiveY hn q (fin5ToFinN hn 2) = a ∧
      rankFiveY hn q (fin5ToFinN hn 3) = b + i ∧
      rankFiveY hn q (fin5ToFinN hn 4) = c + j ∧
      rankFiveG hn q (fin5ToFinN hn 0) = i ∧
      rankFiveG hn q (fin5ToFinN hn 1) = j ∧
      rankFiveG hn q (fin5ToFinN hn 2) = a + i * (i - 1) ∧
      rankFiveG hn q (fin5ToFinN hn 3) = b + (2 * i - 1) * j ∧
      rankFiveG hn q (fin5ToFinN hn 4) = c + j ^ 2 ∧
      ∀ k, outsideFirstFive hn k →
        rankFiveX hn q k = q k ∧
        rankFiveY hn q k = q k ∧
        rankFiveG hn q k = q k

end

end MathlibPlus.Open.ResearchFormalization.Quadratic
