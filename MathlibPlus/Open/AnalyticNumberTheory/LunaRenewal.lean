import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory

/--
The simultaneous renewal equation on the positive-integer logarithmic lattice.
For a prime `p`, translation by `log p` sends the coefficient at `n` to the
coefficient at `p*n`; the right-hand side is the sector with `p ∤ n`.
-/
def claim19113 (B : {n : ℕ // 0 < n} → ℝ) : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p),
    (fun n =>
      B n - Real.rpow (p : ℝ) ((-1 : ℝ) / 2) *
        B ⟨p * n.1, Nat.mul_pos hp.pos n.2⟩) =
      (fun n => if p ∣ n.1 then 0 else B n)

end MathlibPlus.Open.AnalyticNumberTheory
