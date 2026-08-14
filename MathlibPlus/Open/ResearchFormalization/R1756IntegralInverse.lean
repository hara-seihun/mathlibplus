import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1756

open scoped BigOperators

noncomputable section

private def q (n : ℕ) : Polynomial ℤ :=
  Finset.sum (Finset.range (n / 2 + 1)) (fun j =>
    (Nat.choose (n - j) j : ℤ) • (Polynomial.X : Polynomial ℤ) ^ j)

private def g (N : ℕ) (a : Fin (N / 2 + 1)) : Polynomial ℤ :=
  q (a : ℕ) * q (N - (a : ℕ))

private def h (N : ℕ) (a : Fin (N / 2 + 1)) : Polynomial ℤ :=
  (-Polynomial.X : Polynomial ℤ) ^ (a : ℕ) * q (N - 2 * (a : ℕ))

private def tail (N : ℕ) (c : Fin (N / 2 + 1) → ℤ)
    (a : Fin (N / 2 + 1)) : ℤ :=
  Finset.sum (Finset.univ.filter (fun r : Fin (N / 2 + 1) => a ≤ r)) c

private def prior (N : ℕ) (u : Fin (N / 2 + 1) → ℤ)
    (a : Fin (N / 2 + 1)) : Polynomial ℤ :=
  Finset.sum (Finset.univ.filter (fun i : Fin (N / 2 + 1) =>
    (i : ℕ) < (a : ℕ))) (fun i => (u i) • h N i)

private def nextTail (N : ℕ) (c : Fin (N / 2 + 1) → ℤ)
    (a : Fin (N / 2 + 1)) : ℤ :=
  if ha : (a : ℕ) < N / 2 then
    tail N c ⟨(a : ℕ) + 1, by omega⟩
  else
    0

/--
The constructive integral inverse in the two-twig path-position calculation.
The polynomial sequence is the explicit `Q_n` sequence from the admitted claim,
with `t` represented by `Polynomial.X`.  The first conjunct is the asserted
change from the `G_a` coordinates to the successive-difference coordinates
`H_a`; the second makes the unit-diagonal coefficient recovery explicit; the
last records `c_a = s_a - s_(a+1)` with `s_(m+1) = 0`.
-/
def claim_34154 : Prop :=
  ∀ (N : ℕ) (c : Fin (N / 2 + 1) → ℤ),
    let P : Polynomial ℤ :=
      Finset.sum Finset.univ (fun a => (c a) • g N a)
    let s : Fin (N / 2 + 1) → ℤ :=
      fun a => tail N c a
    P = (Finset.sum Finset.univ (fun a => (s a) • h N a)) ∧
      (∀ a,
        (P - prior N s a).coeff (a : ℕ) =
          ((-1 : ℤ) ^ (a : ℕ)) * s a) ∧
      (∀ u : Fin (N / 2 + 1) → ℤ,
        (∀ a,
          (P - prior N u a).coeff (a : ℕ) =
            ((-1 : ℤ) ^ (a : ℕ)) * u a) →
          u = s) ∧
      (∀ a, c a = s a - nextTail N c a)

end

end MathlibPlus.Open.ResearchFormalization.R1756
