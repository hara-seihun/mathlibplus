import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- Exact first-Koszul-kernel classification for the localized scalar binomial. -/
def claim34056 : Prop :=
  ∀ (d : ℕ),
    let R := MvPolynomial ℕ ℤ
    let x : Fin d → R := fun i => MvPolynomial.X (i.val + 1)
    ∀ (h : Fin d → R),
      (∑ i : Fin d, x i * h i = 0) →
          ∃ q : Fin d → Fin d → R,
            (∀ i j, q i j = -q j i) ∧
              (∀ i, h i = ∑ j : Fin d, x j * q i j) ∧
                (let D : Polynomial R :=
                    ∑ i : Fin d, Polynomial.C (h i) * Polynomial.X ^ i.val
                 D =
                   ∑ i : Fin d, (Finset.Ioi i).sum (fun j =>
                     Polynomial.C (q i j) *
                       (Polynomial.C (x j) * Polynomial.X ^ i.val -
                         Polynomial.C (x i) * Polynomial.X ^ j.val)))

end MathlibPlus.Open.ResearchFormalization
