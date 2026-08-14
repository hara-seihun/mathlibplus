import Mathlib

namespace MathlibPlus.Open.R4528

private def partitionWeight (d : Fin 7 →₀ ℕ) : ℕ :=
  ∑ i : Fin 7, (i.1 + 1) * d i

private def componentCount (d : Fin 7 →₀ ℕ) : ℕ :=
  ∑ i : Fin 7, d i

private def abstractHiddenKernel7 (p : MvPolynomial (Fin 7) ℤ) : Prop :=
  (∀ d ∈ p.support, d 0 = 0) ∧
    (∀ d ∈ p.support, partitionWeight d = 7) ∧
    (∀ c : ℕ,
      Finset.sum (p.support.filter (fun d => componentCount d = c))
        (fun d => MvPolynomial.coeff d p) = 0)

noncomputable def delta7 : MvPolynomial (Fin 7) ℤ :=
  MvPolynomial.X (1 : Fin 7) * MvPolynomial.X (4 : Fin 7) -
    MvPolynomial.X (2 : Fin 7) * MvPolynomial.X (3 : Fin 7)

/-- R-4528.5: the first abstract hidden direction at weight seven. -/
def claim52346 : Prop :=
  delta7 ≠ 0 ∧
    abstractHiddenKernel7 delta7 ∧
    delta7.support.card = 2 ∧
    ∀ d ∈ delta7.support, componentCount d = 2

end MathlibPlus.Open.R4528
