import Mathlib

namespace MathlibPlus.Open.Algebra.QuotientEmbeddingInterval

abbrev ambientRing (j : ℕ) := MvPolynomial (Fin j) ℚ

/-- The invariant subring of the polynomial ring on `j` variables. -/
def symmetricRing (j : ℕ) : Subalgebra ℚ (ambientRing j) :=
  { carrier := {p | p.IsSymmetric}
    zero_mem' := MvPolynomial.IsSymmetric.zero
    one_mem' := MvPolynomial.IsSymmetric.one
    add_mem' := fun hp hq => hp.add hq
    mul_mem' := fun hp hq => hp.mul hq
    algebraMap_mem' := fun r => by
      change (MvPolynomial.C r).IsSymmetric
      exact MvPolynomial.IsSymmetric.C r }

/-- The power sums used to generate the consecutive-power-sum ideal. -/
noncomputable def powerSum (j n : ℕ) : symmetricRing j :=
  ⟨∑ i : Fin j, (MvPolynomial.X i : ambientRing j) ^ n, by
    intro e
    simp only [map_sum, map_pow, MvPolynomial.rename_X]
    simpa using (Equiv.Perm.sum_comp e (Finset.univ : Finset (Fin j))
      (fun i => (MvPolynomial.X i : ambientRing j) ^ n) (by simp))⟩

/-- `I_d = (p_(d+1), ..., p_(d+j))` in the invariant ring. -/
noncomputable def consecutivePowerSumIdeal (j d : ℕ) : Ideal (symmetricRing j) :=
  Ideal.span (Set.range (fun i : Fin j => powerSum j (d + i.1 + 1)))

/-- The top elementary symmetric polynomial `e_j = x₁⋯x_j`. -/
noncomputable def topElementary (j : ℕ) : symmetricRing j :=
  ⟨∏ i : Fin j, (MvPolynomial.X i : ambientRing j), by
    intro e
    simp only [map_prod, MvPolynomial.rename_X]
    exact Equiv.prod_comp e (fun i => (MvPolynomial.X i : ambientRing j))⟩

/-- An orbit-sum representative of a symmetric monomial. -/
noncomputable def orbitSum (j : ℕ) (d : Fin j →₀ ℕ) : ambientRing j :=
  ∑ σ : Equiv.Perm (Fin j), MvPolynomial.rename σ (MvPolynomial.monomial d 1)

/-- The symmetric monomial associated with an exponent vector. -/
noncomputable def symmetricMonomial (j : ℕ) (a : Fin j → ℕ) : symmetricRing j :=
  ⟨orbitSum j (Finsupp.equivFunOnFinite.symm a), by
    intro e
    simp only [orbitSum, map_sum, MvPolynomial.rename_rename]
    simpa [Equiv.Perm.mul_apply] using
      (Equiv.sum_comp (Equiv.mulLeft e)
        (fun σ : Equiv.Perm (Fin j) =>
          MvPolynomial.rename σ
            (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm a) 1)) )⟩

def inExponentInterval (j L d : ℕ) (a : Fin j → ℕ) : Prop :=
  ∀ i, L ≤ a i ∧ a i ≤ L + d

/-- The span of symmetric monomials whose individual exponents lie in `[L,L+d]`. -/
noncomputable def intervalImageSpan (j L d : ℕ) :
    Submodule ℚ ((symmetricRing j) ⧸ consecutivePowerSumIdeal j (L + d)) := by
  classical
  exact Submodule.span ℚ
    (Set.range (fun a : {a : Fin j → ℕ // inExponentInterval j L d a} =>
      (Ideal.Quotient.mk (consecutivePowerSumIdeal j (L + d)))
        (symmetricMonomial j a.1)))

/--
Claim 2841: multiplication by `e_j^L` induces an injection from `S/I_d` to
`S/I_(L+d)`, with image the span of the indicated symmetric monomials.
-/
def claim2841 : Prop :=
  ∀ j d L : ℕ,
    ∃ f : ((symmetricRing j) ⧸ consecutivePowerSumIdeal j d) →ₗ[ℚ]
        ((symmetricRing j) ⧸ consecutivePowerSumIdeal j (L + d)),
      (∀ s : symmetricRing j,
        f ((Ideal.Quotient.mk (consecutivePowerSumIdeal j d)) s) =
          (Ideal.Quotient.mk (consecutivePowerSumIdeal j (L + d)))
            (topElementary j ^ L * s)) ∧
      Function.Injective f ∧
      Set.range f =
        (↑(intervalImageSpan j L d) :
          Set ((symmetricRing j) ⧸ consecutivePowerSumIdeal j (L + d)))

end MathlibPlus.Open.Algebra.QuotientEmbeddingInterval
