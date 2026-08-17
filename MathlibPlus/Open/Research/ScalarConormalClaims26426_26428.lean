import MathlibPlus.Open.Research.ScalarAlgebra

namespace MathlibPlus.Open.ResearchFormalizationBatch

open scoped BigOperators
noncomputable section

/-- The conductor generators are indexed by the actual variable names `e_k`, `k ≥ 2`.
The ambient `MvPolynomial ℕ ℚ` reserves indices `0` and `1` for `s` and `z`. -/
abbrev ScalarKernelIndex := {k : ℕ // 2 ≤ k}

def scalarEAt (k : ScalarKernelIndex) : ScalarR :=
  MvPolynomial.X k.1

def scalarEAtInK (k : ScalarKernelIndex) : scalarK :=
  ⟨scalarEAt k, by
    have hk : k.1 = (k.1 - 2) + 2 := (Nat.sub_add_cancel k.2).symm
    rw [scalarEAt, hk]
    exact Ideal.mem_span_range_self⟩

def scalarEAtInA (k : ScalarKernelIndex) : scalarA :=
  ⟨scalarEAt k,
    Algebra.subset_adjoin
      (Set.mem_union_right _ (scalarEAtInK k).property)⟩

abbrev scalarConormalR := Ideal.Cotangent scalarK

def scalarConormalRGenerator (k : ScalarKernelIndex) : scalarConormalR :=
  scalarK.toCotangent (scalarEAtInK k)

abbrev scalarAQuotient := (scalarA : Type) ⧸ scalarKInA

def scalarSInA : scalarA :=
  ⟨scalarS, Algebra.subset_adjoin (Set.mem_union_left _ rfl)⟩

def scalarPolyToAQuotient : Polynomial ℚ →ₐ[ℚ] scalarAQuotient :=
  (Ideal.Quotient.mkₐ ℚ scalarKInA).comp (Polynomial.aeval scalarSInA)

def scalarZPowerEInA (k : ScalarKernelIndex) (a : ℕ) : scalarKInA :=
  ⟨⟨scalarZ ^ a * scalarEAt k,
      Algebra.subset_adjoin
        (Set.mem_union_right _
          (scalarK.mul_mem_left (scalarZ ^ a) (scalarEAtInK k).property))⟩,
    scalarK.mul_mem_left (scalarZ ^ a) (scalarEAtInK k).property⟩

abbrev scalarConormalA := Ideal.Cotangent scalarKInA

def scalarConormalAGenerator (k : ScalarKernelIndex) (a : ℕ) : scalarConormalA :=
  scalarKInA.toCotangent (scalarZPowerEInA k a)

/-- The finite indexing type for the degree-`n` monomials in the shifted sum.
The three entries record the `e_k`, `z^a`, and `s^b` exponents. -/
def ScalarGradeIndex (n : ℕ) :=
  {q : (ScalarKernelIndex × ℕ) × ℕ //
    (q.1.1 : ℕ) + q.1.2 + q.2 = n}

def scalarShiftedDegree (n : ℕ) :
    Submodule ℚ ((ScalarKernelIndex × ℕ) →₀ Polynomial ℚ) :=
  Submodule.span ℚ (Set.range fun q : ScalarGradeIndex n =>
    Finsupp.single q.val.1 (Polynomial.monomial q.val.2 (1 : ℚ)))

def scalarConormalDegree
    [Module (Polynomial ℚ) scalarConormalA]
    (e : scalarConormalA ≃ₗ[Polynomial ℚ]
      ((ScalarKernelIndex × ℕ) →₀ Polynomial ℚ)) (n : ℕ) :
    Submodule ℚ scalarConormalA :=
  (scalarShiftedDegree n).comap (e.restrictScalars ℚ).toLinearMap

def scalarHilbertSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => (Nat.choose n 2 : ℚ)

def scalarHilbertClosedForm : PowerSeries ℚ :=
  PowerSeries.X ^ 2 * (1 - PowerSeries.X)⁻¹ ^ 3

/-- Claim 26426: the conormal module `K/K²` is free over the exact ambient
conductor quotient, with the class of each actual variable `e_k` as its
specified basis vector. -/
def claim_26426 : Prop :=
  ∃ e : scalarConormalR ≃ₗ[ScalarR ⧸ scalarK]
      (ScalarKernelIndex →₀ (ScalarR ⧸ scalarK)),
    ∀ k : ScalarKernelIndex,
      e (scalarConormalRGenerator k) = Finsupp.single k 1

/-- Claim 26427: after restricting to the scalar base `ℚ[s]`, the classes of
`z^a e_k` give the indicated countable free basis. -/
def claim_26427 : Prop :=
  letI : Module (Polynomial ℚ) scalarConormalA :=
    Module.compHom scalarConormalA scalarPolyToAQuotient.toRingHom
  ∃ e : scalarConormalA ≃ₗ[Polynomial ℚ]
      ((ScalarKernelIndex × ℕ) →₀ Polynomial ℚ),
    ∀ k : ScalarKernelIndex, ∀ a : ℕ,
      e (scalarConormalAGenerator k a) = Finsupp.single (k, a) 1

/-- Claim 26428: with the displayed weights, the same named shifted basis has
Hilbert series `t²/(1-t)³`, and its degree-`n` component has dimension
`choose n 2`. -/
def claim_26428 : Prop :=
  letI : Module (Polynomial ℚ) scalarConormalA :=
    Module.compHom scalarConormalA scalarPolyToAQuotient.toRingHom
  ∃ e : scalarConormalA ≃ₗ[Polynomial ℚ]
      ((ScalarKernelIndex × ℕ) →₀ Polynomial ℚ),
    (∀ k : ScalarKernelIndex, ∀ a : ℕ,
      e (scalarConormalAGenerator k a) = Finsupp.single (k, a) 1) ∧
    (∀ n : ℕ,
      Module.finrank ℚ (scalarConormalDegree e n) = Nat.choose n 2) ∧
    scalarHilbertSeries = scalarHilbertClosedForm

end
end MathlibPlus.Open.ResearchFormalizationBatch
