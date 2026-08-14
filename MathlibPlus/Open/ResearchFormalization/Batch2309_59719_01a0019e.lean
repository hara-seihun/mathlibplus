import Mathlib

open scoped BigOperators Interval Pointwise

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-! The arithmetic endpoint-flattening specialization (Claim 2309). -/

def EvenPolynomial (p : Polynomial ℝ) : Prop :=
  ∀ x : ℝ, p.eval (-x) = p.eval x

noncomputable def ArithmeticEndpointSum (c : ℤ) (p : Polynomial ℝ) : ℝ := by
  classical
  exact
    Real.rpow (c : ℝ) (-(1 / 2 : ℝ)) *
      Finset.sum (Finset.Ico (1 : ℤ) c) (fun n => p.eval ((n : ℝ) / (c : ℝ)))

noncomputable def ArithmeticKernel (c : ℤ) (p : Polynomial ℝ) (x : ℝ) : ℝ := by
  classical
  exact
    Real.exp (x / 2) / Real.sqrt (c : ℝ) *
      Finset.sum
        ((Finset.Ico (1 : ℤ) c).filter
          (fun n => (n : ℝ) < (c : ℝ) * Real.exp (-x)))
        (fun n => p.eval ((n : ℝ) * Real.exp x / (c : ℝ)))

noncomputable def CenteredCosineTransform (K : ℝ → ℝ) (L : ℝ) (z : ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..L,
    (K x : ℂ) * Complex.cos (z * ((x - L / 2 : ℝ) : ℂ))

def SimpleComplexZero (F : ℂ → ℂ) (z : ℂ) : Prop :=
  F z = 0 ∧ ∃ d : ℂ, HasDerivAt F d z ∧ d ≠ 0

def EndpointFlatKernel (K : ℝ → ℝ) (L : ℝ) : Prop := by
  classical
  exact
    0 < L ∧
      ContinuousOn K (Set.Icc 0 L) ∧
      (∃ breaks : Finset ℝ,
        (∀ b ∈ breaks, 0 < b ∧ b < L) ∧
          ContDiffOn ℝ 2 K (Set.Ioo 0 L \ (breaks : Set ℝ)) ∧
            (∀ b, (b = 0 ∨ b = L ∨ b ∈ breaks) →
              (b < L → ∃ d : ℝ, HasDerivWithinAt K d (Set.Icc b L) b) ∧
                (0 < b → ∃ d : ℝ, HasDerivWithinAt K d (Set.Icc 0 b) b))) ∧
      K L = 0 ∧ K 0 ≠ 0

def EndpointFlatTailTheorem (K : ℝ → ℝ) (L : ℝ) : Prop :=
  EndpointFlatKernel K L ∧
    ∀ Y : ℝ, 0 < Y →
      ∃ T : ℝ, ∀ z : ℂ,
        T ≤ |z.re| → |z.im| ≤ Y →
          CenteredCosineTransform K L z = 0 →
            z.im = 0 ∧ SimpleComplexZero (CenteredCosineTransform K L) z

def ArithmeticEndpointFlattening : Prop :=
  ∀ (c : ℤ) (p : Polynomial ℝ),
    EvenPolynomial p →
      p.eval 1 = 0 →
        ArithmeticEndpointSum c p ≠ 0 →
          EndpointFlatTailTheorem (ArithmeticKernel c p) (Real.log (c : ℝ))

/-! The CI assertion for the cyclic-primary Cayley graph (Claim 59719). -/

abbrev C2Pow (r : ℕ) := Fin r → ZMod 2

abbrev CyclicPrimaryGroup (r : ℕ) := C2Pow r × ZMod 9

def DistinguishedSubgroup (r : ℕ) : Set (CyclicPrimaryGroup r) :=
  {g | g.1 = 0}

def CayleyGraph {G : Type*} [AddGroup G] (S : Set G)
    (hS : S = -S) (h0 : 0 ∉ S) : SimpleGraph G := by
  refine
    { Adj := fun x y => y - x ∈ S
      symm := ⟨fun x y h => ?_⟩
      loopless := ⟨fun x h => ?_⟩ }
  · rw [hS]
    simpa using h
  · apply h0
    simpa using h

def CyclicPrimaryCI : Prop :=
  ∀ (r : ℕ) (S T : Set (CyclicPrimaryGroup r))
    (hSsub : S ⊆ DistinguishedSubgroup r \ {0})
    (hSsymm : S = -S)
    (hTsub : T ⊆ (Set.univ : Set (CyclicPrimaryGroup r)) \ {0})
    (hTsymm : T = -T),
    let hS0 : (0 : CyclicPrimaryGroup r) ∉ S := by
      intro h
      exact (hSsub h).2 (by simp)
    let hT0 : (0 : CyclicPrimaryGroup r) ∉ T := by
      intro h
      exact (hTsub h).2 (by simp)
    ∀ e : CayleyGraph S hSsymm hS0 ≃g CayleyGraph T hTsymm hT0,
      ∃ α : CyclicPrimaryGroup r ≃+ CyclicPrimaryGroup r,
        α '' S = T

end MathlibPlus.Open.ResearchFormalizationBatch
