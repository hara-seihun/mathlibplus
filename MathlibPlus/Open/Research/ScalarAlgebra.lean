import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

noncomputable section
open scoped BigOperators

/-! A concrete presentation of the scalar pullback algebra. -/

abbrev ScalarR := MvPolynomial ℕ ℚ

def scalarS : ScalarR := MvPolynomial.X 0

def scalarZ : ScalarR := MvPolynomial.X 1

def scalarE (k : ℕ) : ScalarR := MvPolynomial.X (k + 2)

def scalarK : Ideal ScalarR := Ideal.span (Set.range scalarE)

def scalarA : Subalgebra ℚ ScalarR :=
  Algebra.adjoin ℚ ({scalarS} ∪ (scalarK : Set ScalarR))

def scalarConductorCarrier : Set ScalarR :=
  {r | ∀ x : ScalarR, x * r ∈ (scalarA : Set ScalarR)}

def claim_26418 : Prop :=
  scalarConductorCarrier = (scalarK : Set ScalarR)

def claim_26419 : Prop :=
  ∀ x : FractionRing scalarA,
    IsIntegral scalarA x →
      ∃ a : scalarA, algebraMap scalarA (FractionRing scalarA) a = x

def claim_26420 : Prop :=
  (scalarA : Set ScalarR) ⊂ Set.univ ∧
    (∃ e : FractionRing scalarA ≃ₐ[ℚ] FractionRing ScalarR,
      ∀ a : scalarA,
        e (algebraMap scalarA (FractionRing scalarA) a) =
          algebraMap ScalarR (FractionRing ScalarR) (a : ScalarR)) ∧
    ¬ IsIntegral scalarA scalarZ

def scalarKElement (k : scalarK) : scalarA :=
  ⟨(k : ScalarR), Algebra.subset_adjoin (Set.mem_union_right _ k.property)⟩

def claim_26421 : Prop :=
  ∀ k : scalarK, (k : ScalarR) ≠ 0 →
    ∃ e : Localization.Away (scalarKElement k) ≃ₐ[ℚ]
        Localization.Away (k : ScalarR),
      ∀ a : scalarA,
        e (algebraMap scalarA (Localization.Away (scalarKElement k)) a) =
          algebraMap ScalarR (Localization.Away (k : ScalarR)) (a : ScalarR)

def claim_26425 : Prop :=
  ∀ a : scalarA,
    IsUnit a ↔
      ∃ q : ℚ, q ≠ 0 ∧ a = algebraMap ℚ scalarA q

def scalarKInA : Ideal scalarA :=
  Ideal.comap scalarA.val scalarK

def claim_26429 : Prop :=
  ¬ ∃ s : Finset scalarA,
      Ideal.span (↑s : Set scalarA) = scalarKInA

def claim_26430 : Prop :=
  (¬ ∀ I : Ideal scalarA,
      ∃ s : Finset scalarA, Ideal.span (↑s : Set scalarA) = I) ∧
    (¬ ∃ s : Finset scalarA,
      Algebra.adjoin ℚ (↑s : Set scalarA) = ⊤)

end
end MathlibPlus.Open.ResearchFormalizationBatch
