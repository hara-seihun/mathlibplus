import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0331Claims19961_19962

noncomputable section
open Classical
open scoped BigOperators

/-- The support of one actual ground coordinate across a distinct family. -/
def coordinateSupport {γ : Type} (F : Finset (Finset γ)) (x : γ) :
    Finset (Finset γ) :=
  F.filter (fun A => x ∈ A)

def supportFamily {γ : Type} (U : Finset γ)
    (F : Finset (Finset γ)) : Finset (Finset (Finset γ)) :=
  (U.image (coordinateSupport F)).filter Finset.Nonempty

def supportsUnionClosed {γ : Type} (U : Finset γ)
    (F : Finset (Finset γ)) : Prop :=
  ∀ S ∈ supportFamily U F, ∀ T ∈ supportFamily U F,
    S ∪ T ∈ supportFamily U F

def uniformOnGround {γ : Type} (U : Finset γ)
    (F : Finset (Finset γ)) (n : ℕ) : Prop :=
  ∀ A ∈ F, A ⊆ U ∧ A.card = n

def goldenAlpha : ℝ := (3 - Real.sqrt 5) / 2
def goldenAlphaInverse : ℝ := (3 + Real.sqrt 5) / 2

/-- Claim 19961: a distinct n-uniform family with union-closed nonempty
coordinate supports has the exact golden-ratio linear bound. -/
def claim19961 : Prop :=
  ∀ {γ : Type} (U : Finset γ) (F : Finset (Finset γ)) (n : ℕ),
    1 ≤ n →
      uniformOnGround U F n →
        supportsUnionClosed U F →
          (F.card : ℝ) ≤ goldenAlphaInverse * (n : ℝ)

/-- The number of actual ground coordinates having one support pattern. -/
def supportMultiplicity {γ : Type} (U : Finset γ)
    (F : Finset (Finset γ)) (S : Finset (Finset γ)) : ℕ :=
  (U.filter (fun x => coordinateSupport F x = S)).card

def supportPatternCount {γ : Type} (U : Finset γ)
    (F : Finset (Finset γ)) (A : Finset γ) : ℕ :=
  (supportFamily U F).filter (fun S => A ∈ S) |>.card

def weightedSupportCount {γ : Type} (U : Finset γ)
    (F : Finset (Finset γ)) (A : Finset γ) : ℕ :=
  ∑ S ∈ supportFamily U F,
    if A ∈ S then supportMultiplicity U F S else 0

/-- Claim 19962: positive actual-coordinate multiplicities dominate the number
of support patterns, and a golden-alpha frequent member gives the stated bound. -/
def claim19962 : Prop :=
  ∀ {γ : Type} (U : Finset γ) (F : Finset (Finset γ)) (n : ℕ),
    1 ≤ n →
      uniformOnGround U F n →
        (∀ S ∈ supportFamily U F,
          1 ≤ supportMultiplicity U F S) →
          (∀ A ∈ F,
            (n : ℝ) = weightedSupportCount U F A ∧
              (supportPatternCount U F A : ℝ) ≤ n) ∧
            ((∃ A ∈ F,
                goldenAlpha * (supportFamily U F).card ≤
                  supportPatternCount U F A) →
              goldenAlpha * (supportFamily U F).card ≤ n)

end
end MathlibPlus.Open.ResearchFormalization.R0331Claims19961_19962
