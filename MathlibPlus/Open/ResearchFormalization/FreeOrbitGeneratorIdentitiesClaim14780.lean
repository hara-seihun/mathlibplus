import Mathlib
import MathlibPlus.Open.RepresentationTheory.CoefficientRepresentationCharacterTableClaim14726
import MathlibPlus.Open.Research.FormalizationBatch11355

namespace MathlibPlus.Open.ResearchFormalization.FreeOrbitGeneratorIdentitiesClaim14780

noncomputable section

/-- The order-eight Weyl group `W(C₂)`. -/
abbrev WeylC2 := DihedralGroup 4

/-- The two simple reflections used by the coefficient representation. -/
def s₀ : WeylC2 := DihedralGroup.sr 0
def s₁ : WeylC2 := DihedralGroup.sr 1

/-- The concrete mixed Satake parameter carrier. -/
abbrev MixedParameter := ℂ × ℂ

/-- Swapping the two Satake coordinates. -/
def swapParameter (q : MixedParameter) : MixedParameter := (q.2, q.1)

/-- Inverting the first Satake coordinate. -/
def invertFirstParameter (q : MixedParameter) : MixedParameter := (q.1⁻¹, q.2)

/-- The four powers of the rotation `s₀s₁` on the mixed parameter. -/
def rotationParameterAction (i : ZMod 4) (q : MixedParameter) : MixedParameter :=
  if i = 0 then q
  else if i = 1 then swapParameter (invertFirstParameter q)
  else if i = 2 then
    swapParameter (invertFirstParameter (swapParameter (invertFirstParameter q)))
  else invertFirstParameter (swapParameter q)

/-- The signed-permutation `W(C₂)` action on `(y, α)`. -/
def signedPermutationParameterAction : WeylC2 → MixedParameter → MixedParameter
  | DihedralGroup.r i => rotationParameterAction i
  | DihedralGroup.sr i => fun q => swapParameter (rotationParameterAction i q)

/-- The normalized mixed finite-prime point from the weight-12 Delta data. -/
def mixedPrimePoint (p : ℕ) (α : ℂ) : MixedParameter :=
  (MathlibPlus.Open.Research.FormalizationBatch11355.unitaryScale p, α)

/-- The exact arithmetic hypotheses on a mixed finite-prime Satake point. -/
def mixedFinitePrimeHypothesis (p : ℕ) (α : ℂ) : Prop :=
  Nat.Prime p ∧
    ‖α‖ = 1 ∧
      α + α⁻¹ =
        (MathlibPlus.Open.Research.FormalizationBatch11355.ramanujanTau p : ℂ) /
          MathlibPlus.Open.Research.FormalizationBatch11355.unitaryScale p

/-- Freeness of the signed-permutation orbit of the displayed arithmetic point. -/
def mixedPrimeOrbitFree (p : ℕ) (α : ℂ) : Prop :=
  ∀ (g w : WeylC2),
    signedPermutationParameterAction (g * w) (mixedPrimePoint p α) =
        signedPermutationParameterAction w (mixedPrimePoint p α) →
      g = 1

/-- The coefficient carrier in degree `k`, namely the reviewed
`Sym^k(ℂ²) ⊗ Sym^k(ℂ²)` model. -/
abbrev CoefficientTarget (k : ℕ) :=
  MathlibPlus.Open.RepresentationTheory.CoefficientMixedSpace k

/-- A representation of `W(C₂)` on the concrete coefficient carrier. -/
abbrev CoefficientRepresentation (k : ℕ) :=
  WeylC2 →* (CoefficientTarget k ≃ₗ[ℂ] CoefficientTarget k)

/-- The representation values at the two generators are the reviewed factor
swap `S` and left reversal `R_h`. -/
def coefficientGeneratorValues (k : ℕ)
    (ρ : CoefficientRepresentation k) : Prop :=
  (∀ v : CoefficientTarget k,
    (ρ s₀).toLinearMap v =
      MathlibPlus.Open.RepresentationTheory.coefficientFactorSwap k v) ∧
    (∀ v : CoefficientTarget k,
    (ρ s₁).toLinearMap v =
      MathlibPlus.Open.RepresentationTheory.coefficientLeftReversal k v)

/-- Regular invertible transport on the orbit.  The first two conjuncts make
`N₀` the normalized groupoid transport from the seed fibre: in particular its
identity map is the identity equivalence, rather than an arbitrary seed-fibre
automorphism. -/
def regularMixedPrimeTransportData (p : ℕ) (α : ℂ)
    (V : MixedParameter → Type*)
    [∀ q : MixedParameter, AddCommGroup (V q)]
    [∀ q : MixedParameter, Module ℂ (V q)]
    (N₀ : ∀ w : WeylC2,
      V (mixedPrimePoint p α) ≃ₗ[ℂ]
        V (signedPermutationParameterAction w (mixedPrimePoint p α)))
    (N : ∀ (g w : WeylC2),
      V (signedPermutationParameterAction w (mixedPrimePoint p α)) ≃ₗ[ℂ]
        V (signedPermutationParameterAction (g * w) (mixedPrimePoint p α))) : Prop :=
  (∀ w : WeylC2,
    HEq (N 1 w)
      (LinearEquiv.refl ℂ
        (V (signedPermutationParameterAction w (mixedPrimePoint p α))))) ∧
    HEq (N₀ 1) (LinearEquiv.refl ℂ (V (mixedPrimePoint p α))) ∧
    (∀ w : WeylC2,
      HEq (N₀ w) ((N₀ 1).trans (N w 1))) ∧
    (∀ (g w : WeylC2),
      HEq (N₀ (g * w))
        ((N₀ w).trans (N g w))) ∧
    (∀ (g h w : WeylC2),
      HEq (N (g * h) w)
        ((N h w).trans (N g (h * w))))

/-- Transport of every seed map into the concrete coefficient representation,
including the two displayed generator identities. -/
def arbitrarySeedGeneratorTransport (p : ℕ) (α : ℂ) (k : ℕ)
    (V : MixedParameter → Type*)
    [∀ q : MixedParameter, AddCommGroup (V q)]
    [∀ q : MixedParameter, Module ℂ (V q)]
    (N₀ : ∀ w : WeylC2,
      V (mixedPrimePoint p α) ≃ₗ[ℂ]
        V (signedPermutationParameterAction w (mixedPrimePoint p α)))
    (N : ∀ (g w : WeylC2),
      V (signedPermutationParameterAction w (mixedPrimePoint p α)) ≃ₗ[ℂ]
        V (signedPermutationParameterAction (g * w) (mixedPrimePoint p α)))
    (ρ : CoefficientRepresentation k) : Prop :=
  regularMixedPrimeTransportData p α V N₀ N →
    coefficientGeneratorValues k ρ →
      ∀ B₀ : V (mixedPrimePoint p α) →ₗ[ℂ] CoefficientTarget k,
        ∃! B : ∀ w : WeylC2,
          V (signedPermutationParameterAction w (mixedPrimePoint p α)) →ₗ[ℂ]
            CoefficientTarget k,
          B 1 = B₀ ∧
            (∀ (g w : WeylC2),
              (B (g * w)).comp (N g w).toLinearMap =
                (ρ g).toLinearMap.comp (B w)) ∧
            (∀ w : WeylC2,
              B w =
                (ρ w).toLinearMap.comp
                  (B₀.comp (N₀ w).symm.toLinearMap)) ∧
            (∀ w : WeylC2,
              (B (s₀ * w)).comp (N s₀ w).toLinearMap =
                (MathlibPlus.Open.RepresentationTheory.coefficientFactorSwap k).comp (B w)) ∧
            (∀ w : WeylC2,
              (B (s₁ * w)).comp (N s₁ w).toLinearMap =
                (MathlibPlus.Open.RepresentationTheory.coefficientLeftReversal k).comp (B w))

/-- Claim 14780: on every mixed finite-prime orbit, the regular generator
identities can be imposed for arbitrary regular seed coefficient data in the
concrete coefficient representation. -/
def freeOrbitGeneratorIdentities_claim14780 : Prop :=
  ∀ (p : ℕ) (α : ℂ),
    mixedFinitePrimeHypothesis p α →
      mixedPrimeOrbitFree p α ∧
        ∀ (k : ℕ)
          (V : MixedParameter → Type*)
          [∀ q : MixedParameter, AddCommGroup (V q)]
          [∀ q : MixedParameter, Module ℂ (V q)]
          (N₀ : ∀ w : WeylC2,
            V (mixedPrimePoint p α) ≃ₗ[ℂ]
              V (signedPermutationParameterAction w (mixedPrimePoint p α)))
          (N : ∀ (g w : WeylC2),
            V (signedPermutationParameterAction w (mixedPrimePoint p α)) ≃ₗ[ℂ]
              V (signedPermutationParameterAction (g * w) (mixedPrimePoint p α)))
          (ρ : CoefficientRepresentation k),
          regularMixedPrimeTransportData p α V N₀ N →
            coefficientGeneratorValues k ρ →
              arbitrarySeedGeneratorTransport p α k V N₀ N ρ

end
end MathlibPlus.Open.ResearchFormalization.FreeOrbitGeneratorIdentitiesClaim14780
