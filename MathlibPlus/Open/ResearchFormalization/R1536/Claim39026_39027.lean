import MathlibPlus.Open.ResearchFormalization.R1536.Claim39028

namespace MathlibPlus.Open.ResearchFormalization.R1536

open MathlibPlus.Open.GraphTheory.R0943

noncomputable section

/-- Claim 39026: the loopless quotient weight is zero on the identity
block, while each nonidentity D-section has one of the five possible sizes;
the identity-free condition leaves the internal identity section unrestricted. -/
def claim39026 : Prop :=
  ∀ {A : Type*} [Fintype A] [DecidableEq A] [Group A],
    ∀ S : Set (ProductCarrier A),
      ordinaryIdentityFree S →
      ordinaryInverseClosed S →
      looplessQuotientWeight S 1 = 0 ∧
      (∀ a : A, a ≠ 1 →
        looplessQuotientWeight S a = 0 ∨
        looplessQuotientWeight S a = 1 ∨
        looplessQuotientWeight S a = 2 ∨
        looplessQuotientWeight S a = 3 ∨
        looplessQuotientWeight S a = 4) ∧
      (∀ a : A, a ≠ 1 →
        looplessQuotientWeight S a =
          looplessQuotientWeight S (a⁻¹))

/-- Claim 39027: once the normalized actual quotient-image presentation and
full-V4 synchronization are supplied, its normalized residual is identity
based, fixes the identity D-fibre, and is affine on every D-fibre, with the
identity-fibre affine coefficients represented by the identity permutation. -/
def claim39027 : Prop :=
  ∀ {A : Type*} [Fintype A] [DecidableEq A] [CommGroup A],
    Odd (Fintype.card A) →
    ∀ (π : Q8 →* D),
      quaternionProjectionData π →
      ∀ (S T : Set (ProductCarrier A))
        (U V : Subgroup (Equiv.Perm (ProductCarrier A)))
        (f : Equiv.Perm (ProductCarrier A)) (α : A ≃* A),
        regularCopy U →
        regularCopy V →
        looplessSectionData S →
        looplessSectionData T →
        fullV4Synchronization U V →
        actualQuotientImagePresentation S T U V f α →
        let r := (liftedQuotientAutomorphism α)⁻¹ * f
        normalizedResidual π f α r

end

end MathlibPlus.Open.ResearchFormalization.R1536
