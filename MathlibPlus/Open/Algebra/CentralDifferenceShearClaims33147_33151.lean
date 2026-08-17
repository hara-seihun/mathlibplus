import MathlibPlus.Open.Algebra.CentralDifferenceShear

namespace MathlibPlus.Open.Algebra.CentralDifferenceShear

noncomputable section

private def liftIn
    {p : ℕ} {U : Type*} [AddCommGroup U]
    [Module (ZMod p) U]
    (lam : U →ₗ[ZMod p] ZMod p)
    (R : Subgroup (centralDifferenceGamma lam))
    (u : U) (f : ZMod p → ZMod p) : Prop :=
  ∃ g : R, (g : Equiv.Perm (E U p)) = functionModuleElement lam u f

private def standardTranslationIn
    {p : ℕ} {U : Type*} [AddCommGroup U]
    [Module (ZMod p) U]
    (lam : U →ₗ[ZMod p] ZMod p)
    (R : Subgroup (centralDifferenceGamma lam))
    (ell : U) : Prop :=
  ∃ g : R, (g : Equiv.Perm (E U p)) = translation (ell, 0)

private def ambientSubgroupSet
    {p : ℕ} {U : Type*} [AddCommGroup U]
    [Module (ZMod p) U]
    (lam : U →ₗ[ZMod p] ZMod p)
    (R : Subgroup (centralDifferenceGamma lam)) :
    Set (Equiv.Perm (E U p)) :=
  {g | ∃ r : R, (r : Equiv.Perm (E U p)) = g}

private def translationGroup
    {p : ℕ} {U : Type*} [AddCommGroup U]
    [Module (ZMod p) U]
    (lam : U →ₗ[ZMod p] ZMod p) :
    Subgroup (Equiv.Perm (E U p)) :=
  Subgroup.closure (Set.range (fun z : E U p => translation z))

private def centralLiftCommutator
    {p : ℕ} {U : Type*} [AddCommGroup U]
    [Module (ZMod p) U]
    (lam : U →ₗ[ZMod p] ZMod p)
    (ell v : U) (fℓ f : ZMod p → ZMod p) : Prop :=
  functionModuleElement lam ell fℓ * functionModuleElement lam v f =
    functionModuleElement lam v f * functionModuleElement lam ell fℓ

/-- Commutation with a lambda-one lift makes a kernel lift constant, and the
constant kernel line permits the standard kernel translation. -/
def kernelLiftNormalization_claim33147 : Prop :=
  ∀ {p : ℕ} {U : Type*} [AddCommGroup U]
    [Module (ZMod p) U]
    (hp : Nat.Prime p)
    (lam : U →ₗ[ZMod p] ZMod p) (hlam : lam ≠ 0),
    let Gamma := centralDifferenceGamma lam
    ∀ R : Subgroup Gamma,
      regularElementaryAbelian Gamma R →
      Nat.card R = p ^ Module.finrank (ZMod p) (E U p) →
      kernelIntersection R (functionKernel Gamma lam) =
        wTranslationLine Gamma R →
      ∀ (ell v : U) (fℓ f : ZMod p → ZMod p),
        lam ell = 0 → lam v = 1 →
        liftIn lam R ell fℓ → liftIn lam R v f →
        centralLiftCommutator lam ell v fℓ f →
        cyclicShift 1 fℓ = fℓ ∧
        (∃ c : ZMod p, ∀ s, fℓ s = c) ∧
          ∃ r : R, (r : Equiv.Perm (E U p)) = translation (ell, 0)

/-- A lambda-one lift has the kernel-valued p-th power whose function is the
cyclic sum, and exponent p forces that sum to vanish. -/
def exponentPZeroSumLift_claim33148 : Prop :=
  ∀ {p : ℕ} {U : Type*} [AddCommGroup U]
    [Module (ZMod p) U]
    (hp : Nat.Prime p)
    (lam : U →ₗ[ZMod p] ZMod p) (hlam : lam ≠ 0),
    let Gamma := centralDifferenceGamma lam
    ∀ R : Subgroup Gamma,
      regularElementaryAbelian Gamma R →
      Nat.card R = p ^ Module.finrank (ZMod p) (E U p) →
      letI : NeZero p := ⟨Nat.ne_of_gt hp.pos⟩
      ∀ (v : U) (f : ZMod p → ZMod p),
        lam v = 1 → liftIn lam R v f →
        functionModuleElement lam v f ^ p =
            functionModuleElement lam 0
              (fun _ => ∑ s ∈ Finset.range p, f (s : ZMod p)) ∧
          ∑ s ∈ Finset.range p, f (s : ZMod p) = 0

/-- A finite-difference lift is removed by the corresponding central shear;
the fixed translation directions and normalized kernel lifts identify the
conjugated translation group with the regular subgroup. -/
def finiteDifferenceConjugatesTranslations_claim33150 : Prop :=
  ∀ {p : ℕ} {U : Type*} [AddCommGroup U]
    [Module (ZMod p) U]
    (hp : Nat.Prime p)
    (lam : U →ₗ[ZMod p] ZMod p) (hlam : lam ≠ 0),
    let Gamma := centralDifferenceGamma lam
    ∀ R : Subgroup Gamma,
      regularElementaryAbelian Gamma R →
      Nat.card R = p ^ Module.finrank (ZMod p) (E U p) →
      kernelIntersection R (functionKernel Gamma lam) =
        wTranslationLine Gamma R →
      (∀ ell : U, lam ell = 0 → standardTranslationIn lam R ell) →
      ∀ (v : U) (f : ZMod p → ZMod p) (n : ZMod p → ZMod p),
        lam v = 1 → liftIn lam R v f →
        (∀ s, n (s + 1) - n s = f s) →
        centralDifferenceShear lam n * translation (v, 0) *
              (centralDifferenceShear lam n)⁻¹ =
            functionModuleElement lam v f ∧
        centralDifferenceShear lam n * translation (w p) *
              (centralDifferenceShear lam n)⁻¹ = translation (w p) ∧
        (∀ ell : U, lam ell = 0 →
          centralDifferenceShear lam n * translation (ell, 0) *
              (centralDifferenceShear lam n)⁻¹ = translation (ell, 0)) ∧
        Set.image (fun t =>
            (centralDifferenceShear lam n) * t *
              (centralDifferenceShear lam n)⁻¹)
            (translationGroup lam : Set (Equiv.Perm (E U p))) =
          ambientSubgroupSet lam R

/-- A quotient-visible linear kernel lift has the nontrivial full-group
commutator, so it cannot occur with the lambda-one lift in an abelian
regular elementary-abelian witness. -/
def hostileQuotientCocycleCounterfeit_claim33151 : Prop :=
  ∀ {p : ℕ} {U : Type*} [AddCommGroup U]
    [Module (ZMod p) U]
    (hp : Nat.Prime p)
    (lam : U →ₗ[ZMod p] ZMod p) (hlam : lam ≠ 0),
    let Gamma := centralDifferenceGamma lam
    ∀ (ell v : U) (κ : ZMod p),
      lam ell = 0 → lam v = 1 → κ ≠ 0 →
      (functionModuleElement lam ell (fun s => κ * s) *
          functionModuleElement lam v 0 *
          (functionModuleElement lam ell (fun s => κ * s))⁻¹ *
          (functionModuleElement lam v 0)⁻¹ =
        translation (0, κ)) ∧
      functionModuleElement lam ell (fun s => κ * s) *
          functionModuleElement lam v 0 ≠
        functionModuleElement lam v 0 *
          functionModuleElement lam ell (fun s => κ * s) ∧
      ∀ R : Subgroup Gamma,
        liftIn lam R ell (fun s => κ * s) →
        liftIn lam R v 0 →
        ¬ regularElementaryAbelian Gamma R

end

end MathlibPlus.Open.Algebra.CentralDifferenceShear
