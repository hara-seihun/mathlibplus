import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.FixedGaleCirculationClaim61211

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev ProfileIndex := Fin 8
abbrev Coordinate := Fin 4
abbrev Vector (p : ℕ) := Coordinate → ZMod p
abbrev Ambient (p : ℕ) := Vector p × Vector p
abbrev PolynomialRing := MvPolynomial Coordinate ℚ

noncomputable def fixedXEntry (i j : ℕ) : ℤ :=
  if i = 0 then
    if j = 0 then 0 else if j = 1 then 1 else if j = 2 then 2 else 0
  else if i = 1 then
    if j = 0 then 3 else if j = 1 then 2 else if j = 2 then 0 else 3
  else if i = 2 then
    if j = 0 then 3 else if j = 1 then 3 else if j = 2 then 2 else 3
  else
    if j = 0 then 1 else if j = 1 then 1 else if j = 2 then 2 else 3

noncomputable def fixedDInt (i a : ℕ) : ℤ :=
  if i < 4 then
    if i = a then 1 else 0
  else
    fixedXEntry a (i - 4)

noncomputable def fixedUInt (i a : ℕ) : ℤ :=
  if i < 4 then
    -fixedXEntry i a
  else
    if i - 4 = a then 1 else 0

noncomputable def fixedDMod (p : ℕ) (i : ProfileIndex) : Vector p :=
  fun a => (fixedDInt i.1 a.1 : ZMod p)

noncomputable def fixedUMod (p : ℕ) (i : ProfileIndex) : Coordinate → ZMod p :=
  fun a => (fixedUInt i.1 a.1 : ZMod p)

noncomputable def fixedDot (p : ℕ) (i : ProfileIndex)
    (v : Vector p) : ZMod p :=
  ∑ a : Coordinate, fixedUMod p i a * v a

noncomputable def certificateExponent (i : ProfileIndex) : Coordinate →₀ ℕ :=
  Finsupp.single (0 : Coordinate) (Int.toNat (fixedDInt i.1 0)) +
    Finsupp.single (1 : Coordinate) (Int.toNat (fixedDInt i.1 1)) +
    Finsupp.single (2 : Coordinate) (Int.toNat (fixedDInt i.1 2)) +
    Finsupp.single (3 : Coordinate) (Int.toNat (fixedDInt i.1 3))

noncomputable def certificateMonomial (i : ProfileIndex) : PolynomialRing :=
  MvPolynomial.monomial (certificateExponent i) 1

noncomputable def certificateTermCount (i : ProfileIndex) : ℕ :=
  if i.1 = 0 then 188 else if i.1 = 1 then 251 else
  if i.1 = 2 then 124 else if i.1 = 3 then 107 else
  if i.1 = 4 then 70 else if i.1 = 5 then 66 else
  if i.1 = 6 then 58 else 19

noncomputable def denominatorPrimesAllowed (q : ℚ) : Prop :=
  ∀ r : ℕ, Nat.Prime r → r ∣ q.den → r = 2 ∨ r = 3

noncomputable def fixedGaleLaurentCertificate : Prop :=
  ∃ W : ProfileIndex → PolynomialRing,
    (∀ i : ProfileIndex, (W i).support.card = certificateTermCount i) ∧
    (∀ i : ProfileIndex, ∀ m ∈ (W i).support,
      (∀ a : Coordinate, m a ≤ 5) ∧
      denominatorPrimesAllowed ((W i).coeff m)) ∧
    (∀ i : ProfileIndex,
      MvPolynomial.eval (fun _ : Coordinate => (1 : ℚ)) (W i) = -1) ∧
    (∀ a : Coordinate,
      ∑ i : ProfileIndex,
        MvPolynomial.C (fixedUInt i.1 a.1 : ℚ) * W i *
          (certificateMonomial i - 1) = 0)

noncomputable def certificateTermCountTotal : Prop :=
  ∑ i : ProfileIndex, certificateTermCount i = 883

noncomputable def tensorEntry (i : ℕ) (flat : ℕ) : ℤ :=
  fixedUInt i (flat / 4) * fixedDInt i (flat % 4)

noncomputable def minorRow (r : Fin 7) : ℕ :=
  if r.1 = 0 then 1 else if r.1 = 1 then 2 else if r.1 = 2 then 3 else
  if r.1 = 3 then 4 else if r.1 = 4 then 5 else
  if r.1 = 5 then 8 else 13

noncomputable def minorColumn (c : Fin 7) : ℕ := c.1 + 1

noncomputable def tensorMinor : Matrix (Fin 7) (Fin 7) ℤ :=
  fun r c => tensorEntry (minorColumn c) (minorRow r)

noncomputable def tensorGaleIdentity : Prop :=
  ∀ flat : Fin 16, ∑ i : ProfileIndex, tensorEntry i.1 flat.1 = 0

noncomputable def tensorMinorDeterminant : Prop :=
  Matrix.det tensorMinor = -108

noncomputable def affineRow (p : ℕ) (i : ProfileIndex) (c : ZMod p) : Set (Ambient p) :=
  {q | q.2 = fixedDMod p i ∧ fixedDot p i q.1 = c}

noncomputable def selectedAffineRows
    (p : ℕ) (I : Set ProfileIndex) (c : ProfileIndex → ZMod p) : Set (Ambient p) :=
  {q | ∃ i : ProfileIndex, i ∈ I ∧ q ∈ affineRow p i (c i)}

noncomputable def rowSymmetrization (p : ℕ) (S : Set (Ambient p)) : Set (Ambient p) :=
  S ∪ {q | -q ∈ S}

noncomputable def inversePairedRows
    (p : ℕ) (I : Set ProfileIndex) (c : ProfileIndex → ZMod p) : Set (Ambient p) :=
  rowSymmetrization p (selectedAffineRows p I c)

noncomputable def nonlinearShear (p : ℕ) (s : Vector p → Vector p) : Ambient p → Ambient p :=
  fun q => (q.1 + s q.2, q.2)

noncomputable def groupLinearShear
    (p : ℕ) (L : Vector p →ₗ[ZMod p] Vector p) : Ambient p → Ambient p :=
  fun q => (q.1 + L q.2, q.2)

noncomputable def nonlinearShearDifference
    (p : ℕ) (s : Vector p → Vector p) (x : Vector p) : Ambient p → Ambient p :=
  fun q => (q.1 + s (x + q.2) - s x, q.2)

noncomputable def fixedGaleTransportShadow
    (p : ℕ) (s : Vector p → Vector p)
    (lambda : ProfileIndex → ZMod p)
    (L : Vector p →ₗ[ZMod p] Vector p) : Prop :=
  ∀ I : Set ProfileIndex,
    (∀ x : Vector p,
      Set.image (nonlinearShearDifference p s x)
          (selectedAffineRows p I (fun _ => 0)) =
        selectedAffineRows p I lambda) ∧
      Set.image (groupLinearShear p L)
          (selectedAffineRows p I (fun _ => 0)) =
        selectedAffineRows p I lambda ∧
      (∃ e : Ambient p ≃+ Ambient p,
        (∀ q : Ambient p, e q = groupLinearShear p L q) ∧
          ∀ J : Set ProfileIndex,
            e '' selectedAffineRows p J (fun _ => 0) =
              selectedAffineRows p J lambda) ∧
      (∀ x : Vector p,
        rowSymmetrization p
            (Set.image (nonlinearShearDifference p s x)
              (selectedAffineRows p I (fun _ => 0))) =
          rowSymmetrization p
            (Set.image (groupLinearShear p L)
              (selectedAffineRows p I (fun _ => 0)))) ∧
      (∀ x : Vector p,
        rowSymmetrization p
            (Set.image (groupLinearShear p L)
              (selectedAffineRows p I (fun _ => 0))) =
          inversePairedRows p I lambda)

noncomputable def fixedGaleCirculationTheorem : Prop :=
  ∀ p : ℕ, Nat.Prime p → 5 ≤ p →
    ∀ (s : Vector p → Vector p)
      (lambda : ProfileIndex → ZMod p),
      (∀ i : ProfileIndex, ∀ x : Vector p,
        fixedDot p i (s (x + fixedDMod p i) - s x) = lambda i) →
      (∑ i : ProfileIndex, lambda i = 0) ∧
        ∃ L : Vector p →ₗ[ZMod p] Vector p,
          (∀ i : ProfileIndex,
            fixedDot p i (L (fixedDMod p i)) = lambda i) ∧
          fixedGaleTransportShadow p s lambda L

/-- Claim 61211: the exact fixed rank-eight certificate, its tensor minor, the
universal constant-difference circulation theorem, the linear slope shadow,
and the directed and inverse-paired ordinary-undirected row transports. -/
def correctedUniversalCirculationShadow_claim61211 : Prop :=
  fixedGaleLaurentCertificate ∧
    certificateTermCountTotal ∧
    tensorGaleIdentity ∧
    tensorMinorDeterminant ∧
    fixedGaleCirculationTheorem

end

end MathlibPlus.Open.ResearchFormalization.FixedGaleCirculationClaim61211
