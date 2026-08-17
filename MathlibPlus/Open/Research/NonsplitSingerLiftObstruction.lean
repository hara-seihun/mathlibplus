import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch01_01a000fa

namespace MathlibPlus.Open.Research.NonsplitSingerLiftObstruction

abbrev F3Vector (r : ℕ) :=
  MathlibPlus.Open.ResearchFormalizationBatch01_01a000fa.BlockVector r
abbrev C4Cover (r : ℕ) :=
  MathlibPlus.Open.ResearchFormalizationBatch01_01a000fa.BlockGroup r
abbrev C2Quotient (r : ℕ) :=
  MathlibPlus.Open.ResearchFormalizationBatch01_01a000fa.BlockQuotient r

/-- The coordinate vector representing `1` in the chosen field basis. -/
def oneVector (r : ℕ) : F3Vector r :=
  fun i => if i.val = 0 then 1 else 0

/-- The coordinate vector for one basis direction. -/
def basisVector (r : ℕ) (i : Fin r) : F3Vector r :=
  fun j => if j = i then 1 else 0

/-- Primitive Singer multiplication together with its logarithm-parity
 character.  The unique exponent condition is the additive-coordinate form
 of `V = F_(3^r)^+` with a primitive `x`; the displayed successor condition
 records that `x` is the second basis vector. -/
def primitiveSingerLogParity {r : ℕ}
    (S : F3Vector r ≃ₗ[ZMod 3] F3Vector r)
    (η : F3Vector r → ZMod 2) : Prop :=
  (∃ i₁ : Fin r, i₁.val = 1 ∧
    S (oneVector r) = basisVector r i₁) ∧
  (∀ v : F3Vector r, v ≠ 0 →
    ∃! j : Fin (3 ^ r - 1),
      (S ^ (j : ℕ)) (oneVector r) = v) ∧
  (∀ j : Fin (3 ^ r - 1),
    η ((S ^ (j : ℕ)) (oneVector r)) = (j.val % 2 : ZMod 2))

/-- The first-two-coordinate transposition in the displayed basis. -/
def firstTwoCoordinateTransposition {r : ℕ}
    (B : F3Vector r ≃ₗ[ZMod 3] F3Vector r) : Prop :=
  ∃ i₀ i₁ : Fin r,
    i₀.val = 0 ∧ i₁.val = 1 ∧
    (∀ v : F3Vector r,
      B v i₀ = v i₁ ∧ B v i₁ = v i₀ ∧
        (∀ i : Fin r, i ≠ i₀ → i ≠ i₁ → B v i = v i))

/-- The four quotient orbital colors of `C₂ × V`, including the diagonal
 color. -/
def quotientColor {r : ℕ} (p : C2Quotient r) : ZMod 4 :=
  if p.2 = 0 then
    if p.1 = 0 then 0 else 1
  else if p.1 = 0 then 2 else 3

/-- The two odd `C₄` coordinates carry the bits `b(1)=0` and `b(3)=1`. -/
def oddCoordinateBit (a : ZMod 4) : ZMod 2 :=
  if a = 1 then 0 else 1

/-- The complete seven-color displacement tuple: the diagonal and the six
 nonidentity Singer orbitals. -/
def upstairsColor {r : ℕ}
    (η : F3Vector r → ZMod 2) (p : C4Cover r) : ZMod 7 :=
  if p.2 = 0 then
    if p.1 = 0 then 0
    else if p.1 = 2 then 1
    else 2
  else if p.1 = 0 then 3
  else if p.1 = 2 then 4
  else if oddCoordinateBit p.1 + η p.2 = 0 then 5 else 6

/-- The quotient action of a linear map, acting trivially on the `C₂`
 coordinate. -/
def quotientMap {r : ℕ}
    (B : F3Vector r ≃ₗ[ZMod 3] F3Vector r) : C2Quotient r → C2Quotient r :=
  fun p => (p.1, B p.2)

/-- Preservation of all quotient colors by the first-two transposition. -/
def preservesQuotientColors {r : ℕ}
    (B : F3Vector r ≃ₗ[ZMod 3] F3Vector r) : Prop :=
  ∀ p q : C2Quotient r,
    quotientColor (q - p) =
      quotientColor (quotientMap B q - quotientMap B p)

/-- The quotient equivalence used by the explicit block-lift normal form. -/
def quotientLinearEquiv {r : ℕ}
    (B : F3Vector r ≃ₗ[ZMod 3] F3Vector r) : C2Quotient r ≃ C2Quotient r :=
  Equiv.prodCongr (Equiv.refl (ZMod 2)) B.toEquiv

/-- Preservation of the complete upstairs orbital tuple by a switch lift. -/
def preservesUpstairsTuple {r : ℕ}
    (B : F3Vector r ≃ₗ[ZMod 3] F3Vector r)
    (η : F3Vector r → ZMod 2)
    (s : C2Quotient r → ZMod 2) : Prop :=
  ∀ p q : C4Cover r,
    upstairsColor η (q - p) =
      upstairsColor η
        (MathlibPlus.Open.ResearchFormalizationBatch01_01a000fa.blockLift
          (quotientLinearEquiv B) s q -
        MathlibPlus.Open.ResearchFormalizationBatch01_01a000fa.blockLift
          (quotientLinearEquiv B) s p)

/-- Exact finite-field census of the two character-difference values. -/
def characterDifferenceCount {r : ℕ}
    (B : F3Vector r ≃ₗ[ZMod 3] F3Vector r)
    (η : F3Vector r → ZMod 2) (b : ZMod 2) : ℕ :=
  (Finset.univ.filter (fun v : F3Vector r =>
    v ≠ 0 ∧ η (B v) + η v = b)).card

def expectedZeroCount (r : ℕ) : ℕ :=
  if r = 3 then 16 else if r = 5 then 148 else 1480

def expectedOneCount (r : ℕ) : ℕ :=
  if r = 3 then 10 else if r = 5 then 94 else 706

/-- Claim 42372: at each of the three stated odd ranks, the displayed
 quotient transposition preserves every quotient color, while no switch
 function gives a lift preserving the complete upstairs tuple. -/
def claim42372 : Prop :=
  ∀ r : ℕ, (r = 3 ∨ r = 5 ∨ r = 7) →
    ∃ S : F3Vector r ≃ₗ[ZMod 3] F3Vector r,
      ∃ η : F3Vector r → ZMod 2,
        primitiveSingerLogParity S η ∧
        ∃ B : F3Vector r ≃ₗ[ZMod 3] F3Vector r,
          firstTwoCoordinateTransposition B ∧
          preservesQuotientColors B ∧
          characterDifferenceCount B η 0 = expectedZeroCount r ∧
          characterDifferenceCount B η 1 = expectedOneCount r ∧
          (∀ s : C2Quotient r → ZMod 2,
            ¬ preservesUpstairsTuple B η s)

end MathlibPlus.Open.Research.NonsplitSingerLiftObstruction
