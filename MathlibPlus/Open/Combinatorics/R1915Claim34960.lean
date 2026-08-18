import MathlibPlus.Open.Combinatorics.R1915Claim34961

namespace MathlibPlus.Open.Combinatorics.R1915Claim34960

noncomputable section

open Classical
open MathlibPlus.Open.Combinatorics.R1915Claim34961

abbrev Quotient3 := Fin 3 → ZMod 2

/-- The normalized three-point corner `A = {0,1,2}` in the three-bit
quotient. -/
def normalizedCorner : Finset Quotient3 :=
  {0, ![1, 0, 0], ![0, 1, 0]}

/-- The fourth point of the normalized affine plane. -/
def normalizedFourth : Quotient3 :=
  ![1, 1, 0]

/-- The normalized corner plane `P = {0,1,2,3}`. -/
def normalizedPlane : Set Quotient3 :=
  {0, ![1, 0, 0], ![0, 1, 0], ![1, 1, 0]}

/-- The selected complement `S = 𝔽₂³ \ A`. -/
def normalizedSelected : Finset Quotient3 :=
  (Finset.univ : Finset Quotient3) \ normalizedCorner

/-- The selected-set autocorrelation `|S ∩ (S + v)| / 8`. -/
def selectedAutocorrelation
    (S : Finset Quotient3) (v : Quotient3) : ℚ :=
  ((S ∩ S.image (fun x => x + v)).card : ℚ) / 8

/-- Claim 34960: after the stated affine normalization, the complement of the
three-point corner has the three autocorrelation classes, and these values are
also the densities of the literal selected opposite pairs determined by the
actual quotient displacements. -/
def claim34960 : Prop :=
  let A : Finset Quotient3 := normalizedCorner
  let P : Set Quotient3 := normalizedPlane
  let S : Finset Quotient3 := normalizedSelected
  (selectedAutocorrelation S 0 = (5 / 8 : ℚ)) ∧
    (∀ v : Quotient3, v ≠ 0 → v ∈ P →
      selectedAutocorrelation S v = (1 / 2 : ℚ)) ∧
    (∀ v : Quotient3, v ∉ P →
      selectedAutocorrelation S v = (1 / 4 : ℚ)) ∧
    (∀ (n : ℕ) (H : Finset (Fin n))
      (F : Fin n → Cube n → Quotient3)
      (E : Fin n → Cube n → Prop),
      missingCornerData H F (fun _ => A) E →
        (∀ i : Fin n, i ∈ H → F i zeroCube = normalizedFourth) →
          ∀ i : Fin n, i ∈ H →
          ∀ j : Fin n, j ∈ H → i ≠ j →
            let v := directionalDisplacement F i j
            oppositePairDensity E i j = selectedAutocorrelation S v ∧
              oppositePairDensity E i j =
                if v = 0 then (5 / 8 : ℚ)
                else if v ∈ P then (1 / 2 : ℚ)
                else (1 / 4 : ℚ))

end

end MathlibPlus.Open.Combinatorics.R1915Claim34960
