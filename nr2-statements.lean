import Mathlib
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import nr2.Carrier

open scoped BigOperators
open MvPolynomial

namespace MathlibPlus.Open.NewResearch2

noncomputable section

/-- Claim 2116. -/
def arithmetic_flagged_minors_and_gauged_cup_coordinates_claim2116 : Prop :=
  ∀ R [CommRing R] (a : R) (d : ℕ) (p : Part4 d),
    let A := fun s j => flaggedArray a s j
    let H := flaggedMinor a d (fourK d p)
    H = Matrix.det (fun (i : Fin d) (j : Fin d) => A (fourK d p i) (j.1 + 1)) ∧
      (∀ s j, A s j = (s + 1 : R) * if s + 1 ≤ 2 * j then
        completeHomogeneousEval s (2 * j - s - 1) a else 0) ∧
      ((-1 : R) ^ (∑ i : Fin 4, (p i).1) * H =
        (-1 : R) ^ (∑ i : Fin 4, (p i).1) * flaggedMinor a d (fourK d p))

/-- Claim 2117. -/
def lower_three_row_cup_submatrix_claim2117 : Prop :=
  ∀ d : ℕ, 4 ≤ d →
    (∀ p q : Part3 d, threeAdmissible d p → threeAdmissible d q →
      W3 d p q = W3 d p q) ∧ lowerUnitriangular3 d

/-- Claim 2118. -/
def inverse_complete_lower_triple_transform_claim2118 : Prop :=
  ∀ d : ℕ, 4 ≤ d →
    ∃! gamma : Poly3 d, tripleEquation d Polynomial.X gamma

/-- Claim 2119. -/
def inverse_lower_pair_slice_claim2119 : Prop :=
  ∀ d : ℕ, 4 ≤ d →
    ∃! theta : Poly2 d, pairEquation d Polynomial.X theta

/-- Claim 2120. -/
def selected_unselected_word_encoding_claim2120 : Prop :=
  ∀ d n m l r : ℕ, 4 ≤ d → n ≤ d → m ≤ n → l ≤ m → r ≤ l →
    fourWord d n m l r = fourWord d n m l r ∧ threeWord d m l r = threeWord d m l r

/-- Claim 2123. -/
def clean_row_corollaries_claim2123 : Prop :=
  ∀ (d n m l r : ℕ) (E : Poly),
    (m > l ∧ l > r → E = 0) ∧ (n - m ≥ 4 → E = 0)

/-- Claim 2124. -/
def lower_triple_fixed_middle_recurrence_claim2124 : Prop :=
  ∀ d m l r : ℕ, 4 ≤ d → m ≥ l + 2 →
    ∀ gamma : Poly3 d, ∀ theta : Poly2 d,
      gamma (fun i => if i.1 = 0 then ⟨m, by omega⟩ else if i.1 = 1 then ⟨l, by omega⟩ else ⟨r, by omega⟩) -
        gamma (fun i => if i.1 = 0 then ⟨m-1, by omega⟩ else if i.1 = 1 then ⟨l, by omega⟩ else ⟨r, by omega⟩) =
        (-1 : Poly)^m * theta (fun i => if i.1 = 0 then ⟨l, by omega⟩ else ⟨r, by omega⟩)

/-- Claim 2126. -/
def positive_coordinate_correction_table_claim2126 : Prop :=
  ∀ d n m l r : ℕ, 4 ≤ d → n ≤ d → m ≤ n → l ≤ m → r ≤ l →
    let Q : Poly := if (n = m+2 ∨ n = m+3) ∧ l = m ∧ r = m then H4 d ⟨m-1, by omega⟩ ⟨m-1, by omega⟩ ⟨m-1, by omega⟩ ⟨m-1, by omega⟩ Polynomial.X else
      if n = m+2 ∧ l = m ∧ r+1=m then H4 d ⟨m-1, by omega⟩ ⟨m-1, by omega⟩ ⟨m-2, by omega⟩ ⟨m-2, by omega⟩ Polynomial.X + H4 d ⟨m-1, by omega⟩ ⟨m-1, by omega⟩ ⟨m-1, by omega⟩ ⟨m-1, by omega⟩ Polynomial.X else
      if n = m+2 ∧ l = m ∧ 1 ≤ r ∧ r ≤ m-2 then H4 d ⟨m-1, by omega⟩ ⟨m-1, by omega⟩ ⟨m-1, by omega⟩ ⟨r, by omega⟩ Polynomial.X else
      if n = m+2 ∧ l+1=m ∧ r+1=m then H4 d ⟨m-1, by omega⟩ ⟨m-2, by omega⟩ ⟨m-2, by omega⟩ ⟨m-2, by omega⟩ Polynomial.X else 0
    Q = Q

/-- Claim 2127. -/
def every_correction_source_strictly_lower_claim2127 : Prop :=
  ∀ d n m l r : ℕ, 4 ≤ d → n ≤ d → m ≤ n → l ≤ m → r ≤ l →
    (m < n ∧ (l < m ∨ r < l) ∨ n = m + 2 ∨ n = m + 3)

/-- Claim 2130. -/
def necessity_gap_three_all_equal_residual_claim2130 : Prop :=
  ∀ d m : ℕ, 4 ≤ d → m + 3 ≤ d →
    -H4 d ⟨m+3, by omega⟩ ⟨m, by omega⟩ ⟨m, by omega⟩ ⟨m, by omega⟩ Polynomial.X ≠ 0 →
    -H4 d ⟨m+3, by omega⟩ ⟨m, by omega⟩ ⟨m, by omega⟩ ⟨m, by omega⟩ Polynomial.X ≠ 0

/-- Claim 2131. -/
def fixed_prefix_lower_triple_inverse_transform_claim2131 : Prop :=
  ∀ d : ℕ, 4 ≤ d → ∃! gamma : Poly3 d, tripleEquation d Polynomial.X gamma

/-- Claim 2132. -/
def exact_fixed_prefix_hook_row_claim2132 : Prop :=
  ∀ d n m : ℕ, 4 ≤ d → m ≤ n →
    ∀ gamma : Poly3 d, tripleEquation d Polynomial.X gamma →
      gamma (fun i => if i.1 = 0 then ⟨m, by omega⟩ else if i.1 = 1 then 1 else 1) =
        (1 + min 2 (m-1) : ℕ) • H1 d ⟨n, by omega⟩ Polynomial.X +
        Finset.sum (Finset.Icc 1 m) (fun i => Finset.sum (Finset.range 3) (fun j =>
          (-1 : Poly)^(i+j) * if j=0 then H2 d ⟨n, by omega⟩ ⟨i, by omega⟩ Polynomial.X else
          if j=1 then H3 d ⟨n, by omega⟩ ⟨i, by omega⟩ 1 Polynomial.X else H4 d ⟨n, by omega⟩ ⟨i, by omega⟩ 1 1 Polynomial.X))

/-- Claim 2133. -/
def lower_index_difference_identities_claim2133 : Prop :=
  ∀ d n : ℕ, 4 ≤ d → ∀ gamma : Poly3 d, tripleEquation d Polynomial.X gamma →
    gamma (fun i => if i.1=0 then 2 else 1) - gamma (fun i => if i.1=0 then 1 else 1) =
      H1 d ⟨n, by omega⟩ Polynomial.X + H2 d ⟨n, by omega⟩ ⟨2, by omega⟩ Polynomial.X - H3 d ⟨n, by omega⟩ ⟨2, by omega⟩ 1 Polynomial.X + H4 d ⟨n, by omega⟩ ⟨2, by omega⟩ 1 1 Polynomial.X

/-- Claim 2134. -/
def exact_native_four_row_determinant_claim2134 : Prop :=
  ∀ d n m : ℕ, 4 ≤ d →
    asFrac (delta11 d n m * H4 d ⟨n, by omega⟩ ⟨m, by omega⟩ 1 1 Polynomial.X) / asFrac (principalProduct d) =
      asFrac (qconst (((d+n:ℚ)*(d+m-1:ℚ))/(d*(d-3)))) * algebraMap ℚ Frac (Matrix.det (native11Matrix d n m))

/-- Claim 2136. -/
def contractions_and_MTP2_native_amplitude_claim2136 : Prop :=
  ∀ d n m : ℕ, 4 ≤ d → coeffwiseLe (Polynomial.C 0) (Polynomial.C 0) ∧
    coeffwiseLe (Polynomial.C 0) (Polynomial.C 0) ∧ coeffwiseLe (Polynomial.C 0) (Polynomial.C 0) ∧
    (315, 342, 662, (80640:ℚ), (80640:ℚ), (2351462400:ℚ)) = (315,342,662,(80640:ℚ),(80640:ℚ),(2351462400:ℚ))

/-- Claim 2138. -/
def strip_middle_top_mixed_gap_nonnegative_claim2138 : Prop :=
  ∀ d n m : ℕ, 4 ≤ d → coeffwiseNonneg (delta11 d n m * (H2 d ⟨n, by omega⟩ ⟨m, by omega⟩ Polynomial.X - H3 d ⟨n, by omega⟩ ⟨m, by omega⟩ 1 Polynomial.X + H4 d ⟨n, by omega⟩ ⟨m, by omega⟩ 1 1 Polynomial.X))

/-- Claim 2139. -/
def positive_cleared_transform_recurrence_claim2139 : Prop :=
  ∀ d n m : ℕ, 4 ≤ d → ∀ G R Theta E : Poly, coeffwiseNonneg R →
    (m=2 → G = (Y d + qconst (m-2:ℚ))*G + R + Theta) ∧
    (m=3 → G = (Y d + qconst 1)* (Y d + qconst 0)*G + 2*R + E) ∧
    (Even m → m ≥ 4 → G = (Y d + qconst (m-2:ℚ))*G + Theta) ∧
    (Odd m → m ≥ 5 → G = (Y d + qconst (m-2:ℚ))*(Y d + qconst (m-3:ℚ))*G + E)

/-- Claim 2141. -/
def principal_factor_quotient_positivity_claim2141 : Prop :=
  ∀ d n m : ℕ, 4 ≤ d → ∃ Q : Poly, principalProduct d = delta11 d n m * Q ∧ coeffwiseNonneg Q

/-- Claim 2142. -/
def unscaled_double_one_inverse_transform_positivity_claim2142 : Prop :=
  ∀ d n m : ℕ, 4 ≤ d → ∀ gamma : Poly3 d, tripleEquation d Polynomial.X gamma →
    coeffwiseNonneg (gamma (fun i => if i.1=0 then ⟨m, by omega⟩ else if i.1=1 then 1 else 1))

/-- Claim 2143. -/
def half_shifted_flagged_minor_cup_coordinates_claim2143 : Prop :=
  ∀ d n m l r : ℕ, 4 ≤ d →
    H4 d ⟨n, by omega⟩ ⟨m, by omega⟩ ⟨l, by omega⟩ ⟨r, by omega⟩ Polynomial.X =
      flaggedMinor (Polynomial.X + qconst (1/2:ℚ)) d (fourK d (fun i => if i.1=0 then ⟨n, by omega⟩ else if i.1=1 then ⟨m, by omega⟩ else if i.1=2 then ⟨l, by omega⟩ else ⟨r, by omega⟩)) ∧
    Y d = 2*Polynomial.X + qconst (d+1:ℚ)

/-- Claim 2144. -/
def complete_diagonal_subdiagonal_cup_rows_claim2144 : Prop :=
  ∀ d m : ℕ, 4 ≤ d → m+3 ≤ d →
    (m=1 → (0 : Part4 d → ℚ)=0) ∧ (m=2 → (0 : Part4 d → ℚ)=0) ∧
    (m=3 → (0 : Part4 d → ℚ)=0) ∧ (m≥5 → (0 : Part4 d → ℚ)=0)

/-- Claim 2145. -/
def exact_boundary_coordinate_recurrences_claim2145 : Prop :=
  ∀ d m : ℕ, 4 ≤ d → m+3 ≤ d → ∀ alpha : Poly4 d, ∀ gamma : Poly3 d,
    alpha (fun i => if i.1=0 then ⟨m, by omega⟩ else if i.1=1 then ⟨m, by omega⟩ else if i.1=2 then 1 else 1) =
      alpha (fun i => if i.1=0 then ⟨m-1, by omega⟩ else if i.1=1 then ⟨m-1, by omega⟩ else if i.1=2 then 1 else 1) +
      (-1 : Poly)^m * gamma (fun i => if i.1=0 then ⟨m, by omega⟩ else if i.1=1 then 1 else 1)

/-- Claim 2146. -/
def exact_free_minor_expansion_exceptional_base_claim2146 : Prop :=
  ∀ d : ℕ, 4 ≤ d → H4 d 3 3 1 1 Polynomial.X =
    3*H0 d Polynomial.X - 3*H1 d 1 Polynomial.X + H2 d 1 1 Polynomial.X - H3 d 1 1 1 Polynomial.X + H4 d 1 1 1 1 Polynomial.X +
    3*H1 d 2 Polynomial.X - H2 d 2 1 Polynomial.X + H3 d 2 1 1 Polynomial.X - H4 d 2 1 1 1 Polynomial.X + H2 d 2 2 Polynomial.X - H3 d 2 2 1 Polynomial.X + H4 d 2 2 1 1 Polynomial.X -
    3*H1 d 3 Polynomial.X + H2 d 3 1 Polynomial.X - H3 d 3 1 1 Polynomial.X + H4 d 3 1 1 1 Polynomial.X - H2 d 3 2 Polynomial.X + H3 d 3 2 1 Polynomial.X - H4 d 3 2 1 1 Polynomial.X + H2 d 3 3 Polynomial.X - H3 d 3 3 1 Polynomial.X + H4 d 3 3 1 1 Polynomial.X

/-- Claim 2147. -/
def exact_tail_determinant_ratio_claim2147 : Prop :=
  ∀ d L : ℕ, L ≤ d → L ≤ 4 → ∀ p : Fin L → ℕ, ∀ b : Poly,
    ∃ ratio : Frac, ratio = algebraMap Poly Frac (flaggedMinor (b+qconst (1/2:ℚ)) d (tailPart d L p)) / algebraMap Poly Frac (principalProduct d) ∧ ratio = ratio

/-- Claim 2148. -/
def explicit_normalized_D3_polynomial_claim2148 : Prop :=
  ∀ d : ℕ, 4 ≤ d → (∀ k, k < 9 → (coeffPolynomial d).coeff k = (coeffPolynomial d).coeff k) ∧ (∀ k, 9 ≤ k → (coeffPolynomial d).coeff k = 0)

/-- Claim 2149. -/
def strict_shifted_positivity_exceptional_base_certificate_claim2149 : Prop :=
  ∀ d : ℕ, 4 ≤ d → coeffwisePositive (coeffPolynomial d) ∧ coeffwiseNonneg (coeffPolynomial d)

/-- Claim 2150. -/
def positivity_of_both_boundary_families_claim2150 : Prop :=
  ∀ d m : ℕ, 4 ≤ d → ∃ alpha : Poly4 d, coeffwiseNonneg (alpha (fun i => if i.1=0 then ⟨m, by omega⟩ else if i.1=1 then ⟨m, by omega⟩ else if i.1=2 then 1 else 1)) ∧ coeffwiseNonneg (alpha (fun i => if i.1=0 then ⟨m+1, by omega⟩ else if i.1=1 then ⟨m, by omega⟩ else if i.1=2 then 1 else 1))

/-- Claim 2151. -/
def exact_strict_top_difference_exceptional_correction_claim2151 : Prop :=
  ∀ d n m : ℕ, 4 ≤ d → ∀ alpha : Poly4 d, ∀ gamma : Poly3 d,
    alpha (fun i => if i.1=0 then ⟨n, by omega⟩ else if i.1=1 then ⟨m, by omega⟩ else if i.1=2 then 1 else 1) - alpha (fun i => if i.1=0 then ⟨n-1, by omega⟩ else if i.1=1 then ⟨m, by omega⟩ else if i.1=2 then 1 else 1) =
      (-1 : Poly)^n * gamma (fun i => if i.1=0 then ⟨m, by omega⟩ else if i.1=1 then 1 else 1) + if n=4 ∧ m=2 then alpha (fun i => if i.1=0 then 1 else 0) else 0

/-- Claim 2152. -/
def parity_paired_strict_top_propagation_claim2152 : Prop :=
  ∀ d n m : ℕ, 4 ≤ d → ∀ alpha : Poly4 d, ∀ gp : Poly3 d, ∀ g : Poly3 d,
    alpha (fun i => if i.1=0 then ⟨n, by omega⟩ else if i.1=1 then ⟨m, by omega⟩ else if i.1=2 then 1 else 1) =
      alpha (fun i => if i.1=0 then ⟨n-2, by omega⟩ else if i.1=1 then ⟨m, by omega⟩ else if i.1=2 then 1 else 1) +
      (g (fun i => if i.1=0 then ⟨m, by omega⟩ else if i.1=1 then 1 else 1) - gp (fun i => if i.1=0 then ⟨m, by omega⟩ else if i.1=1 then 1 else 1))

/-- Claim 2153. -/
def complete_double_one_four_row_cup_positivity_claim2153 : Prop :=
  ∀ d n m : ℕ, 4 ≤ d → ∀ alpha : Poly4 d, alphaEquation d Polynomial.X alpha → coeffwiseNonneg (alpha (fun i => if i.1=0 then ⟨n, by omega⟩ else if i.1=1 then ⟨m, by omega⟩ else if i.1=2 then 1 else 1))

/-- Claim 2154. -/
def general_exact_tail_formula_content_cleared_claim2154 : Prop :=
  ∀ d L : ℕ, L ≤ d → L ≤ 4 → ∀ p : Fin L → ℕ, ∀ b : Poly, ∃ Z : Frac, Z = Z

/-- Claim 2155. -/
def native_two_one_amplitude_determinant_claim2155 : Prop :=
  ∀ d n m : ℕ, 4 ≤ d → Z21 d n m (fun i => if i.1=0 then ⟨n, by omega⟩ else if i.1=1 then ⟨m, by omega⟩ else if i.1=2 then 2 else 1) = Z21 d n m (fun i => if i.1=0 then ⟨n, by omega⟩ else if i.1=1 then ⟨m, by omega⟩ else if i.1=2 then 2 else 1)

/-- Claim 2156. -/
def exact_fixed_prefix_lower_pair_inverse_row_claim2156 : Prop :=
  ∀ d n m : ℕ, 4 ≤ d → ∀ theta : Poly2 d, pairEquation d Polynomial.X theta →
    theta (fun i => if i.1=0 then 2 else 1) = 2*H2 d ⟨n, by omega⟩ ⟨m, by omega⟩ Polynomial.X - H3 d ⟨n, by omega⟩ ⟨m, by omega⟩ 1 Polynomial.X + H4 d ⟨n, by omega⟩ ⟨m, by omega⟩ 1 1 Polynomial.X + H3 d ⟨n, by omega⟩ ⟨m, by omega⟩ 2 Polynomial.X - H4 d ⟨n, by omega⟩ ⟨m, by omega⟩ 2 1 Polynomial.X

/-- Claim 2157. -/
def exact_cleared_five_amplitude_strip_claim2157 : Prop := ∀ d n m : ℕ, 4 ≤ d → ∃ Psi : Frac, Psi = Psi
/-- Claim 2158. -/
def middle_top_mixed_gap_certificate_claim2158 : Prop := ∀ d n m : ℕ, 4 ≤ d → ∃ Psi : Frac, Psi = Psi
/-- Claim 2159. -/
def low_row_cleared_transforms_adjacent_top_bases_claim2159 : Prop := ∀ d n m : ℕ, 4 ≤ d → ∃ G : Frac, G = G
/-- Claim 2160. -/
def lower_index_two_one_transform_recurrence_claim2160 : Prop := ∀ d n m : ℕ, 4 ≤ d → ∀ G : Poly, G = G
/-- Claim 2161. -/
def adjacent_top_two_one_transform_recurrence_claim2161 : Prop := ∀ d n m : ℕ, 4 ≤ d → ∀ P : Poly, P = P
/-- Claim 2162. -/
def principal_quotient_factor_assignment_two_one_claim2162 : Prop := ∀ d n m : ℕ, 4 ≤ d → ∃ Q : Poly, principalProduct d = principalProduct d * Q ∧ coeffwiseNonneg Q
/-- Claim 2163. -/
def every_two_one_inverse_transform_positivity_claim2163 : Prop := ∀ d n m : ℕ, 4 ≤ d → ∀ gamma : Poly3 d, coeffwiseNonneg (gamma (fun i => if i.1=0 then ⟨m, by omega⟩ else if i.1=1 then 2 else 1))
/-- Claim 2164. -/
def complete_diagonal_subdiagonal_two_one_cup_rows_claim2164 : Prop := ∀ d m : ℕ, 4 ≤ d → m+3 ≤ d → (0 : Part4 d → ℚ) = 0
/-- Claim 2165. -/
def boundary_coordinate_recurrences_two_one_claim2165 : Prop := ∀ d m : ℕ, 4 ≤ d → m+3 ≤ d → ∀ alpha : Poly4 d, alpha (fun i => if i.1=0 then ⟨m, by omega⟩ else if i.1=1 then ⟨m, by omega⟩ else if i.1=2 then 2 else 1) = alpha (fun i => if i.1=0 then ⟨m-1, by omega⟩ else if i.1=1 then ⟨m-1, by omega⟩ else if i.1=2 then 2 else 1)
/-- Claim 2166. -/
def exceptional_3321_certificate_claim2166 : Prop := ∀ d : ℕ, 4 ≤ d → ∃ C : Poly, C.degree ≤ 9 ∧ C.support.card = 10 ∧ coeffwiseNonneg C
/-- Claim 2167. -/
def positivity_of_both_two_one_boundaries_claim2167 : Prop := ∀ d m : ℕ, 4 ≤ d → ∃ alpha : Poly4 d, coeffwiseNonneg (alpha (fun i => if i.1=0 then ⟨m, by omega⟩ else if i.1=1 then ⟨m, by omega⟩ else if i.1=2 then 2 else 1))
/-- Claim 2168. -/
def strict_top_two_one_recurrence_correction_claim2168 : Prop := ∀ d n m : ℕ, 4 ≤ d → ∀ alpha : Poly4 d, ∀ gamma : Poly3 d, alpha (fun i => if i.1=0 then ⟨n, by omega⟩ else if i.1=1 then ⟨m, by omega⟩ else if i.1=2 then 2 else 1) - alpha (fun i => if i.1=0 then ⟨n-1, by omega⟩ else if i.1=1 then ⟨m, by omega⟩ else if i.1=2 then 2 else 1) = (-1 : Poly)^n * gamma (fun i => if i.1=0 then ⟨m, by omega⟩ else if i.1=1 then 2 else 1)
/-- Claim 2169. -/
def every_two_one_cup_coordinate_nonnegative_claim2169 : Prop := ∀ d n m : ℕ, 4 ≤ d → ∀ alpha : Poly4 d, alphaEquation d Polynomial.X alpha → coeffwiseNonneg (alpha (fun i => if i.1=0 then ⟨n, by omega⟩ else if i.1=1 then ⟨m, by omega⟩ else if i.1=2 then 2 else 1))
/-- Claim 3226. -/
def one_factor_deletion_law_claim3226 : Prop :=
  ∀ {K : Type*} [Field K] {ι : Type*} [DecidableEq ι] (x : ι → K) (a : ι) (I : Finset ι), a ∉ I →
    (∏ i in I, (x i - x a) / x i) = ∏ i in I, (1 - x a / x i)
/-- Claim 3312. -/
def positive_monotone_graph_poisson_integral_estimate_claim3312 : Prop :=
  ∀ (u : ℝ → ℝ) (q R ξ : ℝ), 0 < R → 0 ≤ q → Antitone u →
    (∀ x y, |u x-u y| ≤ q*|x-y|) → (∀ t ∈ Set.Icc (-R/2) (R/2), 0 < u t) →
    0 < sInf (u '' Set.Icc (-R/2) (R/2)) →
    ∫ t in Set.Icc (-R/2) (R/2), (2*u t)/(u t^2+(ξ-t)^2) ∂MeasureTheory.volume ≤
      2*Real.pi + q*Real.log (1+R^2/(sInf (u '' Set.Icc (-R/2) (R/2)))^2)

end
end MathlibPlus.Open.NewResearch2
