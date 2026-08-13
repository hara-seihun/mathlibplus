import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics.AdmittedClaimArithmetic

/-- Claim 41544: the three finite parameter choices have cardinality 6*6*7. -/
theorem claim41544_triangular_stabilizer_count :
    (6 : ℕ) * 6 * 7 = 252 := by
  norm_num

/-- Claim 28911: the normalized triangular choices have cardinality 6*7*2. -/
theorem claim28911_triangular_stabilizer_count :
    (6 : ℕ) * 7 * 2 = 84 := by
  norm_num

/-- Claim 38436: the nonconstant eight-bit masks are counted by 2^8-2. -/
theorem claim38436_nonconstant_mask_count :
    (2 : ℕ) ^ 8 - 2 = 254 := by
  norm_num

/-- Claim 43454: ten binary choices give the ordinary-fusion count. -/
theorem claim43454_fusion_count :
    (2 : ℕ) ^ 10 = 1024 := by
  norm_num

/-- Claim 43454: the stated complement-pair count is half the fusion count. -/
theorem claim43454_complement_pair_count :
    (2 : ℕ) ^ 10 / 2 = 512 := by
  norm_num

/-- Claim 43454: the nine-bit kernel-mask census has 512 masks. -/
theorem claim43454_kernel_mask_count :
    (2 : ℕ) ^ 9 = 512 := by
  norm_num

/-- Claim 37487: the normalized p=3,n=3 point-stabilizer census has 3^10 rows. -/
theorem claim37487_point_stabilizer_count :
    (3 : ℕ) ^ 10 = 59049 := by
  norm_num

/-- Claim 50875: the displayed exact area is 5/2 = 2+1/2. -/
theorem claim50875_area_identity :
    (5 : ℚ) / 2 = 2 + 1 / 2 := by
  norm_num

/-- Claim 25946: the listed parameter dimensions sum to 29. -/
theorem claim25946_nullity_sum :
    (1 : ℕ) + 4 + 6 + 8 + 10 = 29 := by
  norm_num

/-- Claim 25946: subtracting the nullity from 5(N+1) gives 5N-24. -/
theorem claim25946_dimension_difference (N : ℕ) (hN : 9 ≤ N) :
    5 * (N + 1) - 29 = 5 * N - 24 := by
  omega

/-- Claim 27610: the four displacement-rank counts sum to 40,320. -/
theorem claim27610_rank_census_total :
    (8 : ℕ) + 392 + 6832 + 33088 = 40320 := by
  norm_num

/-- Claim 27610: the four affine-rank counts sum to 1,344. -/
theorem claim27610_affine_census_total :
    (8 : ℕ) + 168 + 784 + 384 = 1344 := by
  norm_num

/-- Claim 27610: the four nonlinear-rank counts sum to 38,976. -/
theorem claim27610_nonlinear_census_total :
    (0 : ℕ) + 224 + 6048 + 32704 = 38976 := by
  norm_num

/-- Claim 27610: affine and nonlinear rows partition the full permutation census. -/
theorem claim27610_affine_nonlinear_total :
    (1344 : ℕ) + 38976 = 40320 := by
  norm_num

/-- Claim 27610: the reported composition replay count is 32 times 40,320. -/
theorem claim27610_composition_replay_count :
    (40320 : ℕ) * 32 = 1290240 := by
  norm_num

/-- Claim 27610: the identity-predecessor replay count is 8 times 40,320. -/
theorem claim27610_predecessor_replay_count :
    (40320 : ℕ) * 8 = 322560 := by
  norm_num

/-- Claim 31700: the reported base/scalar count has the displayed factorization. -/
theorem claim31700_base_scalar_factorization :
    (114 : ℕ) * 243 = 27702 := by
  norm_num

/-- Claim 52050: the mixed-row formula at K=3 gives the stated support-three count 9. -/
theorem claim52050_mixed_rows_three :
    (∑ j ∈ Finset.Icc 1 3, (j + 1)) = 9 := by
  decide

/-- Claim 52050: the same formula at K=4 gives the stated count 14. -/
theorem claim52050_mixed_rows_four :
    (∑ j ∈ Finset.Icc 1 4, (j + 1)) = 14 := by
  decide

/-- Claim 48672: the stated Chern-number consequence is arithmetic. -/
theorem claim48672_c2_arithmetic
    (chi kSquared c₂ : ℤ)
    (hχ : chi = 1) (hK : kSquared = 2)
    (hNoether : c₂ = 12 * chi - kSquared) :
    c₂ = 10 := by
  omega

end MathlibPlus.Combinatorics.AdmittedClaimArithmetic
