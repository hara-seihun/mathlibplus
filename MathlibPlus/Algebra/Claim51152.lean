import Mathlib

namespace MathlibPlus.Algebra.Claim51152

/--
The algebraic core of claim 51152.  The inverse witness `r` encodes that
multiplication by `4` is invertible.  The pointwise fourth-power condition and
`_horder_four` encode an automorphism of exact order four; only the former is
needed by the displayed contraction.  For a norm-zero vector, the stated
weighted orbit sum is therefore a coboundary for `q - 1`.
-/
theorem normZeroOrderFour_coboundary
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (q : M ≃ₗ[R] M) (r : R) (c : M)
    (hfour : (4 : R) * r = 1)
    (hq4 : ∀ x : M, q (q (q (q x))) = x)
    (_horder_four : ∃ x : M, q (q x) ≠ x)
    (hnorm : c + q c + q (q c) + q (q (q c)) = 0) :
    q (r • (q c + 2 • q (q c) + 3 • q (q (q c)))) -
        r • (q c + 2 • q (q c) + 3 • q (q (q c))) = c := by
  let k : M := r • (q c + 2 • q (q c) + 3 • q (q (q c)))
  have hqk : q k = r • (q (q c) + 2 • q (q (q c)) + 3 • c) := by
    dsimp [k]
    simp only [map_smul, map_add, map_nsmul]
    rw [hq4 c]
  have hsum0 : q c + q (q c) + q (q (q c)) + c = 0 := by
    calc
      q c + q (q c) + q (q (q c)) + c =
          c + q c + q (q c) + q (q (q c)) := by abel
      _ = 0 := hnorm
  have hsum : q c + q (q c) + q (q (q c)) = -c :=
    (add_eq_zero_iff_eq_neg).mp hsum0
  rw [show r • (q c + 2 • q (q c) + 3 • q (q (q c))) = k by rfl]
  rw [hqk]
  dsimp [k]
  rw [← smul_sub]
  rw [show q (q c) + 2 • q (q (q c)) + 3 • c -
      (q c + 2 • q (q c) + 3 • q (q (q c))) =
      3 • c - (q c + q (q c) + q (q (q c))) by
    abel]
  rw [hsum, sub_neg_eq_add]
  calc
    r • (3 • c + c) = r • ((4 : R) • c) := by
      congr 1
      rw [← Nat.cast_smul_eq_nsmul R 3 c]
      calc
        (3 : R) • c + c = (3 : R) • c + (1 : R) • c := by simp
        _ = ((3 : R) + 1) • c := by rw [add_smul]
        _ = (4 : R) • c := by norm_num
    _ = (r * (4 : R)) • c := by rw [smul_smul]
    _ = (4 * r) • c := by congr 1 <;> noncomm_ring
    _ = c := by rw [hfour, one_smul]

end MathlibPlus.Algebra.Claim51152
