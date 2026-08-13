import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim30453

/-- Under the stated range, the two norm-forced exponents are strictly ordered. -/
theorem norm_forcing_exponents_strict
    {a b d : ℕ} (ha : 1 ≤ a) (hd : 3 ≤ d) :
    (d - 1) ^ (2 * b) < (d - 1) ^ (a + 2 * b) := by
  have hbase : 1 < d - 1 := by omega
  apply Nat.pow_lt_pow_right hbase
  omega

/-- The norm equality forced by a common root is impossible in the stated
parameter range. -/
theorem norm_forcing_equality_impossible
    {a b d : ℕ} (ha : 1 ≤ a) (hd : 3 ≤ d)
    (h : (d - 1) ^ (2 * b) = (d - 1) ^ (a + 2 * b)) : False := by
  exact (ne_of_lt (norm_forcing_exponents_strict ha hd)) h

/-- Any source common-root predicate that forces the displayed norm equality
has no witness in the stated parameter range. -/
theorem no_common_root_of_norm_forcing
    {a b d : ℕ} (ha : 1 ≤ a) (hd : 3 ≤ d)
    (CommonRoot : Prop)
    (hforce : CommonRoot →
      (d - 1) ^ (2 * b) = (d - 1) ^ (a + 2 * b)) :
    ¬ CommonRoot := by
  intro hroot
  exact norm_forcing_equality_impossible ha hd (hforce hroot)

end MathlibPlus.Algebra.Claim30453
