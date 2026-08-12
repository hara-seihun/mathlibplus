import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim20924

/--
The arithmetic consequence in claim 20924.  The source's equality-case
predicate is not defined in the admitted statement, so the displayed balance
and two fiber floors are retained as explicit hypotheses; no extra structural
meaning is assigned to them.
-/
theorem lowSectionBalanceAndTopFiberFloor_claim20924
    (N d a_i b_jk c : ℕ)
    (_hd : d = 1)
    (hbal : a_i = b_jk + c)
    (hpair : 3 ≤ b_jk)
    (htop : N - 2 ≤ c) :
    N + 1 ≤ a_i := by
  omega

end MathlibPlus.Algebra.Claim20924
