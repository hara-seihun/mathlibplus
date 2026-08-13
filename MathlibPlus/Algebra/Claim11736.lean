import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim11736

/--
Claim 11736: the completed degree-two parameter and exponent dictionary.
The packet does not specify a scalar domain, so the parameters are represented
by real numbers here; the two exponent expressions and their identification
are retained explicitly.
-/
theorem heimBorelParameterDictionary_claim11736
    {u r s : ℝ}
    (hr : r = u + 6)
    (hEquate : s + 1 = 12 + 2 * u) :
    12 + 2 * u = 2 * r ∧ s = 2 * r - 1 := by
  constructor <;> linarith

end MathlibPlus.Algebra.Claim11736
