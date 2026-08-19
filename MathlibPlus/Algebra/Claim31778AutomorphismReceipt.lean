import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim31778

/-- RECEIPT for the arithmetic identity displayed in Claims 31778 and 41542.
The source-specific graph rows and the carrier `Aut(X)` are not specified in
those claim packets and are intentionally not reconstructed here. -/
theorem aut_order_numeric_identity :
    Nat.factorial 7 ^ 8 = 416336312719673760153600000000 := by
  norm_num [Nat.factorial]

end MathlibPlus.Algebra.Claim31778
