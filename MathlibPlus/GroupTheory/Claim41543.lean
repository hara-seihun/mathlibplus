import Mathlib.Tactic

namespace MathlibPlus
namespace GroupTheory

/-- The exact factorial evaluation for the point-stabilizer order in claim
41543.  The packet-specific automorphism-group decomposition is not recreated;
this declaration records the displayed arithmetic consequence. -/
theorem exactPointStabilizerOrder_claim41543 :
    Nat.factorial 6 * Nat.factorial 6 * (Nat.factorial 7)^6 =
      8496659443258648166400000000 := by
  norm_num [Nat.factorial]

end GroupTheory
end MathlibPlus
