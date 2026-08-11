import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim13215

 theorem reciprocalTraceLift {K : Type*} [Field K] (x : K) (hx : x ≠ 0) :
    let Q : K → K := fun t => t ^ 3 - t + 1
    let P : K → K := fun y => y ^ 6 + 2 * y ^ 4 + y ^ 3 + 2 * y ^ 2 + 1
    P x = x ^ 3 * Q (x + x⁻¹) := by
  dsimp
  field_simp [hx]
  ring

end MathlibPlus.Algebra.Claim13215
