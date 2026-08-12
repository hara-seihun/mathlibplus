import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim15640

theorem exteriorSquareGeometricModes (u v b c : ℂ) :
    (u + v) * (b ^ 2 * u + c ^ 2 * v) - (b * u + c * v) ^ 2 =
      u * v * (b - c) ^ 2 := by
  ring

end MathlibPlus.Algebra.Claim15640
