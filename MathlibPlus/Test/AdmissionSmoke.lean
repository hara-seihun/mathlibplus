import Mathlib

/-! Admission pipeline smoke test: a real (trivial) theorem. -/

namespace MathlibPlus

theorem admission_smoke (n : ℕ) : n + 0 = n := Nat.add_zero n

end MathlibPlus
