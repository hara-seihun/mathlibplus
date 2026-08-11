import Mathlib

namespace MathlibPlus
namespace Combinatorics

/-- The fourteen displayed unordered-orbital sizes sum to all unordered pairs
of a 300-element set. -/
theorem fourteen_unordered_orbital_sizes_claim31152 :
    let sizes : List ℕ :=
      [300, 300, 1800, 1800, 2250, 3000, 3600, 3600,
       3600, 3600, 4500, 4500, 6000, 6000]
    sizes.sum = 44850 ∧ Nat.choose 300 2 = 44850 := by
  dsimp
  constructor
  · norm_num
  · rw [Nat.choose_two_right]

end Combinatorics
end MathlibPlus
