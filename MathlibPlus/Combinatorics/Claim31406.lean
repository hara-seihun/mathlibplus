import Mathlib.Algebra.Ring.Basic

namespace MathlibPlus.Combinatorics.Claim31406

/-- Exact retained one-well face count in claim 31406. -/
theorem exactDelaunayCount_claim31406
    (r a b c d n : ℕ)
    (hn : n = 3 * r ^ 2 + 3 * r + 1 + a + b + c + d) :
    6 * r ^ 2 = 2 * n - (6 * r + 2 + 2 * (a + b + c + d)) := by
  subst n
  omega

/-- The exact displayed deficit is at most `14 r + 2` when each tail length
is at most `r`.  This retains the arithmetic budget while leaving the
Delaunay geometry and strict-diameter construction as source interfaces. -/
theorem delaunayDeficitBound_claim31406
    (r a b c d n : ℕ)
    (hn : n = 3 * r ^ 2 + 3 * r + 1 + a + b + c + d)
    (ha : a ≤ r) (hb : b ≤ r) (hc : c ≤ r) (hd : d ≤ r) :
    2 * n - 6 * r ^ 2 ≤ 14 * r + 2 := by
  subst n
  omega

end MathlibPlus.Combinatorics.Claim31406
