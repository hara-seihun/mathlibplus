import Mathlib

namespace MathlibPlus.Combinatorics.UnionClosed

/-- If a family of size `m` loses `k` members and an element of frequency `f`
occurs in `d` of those deleted members, its updated slack has the displayed
integer form. -/
theorem deletionSlackIdentity (m f d k : ℤ) :
    (m - k) - 2 * (f - d) = (m - 2 * f) - k + 2 * d := by
  ring

end MathlibPlus.Combinatorics.UnionClosed
