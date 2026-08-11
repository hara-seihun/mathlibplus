import Mathlib

namespace MathlibPlus
namespace GraphTheory

/-- Euler's equation and the face-degree accounting imply the exact
triangle-free plane-graph edge identity from claim 34444. -/
theorem triangle_free_plane_graph_identity_claim34444
    (n m c f b E : ℚ)
    (hEuler : n - m + f = 1 + c)
    (hFaces : 2 * m = b + 4 * (f - 1) + E) :
    m = 2 * n - 2 * c - (b + E) / 2 := by
  linarith

end GraphTheory
end MathlibPlus
