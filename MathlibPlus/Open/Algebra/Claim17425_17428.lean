import Mathlib
import MathlibPlus.Algebra.Claim17423PathComplex

open scoped BigOperators
open MathlibPlus.Algebra.Claim17423

namespace MathlibPlus.Open.Algebra.Claim17425_17428

noncomputable section

/-- The prefix sum `S_k(E) = sum_{j <= k} e_j` on the ordered path. -/
def prefixSum {N : ℕ} (e : VertexChain ℝ N) (k : Fin (N + 1)) : ℝ :=
  ∑ j ∈ Finset.Iic k, e j

/-- The edge coefficients in the canonical filling formula. -/
def canonicalFilling {N : ℕ} (e : VertexChain ℝ N) : EdgeChain ℝ N :=
  fun j => -prefixSum e j.castSucc

/-- The finite edge `ell-infinity` norm. -/
def fillingInfinityNorm {N : ℕ} (H : EdgeChain ℝ N) : ℝ :=
  sSup {r : ℝ | ∃ j : Fin N, r = |H j|}

/-- Inserting vertices between the old ordered vertices, with zero event at
all inserted vertices. -/
def pathSubdivision {N M : ℕ}
    (ι : Fin (N + 1) → Fin (M + 1))
    (e : VertexChain ℝ N) (e' : VertexChain ℝ M) : Prop :=
  StrictMono ι ∧
    ι 0 = 0 ∧
    ι (Fin.last N) = Fin.last M ∧
    (∀ i : Fin (N + 1), e' (ι i) = e i) ∧
    (∀ v : Fin (M + 1), v ∉ Set.range ι → e' v = 0)

/-- Every zero-mass event chain has the unique path-boundary filling, and its
edge coefficients are the displayed signed prefix sums. -/
def claim17425 : Prop :=
  ∀ (N : ℕ) (e : VertexChain ℝ N),
    IsZeroMass e →
      (∃! H : EdgeChain ℝ N, pathBoundary H = e) ∧
        (∀ H : EdgeChain ℝ N,
          pathBoundary H = e →
            ∀ j : Fin N, H j = -prefixSum e j.castSucc)

/-- Inserting zero-event vertices into a finite path repeats the adjacent
prefix values and leaves the canonical filling's infinity norm unchanged. -/
def claim17428 : Prop :=
  ∀ (N M : ℕ)
    (e : VertexChain ℝ N) (e' : VertexChain ℝ M)
    (ι : Fin (N + 1) → Fin (M + 1)),
    IsZeroMass e →
      pathSubdivision ι e e' →
        fillingInfinityNorm (canonicalFilling e) =
          fillingInfinityNorm (canonicalFilling e')

end

end MathlibPlus.Open.Algebra.Claim17425_17428
