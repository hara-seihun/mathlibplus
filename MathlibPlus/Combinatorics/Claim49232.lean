import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Abel

open scoped BigOperators

namespace MathlibPlus.Combinatorics

/--
Claim 49232: once an edge cut has the two component distance laws, the
coefficient-one depth-potential difference follows by finite-sum algebra.
The graph-specific facts that removing the edge produces the partition and
that distances change by one are explicit hypotheses; the arbitrary labeling
`a` records the termwise form of the identity.
-/
theorem depthPotentialEdgeDifference_claim49232
    {V A : Type*} [Fintype V] [DecidableEq V] [AddCommGroup A]
    (dist : V → V → ℕ) (a : V → A) (r s : V)
    (Qr Qs : Finset V)
    (hpart : Qr ∪ Qs = Finset.univ)
    (hdisj : Disjoint Qr Qs)
    (hleft : ∀ v ∈ Qr, dist s v = dist r v + 1)
    (hright : ∀ v ∈ Qs, dist r v = dist s v + 1) :
    (∑ v : V, (dist s v) • a v) - (∑ v : V, (dist r v) • a v) =
      (∑ v ∈ Qr, a v) - (∑ v ∈ Qs, a v) := by
  have hsum_s :
      (∑ v : V, (dist s v) • a v) =
        (∑ v ∈ Qr, (dist s v) • a v) +
          (∑ v ∈ Qs, (dist s v) • a v) := by
    rw [← hpart, Finset.sum_union hdisj]
  have hsum_r :
      (∑ v : V, (dist r v) • a v) =
        (∑ v ∈ Qr, (dist r v) • a v) +
          (∑ v ∈ Qs, (dist r v) • a v) := by
    rw [← hpart, Finset.sum_union hdisj]
  have hQr :
      (∑ v ∈ Qr, (dist s v) • a v) =
        (∑ v ∈ Qr, (dist r v) • a v) + (∑ v ∈ Qr, a v) := by
    calc
      (∑ v ∈ Qr, (dist s v) • a v) =
          ∑ v ∈ Qr, (dist r v + 1) • a v := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [hleft v hv]
      _ = (∑ v ∈ Qr, (dist r v) • a v) + (∑ v ∈ Qr, a v) := by
        simp [add_nsmul, Finset.sum_add_distrib, one_nsmul]
  have hQs :
      (∑ v ∈ Qs, (dist r v) • a v) =
        (∑ v ∈ Qs, (dist s v) • a v) + (∑ v ∈ Qs, a v) := by
    calc
      (∑ v ∈ Qs, (dist r v) • a v) =
          ∑ v ∈ Qs, (dist s v + 1) • a v := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [hright v hv]
      _ = (∑ v ∈ Qs, (dist s v) • a v) + (∑ v ∈ Qs, a v) := by
        simp [add_nsmul, Finset.sum_add_distrib, one_nsmul]
  rw [hsum_s, hsum_r, hQr, hQs]
  abel

end MathlibPlus.Combinatorics
