import Mathlib

namespace MathlibPlus.Combinatorics.QuadraticCurvature

/-- Claim 5178: the quadratic curvature identity in every field.

The extracted sentence does not define `χ`; in the source vocabulary it is the
curvature `χ = 2 - d`.  That convention is made explicit by the local binding
rather than being introduced as an unstated hypothesis. -/
theorem quadraticCurvatureIdentity (K : Type*) [Field K] (d : ℕ) :
    let χ : K := 2 - (d : K)
    (2 : K) * (Nat.choose d 2 : K) = χ ^ 2 - 3 * χ + 2 := by
  dsimp
  have hchoose : (2 : K) * (Nat.choose d 2 : K) =
      (d : K) * ((d : K) - 1) := by
    induction d with
    | zero => norm_num
    | succ d ih =>
      simp only [Nat.choose_succ_succ, Nat.choose_one_right,
        Nat.cast_add, Nat.cast_one]
      change (2 : K) * ((d : K) + (Nat.choose d 2 : K)) =
        ((d : K) + 1) * ((d : K) + 1 - 1)
      rw [mul_add, ih]
      ring
  rw [hchoose]
  ring

end MathlibPlus.Combinatorics.QuadraticCurvature
namespace MathlibPlus.Combinatorics.Claim43806

private lemma card_lower_corners (n : ℕ) (i : Fin n) :
    Fintype.card {s : Finset (Fin n) // i ∉ s} = 2 ^ (n - 1) := by
  classical
  rw [Fintype.card_subtype]
  change (Finset.univ.filter (fun s : Finset (Fin n) => i ∉ s)).card = _
  have hfilter : (Finset.univ.filter (fun s : Finset (Fin n) => i ∉ s)) =
      (Finset.univ.erase i).powerset := by
    ext s
    simp [Finset.subset_iff]
  rw [hfilter, Finset.card_powerset]
  simp

private lemma card_two_coordinate_sets (n : ℕ) :
    Fintype.card {s : Finset (Fin n) // s.card = 2} = Nat.choose n 2 := by
  classical
  rw [Fintype.card_subtype]
  change (Finset.univ.filter (fun s : Finset (Fin n) => s.card = 2)).card = _
  have hfilter : (Finset.univ.filter (fun s : Finset (Fin n) => s.card = 2)) =
      (Finset.univ).powersetCard 2 := by
    ext s
    simp
  rw [hfilter, Finset.card_powersetCard]
  simp

private lemma card_disjoint_lower_corners (n : ℕ) (p : Finset (Fin n)) :
    Fintype.card {s : Finset (Fin n) // Disjoint s p} = 2 ^ (n - p.card) := by
  classical
  rw [Fintype.card_subtype]
  change (Finset.univ.filter (fun s : Finset (Fin n) => Disjoint s p)).card = _
  have hfilter : (Finset.univ.filter (fun s : Finset (Fin n) => Disjoint s p)) =
      (Finset.univ \ p).powerset := by
    ext s
    simp [Finset.disjoint_left, Finset.subset_iff]
  rw [hfilter, Finset.card_powerset]
  rw [Finset.card_sdiff]
  simp

/-- The edge and coordinate-square counts in the `n`-dimensional Boolean cube.
The lower corner of an edge omits its varying coordinate; the lower corner of a
coordinate square is disjoint from its two-element coordinate set. -/
theorem hypercube_edge_face_counts_claim43806 (n : ℕ) (hn : 2 ≤ n) :
    let Edge := Σ i : Fin n, {s : Finset (Fin n) // i ∉ s}
    let Face := Σ p : {s : Finset (Fin n) // s.card = 2},
      {s : Finset (Fin n) // Disjoint s p}
    Fintype.card Edge = n * 2 ^ (n - 1) ∧
      Fintype.card Face = Nat.choose n 2 * 2 ^ (n - 2) := by
  dsimp
  constructor
  · rw [Fintype.card_sigma]
    simp_rw [card_lower_corners]
    simp [Finset.sum_const]
  · rw [Fintype.card_sigma]
    simp_rw [card_disjoint_lower_corners]
    have hcard (p : {s : Finset (Fin n) // s.card = 2}) :
        n - p.1.card = n - 2 := by omega
    simp_rw [hcard]
    simp [Finset.sum_const, card_two_coordinate_sets]

end MathlibPlus.Combinatorics.Claim43806
