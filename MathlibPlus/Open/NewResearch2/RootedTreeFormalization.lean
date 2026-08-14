import Mathlib

noncomputable section

namespace MathlibPlus.Open.NewResearch2.RootedTrees

attribute [local instance] Classical.propDecidable Classical.decEq

private abbrev Graph (n : ℕ) := Fin n → Fin n → Bool

private def simple (G : Graph n) : Prop :=
  (∀ u v, G u v = G v u) ∧ ∀ u, G u u = false

private def degree (G : Graph n) (v : Fin n) : ℕ :=
  Fintype.card {u : Fin n // G v u = true}

private structure RootedGraph (n : ℕ) where
  graph : Graph n
  root : Fin n

private def rootedIso (G H : RootedGraph n) : Prop :=
  ∃ e : Fin n ≃ Fin n, e G.root = H.root ∧
    ∀ u v, G.graph u v = H.graph (e u) (e v)

private def pathStarJoin (m : ℕ) : Graph (2 * m) :=
  fun i j =>
    if i.1 < m ∧ j.1 < m then
      if i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 then true else false
    else if m ≤ i.1 ∧ m ≤ j.1 then
      if (i.1 = m ∧ j.1 ≠ m) ∨ (j.1 = m ∧ i.1 ≠ m) then true else false
    else if (i.1 = 0 ∧ j.1 = m) ∨ (j.1 = 0 ∧ i.1 = m) then true else false

private def endpointRoot (m : ℕ) (hm : 0 < m) : Fin (2 * m) :=
  ⟨0, by exact Nat.mul_pos (by norm_num) hm⟩
private def centerRoot (m : ℕ) (hm : 0 < m) : Fin (2 * m) :=
  ⟨m, by nlinarith⟩

private def pathRooted (m : ℕ) (hm : 0 < m) : RootedGraph (2 * m) :=
  ⟨pathStarJoin m, endpointRoot m hm⟩

private def starRooted (m : ℕ) (hm : 0 < m) : RootedGraph (2 * m) :=
  ⟨pathStarJoin m, centerRoot m hm⟩

/-- Joining the endpoint-rooted path and center-rooted star gives two rooted
presentations of the same unrooted tree, separated by their root degrees. -/
def claim33868 : Prop :=
  ∀ (m : ℕ) (hm : 4 ≤ m),
    let hm0 : 0 < m := by omega
    simple (pathStarJoin m) ∧
      degree (pathStarJoin m) (endpointRoot m hm0) = 2 ∧
      degree (pathStarJoin m) (centerRoot m hm0) = m ∧
      ¬ rootedIso (pathRooted m hm0) (starRooted m hm0)

end MathlibPlus.Open.NewResearch2.RootedTrees
