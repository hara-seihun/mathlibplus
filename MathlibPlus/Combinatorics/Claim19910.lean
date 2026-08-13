import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics.Claim19910

/-- Renumber the vertices of an unordered edge by a permutation. -/
def permutedEdge {V : Type*} [DecidableEq V]
    (e : Equiv.Perm V) (s : Finset V) : Finset V := s.image e

/-- Renumber every edge in a finite graph represented by its edge set. -/
def permutedGraph {V : Type*} [DecidableEq V]
    (e : Equiv.Perm V) (G : Finset (Finset V)) : Finset (Finset V) :=
  G.image (permutedEdge e)

theorem permutedEdge_injective {V : Type*} [DecidableEq V]
    (e : Equiv.Perm V) : Function.Injective (permutedEdge e) := by
  intro s t h
  apply Finset.ext
  intro x
  constructor
  · intro hx
    have : e x ∈ permutedEdge e s := by
      simp [permutedEdge, hx]
    rw [h] at this
    simpa [permutedEdge] using this
  · intro hx
    have : e x ∈ permutedEdge e t := by
      simp [permutedEdge, hx]
    rw [← h] at this
    simpa [permutedEdge] using this

theorem permutedEdge_card {V : Type*} [DecidableEq V]
    (e : Equiv.Perm V) (s : Finset V) :
    (permutedEdge e s).card = s.card := by
  rw [permutedEdge, Finset.card_image_iff]
  exact e.injective.injOn

theorem permutedEdge_one {V : Type*} [DecidableEq V]
    (s : Finset V) : permutedEdge (1 : Equiv.Perm V) s = s := by
  simp [permutedEdge]

theorem permutedEdge_mul {V : Type*} [DecidableEq V]
    (e₁ e₂ : Equiv.Perm V) (s : Finset V) :
    permutedEdge (e₁ * e₂) s = permutedEdge e₁ (permutedEdge e₂ s) := by
  ext x
  simp [permutedEdge]

theorem permutedGraph_one {V : Type*} [DecidableEq V]
    (G : Finset (Finset V)) : permutedGraph (1 : Equiv.Perm V) G = G := by
  ext s
  constructor
  · intro hs
    simp only [permutedGraph, Finset.mem_image] at hs
    rcases hs with ⟨t, ht, hts⟩
    have hts' : t = s := by simpa [permutedEdge] using hts
    rw [← hts']
    exact ht
  · intro hs
    apply Finset.mem_image.mpr
    exact ⟨s, hs, by simp [permutedEdge]⟩

theorem permutedGraph_mul {V : Type*} [DecidableEq V]
    (e₁ e₂ : Equiv.Perm V) (G : Finset (Finset V)) :
    permutedGraph (e₁ * e₂) G = permutedGraph e₁ (permutedGraph e₂ G) := by
  rw [permutedGraph, permutedGraph, permutedGraph, Finset.image_image]
  apply Finset.image_congr
  intro s hs
  simpa [Function.comp_def] using permutedEdge_mul e₁ e₂ s

theorem permutedGraph_card {V : Type*} [DecidableEq V]
    (e : Equiv.Perm V) (G : Finset (Finset V)) :
    (permutedGraph e G).card = G.card := by
  classical
  rw [permutedGraph, Finset.card_image_iff]
  exact (permutedEdge_injective e).injOn

end MathlibPlus.Combinatorics.Claim19910
