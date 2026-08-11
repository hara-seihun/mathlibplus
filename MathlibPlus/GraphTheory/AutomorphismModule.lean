import Mathlib

namespace MathlibPlus.GraphTheory

/-- A graph automorphism with one nontrivial moved orbit makes that orbit a
homogeneous module: every fixed vertex outside it sees all orbit vertices in
exactly the same way. -/
theorem homogeneousModule_of_single_moved_orbit
    {V : Type*} (G : SimpleGraph V) (σ : Equiv.Perm V) (x : V) (O : Set V)
    (hσ : ∀ u v : V, G.Adj (σ u) (σ v) ↔ G.Adj u v)
    (_hx : σ x ≠ x)
    (hO : ∀ y : V, y ∈ O ↔ ∃ n : ℕ, (σ : V → V)^[n] x = y)
    (hfixed : ∀ u : V, u ∉ O → σ u = u) :
    ∀ u : V, u ∉ O → ∀ y : V, y ∈ O → (G.Adj u y ↔ G.Adj u x) := by
  intro u hu y hy
  obtain ⟨n, rfl⟩ := (hO y).mp hy
  have huσ : σ u = u := hfixed u hu
  have hiter : ∀ n : ℕ, G.Adj u ((σ : V → V)^[n] x) ↔ G.Adj u x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        calc
          G.Adj u (σ ((σ : V → V)^[n] x)) ↔
              G.Adj (σ u) (σ ((σ : V → V)^[n] x)) := by rw [huσ]
          _ ↔ G.Adj u ((σ : V → V)^[n] x) := hσ u ((σ : V → V)^[n] x)
          _ ↔ G.Adj u x := ih
  exact hiter n

end MathlibPlus.GraphTheory
