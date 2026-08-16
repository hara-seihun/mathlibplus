import Mathlib

open scoped BigOperators
open Filter
open Asymptotics

namespace MathlibPlus.Open.ResearchFormalization.GraphComponentLoadClaim15448

/--
Claim 15448.  A concrete family of disjoint regular straight arcs has total
length `S_L` and only `J_L = o(L * S_L)` components, while every component is
`o(S_L)` in length.  Thus a graph-load bound by itself does not supply a
macroscopic component; the components must be stitched together.
-/
def claim15448_lowTotalGraphLoadDoesNotForceMacroscopicComponent : Prop :=
  let Point := ℂ
  let endpoint : ∀ n : ℕ, Fin (n + 1) → Point × Point :=
    fun n k =>
      (((2 * (k : ℕ) : ℕ) : ℂ), ((2 * (k : ℕ) + 1 : ℕ) : ℂ))
  let component : ∀ n : ℕ, Fin (n + 1) → Set Point :=
    fun n k => segment ℝ (endpoint n k).1 (endpoint n k).2
  let graph : ℕ → Set Point :=
    fun n => ⋃ k : Fin (n + 1), component n k
  (Tendsto
      (fun n : ℕ =>
        (((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ))) atTop atTop) ∧
    IsLittleO atTop
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ))
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) ∧
    (∀ n : ℕ,
      ∑ k : Fin (n + 1),
        dist (endpoint n k).1 (endpoint n k).2 = ((n + 1 : ℕ) : ℝ)) ∧
    (∀ n : ℕ, ∀ k : Fin (n + 1),
      IsConnected (component n k) ∧
        (component n k).Nonempty ∧
        component n k ⊆ graph n ∧
        ∀ D : Set Point,
          IsConnected D →
            component n k ⊆ D → D ⊆ graph n → D ⊆ component n k) ∧
    (∀ n : ℕ, ∀ i k : Fin (n + 1),
      i ≠ k → Disjoint (component n i) (component n k)) ∧
    (∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        ∀ k : Fin (n + 1),
          dist (endpoint n k).1 (endpoint n k).2 <
            ε * ((n + 1 : ℕ) : ℝ)) ∧
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ k : Fin (n + 1),
          c * ((n + 1 : ℕ) : ℝ) ≤
            dist (endpoint n k).1 (endpoint n k).2

end MathlibPlus.Open.ResearchFormalization.GraphComponentLoadClaim15448
