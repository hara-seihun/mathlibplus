import Mathlib

namespace MathlibPlus.Open

/-- Claim 59527: independent non-full directions admit a correction, even a linear one. -/
def claim59527 : Prop :=
  ∀ (F H D : Type*)
    [Field F]
    [AddCommGroup H] [AddCommGroup D]
    [Module F H] [Module F D],
    ∀ (K : H → Submodule F D) (G : H → D),
      let Q : Set H := {h | K h ≠ ⊤}
      LinearIndependent F (fun h : Q => (h : H)) →
        (∃ c : H → D,
          ∀ x h : H, c (x + h) - c x - G h ∈ K h) ∧
        (∃ c : H →ₗ[F] D,
          ∀ x h : H, c (x + h) - c x - G h ∈ K h)

/-- Claim 59531: a nested rankwise nonempty PSD-pencil family may have no strict interior. -/
def claim59531 : Prop :=
  let K : ℕ → ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
    fun _ τ => Matrix.diagonal (fun i : Fin 2 => if i = 0 then τ - 1 else 1 - τ)
  let C : ℕ → Set ℝ := fun n => {τ | Matrix.PosSemidef (K n τ)}
  let L : ℕ → ℝ := fun _ => 1
  let U : ℕ → ℝ := fun _ => 1
  (∀ n : ℕ,
      ∃ A B : Matrix (Fin 2) (Fin 2) ℝ,
        Matrix.IsSymm A ∧ Matrix.IsSymm B ∧
          ∀ τ : ℝ, K n τ = A + τ • B) ∧
    (∀ n : ℕ,
      C n = Set.Icc (L n) (U n) ∧
        Set.Icc (L n) (U n) = ({1} : Set ℝ)) ∧
    (∀ n : ℕ, Set.Nonempty (C n)) ∧
    (∀ m n : ℕ, C m ⊆ C n ∨ C n ⊆ C m) ∧
    (∀ τ : ℝ, (∀ n : ℕ, τ ∈ C n) ↔ τ = 1) ∧
    Filter.Tendsto L Filter.atTop (nhds (1 : ℝ)) ∧
    Filter.Tendsto U Filter.atTop (nhds (1 : ℝ)) ∧
    (∀ n : ℕ, ¬ (L n < 1 ∧ 1 < U n))

end MathlibPlus.Open
