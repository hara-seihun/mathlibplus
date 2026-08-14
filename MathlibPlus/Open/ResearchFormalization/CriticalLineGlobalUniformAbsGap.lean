import Mathlib

namespace MathlibPlus.Open

/--
A bounded coercive invariant quadratic form on all local two-dimensional blocks
forces a uniform strict bound on the block parameters.
-/
def criticalLineGlobalUniformAbsGap : Prop :=
  let C : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun c => !![0, -1; 1, -2 * c]
  ∀ (I : Type) (_hI : Nonempty I) (c : I → ℝ)
    (V : Type) (T : V → V)
    (e : I → EuclideanSpace ℝ (Fin 2) → V) (Q : V → ℝ)
    (G : I → Matrix (Fin 2) (Fin 2) ℝ) (m M : ℝ),
    m > 0 →
    (∀ i, Matrix.IsSymm (G i)) →
    (∀ i (x : EuclideanSpace ℝ (Fin 2)),
      T (e i x) =
        e i (WithLp.toLp (p := (2 : ENNReal))
          ((C (c i)).mulVec x.ofLp))) →
    (∀ v, Q (T v) = Q v) →
    (∀ i (x : EuclideanSpace ℝ (Fin 2)),
      Q (e i x) = dotProduct x.ofLp ((G i).mulVec x.ofLp)) →
    (∀ i (x : EuclideanSpace ℝ (Fin 2)),
      m * ‖x‖ ^ 2 ≤ Q (e i x) ∧ Q (e i x) ≤ M * ‖x‖ ^ 2) →
    let ρ : ℝ := (M - m) / (M + m)
    0 ≤ ρ ∧ ρ < 1 ∧ ∀ i, |c i| ≤ ρ

end MathlibPlus.Open
