import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- Claim 12090: the fixed-root orbit-neighbourhood equation. -/
def claim12090 : Prop :=
  ∀ (G : SimpleGraph (Fin 43)) (v : Fin 43) (σ : Equiv.Perm (Fin 43))
    (p k f a b : ℕ),
    Nat.Prime p →
    σ ^ p = 1 →
    σ ≠ 1 →
    (∀ x y : Fin 43, G.Adj (σ x) (σ y) ↔ G.Adj x y) →
    σ v = v →
    Nat.card {x : Fin 43 // G.Adj v x} = 18 →
    Nat.card {x : Fin 43 // σ x = x} = f →
    Nat.card {x : Fin 43 // σ x ≠ x} = p * k →
    Nat.card {x : Fin 43 // G.Adj v x ∧ σ x ≠ x} = p * a →
    Nat.card {x : Fin 43 // G.Adj v x ∧ σ x = x ∧ x ≠ v} = b →
    let U := {x : Fin 43 // x ≠ v ∧ ¬ G.Adj v x}
    Nat.card U = 24 ∧
    p * a + b = 18 ∧
    ∃ ρ : Equiv.Perm U,
      (∀ x : U, (ρ x).1 = σ x.1) ∧
      Nat.Prime p ∧
      ρ ^ p = 1 ∧
      Nat.card {x : U // ρ x = x} = f - 1 - b ∧
      Nat.card {x : U // ρ x ≠ x} = p * (k - a)

end MathlibPlus.Open.ResearchFormalization
