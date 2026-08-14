import Mathlib

noncomputable section

namespace MathlibPlus.Open.NewResearch2.R0472


private def CompleteTuple {n k : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ f : Fin k → Fin n,
    Function.Injective f ∧
      ∀ i j, i ≠ j → G.Adj (f i) (f j)

private def IndependentTuple {n k : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ f : Fin k → Fin n,
    Function.Injective f ∧
      ∀ i j, i ≠ j → ¬G.Adj (f i) (f j)

private def Good55 (G : SimpleGraph (Fin 43)) : Prop :=
  ¬CompleteTuple (k := 5) G ∧ ¬IndependentTuple (k := 5) G

private def GraphAuto {n : ℕ} (G : SimpleGraph (Fin n))
    (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ u v, G.Adj (σ u) (σ v) ↔ G.Adj u v

private def FullPairDecomp (σ : Equiv.Perm (Fin 43)) (r : Fin 43)
    (reps : Fin 21 → Fin 43) : Prop :=
  (∀ i, reps i ≠ r ∧ reps i ≠ σ (reps i) ∧ σ (reps i) ≠ r) ∧
    (∀ i j, i ≠ j →
      reps i ≠ reps j ∧ reps i ≠ σ (reps j) ∧
        σ (reps i) ≠ reps j ∧ σ (reps i) ≠ σ (reps j)) ∧
    (∀ w : Fin 43, w = r ∨ ∃ i, w = reps i ∨ w = σ (reps i))

private def PairDecomp20 (σ : Equiv.Perm (Fin 43)) (r u v : Fin 43)
    (reps : Fin 20 → Fin 43) : Prop :=
  Function.Involutive σ ∧
    (∀ w, σ w = w ↔ w = r) ∧
    σ r = r ∧ σ u = v ∧ σ v = u ∧
    u ≠ v ∧ u ≠ r ∧ v ≠ r ∧
    (∀ i, reps i ≠ r ∧ reps i ≠ u ∧ reps i ≠ v ∧
      reps i ≠ σ (reps i) ∧ σ (reps i) ≠ r ∧
      σ (reps i) ≠ u ∧ σ (reps i) ≠ v) ∧
    (∀ i j, i ≠ j →
      reps i ≠ reps j ∧ reps i ≠ σ (reps j) ∧
        σ (reps i) ≠ reps j ∧ σ (reps i) ≠ σ (reps j)) ∧
    (∀ w : Fin 43,
      w = r ∨ w = u ∨ w = v ∨
        ∃ i, w = reps i ∨ w = σ (reps i))

private def BalancedCount (G : SimpleGraph (Fin 43))
    (σ : Equiv.Perm (Fin 43)) (u : Fin 43) (reps : Fin 20 → Fin 43) : ℕ :=
  Nat.card {i : Fin 20 //
    (G.Adj u (reps i) ∧ ¬G.Adj u (σ (reps i))) ∨
      (¬G.Adj u (reps i) ∧ G.Adj u (σ (reps i)))}

private def CompleteCount (G : SimpleGraph (Fin 43))
    (σ : Equiv.Perm (Fin 43)) (u : Fin 43) (reps : Fin 20 → Fin 43) : ℕ :=
  Nat.card {i : Fin 20 //
    G.Adj u (reps i) ∧ G.Adj u (σ (reps i))}

/-- Claim 21821: the unique fixed root and the 21 transposition pairs. -/
def claim21821 : Prop :=
  ∀ (G : SimpleGraph (Fin 43)) (σ : Equiv.Perm (Fin 43)) (r : Fin 43),
    Function.Involutive σ →
    σ r = r →
    (∀ w, σ w = w ↔ w = r) →
    GraphAuto G σ →
      ∃ reps : Fin 21 → Fin 43,
        FullPairDecomp σ r reps ∧
          ∀ i, G.Adj r (reps i) ↔ G.Adj r (σ (reps i))

/-- Claim 21822: the two invariant edge-orbit bits and their block types. -/
def claim21822 : Prop :=
  ∀ (G : SimpleGraph (Fin 43)) (σ : Equiv.Perm (Fin 43))
      (u v a b : Fin 43),
    GraphAuto G σ →
    σ u = v → σ v = u → σ a = b → σ b = a →
    u ≠ v ∧ a ≠ b ∧ u ≠ a ∧ u ≠ b ∧ v ≠ a ∧ v ≠ b →
      ∃ e₀ e₁ : Bool,
        (G.Adj u a ↔ e₀ = true) ∧
        (G.Adj v b ↔ e₀ = true) ∧
        (G.Adj u b ↔ e₁ = true) ∧
        (G.Adj v a ↔ e₁ = true) ∧
        (((G.Adj u a ∧ ¬G.Adj u b) ∨
            (¬G.Adj u a ∧ G.Adj u b)) ↔
          ((e₀ = true ∧ e₁ = false) ∨
            (e₀ = false ∧ e₁ = true))) ∧
        ((G.Adj u a ∧ G.Adj u b) ↔
          (e₀ = true ∧ e₁ = true))

/-- Claim 21826: degree is the internal neighbor plus complete and balanced blocks. -/
def claim21826 : Prop :=
  ∀ (G : SimpleGraph (Fin 43)) (σ : Equiv.Perm (Fin 43))
      (r u v : Fin 43) (reps : Fin 20 → Fin 43) (F B : ℕ),
    GraphAuto G σ →
    PairDecomp20 σ r u v reps →
    G.Adj u v →
    ¬G.Adj r u →
    F = CompleteCount G σ u reps →
    B = BalancedCount G σ u reps →
      Nat.card {w : Fin 43 // G.Adj u w} = 1 + 2 * F + B

/-- Claim 21827: the degree interval forced by (5,5)-goodness. -/
def claim21827 : Prop :=
  ∀ (G : SimpleGraph (Fin 43)),
    Good55 G →
      ∀ v : Fin 43,
        18 ≤ Nat.card {w : Fin 43 // G.Adj v w} ∧
          Nat.card {w : Fin 43 // G.Adj v w} ≤ 24

/-- Claim 21828: a mismatched root/internal pair has five balanced blocks. -/
def claim21828 : Prop :=
  ∀ (G : SimpleGraph (Fin 43)) (σ : Equiv.Perm (Fin 43))
      (r u v : Fin 43) (reps : Fin 20 → Fin 43),
    Good55 G →
    GraphAuto G σ →
    PairDecomp20 σ r u v reps →
    G.Adj u v ≠ G.Adj r u →
      5 ≤ BalancedCount G σ u reps

/-- Claim 21830: in the matching case only the retained four-block condition is stated. -/
def claim21830 : Prop :=
  ∀ (G : SimpleGraph (Fin 43)) (σ : Equiv.Perm (Fin 43))
      (r u v : Fin 43) (reps : Fin 20 → Fin 43),
    Good55 G →
    GraphAuto G σ →
    PairDecomp20 σ r u v reps →
    G.Adj u v ↔ G.Adj r u →
      4 ≤ BalancedCount G σ u reps

end MathlibPlus.Open.NewResearch2.R0472
