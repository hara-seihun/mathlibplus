import Mathlib

namespace MathlibPlus.Open.GroupTheory

/-- Faithful registry node for the pointwise distinct-prime lift.  The packet's
pure-C₅ transporter predicate and the later Record-10 inflation are kept as
explicit interfaces; the declaration records the pointwise consequence for
all distinct odd-prime coordinates. -/
def pointwiseDistinctPrimeLift_claim37270 : Prop :=
  ∀ (ι : Type*) [Fintype ι] (p₅ : ι) (q : ι → ℕ)
    (g : (∀ p, Fin (q p)) → (∀ p, Fin (q p)))
    (pureC₅Translation :
      ((∀ p, Fin (q p)) → (∀ p, Fin (q p))) → Prop),
    q p₅ = 5 →
    pureC₅Translation g →
    ∀ (x : ∀ p, Fin (q p)) (p : ι),
      p ≠ p₅ → Nat.Prime (q p) → q p % 2 = 1 →
      g x p = x p

end MathlibPlus.Open.GroupTheory
