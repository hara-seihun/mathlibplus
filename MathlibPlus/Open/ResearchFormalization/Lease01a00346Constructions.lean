import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Lease01a00346Constructions

/-- Adjacency in the cycle `C_j`, written on the standard finite carrier. -/
def cycleAdj (j : ℕ) (i l : Fin j) : Prop :=
  i ≠ l ∧ (((i.val + 1) % j = l.val) ∨ ((l.val + 1) % j = i.val))

/-- The redundant cycle graph with `n` vertices in each part. -/
def redundantlyConnectedCycleAdj (n j : ℕ)
    (p q : Fin j × Fin n) : Prop :=
  p.1 ≠ q.1 ∧ cycleAdj j p.1 q.1

/-- Claim 23924: `RCC_(n,j)` is the complete join of independent parts along
`C_j`. -/
def claim23924 (n j : ℕ)
    (G : (Fin j × Fin n) → (Fin j × Fin n) → Prop) : Prop :=
  G = redundantlyConnectedCycleAdj n j

/-- The fiber map with permutation `φ_h` on each copy of `K`. -/
def fiberMap {K H : Type*}
    (φ : H → Equiv.Perm K) (p : K × H) : K × H :=
  (φ p.2 p.1, p.2)

def inactiveFiberSupport {K H : Type*}
    (φ : H → Equiv.Perm K) : Set H :=
  {h | φ h = Equiv.refl K}

def activeFiberSupport {K H : Type*}
    (φ : H → Equiv.Perm K) : Set H :=
  {h | h ∉ inactiveFiberSupport φ}

/-- Claim 27489: inactive and active fiber supports for the permutation fibers. -/
def claim27489 {K H : Type*} [One H]
    (φ : H → Equiv.Perm K) : Prop :=
  φ 1 = Equiv.refl K ∧
    (∀ p : K × H, fiberMap φ p = (φ p.2 p.1, p.2)) ∧
    inactiveFiberSupport φ = {h | φ h = Equiv.refl K} ∧
    activeFiberSupport φ = (inactiveFiberSupport φ)ᶜ

end MathlibPlus.Open.ResearchFormalization.Lease01a00346Constructions
