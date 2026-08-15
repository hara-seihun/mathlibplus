import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization

attribute [local instance] Classical.propDecidable Classical.decEq

section DihPrime

abbrev primeField (p : ℕ) := ZMod p

def dihedralSign (p : ℕ) := {a : primeField p // a = 1 ∨ a = -1}
abbrev dihedralH (p : ℕ) := dihedralSign p × (primeField p × primeField p)

def signOne (p : ℕ) : dihedralSign p :=
  ⟨1, Or.inl rfl⟩

def signMinusOne (p : ℕ) : dihedralSign p :=
  ⟨-1, Or.inr rfl⟩

def signProduct {p : ℕ} (a b : dihedralSign p) : dihedralSign p :=
  ⟨a.1 * b.1, by
    rcases a.2 with ha | ha <;> rcases b.2 with hb | hb <;>
      simp [ha, hb]⟩

def dihedralMul {p : ℕ} (g h : dihedralH p) : dihedralH p :=
  (signProduct g.1 h.1,
    (g.2.1 + g.1.1 * h.2.1,
      g.2.2 + g.1.1 * h.2.2))

def dihedralInv {p : ℕ} (g : dihedralH p) : dihedralH p :=
  (g.1,
    (-g.1.1 * g.2.1,
      -g.1.1 * g.2.2))

def dihedralIdentity (p : ℕ) : dihedralH p :=
  (signOne p, (0, 0))

def dihedralP (p : ℕ) (t : primeField p) : Set (dihedralH p) :=
  {g | ∃ z : primeField p,
    g = (signMinusOne p, (t + z ^ 2, 2 * z))}

def dihedralC (p : ℕ) (t : primeField p) : Set (dihedralH p) :=
  {g | ∃ z : primeField p,
    g = (signOne p, (z, t))}

def dihedralS (p : ℕ) : Set (dihedralH p) :=
  dihedralP p 0 ∪ dihedralP p 1 ∪ dihedralP p 3 ∪
    dihedralC p 1 ∪ dihedralC p (-1)

def dihedralTheta {p : ℕ} [Fact (Nat.Prime p)]
    (g : dihedralH p) : dihedralH p :=
  (g.1,
    (g.2.1 ^ 2 / (2 : primeField p) - g.2.2,
      g.1.1 * g.2.1))

def dihedralT (p : ℕ) [Fact (Nat.Prime p)] : Set (dihedralH p) :=
  {g | dihedralTheta g ∈ dihedralS p}

def dihedralInverseClosed (R : Set (dihedralH p)) : Prop :=
  ∀ ⦃g : dihedralH p⦄, g ∈ R → dihedralInv g ∈ R

def dihedralCayleyAdj (R : Set (dihedralH p))
    (x y : dihedralH p) : Prop :=
  dihedralMul x (dihedralInv y) ∈ R

def dihedralGraphIsoMap (R Q : Set (dihedralH p))
    (f : dihedralH p → dihedralH p) : Prop :=
  Function.Bijective f ∧
    ∀ x y,
      dihedralCayleyAdj R x y ↔ dihedralCayleyAdj Q (f x) (f y)

def dihedralAutomorphism (f : dihedralH p → dihedralH p) : Prop :=
  Function.Bijective f ∧
    ∀ x y, f (dihedralMul x y) = dihedralMul (f x) (f y)

def dihedralCI (R : Set (dihedralH p)) : Prop :=
  (R ⊆ (Set.univ : Set (dihedralH p)) \ {dihedralIdentity p}) ∧
    dihedralInverseClosed R ∧
    ∀ Q : Set (dihedralH p),
      Q ⊆ (Set.univ : Set (dihedralH p)) \ {dihedralIdentity p} →
      dihedralInverseClosed Q →
      ∀ e : dihedralH p → dihedralH p,
        dihedralGraphIsoMap R Q e →
          ∃ α : dihedralH p → dihedralH p,
            dihedralAutomorphism α ∧ α '' R = Q

/-- The explicit prime-field dihedral Cayley counterexample packet. -/
def claim59787 : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p), 7 ≤ p →
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    let P0 := dihedralP p 0
    let P1 := dihedralP p 1
    let P3 := dihedralP p 3
    let C1 := dihedralC p 1
    let Cminus1 := dihedralC p (-1)
    let S := P0 ∪ P1 ∪ P3 ∪ C1 ∪ Cminus1
    let T := dihedralT p
    (S ⊆ (Set.univ : Set (dihedralH p)) \ {dihedralIdentity p}) ∧
      T ⊆ (Set.univ : Set (dihedralH p)) \ {dihedralIdentity p} ∧
      S.ncard = 5 * p ∧ T.ncard = 5 * p ∧
      dihedralInverseClosed S ∧ dihedralInverseClosed T ∧
      dihedralGraphIsoMap T S dihedralTheta ∧
      (¬ ∃ α : dihedralH p → dihedralH p,
        dihedralAutomorphism α ∧ α '' T = S) ∧
      ¬ dihedralCI S

end DihPrime

end MathlibPlus.Open.ResearchFormalization

end
