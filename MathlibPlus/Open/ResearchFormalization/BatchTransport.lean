import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchTransport

/-- Undirected Cayley adjacency on an additive group, with loops excluded. -/
def cayleyAdj {G : Type*} [AddGroup G] (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ y - x ∈ S

def cayleyTransport {G : Type*} [AddGroup G]
    (S T : Set G) (f : G → G) : Prop :=
  Function.Bijective f ∧ ∀ x y, cayleyAdj S x y ↔ cayleyAdj T (f x) (f y)

def triangularTheta {K A B C : Type*} [Semiring K]
    [AddCommGroup A] [AddCommGroup B] [Module K B]
    [AddCommGroup C] [Module K C]
    (π : C →ₗ[K] B) (s : B → A) : A × C → A × C :=
  fun z => (z.1 + s (π z.2), z.2)

def linearShear {K A B C : Type*} [Semiring K]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    [AddCommGroup C] [Module K C]
    (π : C →ₗ[K] B) (L : B →ₗ[K] A) : A × C → A × C :=
  fun z => (z.1 + L (π z.2), z.2)

/-- Quotient-identity triangular transport in the exact dimension ranges of the
admitted statement. -/
def quotientIdentityTriangularTransport (p : ℕ) (hp : Nat.Prime p)
    (hp5 : 5 ≤ p) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ∀ (A B C : Type*)
    [AddCommGroup A] [Module (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B]
    [AddCommGroup C] [Module (ZMod p) C]
    [FiniteDimensional (ZMod p) A]
    [FiniteDimensional (ZMod p) B]
    [FiniteDimensional (ZMod p) C]
    (π : C →ₗ[ZMod p] B) (hπ : Function.Surjective π)
    (s : B → A) (hs : s 0 = 0),
    (Module.finrank (ZMod p) A ≤ 2 ∨
      Module.finrank (ZMod p) B ≤ 2 ∨
      (Module.finrank (ZMod p) A = 3 ∧ Module.finrank (ZMod p) B = 3)) →
    ∀ S : Set (A × C),
      0 ∉ S →
      cayleyTransport S
        (triangularTheta π s '' S) (triangularTheta π s) →
      ∃ L : B →ₗ[ZMod p] A,
        triangularTheta π s '' S = linearShear π L '' S

def inverseClosed (G : Type*) [AddGroup G] (S : Set G) : Prop :=
  ∀ x, x ∈ S ↔ -x ∈ S

def connectedInverseClosed (G : Type*) [AddCommGroup G]
    (S : Set G) : Prop :=
  inverseClosed G S ∧ 0 ∉ S ∧ AddSubgroup.closure S = ⊤

/-- The exact interval of elementary abelian ranks carrying ordinary
undirected CI counterexamples.  The lower bound is kept as the equivalent
integer inequality `2*p+7 ≤ 3*r`. -/
def uniformNonCIInterval : Prop :=
  ∀ (p : ℕ), (hp : Nat.Prime p) → 13 ≤ p →
    ∀ r : ℕ, 2 * p + 7 ≤ 3 * r → r ≤ 2 * p + 2 →
      letI : Fact p.Prime := ⟨hp⟩
      let G := Fin r → ZMod p
      ∃ S T : Set G,
        connectedInverseClosed G S ∧ connectedInverseClosed G T ∧
        (∃ f : G ≃ G,
          ∀ x y, cayleyAdj S x y ↔ cayleyAdj T (f x) (f y)) ∧
        ¬ (∃ f : G ≃+ G, ∀ x, x ∈ S ↔ f x ∈ T)

end MathlibPlus.Open.ResearchFormalization.BatchTransport
