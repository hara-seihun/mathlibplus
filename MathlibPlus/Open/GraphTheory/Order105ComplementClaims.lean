import Mathlib

namespace MathlibPlus.Open.GraphTheory.Order105

/-- The fixed order-105 coordinate carrier `C₃₅ ⋊₁₆ C₃`, with the
fiber coordinate written first and the quotient coordinate second. -/
abbrev G105 := ZMod 3 × ZMod 35

def g105One : G105 := (0, 0)

def g105Action16 (i : ZMod 3) : ZMod 35 :=
  (16 : ZMod 35) ^ i.val

def g105Mul (x y : G105) : G105 :=
  (x.1 + y.1, x.2 + g105Action16 x.1 * y.2)

def g105Inv (x : G105) : G105 :=
  (-x.1, (g105Action16 x.1)⁻¹ * (-x.2))

/-- Multiplication-preserving bijections of the displayed fixed group model. -/
def g105Automorphism (α : G105 ≃ G105) : Prop :=
  α g105One = g105One ∧
    ∀ x y : G105, α (g105Mul x y) = g105Mul (α x) (α y)

def g105Signed (ε : ZMod 3) : Prop :=
  ε = 1 ∨ ε = -1

/-- A normalized blockwise chart in the fixed `C₃₅ ⋊₁₆ C₃` coordinates. -/
def g105NormalizedChart (f : G105 ≃ G105)
    (ε τ : ZMod 35 → ZMod 3) : Prop :=
  f g105One = g105One ∧
    (∀ n : ZMod 35, g105Signed (ε n)) ∧
    τ 0 = 0 ∧
    ∀ i : ZMod 3, ∀ n : ZMod 35,
      f (i, n) = (ε n * i + τ n, n)

def g105Derivative (f : G105 ≃ G105) (g c : G105) : G105 :=
  g105Mul (f (g105Mul c g)) (g105Inv (f g))

def g105NormalizedDerivative (f : G105 ≃ G105) (g : G105) : G105 → G105 :=
  fun c => f.symm (g105Derivative f g c)

def g105DerivativeInvariant (f : G105 ≃ G105) (S : Set G105) : Prop :=
  ∀ g : G105,
    Set.image (g105NormalizedDerivative f g) S = S

def g105InverseClosedFree (S : Set G105) : Prop :=
  S ⊆ {x : G105 | x ≠ g105One} ∧
    ∀ ⦃x : G105⦄, x ∈ S → g105Inv x ∈ S

/-- Claim 37521: every normalized chart in the equal-quotient branch has an
automorphism shadow on every inverse-closed derivative-invariant connection
set. -/
def claim37521_equalQuotientComplementLiftAutomorphismShadow : Prop :=
  ∀ (f : G105 ≃ G105) (ε τ : ZMod 35 → ZMod 3),
    g105NormalizedChart f ε τ →
      ∀ S : Set G105,
        g105InverseClosedFree S →
          g105DerivativeInvariant f S →
            ∃ α : G105 ≃ G105,
              g105Automorphism α ∧ Set.image f S = Set.image α S

/-- The image of one displayed three-point block under a permutation. -/
def g105MapsBlock (p : Equiv.Perm G105)
    (B C : Finset G105) : Prop :=
  ∀ x : G105, x ∈ C ↔ ∃ y : G105, y ∈ B ∧ p y = x

def g105CommonThirtyFiveBlocks (blocks : Finset (Finset G105)) : Prop :=
  blocks.card = 35 ∧
    (∀ B ∈ blocks, B.card = 3 ∧ B.Nonempty) ∧
    (∀ B ∈ blocks, ∀ C ∈ blocks, B ≠ C →
      ∀ x : G105, x ∈ B → x ∉ C) ∧
    (∀ x : G105, ∃ B ∈ blocks, x ∈ B)

def g105PreservesBlocks (R : Subgroup (Equiv.Perm G105))
    (blocks : Finset (Finset G105)) : Prop :=
  ∀ r : R, ∀ B ∈ blocks,
    ∃ C ∈ blocks, g105MapsBlock (r : Equiv.Perm G105) B C

/-- Equality of the literal permutations induced on the thirty-five named
blocks.  The matching element is chosen once per group element, not once per
source block. -/
def g105SameLiteralBlockAction
    (R T : Subgroup (Equiv.Perm G105))
    (blocks : Finset (Finset G105)) : Prop :=
  (∀ r : R, ∃ t : T,
    ∀ B C : Finset G105, B ∈ blocks → C ∈ blocks →
      (g105MapsBlock (r : Equiv.Perm G105) B C ↔
        g105MapsBlock (t : Equiv.Perm G105) B C)) ∧
  (∀ t : T, ∃ r : R,
    ∀ B C : Finset G105, B ∈ blocks → C ∈ blocks →
      (g105MapsBlock (t : Equiv.Perm G105) B C ↔
        g105MapsBlock (r : Equiv.Perm G105) B C))

/-- A permutation subgroup is a regular copy of the displayed order-105
model when its marked bijection preserves the displayed multiplication. -/
def g105RegularCopy (R : Subgroup (Equiv.Perm G105)) : Prop :=
  ∃ e : G105 ≃ R,
    e g105One = 1 ∧
      (∀ x y : G105, e (g105Mul x y) = e x * e y) ∧
      (∀ x : G105, e (g105Inv x) = (e x)⁻¹) ∧
      ∀ x y : G105, ∃! r : R, (r : Equiv.Perm G105) x = y

def g105CayleyAdjacency (S : Set G105) (x y : G105) : Prop :=
  x ≠ y ∧ g105Mul y (g105Inv x) ∈ S

def g105GraphAutomorphism (S : Set G105) (p : Equiv.Perm G105) : Prop :=
  ∀ x y : G105,
    g105CayleyAdjacency S x y ↔
      g105CayleyAdjacency S (p x) (p y)

def g105ContainsCayleyGraph (S : Set G105)
    (R : Subgroup (Equiv.Perm G105)) : Prop :=
  ∀ r : R, g105GraphAutomorphism S (r : Equiv.Perm G105)

def g105ConjugatesInGraph (S : Set G105)
    (R T : Subgroup (Equiv.Perm G105)) : Prop :=
  ∃ p : Equiv.Perm G105,
    g105GraphAutomorphism S p ∧
      ∀ h : Equiv.Perm G105,
        h ∈ T ↔ ∃ r : R, h = p * (r : Equiv.Perm G105) * p⁻¹

/-- Claim 37522: two regular order-105 copies with the same literal
thirty-five-block quotient action are conjugate in every containing
inverse-closed Cayley graph. -/
def claim37522_regularCopyConjugacyInEveryContainingUndirectedCayleyGraph : Prop :=
  ∀ (R T : Subgroup (Equiv.Perm G105))
    (blocks : Finset (Finset G105)) (S : Set G105),
    g105RegularCopy R →
      g105RegularCopy T →
      g105CommonThirtyFiveBlocks blocks →
      g105PreservesBlocks R blocks →
      g105PreservesBlocks T blocks →
      g105SameLiteralBlockAction R T blocks →
      g105InverseClosedFree S →
      g105ContainsCayleyGraph S R →
      g105ContainsCayleyGraph S T →
      g105ConjugatesInGraph S R T

end MathlibPlus.Open.GraphTheory.Order105
