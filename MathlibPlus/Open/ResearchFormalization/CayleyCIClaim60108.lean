import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

abbrev CayleyVector (p r : ℕ) := Fin r → ZMod p

def identityFree {G : Type*} [Zero G] (S : Set G) : Prop :=
  (0 : G) ∉ S

def inverseClosed {G : Type*} [Neg G] (S : Set G) : Prop :=
  ∀ x, x ∈ S → -x ∈ S

def nonzeroComplement {G : Type*} [Zero G] (S : Set G) : Set G :=
  Set.univ \ (S ∪ ({0} : Set G))

def cayleyAdj {G : Type*} [AddGroup G]
    (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ y - x ∈ S

def cayleyIsomorphic {G : Type*} [AddGroup G]
    (S T : Set G) : Prop :=
  ∃ e : G ≃ G, ∀ x y,
    cayleyAdj S x y ↔ cayleyAdj T (e x) (e y)

noncomputable def spanDimension (p r : ℕ) [Fact (Nat.Prime p)]
    (S : Set (CayleyVector p r)) : ℕ :=
  Module.finrank (ZMod p)
    (Submodule.span (ZMod p) S)

def mapsConnectionSet {p r : ℕ} [Fact (Nat.Prime p)]
    (e : CayleyVector p r ≃ₗ[ZMod p] CayleyVector p r)
    (S T : Set (CayleyVector p r)) : Prop :=
  ∀ x, x ∈ S ↔ e x ∈ T

def cayleyDefectConclusion {p r : ℕ} [Fact (Nat.Prime p)]
    (S T : Set (CayleyVector p r)) : Prop :=
  let Sstar := nonzeroComplement S
  let Tstar := nonzeroComplement T
  let d := spanDimension p r S
  let e := spanDimension p r Sstar
  spanDimension p r T = d ∧
    spanDimension p r Tstar = e ∧
    6 ≤ d ∧ 6 ≤ e ∧
    2 * d + 2 ≤ S.ncard ∧
    2 * e + 2 ≤ Sstar.ncard ∧
    (Submodule.span (ZMod p) S = ⊤ ∨
      Submodule.span (ZMod p) Sstar = ⊤) ∧
    14 ≤ S.ncard ∧
    S.ncard ≤ p ^ r - 15 ∧
    2 * r + 2 ≤ max S.ncard (p ^ r - 1 - S.ncard)

/--
Fourteen-point span/co-span obstruction for the elementary-abelian residual
range, including the stated swap and nonzero-complement invariances.
-/
def claim60108 : Prop :=
  ∀ (p r : ℕ), (hp : Nat.Prime p) → 5 ≤ p → 6 ≤ r → r ≤ 2 * p + 2 →
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    ∀ S T : Set (CayleyVector p r),
      identityFree S ∧ identityFree T ∧
      inverseClosed S ∧ inverseClosed T ∧
      cayleyIsomorphic S T ∧
      (¬ ∃ e : CayleyVector p r ≃ₗ[ZMod p] CayleyVector p r,
        mapsConnectionSet e S T) →
      cayleyDefectConclusion S T ∧
        cayleyDefectConclusion T S ∧
        cayleyDefectConclusion (nonzeroComplement S) (nonzeroComplement T)

end MathlibPlus.Open.ResearchFormalization
