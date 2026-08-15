import Mathlib

namespace ResearchFormalization

/-- The multiplication displayed in the admitted claim, on `ZMod 3 × M`. -/
def em3Mul {M : Type} [AddCommGroup M] (l : ℤ)
    (a b : ZMod 3 × M) : ZMod 3 × M :=
  (a.1 + b.1, a.2 + (l ^ ZMod.val a.1 : ℤ) • b.2)

/-- The three offsets appearing in the claimed affine normal form. -/
def em3LayerOffset {M : Type} [AddCommGroup M] (l : ℤ) (c : M) : ZMod 3 → M :=
  fun i => if ZMod.val i = 0 then 0 else
    if ZMod.val i = 1 then c else (1 + l : ℤ) • c

/-- The claimed affine permutation of `ZMod 3 × M`. -/
def em3Phi {M : Type} [AddCommGroup M] (l : ℤ) (L : M ≃+ M) (c : M) :
    Equiv.Perm (ZMod 3 × M) :=
  { toFun := fun p => (p.1, L p.2 + em3LayerOffset l c p.1)
    invFun := fun p => (p.1, L.symm (p.2 - em3LayerOffset l c p.1))
    left_inv := by
      rintro ⟨i, x⟩
      simp [em3LayerOffset]
    right_inv := by
      rintro ⟨i, x⟩
      simp [em3LayerOffset] }

/-- The inverse map of the displayed `E(M,3)` multiplication. -/
def em3Inv {M : Type} [AddCommGroup M] (l : ℤ)
    (p : ZMod 3 × M) : ZMod 3 × M :=
  (-p.1, -(l ^ ZMod.val (-p.1) : ℤ) • p.2)

/-- Preservation of the displayed multiplication by a permutation. -/
def em3PreservesMul {M : Type} [AddCommGroup M] (l : ℤ)
    (f : Equiv.Perm (ZMod 3 × M)) : Prop :=
  ∀ a b, f (em3Mul l a b) = em3Mul l (f a) (f b)

/-- The group of permutations preserving the displayed multiplication.  The main
statement below also records that this closure is exactly the automorphism set. -/
def em3AutomorphismGroup {M : Type} [AddCommGroup M] (l : ℤ) :
    Subgroup (Equiv.Perm (ZMod 3 × M)) :=
  Subgroup.closure {f : Equiv.Perm (ZMod 3 × M) | em3PreservesMul l f}

/-- The affine semidirect product `M ⋊ Aut(M)`, expressed using the
multiplicative synonym of the additive group. -/
abbrev em3AffineSemidirect (M : Type) [AddCommGroup M] :=
  SemidirectProduct (Multiplicative M) (MulAut (Multiplicative M))
    (MonoidHom.id (MulAut (Multiplicative M)))

/-- Convert an automorphism of the multiplicative synonym back to an additive
automorphism of `M`. -/
def em3AddAutOfMulAut {M : Type} [AddCommGroup M]
    (L : MulAut (Multiplicative M)) : M ≃+ M :=
  (AddEquiv.toMultiplicative (G := M) (H := M)).symm L

/-- The layer of a subset of the displayed carrier. -/
def em3Layer {M : Type} [AddCommGroup M]
    (S : Set (ZMod 3 × M)) (i : ZMod 3) : Set M :=
  {x | (i, x) ∈ S}

/-- The inverse-closed predicate, using the inverse supplied by the displayed
`E(M,3)` multiplication. -/
def em3InverseClosed {M : Type} [AddCommGroup M] (l : ℤ)
    (S : Set (ZMod 3 × M)) : Prop :=
  ∀ p, p ∈ S → em3Inv l p ∈ S

/-- Image of a layer under a linear automorphism. -/
def em3LinearImage {M : Type} [AddCommGroup M]
    (L : M ≃+ M) (A : Set M) : Set M :=
  {x | ∃ y, y ∈ A ∧ x = L y}

/-- Image of a layer under an affine map. -/
def em3AffineImage {M : Type} [AddCommGroup M]
    (L : M ≃+ M) (c : M) (A : Set M) : Set M :=
  {x | ∃ y, y ∈ A ∧ x = L y + c}

/-- The two layer equalities stated in the inverse-closedness criterion. -/
def em3InverseLayerCondition {M : Type} [AddCommGroup M] (l : ℤ)
    (S : Set (ZMod 3 × M)) : Prop :=
  (∀ x, x ∈ em3Layer S (0 : ZMod 3) ↔ -x ∈ em3Layer S (0 : ZMod 3)) ∧
  (∀ x, x ∈ em3Layer S (2 : ZMod 3) ↔
    ∃ y, y ∈ em3Layer S (1 : ZMod 3) ∧
      x = -(l ^ 2 : ℤ) • y)

end ResearchFormalization

namespace MathlibPlus.Open

/-- Complete automorphism-orbit normal form for fixed-point-free scalar
`E(M,3)`, including its inverse-closed subset orbit criterion. -/
def completeFixedPointFreeScalarEM3AutomorphismOrbitNormalForm : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Fintype M] [Nontrivial M]
    (e : ℕ) (l : ℤ),
    AddMonoid.exponent M = e →
    Int.ModEq (e : ℤ) (l ^ 3) 1 →
    Int.gcd (l * (l - 1)) (e : ℤ) = 1 →
    let G := ZMod 3 × M
    let A := ResearchFormalization.em3AutomorphismGroup l
    (∀ f : Equiv.Perm G,
        ResearchFormalization.em3PreservesMul l f ↔
          ∃! p : (M ≃+ M) × M,
            f = ResearchFormalization.em3Phi l p.1 p.2) ∧
    (∀ L : M ≃+ M, ∀ c : M,
      ResearchFormalization.em3PreservesMul l
        (ResearchFormalization.em3Phi l L c)) ∧
    (∀ f : Equiv.Perm G,
      f ∈ A ↔ ResearchFormalization.em3PreservesMul l f) ∧
    (∀ f : Equiv.Perm G,
      ResearchFormalization.em3PreservesMul l f →
        ∀ p : G, (f p).1 = p.1) ∧
    (Nat.card A = Nat.card M *
      Nat.card (MulAut (Multiplicative M))) ∧
    (∃ Ψ : ResearchFormalization.em3AffineSemidirect M →* A,
      Function.Bijective Ψ ∧
      ∀ p,
        ((Ψ p : A) : Equiv.Perm G) =
          ResearchFormalization.em3Phi l
            (ResearchFormalization.em3AddAutOfMulAut p.right)
            (Multiplicative.toAdd p.left)) ∧
    (∀ S : Set G,
      ResearchFormalization.em3InverseClosed l S ↔
        ResearchFormalization.em3InverseLayerCondition l S) ∧
    (∀ S T : Set G,
      ResearchFormalization.em3InverseClosed l S →
      ResearchFormalization.em3InverseClosed l T →
      ((∃ f : Equiv.Perm G,
          ResearchFormalization.em3PreservesMul l f ∧ Set.image f S = T) ↔
        ∃ L : M ≃+ M, ∃ c : M,
          ResearchFormalization.em3Layer T (0 : ZMod 3) =
            ResearchFormalization.em3LinearImage L
              (ResearchFormalization.em3Layer S (0 : ZMod 3)) ∧
          ResearchFormalization.em3Layer T (1 : ZMod 3) =
            ResearchFormalization.em3AffineImage L c
              (ResearchFormalization.em3Layer S (1 : ZMod 3)))) ∧
    (∀ S T : Set G,
      ResearchFormalization.em3InverseClosed l S →
      ResearchFormalization.em3InverseClosed l T →
      ∀ L : M ≃+ M, ∀ c : M,
        ResearchFormalization.em3Layer T (0 : ZMod 3) =
            ResearchFormalization.em3LinearImage L
              (ResearchFormalization.em3Layer S (0 : ZMod 3)) →
        ResearchFormalization.em3Layer T (1 : ZMod 3) =
            ResearchFormalization.em3AffineImage L c
              (ResearchFormalization.em3Layer S (1 : ZMod 3)) →
        ResearchFormalization.em3Layer T (2 : ZMod 3) =
            ResearchFormalization.em3AffineImage L ((1 + l : ℤ) • c)
              (ResearchFormalization.em3Layer S (2 : ZMod 3)))

end MathlibPlus.Open
