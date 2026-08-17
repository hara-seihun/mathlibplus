import Mathlib

namespace MathlibPlus.Open.Research.Q12PrimeCover

abbrev Q12Carrier := ZMod 3 × ZMod 4
abbrev PrimeCoverCarrier (p : ℕ) := ZMod p × Q12Carrier

def q12Parity (i : ZMod 4) : ZMod 3 :=
  (-1 : ZMod 3) ^ i.val

def primeParity (p : ℕ) (i : ZMod 4) : ZMod p :=
  (-1 : ZMod p) ^ i.val

def q12One : Q12Carrier := (0, 0)

def q12Mul (h k : Q12Carrier) : Q12Carrier :=
  (h.1 + q12Parity h.2 * k.1, h.2 + k.2)

def q12Inv (h : Q12Carrier) : Q12Carrier :=
  (-q12Parity h.2 * h.1, -h.2)

def primeCoverOne (p : ℕ) : PrimeCoverCarrier p := (0, q12One)

def primeCoverMul (p : ℕ)
    (x y : PrimeCoverCarrier p) : PrimeCoverCarrier p :=
  (x.1 + primeParity p x.2.2 * y.1, q12Mul x.2 y.2)

def primeCoverInv (p : ℕ) (x : PrimeCoverCarrier p) : PrimeCoverCarrier p :=
  (-primeParity p x.2.2 * x.1, q12Inv x.2)

/-- The two cubic cycles in the layer-major coordinates of `Q₁₂`. -/
def q12Cycle3 (a b c : Q12Carrier) : Equiv.Perm Q12Carrier :=
  Equiv.swap a b * Equiv.swap b c

def q12Switch : Equiv.Perm Q12Carrier :=
  q12Cycle3 (1, 1) (1, 3) (2, 2) *
    q12Cycle3 (2, 1) (1, 2) (2, 3)

def q12SwitchInv : Equiv.Perm Q12Carrier := q12Switch.symm

def q12RelativeDerivative (σ σInv : Equiv.Perm Q12Carrier)
    (k h : Q12Carrier) : Q12Carrier :=
  σInv (q12Mul (q12Inv (σ k)) (σ (q12Mul k h)))

def q12DerivativeStep (σ σInv : Equiv.Perm Q12Carrier)
    (x y : Q12Carrier) : Prop :=
  y = q12Inv x ∨ x = q12Inv y ∨
    (∃ k, y = q12RelativeDerivative σ σInv k x) ∨
    (∃ k, x = q12RelativeDerivative σ σInv k y)

def q12DerivativeAtom (σ σInv : Equiv.Perm Q12Carrier)
    (x : Q12Carrier) : Set Q12Carrier :=
  {y | Relation.ReflTransGen (q12DerivativeStep σ σInv) x y}

def q12ProjectedDerivativeAtoms (σ σInv : Equiv.Perm Q12Carrier) :
    Set (Set Q12Carrier) :=
  {C | ∃ x, x ≠ q12One ∧ C = q12DerivativeAtom σ σInv x}

def q12AtomA : Set Q12Carrier :=
  {(0, 1), (0, 2), (0, 3)}

def q12AtomB : Set Q12Carrier :=
  (Set.univ : Set Q12Carrier) \ ({q12One} ∪ q12AtomA)

def q12Axis : Set Q12Carrier :=
  {h | h.1 = 0}

def q12Subgroup (K : Set Q12Carrier) : Prop :=
  q12One ∈ K ∧
    (∀ x y, x ∈ K → y ∈ K → q12Mul x y ∈ K) ∧
    (∀ x, x ∈ K → q12Inv x ∈ K)

def q12ContainsCompleteAtom (K : Set Q12Carrier) : Prop :=
  q12AtomA ⊆ K ∨ q12AtomB ⊆ K

def q12Chi (p : ℕ) (h : Q12Carrier) : ZMod p :=
  (-1 : ZMod p) ^ h.2.val

def q12ChiUnit (p : ℕ) (h : Q12Carrier) : (ZMod p)ˣ :=
  (-1 : (ZMod p)ˣ) ^ h.2.val

def q12ScalarA (p : ℕ) (lam : Q12Carrier → (ZMod p)ˣ)
    (σ : Equiv.Perm Q12Carrier) (k : Q12Carrier) : (ZMod p)ˣ :=
  lam k * q12ChiUnit p k / q12ChiUnit p (σ k)

def q12ScalarStabilizer (p : ℕ) (lam : Q12Carrier → (ZMod p)ˣ)
    (σ : Equiv.Perm Q12Carrier) : Set Q12Carrier :=
  {h | ∀ k, q12ScalarA p lam σ (q12Mul h k) = q12ScalarA p lam σ k}

def q12DerivativeCoefficient (p : ℕ) (lam : Q12Carrier → (ZMod p)ˣ)
    (σ : Equiv.Perm Q12Carrier) (h k : Q12Carrier) : ZMod p :=
  (lam (q12Mul h k) : ZMod p) * q12Chi p h -
    q12Chi p (σ (q12Mul h k)) * (q12Chi p (σ k))⁻¹ * (lam k : ZMod p)

def q12AtomTranslationSet (p : ℕ) (lam : Q12Carrier → (ZMod p)ˣ)
    (σ : Equiv.Perm Q12Carrier) (C : Set Q12Carrier) : Set (ZMod p) :=
  {v | ∃ h ∈ C, ∃ k y,
    v = q12DerivativeCoefficient p lam σ h k * y}

def q12AtomSaturated (p : ℕ) (lam : Q12Carrier → (ZMod p)ˣ)
    (σ : Equiv.Perm Q12Carrier) (C : Set Q12Carrier) : Prop :=
  q12AtomTranslationSet p lam σ C = Set.univ

def gpAffineLift (p : ℕ) (lam : Q12Carrier → (ZMod p)ˣ)
    (τ : Q12Carrier → ZMod p) (σ : Equiv.Perm Q12Carrier) :
    PrimeCoverCarrier p → PrimeCoverCarrier p :=
  fun z => ((lam z.2 : ZMod p) * z.1 + τ z.2, σ z.2)

def gpAffineLiftInv (p : ℕ) (lam : Q12Carrier → (ZMod p)ˣ)
    (τ : Q12Carrier → ZMod p) (σInv : Equiv.Perm Q12Carrier) :
    PrimeCoverCarrier p → PrimeCoverCarrier p :=
  fun z =>
    (((lam (σInv z.2) : ZMod p)⁻¹ * (z.1 - τ (σInv z.2))), σInv z.2)

def gpRelativeDerivative (p : ℕ) (lam : Q12Carrier → (ZMod p)ˣ)
    (τ : Q12Carrier → ZMod p) (σ σInv : Equiv.Perm Q12Carrier)
    (k z : PrimeCoverCarrier p) : PrimeCoverCarrier p :=
  gpAffineLiftInv p lam τ σInv
    (primeCoverMul p
      (primeCoverInv p (gpAffineLift p lam τ σ k))
      (gpAffineLift p lam τ σ (primeCoverMul p k z)))

def gpInverseClosed (p : ℕ) (S : Set (PrimeCoverCarrier p)) : Prop :=
  ∀ x, x ∈ S → primeCoverInv p x ∈ S

def gpDerivativeInvariant (p : ℕ) (lam : Q12Carrier → (ZMod p)ˣ)
    (τ : Q12Carrier → ZMod p) (σ σInv : Equiv.Perm Q12Carrier)
    (S : Set (PrimeCoverCarrier p)) : Prop :=
  ∀ k, Set.image (gpRelativeDerivative p lam τ σ σInv k) S = S

def gpAutomorphism (p : ℕ)
    (α : PrimeCoverCarrier p → PrimeCoverCarrier p) : Prop :=
  Function.Bijective α ∧
    α (primeCoverOne p) = primeCoverOne p ∧
    (∀ x y, α (primeCoverMul p x y) =
      primeCoverMul p (α x) (α y))

/-- Claim 31986: the normalized affine-lift harmlessness theorem for the
inverse switch on the explicit prime-cover chart. -/
def claim31986 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 3 < p →
    ∀ (lam : Q12Carrier → (ZMod p)ˣ) (τ : Q12Carrier → ZMod p),
      lam q12One = 1 → τ q12One = 0 →
      ∀ S : Set (PrimeCoverCarrier p),
        gpInverseClosed p S →
        gpDerivativeInvariant p lam τ q12SwitchInv q12Switch S →
        ∃ α : PrimeCoverCarrier p → PrimeCoverCarrier p,
          gpAutomorphism p α ∧
            Set.image α S =
              Set.image (gpAffineLift p lam τ q12SwitchInv) S

/-- Claim 31987: the inversion-closed projected derivative atoms are exactly
A and B. -/
def claim31987 : Prop :=
  q12ProjectedDerivativeAtoms q12Switch q12SwitchInv =
      {q12AtomA, q12AtomB} ∧
    q12AtomA ⊆ (Set.univ : Set Q12Carrier) \ {q12One} ∧
    q12AtomB ⊆ (Set.univ : Set Q12Carrier) \ {q12One}

/-- Claim 31988: complete derivative atoms occur in only the fixed C₄ axis
or all of Q₁₂, with the stated atom containment. -/
def claim31988 : Prop :=
  (∀ K : Set Q12Carrier, q12Subgroup K →
    (q12ContainsCompleteAtom K ↔
      K = q12Axis ∨ K = (Set.univ : Set Q12Carrier))) ∧
  q12AtomA ⊆ q12Axis ∧
  ¬ q12AtomB ⊆ q12Axis ∧
  q12AtomA ⊆ (Set.univ : Set Q12Carrier) ∧
  q12AtomB ⊆ (Set.univ : Set Q12Carrier)

/-- Claim 31989: the scalar stabilizer and prime-fibre saturation dichotomy. -/
def claim31989 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 3 < p →
    ∀ lam : Q12Carrier → (ZMod p)ˣ,
      let Q := q12ScalarStabilizer p lam q12Switch
      (∀ h, h ∉ Q →
          ∃ k, q12DerivativeCoefficient p lam q12Switch h k ≠ 0) ∧
      (∀ h, h ∉ Q →
        (h ∈ q12AtomA →
          q12AtomSaturated p lam q12Switch q12AtomA) ∧
        (h ∈ q12AtomB →
          q12AtomSaturated p lam q12Switch q12AtomB)) ∧
      (Q ≠ q12Axis → Q ≠ (Set.univ : Set Q12Carrier) →
        q12AtomSaturated p lam q12Switch q12AtomA ∧
        q12AtomSaturated p lam q12Switch q12AtomB)

end MathlibPlus.Open.Research.Q12PrimeCover
