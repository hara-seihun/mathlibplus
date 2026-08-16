import Mathlib

namespace MathlibPlus.Open

/-- The explicit pair carrier for the generalized dihedral extension E(C_m,k). -/
def eCarrier (m k : ℕ) := ZMod m × ZMod k

def eSign (m k : ℕ) [NeZero k] (i : ZMod k) : ZMod m :=
  if i.val % 2 = 0 then 1 else -1

def eMul (m k : ℕ) [NeZero k] (x y : eCarrier m k) : eCarrier m k :=
  (x.1 + eSign m k x.2 * y.1, x.2 + y.2)

def eInv (m k : ℕ) [NeZero k] (x : eCarrier m k) : eCarrier m k :=
  (-eSign m k x.2 * x.1, -x.2)

def eIdentity (m k : ℕ) : eCarrier m k := (0, 0)

def eIdentityFree (m k : ℕ) [NeZero k] (S : Set (eCarrier m k)) : Prop :=
  ∀ x, x ∈ S → x ≠ eIdentity m k

def eInverseClosed (m k : ℕ) [NeZero k] (S : Set (eCarrier m k)) : Prop :=
  ∀ x, x ∈ S → eInv m k x ∈ S

def eCayleyGraphIso (m k : ℕ) [NeZero k]
    (S T : Set (eCarrier m k)) : Prop :=
  ∃ f : eCarrier m k ≃ eCarrier m k,
    ∀ x y,
      (x ≠ y ∧ eMul m k (eInv m k x) y ∈ S) ↔
        (f x ≠ f y ∧ eMul m k (eInv m k (f x)) (f y) ∈ T)

def eAutomorphism (m k : ℕ) [NeZero k]
    (f : eCarrier m k ≃ eCarrier m k) : Prop :=
  ∀ x y, f (eMul m k x y) = eMul m k (f x) (f y)

def eTransports (f : α ≃ α) (S T : Set α) : Prop :=
  ∀ x, x ∈ S ↔ f x ∈ T

def eQuotient (m : ℕ) (x : eCarrier m 8) : eCarrier m 4 :=
  (x.1, (x.2.val : ZMod 4))

def ePullback (m : ℕ) (U : Set (eCarrier m 4)) : Set (eCarrier m 8) :=
  {x | eQuotient m x ∈ U}

/-- Central-pullback cancellation for E(C_m,8) and its E(C_m,4) quotient. -/
def centralPullbackCancellation : Prop :=
  ∀ (m : ℕ), 1 < m → Odd m →
    ∀ U V : Set (eCarrier m 4),
      eIdentityFree m 4 U → eInverseClosed m 4 U →
      eIdentityFree m 4 V → eInverseClosed m 4 V →
      let S := ePullback m U
      let T := ePullback m V
      (eCayleyGraphIso m 8 S T ↔ eCayleyGraphIso m 4 U V) ∧
        ((∃ α : eCarrier m 8 ≃ eCarrier m 8,
            eAutomorphism m 8 α ∧ eTransports α S T) ↔
          (∃ β : eCarrier m 4 ≃ eCarrier m 4,
            eAutomorphism m 4 β ∧ eTransports β U V))
    ∧
      (∀ U V : Set (eCarrier 35 4),
        eIdentityFree 35 4 U → eInverseClosed 35 4 U →
        eIdentityFree 35 4 V → eInverseClosed 35 4 V →
        Set.ncard U = Set.ncard V →
        (Set.ncard U ≤ 11 ∨
          (128 ≤ Set.ncard U ∧ Set.ncard U ≤ 139)) →
        eCayleyGraphIso 35 8 (ePullback 35 U) (ePullback 35 V) →
        ∃ α : eCarrier 35 8 ≃ eCarrier 35 8,
          eAutomorphism 35 8 α ∧
            eTransports α (ePullback 35 U) (ePullback 35 V))

/-- The explicit semidirect-product carrier V ⋊ C₃ used by E(V,3). -/
def vCarrier (V : Type*) := V × ZMod 3

def vScalar (p : ℕ) (omega : ZMod p) (i : ZMod 3) : ZMod p :=
  omega ^ i.val

def vMul {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (omega : ZMod p) (x y : vCarrier V) : vCarrier V :=
  (x.1 + vScalar p omega x.2 • y.1, x.2 + y.2)

def vInv {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (omega : ZMod p) (x : vCarrier V) : vCarrier V :=
  ((vScalar p omega x.2)⁻¹ • (-x.1), -x.2)

def vIdentity {V : Type*} [AddCommGroup V] : vCarrier V := (0, 0)

def vIdentityFree {V : Type*} [AddCommGroup V]
    (S : Set (vCarrier V)) : Prop :=
  ∀ x, x ∈ S → x ≠ vIdentity

def vInverseClosed {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (omega : ZMod p) (S : Set (vCarrier V)) : Prop :=
  ∀ x, x ∈ S → vInv omega x ∈ S

def vCayleyGraphIso {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (omega : ZMod p) (S T : Set (vCarrier V)) : Prop :=
  ∃ f : vCarrier V ≃ vCarrier V,
    ∀ x y,
      (x ≠ y ∧ vMul omega (vInv omega x) y ∈ S) ↔
        (f x ≠ f y ∧ vMul omega (vInv omega (f x)) (f y) ∈ T)

def vAutomorphism {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (omega : ZMod p) (f : vCarrier V ≃ vCarrier V) : Prop :=
  ∀ x y, f (vMul omega x y) = vMul omega (f x) (f y)

def vTransports {V : Type*} (f : vCarrier V ≃ vCarrier V)
    (S T : Set (vCarrier V)) : Prop :=
  ∀ x, x ∈ S ↔ f x ∈ T

def vConnectionSet {p : ℕ} {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V]
    (U W : Submodule (ZMod p) V) : Set (vCarrier V) :=
  {x | x.2 = 0 ∧
    ((x.1 ∈ U ∧ x.1 ≠ 0) ∨ (x.1 ∈ W ∧ x.1 ≠ 0))}

def vHasComplementaryForm {p : ℕ} {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V]
    (T : Set (vCarrier V)) (U W : Submodule (ZMod p) V) : Prop :=
  ∀ x, x ∈ T ↔ x.2 = 0 ∧
    ((x.1 ∈ U ∧ x.1 ≠ 0) ∨ (x.1 ∈ W ∧ x.1 ≠ 0))

def vUnorderedDimensions {p : ℕ} {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] [Fact (Nat.Prime p)] [NeZero p]
    (U W U' W' : Submodule (ZMod p) V) : Prop :=
  (Module.finrank (ZMod p) U' = Module.finrank (ZMod p) U ∧
      Module.finrank (ZMod p) W' = Module.finrank (ZMod p) W) ∨
    (Module.finrank (ZMod p) U' = Module.finrank (ZMod p) W ∧
      Module.finrank (ZMod p) W' = Module.finrank (ZMod p) U)

/-- Complementary subspace pairs are CI connection sets in E(V,3). -/
def complementarySubspacePairCI : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p),
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    letI : NeZero p := ⟨hp.ne_zero⟩
    ∀ (V : Type*) [AddCommGroup V] [Module (ZMod p) V]
      [FiniteDimensional (ZMod p) V] [Nontrivial V],
      ∀ omega : ZMod p, orderOf omega = 3 →
      ∀ U W : Submodule (ZMod p) V,
        U ≠ ⊥ → W ≠ ⊥ → U ⊔ W = ⊤ → Disjoint U W →
        let S := vConnectionSet U W
        vIdentityFree S ∧ vInverseClosed omega S ∧
          ∀ T : Set (vCarrier V),
            vIdentityFree T → vInverseClosed omega T →
            vCayleyGraphIso omega S T →
            ∃ α : vCarrier V ≃ vCarrier V,
              vAutomorphism omega α ∧ vTransports α S T ∧
              (∃ U' W' : Submodule (ZMod p) V,
                U' ≠ ⊥ ∧ W' ≠ ⊥ ∧ U' ⊔ W' = ⊤ ∧ Disjoint U' W' ∧
                vHasComplementaryForm T U' W' ∧
                vUnorderedDimensions U W U' W')

end MathlibPlus.Open
