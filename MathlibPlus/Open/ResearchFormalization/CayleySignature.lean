import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.CayleySignature

abbrev CayleyVertex (p r : ℕ) := Fin r → ZMod p

def inverseClosed {p r : ℕ}
    (S : Finset (CayleyVertex p r)) : Prop :=
  ∀ x, x ∈ S → -x ∈ S

def identityFree {p r : ℕ}
    (S : Finset (CayleyVertex p r)) : Prop :=
  0 ∉ S

def cayleyAdj {p r : ℕ}
    (S : Finset (CayleyVertex p r))
    (x y : CayleyVertex p r) : ℕ :=
  if y - x ∈ S then 1 else 0

def cayleyMatrix {p r : ℕ}
    (S : Finset (CayleyVertex p r)) :
    Matrix (CayleyVertex p r) (CayleyVertex p r) ℕ :=
  fun x y => cayleyAdj S x y

def rootedWalkSignature {p r : ℕ} [NeZero p]
    (S : Finset (CayleyVertex p r)) (x : CayleyVertex p r) :
    Fin (Fintype.card (CayleyVertex p r)) → ℕ :=
  fun n => (cayleyMatrix S ^ (n : ℕ)) 0 x

def equalRootedWalkSignatures {p r : ℕ} [NeZero p]
    (S : Finset (CayleyVertex p r))
    (x y : CayleyVertex p r) : Prop :=
  rootedWalkSignature S x = rootedWalkSignature S y

def rootedPrefixComplete {p r : ℕ} [NeZero p]
    (S : Finset (CayleyVertex p r)) : Prop :=
  ∀ x y, equalRootedWalkSignatures S x y →
    ∀ n : ℕ,
      (cayleyMatrix S ^ n) 0 x = (cayleyMatrix S ^ n) 0 y

def walkSeparation {p r : ℕ} [NeZero p]
    (S : Finset (CayleyVertex p r)) : Prop :=
  ∀ x y,
    equalRootedWalkSignatures S x y ↔ y = x ∨ y = -x

/-- The rooted-walk prefix and the exact separation predicate on one
prime-power Cayley fibre. -/
def RootedWalkSignatureAndSeparation
    (p r : ℕ) (hp : Nat.Prime p)
    (S : Finset (CayleyVertex p r)) : Prop := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact
    identityFree S ∧
    inverseClosed S ∧
    rootedPrefixComplete S ∧
    walkSeparation S

end MathlibPlus.Open.ResearchFormalization.CayleySignature
