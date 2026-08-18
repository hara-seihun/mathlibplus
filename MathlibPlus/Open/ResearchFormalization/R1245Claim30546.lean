import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1245Claim30546

noncomputable section

abbrev Cn (n : ℕ) := ZMod n
abbrev Q4n (n : ℕ) := Cn n × Fin 4

def oddSquarefreeNat (n : ℕ) : Prop :=
  Odd n ∧ ∀ p : ℕ, Nat.Prime p → ¬ p ^ 2 ∣ n

def fourLayerMul {n : ℕ} (x y : Q4n n) : Q4n n :=
  (x.1 + (-1 : Cn n) ^ x.2.val * y.1, x.2 + y.2)

def fourLayerInv {n : ℕ} (x : Q4n n) : Q4n n :=
  (-((-1 : Cn n) ^ x.2.val * x.1), -x.2)

def fourLayerIdentity {n : ℕ} : Q4n n := (0, 0)

def c4BaseAutomorphism (π : Equiv.Perm (Fin 4)) : Prop :=
  ∀ i j : Fin 4, π (i + j) = π i + π j

def normalizedBlockAffine {n : ℕ}
    (lambdas : Fin 4 → (Cn n)ˣ) (τ : Fin 4 → Cn n)
    (π : Equiv.Perm (Fin 4)) (f : Equiv.Perm (Q4n n)) : Prop :=
  π 0 = 0 ∧ τ 0 = 0 ∧
    ∀ (x : Cn n) (i : Fin 4),
      f (x, i) = (((lambdas i : (Cn n)ˣ) : Cn n) * x + τ i, π i)

def primeCoordinateSubgroup (n p : ℕ) : AddSubgroup (Cn n) :=
  AddSubgroup.zmultiples (n / p : Cn n)

def primeCoordinate (n p : ℕ) (hpn : p ∣ n) : Cn n →+* ZMod p :=
  ZMod.castHom hpn (ZMod p)

def primeCoordinateProduct (n : ℕ) (selected : ℕ → Prop) : AddSubgroup (Cn n) :=
  AddSubgroup.closure
    {x : Cn n | ∃ p : ℕ, Nat.Prime p ∧ p ∣ n ∧ selected p ∧
      x ∈ primeCoordinateSubgroup n p}

def normalizedRelativeDerivative {n : ℕ}
    (f : Equiv.Perm (Q4n n)) (g : Q4n n) : Q4n n → Q4n n :=
  fun x => fourLayerMul (f (fourLayerMul g x)) (fourLayerInv (f g))

def purePrimeTranslation {n : ℕ} (p : ℕ)
    (r : Q4n n → Q4n n) (a : Cn n) : Prop :=
  a ∈ primeCoordinateSubgroup n p ∧ a ≠ 0 ∧
    ∀ (i : Fin 4), i ≠ 0 → ∀ x : Cn n,
      r (x, i) = (x + a, i)

def scalarActiveAt {n : ℕ}
    (f : Equiv.Perm (Q4n n)) (p : ℕ) : Prop :=
  ∃ g : Q4n n, ∃ a : Cn n,
    purePrimeTranslation p (normalizedRelativeDerivative f g) a

def dCoordinate {n : ℕ}
    (π : Equiv.Perm (Fin 4)) (τ : Fin 4 → Cn n) (i : Fin 4) : Cn n :=
  (-1 : Cn n) ^ (π i).val * τ i

def deltaCoordinate {n : ℕ}
    (π : Equiv.Perm (Fin 4)) (τ : Fin 4 → Cn n) : Cn n :=
  dCoordinate π τ 1 - dCoordinate π τ 2 - dCoordinate π τ 3

def translationActiveAt {n : ℕ}
    (f : Equiv.Perm (Q4n n)) (π : Equiv.Perm (Fin 4))
    (τ : Fin 4 → Cn n) (p : ℕ) (hpn : p ∣ n) : Prop :=
  ¬ scalarActiveAt f p ∧
    primeCoordinate n p hpn (deltaCoordinate π τ) ≠ 0

def quietAt {n : ℕ}
    (f : Equiv.Perm (Q4n n)) (π : Equiv.Perm (Fin 4))
    (τ : Fin 4 → Cn n) (p : ℕ) (hpn : p ∣ n) : Prop :=
  ¬ scalarActiveAt f p ∧
    primeCoordinate n p hpn (deltaCoordinate π τ) = 0

def sectionOf {n : ℕ} (S : Set (Q4n n)) (i : Fin 4) : Set (Cn n) :=
  {x | (x, i) ∈ S}

def sectionPeriodicBy {n : ℕ}
    (A : AddSubgroup (Cn n)) (T : Set (Cn n)) : Prop :=
  ∀ a : A, ∀ x : Cn n, x ∈ T ↔ x + a.1 ∈ T

def everyNonzeroSectionPeriodic {n : ℕ}
    (A : AddSubgroup (Cn n)) (S : Set (Q4n n)) : Prop :=
  ∀ i : Fin 4, i ≠ 0 → sectionPeriodicBy A (sectionOf S i)

def identityFree {n : ℕ} (S : Set (Q4n n)) : Prop :=
  fourLayerIdentity ∉ S

def inverseClosed {n : ℕ} (S : Set (Q4n n)) : Prop :=
  ∀ x : Q4n n, x ∈ S ↔ fourLayerInv x ∈ S

def relativeDerivativeInvariant {n : ℕ}
    (f : Equiv.Perm (Q4n n)) (S : Set (Q4n n)) : Prop :=
  ∀ g : Q4n n,
    Set.image (normalizedRelativeDerivative f g) S = S

def deltaCoordinateProduct {n : ℕ} (δ : Cn n) : AddSubgroup (Cn n) :=
  primeCoordinateProduct n (fun p =>
    ∃ hpn : p ∣ n, primeCoordinate n p hpn δ ≠ 0)

def deltaCoordinateGeneration {n : ℕ} (δ : Cn n) : Prop :=
  AddSubgroup.zmultiples δ = deltaCoordinateProduct δ

/-- Claim 30546: in the nonautomorphic base branch, the active prime
coordinates generate A, all nonzero sections are A-periodic, the delta
subgroup has exactly its nonzero CRT coordinates, and every coordinate that
survives the quotient by A is quiet. -/
def claim30546 : Prop :=
  ∀ (n : ℕ), oddSquarefreeNat n →
    ∀ (lambdas : Fin 4 → (Cn n)ˣ) (τ : Fin 4 → Cn n)
      (π : Equiv.Perm (Fin 4)) (f : Equiv.Perm (Q4n n))
      (S : Set (Q4n n)),
      normalizedBlockAffine lambdas τ π f →
      ¬ c4BaseAutomorphism π →
      identityFree S ∧ inverseClosed S ∧ relativeDerivativeInvariant f S →
      let A := primeCoordinateProduct n (fun p =>
        scalarActiveAt f p ∨
          ∃ hpn : p ∣ n, translationActiveAt f π τ p hpn)
      everyNonzeroSectionPeriodic A S ∧
        deltaCoordinateGeneration (deltaCoordinate π τ) ∧
        ∀ (p : ℕ) (hp : Nat.Prime p) (hpn : p ∣ n),
          ¬ primeCoordinateSubgroup n p ≤ A →
            quietAt f π τ p hpn

end

end MathlibPlus.Open.ResearchFormalization.R1245Claim30546
