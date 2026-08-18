import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1261Claim30734

open scoped BigOperators

noncomputable section

/-- The displayed generalized-quaternion carrier Cₙ ⋊inv C₄. -/
abbrev Q4n (n : ℕ) := ZMod n × ZMod 4

def qOne (n : ℕ) : Q4n n := (0, 0)

def qMul (n : ℕ) (a b : Q4n n) : Q4n n :=
  (a.1 + ((-1 : ZMod n) ^ a.2.val) * b.1, a.2 + b.2)

def qInv (n : ℕ) (a : Q4n n) : Q4n n :=
  (-(((-1 : ZMod n) ^ a.2.val) * a.1), -a.2)

def qGroupLaws (n : ℕ) : Prop :=
  (∀ a b c : Q4n n, qMul n (qMul n a b) c = qMul n a (qMul n b c)) ∧
    (∀ a : Q4n n,
      qMul n (qOne n) a = a ∧ qMul n a (qOne n) = a ∧
        qMul n (qInv n a) a = qOne n ∧ qMul n a (qInv n a) = qOne n)

def qSubgroup (n : ℕ) (K : Set (Q4n n)) : Prop :=
  qOne n ∈ K ∧
    (∀ a, a ∈ K → qInv n a ∈ K) ∧
      ∀ a b, a ∈ K → b ∈ K → qMul n a b ∈ K

def qOddHall (n : ℕ) : Set (Q4n n) :=
  {a | a.2 = 0}

/-- The characteristic cyclic subgroup C_d is the d-torsion in the odd
coordinate, not the kernel of multiplication by n/d. -/
def qPrefix (n d : ℕ) : Set (Q4n n) :=
  {a | a.2 = 0 ∧ d • a.1 = 0}

def qAutomorphism (n : ℕ) (alpha : Q4n n → Q4n n) : Prop :=
  Function.Bijective alpha ∧
    ∀ a b, alpha (qMul n a b) = qMul n (alpha a) (alpha b)

def regularQ4nCopy {Omega : Type*} [Fintype Omega]
    (n : ℕ) (rho : Q4n n → Equiv.Perm Omega) : Prop :=
  ∃ e : Q4n n ≃ Omega,
    ∀ a x, rho a (e x) = e (qMul n a x)

def orbitSet {Omega : Type*}
    (rho : Q4n n → Equiv.Perm Omega)
    (K : Set (Q4n n)) (x : Omega) : Set Omega :=
  {y | ∃ a, a ∈ K ∧ rho a x = y}

def orbitPartition {Omega : Type*}
    (rho : Q4n n → Equiv.Perm Omega)
    (K : Set (Q4n n)) : Set (Set Omega) :=
  Set.range (orbitSet rho K)

def blockStabilizer {Omega : Type*}
    (rho : Q4n n → Equiv.Perm Omega) (B : Set Omega) : Set (Q4n n) :=
  {a | Set.image (rho a) B = B}

def prefixProduct {r : ℕ} (p : Fin r → ℕ) (j : Fin r) : ℕ :=
  Finset.prod (Finset.Iic j) p

def descendingPrimeData {r : ℕ} (p : Fin r → ℕ) (n : ℕ) : Prop :=
  1 < n ∧ Odd n ∧ Squarefree n ∧
    n = Finset.univ.prod p ∧
      (∀ i : Fin r, Nat.Prime (p i)) ∧
        (∀ i j : Fin r, i < j → p j < p i)

def commonPrefixBlock {Omega : Type*}
    (rho : Q4n n → Equiv.Perm Omega) (d : ℕ) (B : Set Omega) : Prop :=
  B ∈ orbitPartition rho (qPrefix n d) ∧ Set.ncard B = d

def characteristicPrefix (n d : ℕ) : Prop :=
  (d ∣ n) ∧ qSubgroup n (qPrefix n d) ∧
    (∀ alpha : Q4n n → Q4n n, qAutomorphism n alpha →
      Set.image alpha (qPrefix n d) = qPrefix n d) ∧
      (∀ K : Set (Q4n n), qSubgroup n K → K ⊆ qOddHall n →
        Set.ncard K = d → K = qPrefix n d)

/-- Claim 30734: in the exact odd square-free nonexceptional Q₄ₙ chain,
common regular blocks have the unique characteristic cyclic odd-Hall
stabilizer of the displayed prefix order. -/
def claim_30734 : Prop :=
  ∀ (r : ℕ) (p : Fin r → ℕ) (n : ℕ),
    descendingPrimeData p n →
      ¬ 3 ∣ n →
        ∀ (j : Fin r),
          let d := prefixProduct p j
          d ∣ n →
            ∀ (Omega : Type*) [Fintype Omega]
            (rhoR rhoT : Q4n n → Equiv.Perm Omega),
            regularQ4nCopy n rhoR →
              regularQ4nCopy n rhoT →
                ∀ B : Set Omega,
                  commonPrefixBlock rhoR d B →
                    commonPrefixBlock rhoT d B →
                      orbitPartition rhoR (qPrefix n d) =
                        orbitPartition rhoT (qPrefix n d) →
                        characteristicPrefix n d ∧
                          (∀ K : Set (Q4n n), qSubgroup n K →
                            Odd (Set.ncard K) → K ⊆ qOddHall n) ∧
                            (∀ K : Set (Q4n n), qSubgroup n K →
                              K ⊆ qOddHall n → Set.ncard K = d →
                                K = qPrefix n d) ∧
                              Set.ncard (blockStabilizer rhoR B) = d ∧
                                Set.ncard (blockStabilizer rhoT B) = d ∧
                                  blockStabilizer rhoR B = qPrefix n d ∧
                                    blockStabilizer rhoT B = qPrefix n d

end

end MathlibPlus.Open.ResearchFormalization.R1261Claim30734
