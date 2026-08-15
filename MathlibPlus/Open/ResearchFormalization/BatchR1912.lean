import Mathlib

open scoped BigOperators
open Finset
open Set

namespace MathlibPlus.Open.ResearchFormalization.R1912

noncomputable section

def SmallPrimes (z : ℕ) : Finset ℕ :=
  (Finset.range (z + 1)).filter Nat.Prime

def AvoidsResidues (X : Finset ℕ) (z : ℕ) : Prop :=
  ∀ q ∈ SmallPrimes z, ∃ a : Fin q, ∀ n ∈ X, n % q ≠ a.1

def Fiber (R : Finset ℕ) (p : ℕ) (a : Fin p) : Finset ℕ :=
  R.filter (fun n => n % p = a.1)

def MFiber (R : Finset ℕ) (p : ℕ) (a : Fin p) : Finset ℕ :=
  (Fiber R p a).image (fun n => (n - a.1) / p)

def FiberCount (R : Finset ℕ) (p : ℕ) (a : Fin p) : ℕ :=
  (Fiber R p a).card

def SP (R : Finset ℕ) (p : ℕ) : ℕ :=
  (Finset.univ : Finset (Fin p)).sum (fun a => (FiberCount R p a) ^ 2)

def AP (z : ℕ) : ℝ :=
  (SmallPrimes z).sum (fun q => Real.log (q : ℝ) / (q - 1 : ℝ))

def Theta (z : ℕ) : ℝ :=
  (SmallPrimes z).sum (fun q => Real.log (q : ℝ))

def DP (N p : ℕ) : ℝ :=
  Real.log (Nat.max 1 ((N - 1) / p) : ℝ)

def Variance (R : Finset ℕ) (p : ℕ) : ℝ :=
  (SP R p : ℝ) - (R.card : ℝ) ^ 2 / p

def residueFiberCounts (X : Finset ℕ) (q : ℕ) : Fin q → ℕ :=
  fun b => (X.filter (fun m => m % q = b.1)).card

def congruentPairCount (X : Finset ℕ) (q : ℕ) : ℕ :=
  (Finset.univ : Finset (Fin q)).sum (fun b => Nat.choose (residueFiberCounts X q b) 2)

def divisorLogSum (z h : ℕ) : ℝ :=
  ((SmallPrimes z).filter (fun q => q ∣ h)).sum (fun q => Real.log (q : ℝ))

def claim34916 : Prop :=
  ∀ (N z : ℕ) (R : Finset ℕ),
    R ⊆ Finset.Icc 0 (N - 1) ∧ AvoidsResidues R z →
    ∀ (p : ℕ) (hp : p.Prime) (hzp : z < p),
      ∃ (rFib : Fin p → ℕ) (r S : ℕ) (V : ℝ)
          (Az θ D : ℝ),
        (∀ a, rFib a = FiberCount R p a) ∧
        r = R.card ∧
        S = (Finset.univ : Finset (Fin p)).sum (fun a => (rFib a) ^ 2) ∧
        V = (S : ℝ) - (r : ℝ) ^ 2 / p ∧
        Az = AP z ∧ θ = Theta z ∧ D = DP N p

def claim34917 : Prop :=
  ∀ (N z p : ℕ) (R : Finset ℕ),
    R ⊆ Finset.Icc 0 (N - 1) ∧ AvoidsResidues R z ∧
    p.Prime ∧ z < p →
      ((AP z - DP N p) * SP R p : ℝ) ≤
        (Theta z - DP N p) * R.card ∧
      (∀ a : Fin p,
        (∀ m ∈ MFiber R p a, m ≤ (N - 1) / p) ∧
        (∀ m₁ ∈ MFiber R p a, ∀ m₂ ∈ MFiber R p a,
          |(m₁ : ℤ) - m₂| ≤ ((N - 1) / p : ℤ)) ∧
        AvoidsResidues (MFiber R p a) z ∧
        (∀ q ∈ SmallPrimes z,
          (congruentPairCount (MFiber R p a) q : ℝ) ≥
            ((FiberCount R p a : ℝ) ^ 2 / (q - 1) - FiberCount R p a) / 2) ∧
        (∀ m₁ ∈ MFiber R p a, ∀ m₂ ∈ MFiber R p a, m₁ ≠ m₂ →
          divisorLogSum z (Int.natAbs ((m₁ : ℤ) - (m₂ : ℤ))) ≤ DP N p)
      )

def claim34918 : Prop :=
  (∀ (X : Finset ℕ) (q : ℕ),
    q.Prime →
    (∃ b : Fin q, ∀ m ∈ X, m % q ≠ b.1) →
      (congruentPairCount X q : ℝ) ≥
        ((X.card : ℝ) ^ 2 / (q - 1) - X.card) / 2) ∧
  (∀ (N p z h : ℕ),
    p.Prime → z < p → 0 < h → h ≤ (N - 1) / p →
      ((SmallPrimes z).filter (fun q => q ∣ h)).prod id ≤ h ∧
      divisorLogSum z h ≤ DP N p)

def claim34920 : Prop :=
  let Q : ℕ := 30
  let N : ℕ := 15
  let t : ℕ := 23
  let p : ℕ := 7
  let R : Finset ℕ :=
    (Finset.range N).filter (fun n => Nat.Coprime (t + n) Q)
  R = ({0, 6, 8, 14} : Finset ℕ) ∧
  (∀ a : Fin p, FiberCount R p a =
    (![2, 1, 0, 0, 0, 0, 1] : Fin 7 → ℕ) a) ∧
  R.card = 4 ∧ SP R p = 6 ∧
  Variance R p = (26 : ℝ) / 7 ∧
  (26 : ℝ) / 7 > 4 * (1 - (1 : ℝ) / 7)

end
end MathlibPlus.Open.ResearchFormalization.R1912
