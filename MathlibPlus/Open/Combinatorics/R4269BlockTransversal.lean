import Mathlib
import MathlibPlus.Open.Combinatorics.IncidenceSunflower

namespace MathlibPlus.Open.Combinatorics.R4269

/-- The exact block-transversal family is free of `k`-sunflowers when
`q = k - 1`, on the finite carrier fixed by Claim 51274. -/
def claim51275 (k n : ℕ) (_hk : 3 ≤ k) : Prop :=
  let q := k - 1
  let Point := Fin n × Fin q
  let block : Fin n → Finset Point :=
    fun j => Finset.univ.image (fun b : Fin q => (j, b))
  let transversal : (Fin n → Fin q) → Finset Point :=
    fun x => Finset.univ.image (fun j : Fin n => (j, x j))
  let transversals : Finset (Finset Point) :=
    Finset.univ.image transversal
  isKSunflowerFree transversals k

/-- The block-transversal family has matching number `q`, its links have the
exact block-count formula, and it satisfies the standard `q`-spread
inequality. -/
def claim51276 (k n : ℕ) (_hk : 3 ≤ k) : Prop :=
  let q := k - 1
  let Point := Fin n × Fin q
  let block : Fin n → Finset Point :=
    fun j => Finset.univ.image (fun b : Fin q => (j, b))
  let transversal : (Fin n → Fin q) → Finset Point :=
    fun x => Finset.univ.image (fun j : Fin n => (j, x j))
  let transversals : Finset (Finset Point) :=
    Finset.univ.image transversal
  let isMatching : ℕ → Prop :=
    fun r =>
      ∃ M : Fin r → Finset Point,
        (∀ i, M i ∈ transversals) ∧
          (∀ i j : Fin r, i ≠ j → M i ≠ M j ∧ Disjoint (M i) (M j))
  let link : Finset Point → Finset (Finset Point) :=
    fun S => transversals.filter (fun T => S ⊆ T)
  let meetingBlocks : Finset Point → Finset (Fin n) :=
    fun S => Finset.univ.filter (fun j => (S ∩ block j).Nonempty)
  (isMatching q ∧ ¬ isMatching (q + 1)) ∧
    (∀ S : Finset Point, S.Nonempty →
      (∀ j : Fin n, 2 ≤ (S ∩ block j).card → link S = ∅) ∧
        (∀ t : ℕ,
          (∀ j : Fin n, (S ∩ block j).card ≤ 1) →
            (meetingBlocks S).card = t →
              (link S).card = q ^ (n - t))) ∧
    (∀ S : Finset Point, S.Nonempty →
      (q : ℝ) ^ S.card * ((link S).card : ℝ) ≤
        (transversals.card : ℝ))

/-- The distinguished zero-coordinate set is shattered and has maximum
possible shattered cardinality for the same block-transversal family. -/
def claim51277 (k n : ℕ) (_hk : 3 ≤ k) : Prop :=
  let q := k - 1
  let Point := Fin n × Fin q
  let block : Fin n → Finset Point :=
    fun j => Finset.univ.image (fun b : Fin q => (j, b))
  let transversal : (Fin n → Fin q) → Finset Point :=
    fun x => Finset.univ.image (fun j : Fin n => (j, x j))
  let transversals : Finset (Finset Point) :=
    Finset.univ.image transversal
  let D : Finset Point :=
    Finset.univ.filter (fun p : Point => p.2.val = 0)
  let isShattered : Finset Point → Prop :=
    fun A =>
      ∀ Y : Finset Point, Y ⊆ A →
        ∃ T : Finset Point, T ∈ transversals ∧ T ∩ A = Y
  D.card = n ∧
    isShattered D ∧
      (∀ A : Finset Point, isShattered A → A.card ≤ n)

end MathlibPlus.Open.Combinatorics.R4269
