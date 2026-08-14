import Mathlib

namespace MathlibPlus.Open.Probability

noncomputable section

abbrev BooleanAssignment (n : ℕ) := Fin n → Bool

def signedBoolean (b : Bool) : ℝ := if b then 1 else -1

/-- A two-address signed Boolean multiplexer: the four address patterns are
literally the four elements of `Bool × Bool`, and the selected data coordinates
are injective and disjoint from the two address coordinates. -/
structure SignedTwoAddressMultiplexer (n : ℕ) where
  address : Fin 2 → Fin n
  data : Bool × Bool → Fin n
  address_injective : Function.Injective address
  data_injective : Function.Injective data
  address_data_disjoint : ∀ i b, address i ≠ data b
  sign : Bool × Bool → Bool

def shiftIndex {n : ℕ} [NeZero n] (t i : Fin n) : Fin n :=
  ⟨(t.1 + i.1) % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩

def shiftedAssignment {n : ℕ} [NeZero n]
    (t : Fin n) (x : BooleanAssignment n) : BooleanAssignment n :=
  fun i => x (shiftIndex t i)

def multiplexerValue {n : ℕ}
    (h : SignedTwoAddressMultiplexer n) (x : BooleanAssignment n) : ℝ :=
  signedBoolean (h.sign (x (h.address 0), x (h.address 1))) *
    signedBoolean (x (h.data (x (h.address 0), x (h.address 1))))

def cyclicAverage {n : ℕ} [NeZero n]
    (h : SignedTwoAddressMultiplexer n) : BooleanAssignment n → ℝ :=
  fun x => (1 / (n : ℝ)) *
    ∑ t : Fin n, multiplexerValue h (shiftedAssignment t x)

def uniformMean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (1 / (Fintype.card α : ℝ)) * ∑ x : α, f x

def variance {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  uniformMean (fun x => (f x - uniformMean f) ^ 2)

def addressRole {n : ℕ} [NeZero n]
    (h : SignedTwoAddressMultiplexer n) (t i : Fin n) : Prop :=
  shiftIndex t (h.address 0) = i ∨ shiftIndex t (h.address 1) = i

def dataRole {n : ℕ} [NeZero n]
    (h : SignedTwoAddressMultiplexer n) (t i : Fin n) : Prop :=
  ∃ b : Bool × Bool, shiftIndex t (h.data b) = i

def roleCountAddress {n : ℕ} [NeZero n]
    (h : SignedTwoAddressMultiplexer n) (i : Fin n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun t : Fin n => addressRole h t i)).card

def roleCountData {n : ℕ} [NeZero n]
    (h : SignedTwoAddressMultiplexer n) (i : Fin n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun t : Fin n => dataRole h t i)).card

def expectedSaving {n : ℕ} [NeZero n]
    (h : SignedTwoAddressMultiplexer n) (i : Fin n) : ℝ :=
  ((roleCountAddress h i : ℝ) +
      (roleCountData h i : ℝ) * (1 / 4)) / (n : ℝ)

def maximumSaving {n : ℕ} [NeZero n]
    (h : SignedTwoAddressMultiplexer n) : ℝ := by
  classical
  let hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨0, Finset.mem_univ 0⟩
  exact (Finset.univ : Finset (Fin n)).sup' hne (expectedSaving h)

/-- The role-count accounting lemma: two address appearances and four data
appearances per ambient coordinate give the exact saving `3/n`. -/
def uniformRoleCountSaving : Prop :=
  ∀ (n : ℕ), ∀ hn : 6 ≤ n,
    letI : NeZero n :=
      ⟨Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hn)⟩
    ∀ h : SignedTwoAddressMultiplexer n, ∀ i : Fin n,
      roleCountAddress h i = 2 ∧
      roleCountData h i = 4 ∧
      expectedSaving h i = 3 / (n : ℝ)

/-- The uniform cyclic factor-two assertion, with the Boolean function, cyclic
average, variance, and maximum-saving conventions all explicit. -/
def uniformCyclicFactorTwo : Prop :=
  ∀ (n : ℕ), ∀ hn : 6 ≤ n,
    letI : NeZero n :=
      ⟨Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hn)⟩
    ∀ h : SignedTwoAddressMultiplexer n,
      (∀ i : Fin n, expectedSaving h i = 3 / (n : ℝ)) ∧
      variance (cyclicAverage h) ≤ 6 / (n : ℝ) ∧
      6 / (n : ℝ) = 2 * maximumSaving h

end

end MathlibPlus.Open.Probability
