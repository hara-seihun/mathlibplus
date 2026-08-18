import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0871Claim29625

noncomputable section

abbrev BinaryPolynomial := MvPolynomial (Fin 2) ℚ

def scalar (lam : ℚ) : BinaryPolynomial :=
  (algebraMap ℚ BinaryPolynomial) lam

def firstSplitContext
    (h : ℕ) (lam : ℚ)
    (A B D : PowerSeries BinaryPolynomial)
    (a b c d H X Y Z : BinaryPolynomial) : Prop :=
  h > 0 ∧
    lam ≠ 0 ∧ lam ≠ 1 ∧
    H ≠ 0 ∧ X ≠ 0 ∧ Y ≠ 0 ∧ Z ≠ 0 ∧
    IsCoprime X Y ∧ IsCoprime X Z ∧ IsCoprime Y Z ∧
    (∀ k < h, PowerSeries.coeff k A = 0) ∧
    (∀ k < h, PowerSeries.coeff k B = 0) ∧
    (∀ k < h, PowerSeries.coeff k D = 0) ∧
    PowerSeries.coeff h A = H * X * Z ∧
    PowerSeries.coeff h B = H * Y * Z ∧
    PowerSeries.coeff h D = (scalar lam - 1) * H * X * Y ∧
    PowerSeries.coeff (h + 1) A = a ∧
    PowerSeries.coeff (h + 1) B = b ∧
    PowerSeries.coeff (h + 1) D = d ∧
    Z = scalar lam * X - Y ∧
    d = (scalar lam - 1) * c ∧
    D * (PowerSeries.C (scalar lam) * A - B) =
      PowerSeries.C (scalar lam - 1) * A * B

def tangentEquation
    (lam : ℚ) (X Y Z a b c : BinaryPolynomial) : Prop :=
  a * Y ^ 2 - scalar lam * b * X ^ 2 + c * Z ^ 2 = 0

/-- The two displayed Hilbert--Burch channel columns. -/
def channelOne (lam : ℚ) (X Y : BinaryPolynomial) : Fin 3 → BinaryPolynomial :=
  ![-X, scalar lam * X - 2 * Y, X]

def channelTwo (lam : ℚ) (X Y : BinaryPolynomial) : Fin 3 → BinaryPolynomial :=
  ![2 * scalar lam * X - Y, scalar lam * Y, Y]

def channelRelation
    (lam : ℚ) (X Y Z a b c P Q : BinaryPolynomial) : Prop :=
  a = P * channelOne lam X Y 0 + Q * channelTwo lam X Y 0 ∧
    b = P * channelOne lam X Y 1 + Q * channelTwo lam X Y 1 ∧
      c = P * channelOne lam X Y 2 + Q * channelTwo lam X Y 2

def minorRows12 (lam : ℚ) (X Y : BinaryPolynomial) : BinaryPolynomial :=
  channelOne lam X Y 0 * channelTwo lam X Y 1 -
    channelTwo lam X Y 0 * channelOne lam X Y 1

def minorRows13 (lam : ℚ) (X Y : BinaryPolynomial) : BinaryPolynomial :=
  channelOne lam X Y 0 * channelTwo lam X Y 2 -
    channelTwo lam X Y 0 * channelOne lam X Y 2

def minorRows23 (lam : ℚ) (X Y : BinaryPolynomial) : BinaryPolynomial :=
  channelOne lam X Y 1 * channelTwo lam X Y 2 -
    channelTwo lam X Y 1 * channelOne lam X Y 2

def rationalUnitMultiple (u : ℚ) (p q : BinaryPolynomial) : Prop :=
  u ≠ 0 ∧ p = scalar u * q

/-- Claim 29625: in the exact all-distinct first-split setting, every tangent
triple has one and only one pair of channel quotients, the displayed columns
have the three asserted maximal minors up to nonzero rational units, and the
unique pair is the complete deformation-channel list. -/
def claim29625 : Prop :=
  ∀ (h : ℕ) (lam : ℚ)
    (A B D : PowerSeries BinaryPolynomial)
    (a b c d H X Y Z : BinaryPolynomial),
    firstSplitContext h lam A B D a b c d H X Y Z →
      (∀ (u v w : BinaryPolynomial),
        tangentEquation lam X Y Z u v w →
          ∃! channels : BinaryPolynomial × BinaryPolynomial,
            channelRelation lam X Y Z u v w channels.1 channels.2) ∧
      (∀ (P Q : BinaryPolynomial),
        tangentEquation lam X Y Z
          (P * channelOne lam X Y 0 + Q * channelTwo lam X Y 0)
          (P * channelOne lam X Y 1 + Q * channelTwo lam X Y 1)
          (P * channelOne lam X Y 2 + Q * channelTwo lam X Y 2)) ∧
      rationalUnitMultiple (-2 : ℚ) (minorRows12 lam X Y) (Z ^ 2) ∧
      rationalUnitMultiple (-2 * lam) (minorRows13 lam X Y) (X ^ 2) ∧
      rationalUnitMultiple (-2 : ℚ) (minorRows23 lam X Y) (Y ^ 2)

end

end MathlibPlus.Open.ResearchFormalization.R0871Claim29625
