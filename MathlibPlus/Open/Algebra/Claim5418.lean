import Mathlib

namespace MathlibPlus.Open.Algebra.Claim5418

open scoped BigOperators

noncomputable section

/-- The complete homogeneous polynomial in two variables. -/
def completeHomogeneous2 {R : Type*} [CommRing R]
    (k : ℕ) (x y : R) : R :=
  ∑ i ∈ Finset.range (k + 1),
    x ^ i * y ^ (k - i)

/-- The complete homogeneous polynomial in three variables. -/
def completeHomogeneous3 {R : Type*} [CommRing R]
    (k : ℕ) (x y z : R) : R :=
  ∑ i ∈ Finset.range (k + 1),
    ∑ j ∈ Finset.range (k - i + 1),
      x ^ i * y ^ j * z ^ (k - i - j)

/-- The bracket used in the packet, with its two-variable and three-variable
specializations made explicit for the alternating extension. -/
def harmonicBracket2 {R : Type*} [CommRing R]
    (a b : ℕ) (x y p : R) : R :=
  p ^ b * completeHomogeneous2 a x y -
    p ^ a * completeHomogeneous2 b x y

def harmonicBracket3 {R : Type*} [CommRing R]
    (a b : ℕ) (x y z p : R) : R :=
  p ^ b * completeHomogeneous3 a x y z -
    p ^ a * completeHomogeneous3 b x y z

/-- The six-term alternating sum in three variables. -/
def alt3 {R : Type*} [CommRing R]
    (f : R → R → R → R) (u v w : R) : R :=
  f u v w - f u w v - f v u w + f v w u + f w u v - f w v u

/-- Claim 5418: every indexed harmonic bracket obeys the displayed
alternating extension identity. -/
def claim5418 : Prop :=
  ∀ {R : Type*} [CommRing R] (a b : ℕ), a < b →
    ∀ (u v w p : R),
      alt3
          (fun x y _z =>
            x * y * (x - y) * harmonicBracket2 a b (x ^ 2) (y ^ 2) p)
          u v w =
        2 * (u - v) * (u - w) * (v - w) *
          harmonicBracket3 a b (u ^ 2) (v ^ 2) (w ^ 2) p

end
end MathlibPlus.Open.Algebra.Claim5418
