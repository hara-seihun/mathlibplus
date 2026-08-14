import Mathlib

namespace MathlibPlus.Open.Research

/-- A concrete multiplicative model of the two-element group. -/
abbrev C2 := Multiplicative (ZMod 2)

/-- A central element in a group. -/
def IsCentralElement {G : Type} [Group G] (z : G) : Prop :=
  ∀ g : G, g * z = z * g

/-- Claim 35832: the generalized quaternion presentation has the dihedral quotient. -/
def claim35832 : Prop :=
  ∀ n : Nat, n % 2 = 1 →
    ∃ (a b z : QuaternionGroup n)
      (π : QuaternionGroup n →* DihedralGroup n),
      Subgroup.closure ({a, b} : Set (QuaternionGroup n)) = ⊤ ∧
      a ^ (2 * n) = 1 ∧
      b ^ 2 = a ^ n ∧
      b⁻¹ * a * b = a⁻¹ ∧
      z = a ^ n ∧
      z ^ 2 = 1 ∧
      z ≠ 1 ∧
      IsCentralElement z ∧
      Function.Surjective π ∧
      MonoidHom.ker π = Subgroup.closure ({z} : Set (QuaternionGroup n))

/-- Claim 35839: subgroup characters extend when the dihedral parameter is odd. -/
def claim35839 : Prop :=
  ∀ n : Nat, n % 2 = 1 →
    ∀ (L : Subgroup (DihedralGroup n)) (f : L →* C2),
      ∃ χ : DihedralGroup n →* C2,
        ∀ x : L, χ (x : DihedralGroup n) = f x

end MathlibPlus.Open.Research
