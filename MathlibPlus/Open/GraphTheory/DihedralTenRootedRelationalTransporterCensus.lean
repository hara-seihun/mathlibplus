import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Exact rooted-map census behind directed binary-relational CI for the
 dihedral group of order ten. -/
def dihedralTenRootedRelationalTransporterCensus : Prop :=
  let G := ZMod 5 × Bool
  let one : G := (0, false)
  let mul : G → G → G := fun x y =>
    (x.1 + if x.2 then -y.1 else y.1, Bool.xor x.2 y.2)
  let inv : G → G := fun x =>
    if x.2 then x else (-x.1, false)
  let diff : G → G → G := fun x y => mul (inv x) y
  let image : Equiv.Perm G → Finset G → Finset G := fun q S => S.image q
  let rooted : Finset (Equiv.Perm G) :=
    Finset.univ.filter fun q => q one = one
  let isAut : Equiv.Perm G → Prop := fun a =>
    ∀ x y, a (mul x y) = mul (a x) (a y)
  let admissible : Equiv.Perm G → Finset G → Prop := fun q S =>
    ∀ x y, diff x y ∈ S ↔ diff (q x) (q y) ∈ image q S
  let universal : Equiv.Perm G → Equiv.Perm G → Prop := fun q a =>
    isAut a ∧ ∀ S, admissible q S → image a S = image q S
  let admissibleCount : Equiv.Perm G → ℕ := fun q =>
    ((Finset.univ : Finset (Finset G)).filter (admissible q)).card
  let universalCount : Equiv.Perm G → ℕ := fun q =>
    ((Finset.univ : Finset (Equiv.Perm G)).filter (universal q)).card
  rooted.card = 362880 ∧
  (rooted.filter fun q => admissibleCount q = 4 ∧ universalCount q = 20).card =
    351000 ∧
  (rooted.filter fun q => admissibleCount q = 8 ∧ universalCount q = 4).card =
    7500 ∧
  (rooted.filter fun q => admissibleCount q = 8 ∧ universalCount q = 20).card =
    2340 ∧
  (rooted.filter fun q => admissibleCount q = 16 ∧ universalCount q = 2).card =
    1500 ∧
  (rooted.filter fun q => admissibleCount q = 16 ∧ universalCount q = 4).card =
    500 ∧
  (rooted.filter fun q => admissibleCount q = 16 ∧ universalCount q = 10).card =
    20 ∧
  (rooted.filter fun q => admissibleCount q = 1024 ∧ universalCount q = 1).card =
    20

end MathlibPlus.Open.GraphTheory
