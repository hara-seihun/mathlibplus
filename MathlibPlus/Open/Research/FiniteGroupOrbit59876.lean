import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research

/-- The field used in the finite semidirect-product claim. -/
abbrev F7 := ZMod 7

/-- `G = (Z/3Z) × F_7^2`, with the displayed semidirect-product law. -/
abbrev G59876 := ZMod 3 × (F7 × F7)

def twoPow59876 (i : ZMod 3) : F7 :=
  (2 : F7) ^ i.val

def groupMul59876 (a b : G59876) : G59876 :=
  (a.1 + b.1,
    (a.2.1 + twoPow59876 a.1 * b.2.1,
      a.2.2 + twoPow59876 a.1 * b.2.2))

def groupInv59876 (a : G59876) : G59876 :=
  (-a.1,
    (-((twoPow59876 a.1)⁻¹ * a.2.1),
      -((twoPow59876 a.1)⁻¹ * a.2.2)))

def groupOne59876 : G59876 := (0, (0, 0))

def isGroupAutomorphism59876 (e : Equiv.Perm G59876) : Prop :=
  e groupOne59876 = groupOne59876 ∧
    ∀ x y : G59876, e (groupMul59876 x y) = groupMul59876 (e x) (e y)

noncomputable def automorphisms59876 : Finset (Equiv.Perm G59876) := by
  classical
  exact (Finset.univ : Finset (Equiv.Perm G59876)).filter isGroupAutomorphism59876

def imageSubset59876 (e : Equiv.Perm G59876) (S : Finset G59876) : Finset G59876 :=
  S.map e.toEmbedding

noncomputable def automorphismOrbit59876 (S : Finset G59876) : Finset (Finset G59876) :=
  automorphisms59876.image (fun e => imageSubset59876 e S)

def identityFreeInverseClosed59876 (S : Finset G59876) : Prop :=
  groupOne59876 ∉ S ∧ ∀ g ∈ S, groupInv59876 g ∈ S

def admissibleSubset59876 (k : Nat) (S : Finset G59876) : Prop :=
  S.card = 2 * k ∧ identityFreeInverseClosed59876 S

/-- `a k` is the number of automorphism orbits of the indicated subsets. -/
noncomputable def a59876 (k : Nat) : Nat := by
  classical
  exact (Finset.image automorphismOrbit59876
    ((Finset.univ : Finset (Finset G59876)).filter (admissibleSubset59876 k))).card

def listedFirst37_59876 : List Nat :=
  [1,
    2,
    4,
    15,
    60,
    325,
    2391,
    18869,
    144164,
    1008785,
    6368245,
    36246070,
    186717466,
    874842037,
    3746460641,
    14730055911,
    53384380454,
    178971631494,
    556758617990,
    1611596466968,
    4351188406414,
    10981375882580,
    25955681134926,
    57553463988572,
    119902433975513,
    235007938808131,
    433859733153148,
    755235977158586,
    1240743232880233,
    1925289423195690,
    2823755875199406,
    3916820671578127,
    5140825207298441,
    6387084137251045,
    7514215225072848,
    8372981691695399,
    8838146837490987]

def admittedClaim59876 : Prop :=
  (∀ k : Nat, 0 ≤ k ∧ k ≤ 73 → a59876 k = a59876 (73 - k)) ∧
    (List.range 37).map a59876 = listedFirst37_59876 ∧
    (Finset.sum (Finset.range 74) a59876) = 95610260774263876

end MathlibPlus.Open.Research
