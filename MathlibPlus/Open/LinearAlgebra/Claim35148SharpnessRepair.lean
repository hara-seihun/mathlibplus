import Mathlib
import MathlibPlus.Open.ResearchBatch.Lease_01a001c2.Pullback

namespace MathlibPlus.Open.LinearAlgebra.Claim35148

noncomputable section
open Classical
open MathlibPlus.Open.ResearchBatch.Pullback

abbrev F2 := ZMod 2
abbrev FixtureSpace (n : ℕ) := Vec n
abbrev FixtureQuotient := Vec3

def fixtureCoordinateVector (n : ℕ) (k : Fin n) : FixtureSpace n :=
  Pi.single k 1

def fixtureCoordinateCharacter (n : ℕ) (k : Fin n) :
    FixtureSpace n →ₗ[F2] F2 :=
  LinearMap.proj k

def firstPartner (i : Fin 3) : Fin 3 :=
  if i = 0 then 1 else if i = 1 then 0 else 0

def secondPartner (i : Fin 3) : Fin 3 :=
  if i = 0 then 2 else if i = 1 then 2 else 1

def fixtureMap (n : ℕ) (h5 : 5 ≤ n) (i : Fin 3) :
    FixtureSpace n →ₗ[F2] FixtureQuotient :=
  LinearMap.pi (fun r =>
    if r = 0 then
      fixtureCoordinateCharacter n (heavyIndex n h5 (firstPartner i)) +
        fixtureCoordinateCharacter n (heavyIndex n h5 (secondPartner i))
    else if r = 1 then
      fixtureCoordinateCharacter n (index3 n h5)
    else
      fixtureCoordinateCharacter n (index4 n h5))

def fixturePairBase (n : ℕ) (h5 : 5 ≤ n) (i j : Fin 3) :
    Submodule F2 (FixtureSpace n) :=
  LinearMap.ker (fixtureCoordinateCharacter n (heavyIndex n h5 i)) ⊓
    LinearMap.ker (fixtureCoordinateCharacter n (heavyIndex n h5 j))

def fixturePairImage (n : ℕ) (h5 : 5 ≤ n) (i j : Fin 3) :
    Submodule F2 (FixtureQuotient × FixtureQuotient) :=
  LinearMap.range
    ((LinearMap.prod (fixtureMap n h5 i) (fixtureMap n h5 j)).comp
      ((fixturePairBase n h5 i j).subtype))

def fixtureDeletedPairImage (n : ℕ) (h5 : 5 ≤ n)
    (i j : Fin 3) (k : Fin n) :
    Submodule F2 (FixtureQuotient × FixtureQuotient) :=
  LinearMap.range
    ((LinearMap.prod (fixtureMap n h5 i) (fixtureMap n h5 j)).comp
      ((fixturePairBase n h5 i j ⊓
        LinearMap.ker (fixtureCoordinateCharacter n k)).subtype))

def fixtureDefectSet (n : ℕ) (h5 : 5 ≤ n) (i j : Fin 3) : Set (Fin n) :=
  {k | k ≠ heavyIndex n h5 i ∧ k ≠ heavyIndex n h5 j ∧
    fixtureDeletedPairImage n h5 i j k ≠ fixturePairImage n h5 i j}

def threeHeavyDirectionDefectSharpness_claim35148 : Prop :=
  ∀ (n : ℕ), ∀ h5 : 5 ≤ n,
    (∀ i : Fin 3, Function.Surjective (fixtureMap n h5 i)) ∧
    (∀ i : Fin 3,
      Module.finrank F2 (LinearMap.range (fixtureMap n h5 i)) = 3) ∧
    (∀ i j : Fin 3, i ≠ j →
      ∀ y : FixtureQuotient × FixtureQuotient,
        y ∈ fixturePairImage n h5 i j ↔ y.1 = y.2) ∧
    (∀ i j : Fin 3, i ≠ j →
      Module.finrank F2
          (Submodule.dualAnnihilator (fixturePairImage n h5 i j)) = 3 ∧
        Set.ncard (fixtureDefectSet n h5 i j) = 3 ∧
        Set.ncard (fixtureDefectSet n h5 i j) =
          3 + 3 - Module.finrank F2
            (Submodule.dualAnnihilator (fixturePairImage n h5 i j))) ∧
    fixtureDefectSet n h5 0 1 =
      ({heavyIndex n h5 2, index3 n h5, index4 n h5} : Set (Fin n)) ∧
    fixtureDefectSet n h5 0 2 =
      ({heavyIndex n h5 1, index3 n h5, index4 n h5} : Set (Fin n)) ∧
    fixtureDefectSet n h5 1 2 =
      ({heavyIndex n h5 0, index3 n h5, index4 n h5} : Set (Fin n)) ∧
    (∀ i : Fin 3, ∀ k : Fin n, 5 ≤ k.1 →
      fixtureMap n h5 i (fixtureCoordinateVector n k) = 0)

end
end MathlibPlus.Open.LinearAlgebra.Claim35148
