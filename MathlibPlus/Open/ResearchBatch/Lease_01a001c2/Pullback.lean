import Mathlib

namespace MathlibPlus.Open.ResearchBatch.Pullback

noncomputable section
open Classical

abbrev F2 := ZMod 2
abbrev Vec (n : ℕ) := Fin n → F2
abbrev Vec3 := Fin 3 → F2

def eps (n : ℕ) (i : Fin n) : Vec n :=
  fun k => if k = i then 1 else 0

def heavyIndex (n : ℕ) (h5 : 5 ≤ n) (i : Fin 3) : Fin n :=
  ⟨i.1, by omega⟩

def index3 (n : ℕ) (h5 : 5 ≤ n) : Fin n := ⟨3, by omega⟩
def index4 (n : ℕ) (h5 : 5 ≤ n) : Fin n := ⟨4, by omega⟩

def zVector (n : ℕ) (h5 : 5 ≤ n) : Vec n :=
  eps n ⟨0, by omega⟩ + eps n ⟨1, by omega⟩ + eps n ⟨2, by omega⟩

def enlargedU (n : ℕ) (h5 : 5 ≤ n) (i : Fin 3) :
    Submodule F2 (Vec n) :=
  Submodule.span F2
    {zVector n h5 + eps n (heavyIndex n h5 i),
      eps n (index3 n h5), eps n (index4 n h5)}

def enlargedA (n : ℕ) (h5 : 5 ≤ n) (i : Fin 3) :
    Submodule F2 (Vec n) :=
  Submodule.span F2
    {zVector n h5, eps n (heavyIndex n h5 i),
      eps n (index3 n h5), eps n (index4 n h5)}

def commonCenter (n : ℕ) (h5 : 5 ≤ n) : Submodule F2 (Vec n) :=
  Submodule.span F2
    {zVector n h5, eps n (index3 n h5), eps n (index4 n h5)}

def threeMap (n : ℕ) (h5 : 5 ≤ n) (i j k : Fin 3) : Vec n → Vec3 :=
  fun x => fun r => if r = 0 then x (heavyIndex n h5 j) + x (heavyIndex n h5 k)
    else if r = 1 then x (index3 n h5) else x (index4 n h5)

def pairImage (n : ℕ) (h5 : 5 ≤ n) (i j k : Fin 3) : Set (Vec3 × Vec3) :=
  {u | ∃ x : Vec n,
    x (heavyIndex n h5 i) = 0 ∧ x (heavyIndex n h5 j) = 0 ∧
      u = (threeMap n h5 i j k x, threeMap n h5 j i k x)}

def tripleImage (n : ℕ) (h5 : 5 ≤ n) : Set (Fin 3 → Vec3) :=
  {u | ∃ x : Vec n,
    x (heavyIndex n h5 0) = 0 ∧ x (heavyIndex n h5 1) = 0 ∧
      x (heavyIndex n h5 2) = 0 ∧
      u = fun _ => fun r => if r = 0 then 0 else
        if r = 1 then x (index3 n h5) else x (index4 n h5)}

def fullDiagonal : Set (Vec3 × Vec3) := {u | u.1 = u.2}
def properTriplePairDiagonal : Set (Vec3 × Vec3) :=
  {u | u.1 = u.2 ∧ u.1 0 = 0}

def claim_35141 : Prop :=
  ∀ n : ℕ, ∀ h5 : 5 ≤ n, ∀ i j : Fin 3, i ≠ j →
    enlargedA n h5 i ⊓ enlargedA n h5 j = commonCenter n h5 ∧
    commonCenter n h5 ≤ enlargedA n h5 i ∧
    enlargedU n h5 i ≤ enlargedA n h5 i

def claim_35142 : Prop :=
  ∀ n : ℕ, ∀ h5 : 5 ≤ n, ∀ i j k : Fin 3,
    i ≠ j → i ≠ k → j ≠ k →
    pairImage n h5 i j k = fullDiagonal ∧
    Set.image (fun u : Fin 3 → Vec3 => (u i, u j)) (tripleImage n h5) =
      properTriplePairDiagonal ∧
    properTriplePairDiagonal ⊂ fullDiagonal

end
end MathlibPlus.Open.ResearchBatch.Pullback
