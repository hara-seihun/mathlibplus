import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1817

abbrev claim32556_Field (p : ℕ) := ZMod p
abbrev claim32556_Plane (p : ℕ) := claim32556_Field p × claim32556_Field p
abbrev claim32556_Functions (p : ℕ) := claim32556_Field p → claim32556_Field p

def claim32556_shear (p : ℕ) (f : claim32556_Functions p) :
    Equiv.Perm (claim32556_Plane p) :=
  let F := claim32556_Field p
  let e := Equiv.sigmaEquivProd F F
  let s := (e.symm.trans (Equiv.sigmaCongrRight (fun x => Equiv.addRight (f x)))).trans e
  (Equiv.prodComm F F).trans (s.trans (Equiv.prodComm F F).symm)

def claim32556_translationGroup (p : ℕ) :
    Subgroup (Equiv.Perm (claim32556_Plane p)) :=
  Subgroup.closure (Set.range (Equiv.addRight : claim32556_Plane p → Equiv.Perm (claim32556_Plane p)))

def claim32556_conjugateGroup (p : ℕ) (f : claim32556_Functions p) :
    Subgroup (Equiv.Perm (claim32556_Plane p)) :=
  Subgroup.map (MulAut.conj (claim32556_shear p f)⁻¹)
    (claim32556_translationGroup p)

def claim32556_generatedGroup (p : ℕ) (f : claim32556_Functions p) :
    Subgroup (Equiv.Perm (claim32556_Plane p)) :=
  Subgroup.closure
    ((claim32556_translationGroup p : Set (Equiv.Perm (claim32556_Plane p))) ∪
      (claim32556_conjugateGroup p f : Set (Equiv.Perm (claim32556_Plane p))))

def claim32556_shift (p : ℕ) (a : claim32556_Field p)
    (h : claim32556_Functions p) : claim32556_Functions p :=
  fun x => h (x + a)

def claim32556_difference (p : ℕ) (h : claim32556_Functions p) : claim32556_Functions p :=
  claim32556_shift p 1 h - h

def claim_32556 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → p % 2 = 1 →
    ∀ (f : claim32556_Functions p), f 0 = 0 →
      (∀ z x, claim32556_shear p f (z, x) = (z + f x, x)) ∧
      (∀ g : Equiv.Perm (claim32556_Plane p),
        g ∈ claim32556_conjugateGroup p f ↔
          ∃ r : Equiv.Perm (claim32556_Plane p),
            r ∈ claim32556_translationGroup p ∧
              g = (claim32556_shear p f)⁻¹ * r * claim32556_shear p f) ∧
      claim32556_generatedGroup p f =
        Subgroup.closure
          ((claim32556_translationGroup p : Set (Equiv.Perm (claim32556_Plane p))) ∪
            (claim32556_conjugateGroup p f : Set (Equiv.Perm (claim32556_Plane p)))) ∧
      (∀ a h x, claim32556_shift p a h x = h (x + a)) ∧
      (∀ h x, claim32556_difference p h x = claim32556_shift p 1 h x - h x)

end MathlibPlus.Open.ResearchFormalization.R1817
