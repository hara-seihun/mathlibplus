import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1817

noncomputable section

abbrev claim32559_Field (p : ℕ) := ZMod p
abbrev claim32559_Plane (p : ℕ) := claim32559_Field p × claim32559_Field p
abbrev claim32559_Functions (p : ℕ) := claim32559_Field p → claim32559_Field p

def claim32559_shear (p : ℕ) (f : claim32559_Functions p) :
    Equiv.Perm (claim32559_Plane p) :=
  let F := claim32559_Field p
  let e := Equiv.sigmaEquivProd F F
  let s := (e.symm.trans (Equiv.sigmaCongrRight (fun x => Equiv.addRight (f x)))).trans e
  (Equiv.prodComm F F).trans (s.trans (Equiv.prodComm F F).symm)

def claim32559_translationGroup (p : ℕ) :
    Subgroup (Equiv.Perm (claim32559_Plane p)) :=
  Subgroup.closure
    (Set.range (Equiv.addRight : claim32559_Plane p → Equiv.Perm (claim32559_Plane p)))

def claim32559_conjugateGroup (p : ℕ) (f : claim32559_Functions p) :
    Subgroup (Equiv.Perm (claim32559_Plane p)) :=
  Subgroup.map (MulAut.conj (claim32559_shear p f)⁻¹)
    (claim32559_translationGroup p)

def claim32559_generatedGroup (p : ℕ) (f : claim32559_Functions p) :
    Subgroup (Equiv.Perm (claim32559_Plane p)) :=
  Subgroup.closure
    ((claim32559_translationGroup p : Set (Equiv.Perm (claim32559_Plane p))) ∪
      (claim32559_conjugateGroup p f : Set (Equiv.Perm (claim32559_Plane p))))

def claim32559_shift (p : ℕ) (a : claim32559_Field p)
    (h : claim32559_Functions p) : claim32559_Functions p :=
  fun x => h (x + a)

def claim32559_difference (p : ℕ) (h : claim32559_Functions p) : claim32559_Functions p :=
  claim32559_shift p 1 h - h

def claim32559_shiftLinear (p : ℕ) (a : claim32559_Field p) :
    claim32559_Functions p →ₗ[claim32559_Field p] claim32559_Functions p :=
  LinearMap.pi (fun x : claim32559_Field p =>
    LinearMap.proj (R := claim32559_Field p)
      (φ := fun _ : claim32559_Field p => claim32559_Field p) (x + a))

def claim32559_differenceLinear (p : ℕ) :
    claim32559_Functions p →ₗ[claim32559_Field p] claim32559_Functions p :=
  claim32559_shiftLinear p 1 - LinearMap.id

def claim32559_leastPositiveExponent (p : ℕ)
    (f : claim32559_Functions p) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ ((claim32559_differenceLinear p) ^ n) f = 0}

def claim32559_depth (p : ℕ) (f : claim32559_Functions p) : ℕ :=
  @ite ℕ (f = 0) (Classical.propDecidable (f = 0))
    1 (claim32559_leastPositiveExponent p f - 1)

def claim32559_module (p : ℕ) (f : claim32559_Functions p) :
    Submodule (claim32559_Field p) (claim32559_Functions p) :=
  LinearMap.ker ((claim32559_differenceLinear p) ^ claim32559_depth p f)

def claim32559_functionPermutation (p : ℕ)
    (m : claim32559_Functions p) : Equiv.Perm (claim32559_Plane p) :=
  claim32559_shear p m

def claim32559_baseTranslation (p : ℕ)
    (b : claim32559_Field p) : Equiv.Perm (claim32559_Plane p) :=
  Equiv.prodCongr (Equiv.refl (claim32559_Field p)) (Equiv.addRight b)

def claim32559_affinePermutation (p : ℕ)
    (m : claim32559_Functions p) (b : claim32559_Field p) :
    Equiv.Perm (claim32559_Plane p) :=
  (claim32559_functionPermutation p m).trans (claim32559_baseTranslation p b)

def claim_32559 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → p % 2 = 1 →
    ∀ (f : claim32559_Functions p), f 0 = 0 →
      (∀ m b z x,
        claim32559_affinePermutation p m b (z, x) = (z + m x, x + b)) ∧
      (∀ g : Equiv.Perm (claim32559_Plane p),
        g ∈ claim32559_generatedGroup p f →
          ∃! u : claim32559_Functions p × claim32559_Field p,
            u.1 ∈ claim32559_module p f ∧
              g = claim32559_affinePermutation p u.1 u.2) ∧
      (∀ m : claim32559_Functions p, m ∈ claim32559_module p f →
        ∀ b : claim32559_Field p,
          claim32559_affinePermutation p m b ∈ claim32559_generatedGroup p f) ∧
      (∀ b : claim32559_Field p, ∀ m : claim32559_Functions p,
        (claim32559_baseTranslation p b)⁻¹ *
            claim32559_functionPermutation p m * claim32559_baseTranslation p b =
          claim32559_functionPermutation p (claim32559_shift p b m))

end

end MathlibPlus.Open.ResearchFormalization.R1817
