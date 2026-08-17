import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1817

noncomputable section

abbrev claim32558_Field (p : ℕ) := ZMod p
abbrev claim32558_Plane (p : ℕ) := claim32558_Field p × claim32558_Field p
abbrev claim32558_Functions (p : ℕ) := claim32558_Field p → claim32558_Field p

def claim32558_shear (p : ℕ) (f : claim32558_Functions p) :
    Equiv.Perm (claim32558_Plane p) :=
  let F := claim32558_Field p
  let e := Equiv.sigmaEquivProd F F
  let s := (e.symm.trans (Equiv.sigmaCongrRight (fun x => Equiv.addRight (f x)))).trans e
  (Equiv.prodComm F F).trans (s.trans (Equiv.prodComm F F).symm)

def claim32558_translationGroup (p : ℕ) :
    Subgroup (Equiv.Perm (claim32558_Plane p)) :=
  Subgroup.closure
    (Set.range (Equiv.addRight : claim32558_Plane p → Equiv.Perm (claim32558_Plane p)))

def claim32558_conjugateGroup (p : ℕ) (f : claim32558_Functions p) :
    Subgroup (Equiv.Perm (claim32558_Plane p)) :=
  Subgroup.map (MulAut.conj (claim32558_shear p f)⁻¹)
    (claim32558_translationGroup p)

def claim32558_generatedGroup (p : ℕ) (f : claim32558_Functions p) :
    Subgroup (Equiv.Perm (claim32558_Plane p)) :=
  Subgroup.closure
    ((claim32558_translationGroup p : Set (Equiv.Perm (claim32558_Plane p))) ∪
      (claim32558_conjugateGroup p f : Set (Equiv.Perm (claim32558_Plane p))))

def claim32558_shift (p : ℕ) (a : claim32558_Field p)
    (h : claim32558_Functions p) : claim32558_Functions p :=
  fun x => h (x + a)

def claim32558_difference (p : ℕ) (h : claim32558_Functions p) : claim32558_Functions p :=
  claim32558_shift p 1 h - h

def claim32558_shiftLinear (p : ℕ) (a : claim32558_Field p) :
    claim32558_Functions p →ₗ[claim32558_Field p] claim32558_Functions p :=
  LinearMap.pi (fun x : claim32558_Field p =>
    LinearMap.proj (R := claim32558_Field p)
      (φ := fun _ : claim32558_Field p => claim32558_Field p) (x + a))

def claim32558_differenceLinear (p : ℕ) :
    claim32558_Functions p →ₗ[claim32558_Field p] claim32558_Functions p :=
  claim32558_shiftLinear p 1 - LinearMap.id

def claim32558_leastPositiveExponent (p : ℕ)
    (f : claim32558_Functions p) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ ((claim32558_differenceLinear p) ^ n) f = 0}

def claim32558_depth (p : ℕ) (f : claim32558_Functions p) : ℕ :=
  @ite ℕ (f = 0) (Classical.propDecidable (f = 0))
    1 (claim32558_leastPositiveExponent p f - 1)

def claim32558_module (p : ℕ) (f : claim32558_Functions p) :
    Submodule (claim32558_Field p) (claim32558_Functions p) :=
  LinearMap.ker ((claim32558_differenceLinear p) ^ claim32558_depth p f)

def claim32558_constantFunction (p : ℕ)
    (c : claim32558_Field p) : claim32558_Functions p :=
  fun _ => c

def claim32558_differenceGenerator (p : ℕ)
    (f : claim32558_Functions p) (u w : claim32558_Field p) :
    claim32558_Functions p :=
  claim32558_shift p w (claim32558_shift p u f - f)

def claim32558_generatedFunctionModule (p : ℕ) (f : claim32558_Functions p) :
    Submodule (claim32558_Field p) (claim32558_Functions p) :=
  Submodule.span (claim32558_Field p)
    (Set.range (claim32558_constantFunction p) ∪
      Set.range (fun uw : claim32558_Field p × claim32558_Field p =>
        claim32558_differenceGenerator p f uw.1 uw.2))

def claim_32558 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → p % 2 = 1 →
    ∀ (f : claim32558_Functions p), f 0 = 0 →
      claim32558_generatedFunctionModule p f = claim32558_module p f

end

end MathlibPlus.Open.ResearchFormalization.R1817
