import Mathlib

namespace MathlibPlus.Open.Research.NonlinearShear

noncomputable section

abbrev V (p : ℕ) := Fin 6 → ZMod p

def setCoord {α : Type*} [DecidableEq α] (x : α → ZMod p) (i : α)
    (v : ZMod p) : α → ZMod p :=
  Function.update x i v

def coord (i : Fin 6) (x : V p) : ZMod p := x i

def gFunction (x : V p) : V p :=
  setCoord (setCoord x 1 (coord 1 x + coord 0 x)) 2 (coord 2 x + coord 1 x)

def gInverseFunction (x : V p) : V p :=
  setCoord (setCoord x 1 (coord 1 x - coord 0 x)) 2
    (coord 2 x - coord 1 x + coord 0 x)

def half (p : ℕ) (hp : Nat.Prime p) : ZMod p :=
  letI : Fact p.Prime := ⟨hp⟩
  (2 : ZMod p)⁻¹

def hFunction (p : ℕ) (x : V p) : V p :=
  setCoord (setCoord x 2 (coord 2 x + coord 0 x + coord 4 x)) 5
    (coord 5 x + coord 0 x)

def hInverseFunction (x : V p) : V p :=
  setCoord (setCoord x 2 (coord 2 x - coord 0 x - coord 4 x)) 5
    (coord 5 x - coord 0 x)

def tFunction (p : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (x : V p) : V p :=
  setCoord (setCoord x 3 (coord 3 x + coord 4 x)) 2
    (coord 2 x + coord 3 x + coord 4 x * half p hp)

def tInverseFunction (p : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (x : V p) : V p :=
  setCoord (setCoord x 3 (coord 3 x - coord 4 x)) 2
    (coord 2 x - coord 3 x + coord 4 x * half p hp)

def sdFunction (x : V p) : V p :=
  setCoord x 5 (coord 5 x + coord 3 x)

def sdInverseFunction (x : V p) : V p :=
  setCoord x 5 (coord 5 x - coord 3 x)

def seFunction (x : V p) : V p :=
  setCoord x 5 (coord 5 x + coord 4 x)

def seInverseFunction (x : V p) : V p :=
  setCoord x 5 (coord 5 x - coord 4 x)

def permOfInverse {α : Type*} (f g : α → α)
    (hfg : ∀ x, f (g x) = x) (hgf : ∀ x, g (f x) = x) : Equiv.Perm α :=
  { toFun := f
    invFun := g
    left_inv := hgf
    right_inv := hfg }

def G (p : ℕ) : Equiv.Perm (V p) :=
  permOfInverse gFunction gInverseFunction
    (by intro x; funext i; fin_cases i <;> simp [gFunction, gInverseFunction, setCoord, coord] <;> ring)
    (by intro x; funext i; fin_cases i <;> simp [gFunction, gInverseFunction, setCoord, coord] <;> ring)

def H (p : ℕ) : Equiv.Perm (V p) :=
  permOfInverse (hFunction p) hInverseFunction
    (by intro x; funext i; fin_cases i <;> simp [hFunction, hInverseFunction, setCoord, coord] <;> ring)
    (by intro x; funext i; fin_cases i <;> simp [hFunction, hInverseFunction, setCoord, coord] <;> ring)

def twoNeZero (p : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hd : (p : ℤ) ∣ (2 : ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (2 : ℤ) p).mp
    exact_mod_cast h
  have hp_le : p ≤ 2 := by
    have hd' : p ∣ 2 := by exact_mod_cast hd
    exact Nat.le_of_dvd (by omega) hd'
  omega

def T (p : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) : Equiv.Perm (V p) :=
  permOfInverse (tFunction p hp h5) (tInverseFunction p hp h5)
    (by
      letI : Fact p.Prime := ⟨hp⟩
      intro x; funext i
      fin_cases i <;>
        simp [tFunction, tInverseFunction, setCoord, coord, half] <;>
        field_simp [twoNeZero p hp h5] <;> ring)
    (by
      letI : Fact p.Prime := ⟨hp⟩
      intro x; funext i
      fin_cases i <;>
        simp [tFunction, tInverseFunction, setCoord, coord, half] <;>
        field_simp [twoNeZero p hp h5] <;> ring)

def Sd (p : ℕ) : Equiv.Perm (V p) :=
  permOfInverse sdFunction sdInverseFunction
    (by intro x; funext i; fin_cases i <;> simp [sdFunction, sdInverseFunction, setCoord, coord] <;> ring)
    (by intro x; funext i; fin_cases i <;> simp [sdFunction, sdInverseFunction, setCoord, coord] <;> ring)

def Se (p : ℕ) : Equiv.Perm (V p) :=
  permOfInverse seFunction seInverseFunction
    (by intro x; funext i; fin_cases i <;> simp [seFunction, seInverseFunction, setCoord, coord] <;> ring)
    (by intro x; funext i; fin_cases i <;> simp [seFunction, seInverseFunction, setCoord, coord] <;> ring)

def pointGroup (p : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) : Subgroup (Equiv.Perm (V p)) :=
  Subgroup.closure
    ({G p, H p, T p hp h5, Sd p, Se p} : Set (Equiv.Perm (V p)))

def seed (j : Fin 6) : V p := Pi.single j 1

def pointOrbit (p : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (x : V p) : Set (V p) :=
  {y | ∃ g : pointGroup p hp h5, (g : Equiv.Perm (V p)) x = y}

def negSet (S : Set (V p)) : Set (V p) :=
  {x | ∃ y ∈ S, x = -y}

def connectionSet (p : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) : Set (V p) :=
  ⋃ j : Fin 6, pointOrbit p hp h5 (seed j) ∪ negSet (pointOrbit p hp h5 (seed j))

def cayleyGraph (p : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) : SimpleGraph (V p) :=
  SimpleGraph.fromRel (fun x y => y - x ∈ connectionSet p hp h5)

def inverseClosed (S : Set (V p)) : Prop :=
  ∀ x, x ∈ S ↔ -x ∈ S

def additivePeriod (S : Set (V p)) : Set (V p) :=
  {r | ∀ x, x + r ∈ S ↔ x ∈ S}

def additiveRadical (S : Set (V p)) : Set (V p) :=
  additivePeriod S

def lambda (x : V p) : ZMod p := coord 0 x + coord 4 x

def shearVector : V p := Pi.single 2 1 + Pi.single 5 1

def quadratic (p : ℕ) (hp : Nat.Prime p) (s : ZMod p) : ZMod p :=
  letI : Fact p.Prime := ⟨hp⟩
  s * (s - 1) / 2

def shear (p : ℕ) (hp : Nat.Prime p) : V p → V p :=
  fun x => x + quadratic p hp (lambda x) • shearVector

def shearDifference (p : ℕ) (hp : Nat.Prime p) (x h : V p) : V p :=
  shear p hp (x + h) - shear p hp x

def cayleyAdjacency (p : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (x y : V p) : Prop :=
  (cayleyGraph p hp h5).Adj x y

/-- Exact formal alignment of the explicit six-orbit inverse-closed Cayley control. -/
def claim50469 : Prop :=
  ∀ p : ℕ, (hp : Nat.Prime p) → (h5 : 5 ≤ p) →
    inverseClosed (connectionSet p hp h5) ∧
    (∀ j : Fin 6, seed j ∈ connectionSet p hp h5) ∧
    ∀ x y : V p, cayleyAdjacency p hp h5 x y ↔
      x ≠ y ∧ y - x ∈ connectionSet p hp h5

/-- Exact formal alignment of the nonlinear shear and its selected orbit action. -/
def claim50470 : Prop :=
  ∀ p : ℕ, (hp : Nat.Prime p) → (h5 : 5 ≤ p) →
    lambda (p := p) shearVector = 0 ∧
    Function.Bijective (shear p hp) ∧
    shear p hp 0 = 0 ∧
    (∀ x h : V p,
      shearDifference p hp x h =
        h + (quadratic p hp (lambda x + lambda h) -
          quadratic p hp (lambda x)) • shearVector) ∧
    (H p * Se p) ∈ pointGroup p hp h5 ∧
    (∀ h : V p, (H p * Se p) h = h + lambda h • shearVector) ∧
    (∀ x h : V p, lambda h = 0 → shearDifference p hp x h = h) ∧
    (∀ x h : V p, lambda h ≠ 0 →
      shearDifference p hp x h ∈ pointOrbit p hp h5 h)

/-- Exact formal alignment of connectedness and the trivial translation radical. -/
def claim50471 : Prop :=
  ∀ p : ℕ, (hp : Nat.Prime p) → (h5 : 5 ≤ p) →
    LinearIndependent (ZMod p) (seed : Fin 6 → V p) ∧
    (cayleyGraph p hp h5).Connected ∧
    Set.image (fun x : V p => (coord 0 x, coord 4 x))
        (connectionSet p hp h5) =
      ({(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)} : Set (ZMod p × ZMod p)) ∧
    additiveRadical (connectionSet p hp h5) = ({0} : Set (V p))

/-- Exact formal alignment of the displayed nonlinearity witness. -/
def claim50472 : Prop :=
  ∀ p : ℕ, (hp : Nat.Prime p) → (h5 : 5 ≤ p) →
    shear p hp (seed 0) = seed 0 ∧
    shear p hp (2 • seed 0) = 2 • seed 0 + seed 2 + seed 5 ∧
    shear p hp (2 • seed 0) ≠ 2 • shear p hp (seed 0) ∧
    ¬ (∀ x y : V p, shear p hp (x + y) = shear p hp x + shear p hp y)

/-- Exact formal alignment of the resulting nonlinear zero-fixing graph symmetry. -/
def claim50473 : Prop :=
  ∀ p : ℕ, (hp : Nat.Prime p) → (h5 : 5 ≤ p) →
    shear p hp 0 = 0 ∧
    Function.Bijective (shear p hp) ∧
    (∀ x y : V p,
      cayleyAdjacency p hp h5 (shear p hp x) (shear p hp y) ↔
        cayleyAdjacency p hp h5 x y) ∧
    (∀ j : Fin 6,
      shear p hp '' pointOrbit p hp h5 (seed j) = pointOrbit p hp h5 (seed j)) ∧
    ¬ (∀ x y : V p, shear p hp (x + y) = shear p hp x + shear p hp y)

end
end MathlibPlus.Open.Research.NonlinearShear
