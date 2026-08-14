import Mathlib

namespace MathlibPlus.Open.NR2.HardLefschetz

/-- Claim 7908: the hard-Lefschetz Clifford action in the polarized basis. -/
def claim7908 : Prop :=
  ∀ k : ℕ,
    let V := Fin (k + 1) → ℂ
    let H : V → V := fun v i => ((k : ℂ) - 2 * (i.1 : ℂ)) * v i
    let J : V → V := fun v i => v (Fin.rev i)
    let comp : (V → V) → (V → V) → (V → V) := fun f g v => f (g v)
    let Xact : V → V := J
    let Zact : V → V := H
    let Yact : V → V := fun v => -J (H v)
    let cact : V → V := fun v => H (H v)
    comp J H = -comp H J ∧ Xact = J ∧ Zact = H ∧
      Yact = -comp J H ∧ cact = comp H H

/-- Claim 7909: row-vectorization turns the four actions into the four boundary states. -/
def claim7909 : Prop :=
  ∀ k : ℕ,
    let V := Fin (k + 1) → ℂ
    let M := Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ
    let e : ∀ j : Fin (k + 1), V := fun j i => if i = j then 1 else 0
    let H : V → V := fun v i => ((k : ℂ) - 2 * (i.1 : ℂ)) * v i
    let J : V → V := fun v i => v (Fin.rev i)
    let opMatrix : (V → V) → M := fun A i j => A (e j) i
    let w : Fin (k + 1) → ℤ := fun i => (k : ℤ) - 2 * (i.1 : ℤ)
    let pI : M := fun a b => if a = b then 1 else 0
    let pX : M := fun a b => if a.1 + b.1 = k then 1 else 0
    let pZ : M := fun a b => if a = b then (w a : ℂ) else 0
    let pY : M := fun a b => if a.1 + b.1 = k then -(w b : ℂ) else 0
    opMatrix (fun v => v) = pI ∧ opMatrix J = pX ∧
      opMatrix H = pZ ∧ opMatrix (fun v => -J (H v)) = pY

/-- Claim 7910: the Green operator is the inverse on nonzero weights and vanishes on the kernel. -/
def claim7910 : Prop :=
  ∀ k : ℕ,
    let V := Fin (k + 1) → ℂ
    let w : Fin (k + 1) → ℤ := fun i => (k : ℤ) - 2 * (i.1 : ℤ)
    let H : V → V := fun v i => (w i : ℂ) * v i
    let G : V → V := fun v i =>
      if w i = 0 then 0 else ((w i : ℂ)⁻¹) * v i
    let e : ∀ j : Fin (k + 1), V := fun j i => if i = j then 1 else 0
    (∀ i, w i ≠ 0 → G (H (e i)) = e i) ∧
      (∀ i, w i = 0 → G (H (e i)) = 0) ∧
      (Even k → ∀ v, H v = 0 →
        v = v (⟨k / 2, by omega⟩ : Fin (k + 1)) •
          e (⟨k / 2, by omega⟩ : Fin (k + 1))) ∧
      (Odd k → ∀ v, H v = 0 → v = 0)

/-- Claim 7911: the common zero-weight boundary state. -/
def claim7911 : Prop :=
  ∀ k : ℕ,
    let M := Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ
    let v : M := if Even k then
      (fun a b => if a = (⟨k / 2, by omega⟩ : Fin (k + 1)) ∧
          b = (⟨k / 2, by omega⟩ : Fin (k + 1)) then 1 else 0)
      else 0
    (Odd k → v = 0) ∧
      (Even k → v (⟨k / 2, by omega⟩ : Fin (k + 1))
          (⟨k / 2, by omega⟩ : Fin (k + 1)) = 1) ∧
      (∀ a b, v a b ≠ 0 → a = b ∧ a.1 + b.1 = k)

/-- Claim 7912: Green integration of the two weighted boundary states. -/
def claim7912 : Prop :=
  ∀ k : ℕ,
    let M := Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ
    let w : Fin (k + 1) → ℤ := fun i => (k : ℤ) - 2 * (i.1 : ℤ)
    let pI : M := fun a b => if a = b then 1 else 0
    let pX : M := fun a b => if a.1 + b.1 = k then 1 else 0
    let pZ : M := fun a b => if a = b then (w a : ℂ) else 0
    let pY : M := fun a b => if a.1 + b.1 = k then -(w b : ℂ) else 0
    let v : M := if Even k then
      (fun a b => if a = (⟨k / 2, by omega⟩ : Fin (k + 1)) ∧
          b = (⟨k / 2, by omega⟩ : Fin (k + 1)) then 1 else 0)
      else 0
    let Gleft : M → M := fun A a b =>
      if w a = 0 then 0 else ((w a : ℂ)⁻¹) * A a b
    Gleft pZ = pI - v ∧ Gleft pY = pX - v

/-- Claim 7915: torus evaluation recovers the full doubled alignment current. -/
def claim7915 : Prop :=
  ∀ k : ℕ, ∀ y α : ℂˣ,
    let Midx := Fin (k + 1) × Fin (k + 1)
    let W := Midx → ℂ
    let cell : Midx → W := fun p q => if p = q then 1 else 0
    let Qeq : W → W := fun v p => if p.1 = p.2 then v p else 0
    let Qopp : W → W := fun v p =>
      if p.1.val + p.2.val = k then v p else 0
    let weight : Midx → ℂ := fun p =>
      (((y ^ ((k : ℤ) - 2 * (p.1.val : ℤ)) : ℂˣ) : ℂ) *
        ((α ^ ((k : ℤ) - 2 * (p.2.val : ℤ)) : ℂˣ) : ℂ))
    let trace : (W → W) → ℂ := fun op =>
      ∑ p : Midx, op (cell p) p * weight p
    let record13 : ℂ := trace Qeq ^ 2 - trace Qopp ^ 2
    record13 =
      (∑ i : Fin (k + 1),
        (((((y * α) ^ ((k : ℤ) - 2 * (i.1 : ℤ))) : ℂˣ) : ℂ))) ^ 2 -
      (∑ i : Fin (k + 1),
        (((((y / α) ^ ((k : ℤ) - 2 * (i.1 : ℤ))) : ℂˣ) : ℂ))) ^ 2

end MathlibPlus.Open.NR2.HardLefschetz
