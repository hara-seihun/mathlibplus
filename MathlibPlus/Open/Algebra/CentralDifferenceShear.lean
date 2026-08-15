import Mathlib

namespace MathlibPlus.Open.Algebra.CentralDifferenceShear

abbrev E (U : Type*) (p : ℕ) := U × ZMod p

def w {U : Type*} [AddZeroClass U] (p : ℕ) : E U p := (0, 1)

def extendedLambda {p : ℕ} {U : Type*} [AddCommGroup U] [Module (ZMod p) U]
    (lam : U →ₗ[ZMod p] ZMod p) : E U p →ₗ[ZMod p] ZMod p :=
  lam.comp (LinearMap.fst (ZMod p) U (ZMod p))

def centralDifferenceShear {p : ℕ} {U : Type*} [AddCommGroup U] [Module (ZMod p) U]
    (lam : U →ₗ[ZMod p] ZMod p) (n : ZMod p → ZMod p) : Equiv.Perm (E U p) :=
  let e := Equiv.sigmaEquivProd U (ZMod p)
  (e.symm.trans (Equiv.sigmaCongrRight (fun u => Equiv.addRight (n (lam u))))).trans e

def functionModuleElement {p : ℕ} {U : Type*} [AddCommGroup U] [Module (ZMod p) U]
    (lam : U →ₗ[ZMod p] ZMod p) (u : U) (f : ZMod p → ZMod p) : Equiv.Perm (E U p) :=
  let e := Equiv.sigmaEquivProd U (ZMod p)
  (e.symm.trans
      (Equiv.sigmaCongr (Equiv.addRight u)
        (fun a => Equiv.addRight (f (lam a))))).trans e

def translation {p : ℕ} {U : Type*} [AddCommGroup U] [Module (ZMod p) U]
    (z : E U p) : Equiv.Perm (E U p) :=
  Equiv.addRight z

def centralDifferenceGamma {p : ℕ} {U : Type*} [AddCommGroup U] [Module (ZMod p) U]
    (lam : U →ₗ[ZMod p] ZMod p) : Subgroup (Equiv.Perm (E U p)) :=
  Subgroup.closure
    (Set.range (fun z : E U p => translation z) ∪
      Set.range (centralDifferenceShear lam))

abbrev functionKernel {p : ℕ} {U : Type*} [AddCommGroup U] [Module (ZMod p) U]
    (Gamma : Subgroup (Equiv.Perm (E U p)))
    (lam : U →ₗ[ZMod p] ZMod p) : Subgroup Gamma :=
  Subgroup.normalClosure
    {gamma : Gamma |
      ∃ f : ZMod p → ZMod p,
        (gamma : Equiv.Perm (E U p)) = functionModuleElement lam 0 f}

def kernelIntersection {G : Type*} [Group G]
    (R M : Subgroup G) : Subgroup R :=
  Subgroup.comap R.subtype M

def regularElementaryAbelian {p : ℕ} {U : Type*} [AddCommGroup U]
    [Module (ZMod p) U]
    (Gamma : Subgroup (Equiv.Perm (E U p))) (R : Subgroup Gamma) : Prop :=
  (∀ x y : E U p,
    ∃! r : R, (((r : Gamma) : Equiv.Perm (E U p)) x = y)) ∧
  (∀ a b : R, (a : Gamma) * (b : Gamma) = (b : Gamma) * (a : Gamma)) ∧
  (∀ a : R, (a : Gamma) ^ p = 1)

def cyclicShift {p : ℕ} (t : ZMod p) (f : ZMod p → ZMod p) : ZMod p → ZMod p :=
  fun s => f (s + t)

def wTranslationLine {p : ℕ} {U : Type*} [AddCommGroup U]
    [Module (ZMod p) U]
    (Gamma : Subgroup (Equiv.Perm (E U p))) (R : Subgroup Gamma) : Subgroup R :=
  Subgroup.closure
    {r : R |
      (((r : Gamma) : Equiv.Perm (E U p)) = translation (w p))}

def claim33143 {p : ℕ} {U : Type*} [AddCommGroup U]
    [Module (ZMod p) U]
    (hp : Nat.Prime p)
    (lam : U →ₗ[ZMod p] ZMod p) (hlam : lam ≠ 0) : Prop :=
  let Gamma := centralDifferenceGamma lam
  let M := functionKernel Gamma lam
  (extendedLambda lam (w p) = 0) ∧
  (∀ (n : ZMod p → ZMod p) (x : E U p),
    centralDifferenceShear lam n x =
      x + (n (extendedLambda lam x)) • w p) ∧
  (∀ gamma : Gamma,
    ∃! q : U × (ZMod p → ZMod p),
      (gamma : Equiv.Perm (E U p)) = functionModuleElement lam q.1 q.2) ∧
  (∀ gamma : Gamma,
    gamma ∈ M ↔
      ∃ f : ZMod p → ZMod p,
        (gamma : Equiv.Perm (E U p)) = functionModuleElement lam 0 f) ∧
  Nonempty (M ≃* Multiplicative (ZMod p → ZMod p)) ∧
  Nonempty ((Gamma ⧸ M) ≃* Multiplicative U)

def claim33144 {p : ℕ} {U : Type*} [AddCommGroup U]
    [Module (ZMod p) U]
    (hp : Nat.Prime p)
    (lam : U →ₗ[ZMod p] ZMod p) (hlam : lam ≠ 0) : Prop :=
  ∀ (u v : U) (f g : ZMod p → ZMod p),
    functionModuleElement lam u f * functionModuleElement lam v g =
      functionModuleElement lam (u + v) (g + cyclicShift (lam v) f)

def claim33145 {p : ℕ} {U : Type*} [AddCommGroup U]
    [Module (ZMod p) U]
    (hp : Nat.Prime p)
    (lam : U →ₗ[ZMod p] ZMod p) (hlam : lam ≠ 0) : Prop :=
  let Gamma := centralDifferenceGamma lam
  let M := functionKernel Gamma lam
  ∀ R : Subgroup Gamma,
    regularElementaryAbelian Gamma R →
    Nat.card R = p ^ Module.finrank (ZMod p) (E U p) →
    let N := kernelIntersection R M
    Nat.card N = p ∧
      Subgroup.map (QuotientGroup.mk' M) R = ⊤

def claim33146 {p : ℕ} {U : Type*} [AddCommGroup U]
    [Module (ZMod p) U]
    (hp : Nat.Prime p)
    (lam : U →ₗ[ZMod p] ZMod p) (hlam : lam ≠ 0) : Prop :=
  let Gamma := centralDifferenceGamma lam
  let M := functionKernel Gamma lam
  ∀ R : Subgroup Gamma,
    regularElementaryAbelian Gamma R →
    let N := kernelIntersection R M
    N = wTranslationLine Gamma R

end MathlibPlus.Open.Algebra.CentralDifferenceShear
