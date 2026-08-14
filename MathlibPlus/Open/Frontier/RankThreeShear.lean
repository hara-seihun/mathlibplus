import Mathlib

namespace MathlibPlus.Open

namespace RankThreeShear

abbrev FrontierF (p : ℕ) := ZMod p
abbrev FrontierW (p : ℕ) := FrontierF p × FrontierF p
abbrev FrontierC3 := ZMod 3

structure FrontierG (p : ℕ) (ω : FrontierF p) where
  v : FrontierF p
  w : FrontierW p
  k : FrontierC3
deriving DecidableEq

def frontierMul {p : ℕ} (ω : FrontierF p) (x y : FrontierG p ω) : FrontierG p ω :=
  { v := x.v + ω ^ x.k.val * y.v
    w := (x.w.1 + ω ^ x.k.val * y.w.1,
      x.w.2 + ω ^ x.k.val * y.w.2)
    k := x.k + y.k }

instance frontierMulInstance {p : ℕ} (ω : FrontierF p) : Mul (FrontierG p ω) where
  mul := frontierMul ω

def frontierOne {p : ℕ} (ω : FrontierF p) : FrontierG p ω :=
  { v := 0
    w := (0, 0)
    k := 0 }

def frontierInv {p : ℕ} (ω : FrontierF p) (x : FrontierG p ω) : FrontierG p ω :=
  let a : FrontierF p := ω ^ (-x.k).val
  { v := -(a * x.v)
    w := (-(a * x.w.1), -(a * x.w.2))
    k := -x.k }

def frontierShear
    {p : ℕ} {ω : FrontierF p}
    (h : FrontierC3 → FrontierF p → FrontierW p)
    (x : FrontierG p ω) : FrontierG p ω :=
  { x with
    w := (x.w.1 + (h x.k x.v).1, x.w.2 + (h x.k x.v).2) }

def frontierQ
    {p : ℕ} {ω : FrontierF p}
    (h : FrontierC3 → FrontierF p → FrontierW p) :
    FrontierG p ω → FrontierG p ω :=
  frontierShear h

def FrontierAut {p : ℕ} (ω : FrontierF p) :=
  MulEquiv (FrontierG p ω) (FrontierG p ω)

def FrontierInverseClosed
    {p : ℕ} (ω : FrontierF p) (A : Set (FrontierG p ω)) : Prop :=
  ∀ x, x ∈ A → frontierInv ω x ∈ A

def FrontierCayleyConnected
    {p : ℕ} (ω : FrontierF p) (T : Set (FrontierG p ω)) : Prop :=
  ∀ x y,
    Relation.ReflTransGen
      (fun a b => frontierMul ω (frontierInv ω a) b ∈ T) x y

def claim59681 : Prop :=
  ∀ (p : ℕ), Nat.Prime p →
    ∀ (ω : FrontierF p),
    ∀ (hω : ω ^ 3 = 1), ω ≠ 1 →
      ∀ (h : FrontierC3 → FrontierF p → FrontierW p),
        h 0 0 = 0 →
          ∀ (S T : Set (FrontierG p ω)),
            FrontierInverseClosed ω S →
            frontierOne ω ∉ S →
            FrontierInverseClosed ω T →
            frontierOne ω ∉ T →
            (∀ x y,
              frontierMul ω (frontierInv ω x) y ∈ S ↔
                frontierMul ω
                  (frontierInv ω (frontierQ h x))
                  (frontierQ h y) ∈ T) →
            FrontierCayleyConnected ω T →
            (∀ α : FrontierAut ω,
              Set.image α.toEquiv S ≠ T) →
            T.ncard ≥ p + 1

end RankThreeShear

end MathlibPlus.Open
