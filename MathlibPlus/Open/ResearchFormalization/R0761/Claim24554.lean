import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R0761

abbrev BaseV := Multiplicative (ZMod 3 × ZMod 3)
abbrev C2 := Multiplicative (ZMod 2)
abbrev Cp (p : ℕ) := Multiplicative (ZMod p)
abbrev LiftKernel (p : ℕ) := BaseV × Cp p
abbrev LiftGroup (p : ℕ) (φ : C2 →* MulAut (LiftKernel p)) :=
  LiftKernel p ⋊[φ] C2

def baseE₁ : BaseV := Multiplicative.ofAdd (1, 0)
def baseE₂ : BaseV := Multiplicative.ofAdd (0, 1)
def baseV : BaseV := baseE₁ * baseE₂
def baseB : Set BaseV := {1, baseE₁, baseE₂}
def baseW : Set BaseV := (Set.univ : Set BaseV) \ baseB

def liftRot {p : ℕ} {φ : C2 →* MulAut (LiftKernel p)}
    (a : LiftKernel p) : LiftGroup p φ :=
  ⟨a, 1⟩

def liftReflectionGenerator {p : ℕ}
    {φ : C2 →* MulAut (LiftKernel p)} : LiftGroup p φ :=
  ⟨1, Multiplicative.ofAdd 1⟩

def liftPOne (p : ℕ) : Cp p := Multiplicative.ofAdd 1

def liftReflectionLayer {p : ℕ}
    {φ : C2 →* MulAut (LiftKernel p)}
    (U : Set (LiftKernel p)) : Set (LiftGroup p φ) :=
  Set.image2 (fun a b : LiftGroup p φ => a * b)
    (liftRot '' U) ({liftReflectionGenerator} : Set (LiftGroup p φ))

def liftedBLayer {p : ℕ} : Set (LiftKernel p) :=
  (fun b : BaseV => (b, 1)) '' baseB

def liftedWLayer {p : ℕ} : Set (LiftKernel p) :=
  (fun w : BaseV => (w, liftPOne p)) '' baseW

def liftedS {p : ℕ} {φ : C2 →* MulAut (LiftKernel p)} :
    Set (LiftGroup p φ) :=
  {liftRot (baseV, liftPOne p),
      liftRot (baseV⁻¹, (liftPOne p)⁻¹)} ∪
    liftReflectionLayer liftedBLayer ∪
      liftReflectionLayer liftedWLayer

def liftedT {p : ℕ} {φ : C2 →* MulAut (LiftKernel p)} :
    Set (LiftGroup p φ) :=
  {liftRot (baseV⁻¹, liftPOne p),
      liftRot (baseV, (liftPOne p)⁻¹)} ∪
    liftReflectionLayer liftedBLayer ∪
      liftReflectionLayer liftedWLayer

def liftAnchorElement {p : ℕ}
    {φ : C2 →* MulAut (LiftKernel p)}
    (a : BaseV) (z : Cp p) : LiftGroup p φ :=
  liftRot (a, z) * liftReflectionGenerator

def liftAnchor {p : ℕ} {φ : C2 →* MulAut (LiftKernel p)}
    (w : BaseV) : Set (LiftGroup p φ) :=
  {liftReflectionGenerator,
      liftAnchorElement baseE₁ 1,
      liftAnchorElement baseE₂ 1,
      liftAnchorElement w (liftPOne p)}

/-- The valency-eleven lift has an explicit generating anchor, so both of its
 displayed Cayley graphs are connected. -/
def liftedValencyElevenWitnessConnected_claim24554 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 5 ≤ p →
    ∀ (φ : C2 →* MulAut (LiftKernel p)),
      (∀ a : LiftKernel p,
        φ (Multiplicative.ofAdd 1) a = a⁻¹) →
        Set.ncard (liftedS (p := p) (φ := φ)) = 11 ∧
          Set.ncard (liftedT (p := p) (φ := φ)) = 11 ∧
          ∃ w : BaseV,
            w ∈ baseW ∧
              liftPOne p ≠ (1 : Cp p) ∧
                liftAnchor (φ := φ) w ⊆ liftedS (p := p) ∧
                  liftAnchor (φ := φ) w ⊆ liftedT (p := p) ∧
                    Subgroup.closure (liftAnchor (φ := φ) w) = ⊤ ∧
                      Subgroup.closure (liftedS (p := p) (φ := φ)) = ⊤ ∧
                        Subgroup.closure (liftedT (p := p) (φ := φ)) = ⊤

end MathlibPlus.Open.ResearchFormalization.R0761
