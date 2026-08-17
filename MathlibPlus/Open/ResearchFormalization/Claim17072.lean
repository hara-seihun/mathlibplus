import Mathlib
import MathlibPlus.Open.FormalizationBatch
import MathlibPlus.Open.Algebra.TransportBatch

namespace MathlibPlus.Open.ResearchFormalization

open MathlibPlus.Open.FormalizationBatch
open MathlibPlus.Open.Algebra.FormalizationBatch

abbrev V8 := Fin 8
abbrev E8 := Edge V8
abbrev Γ8 := GammaVertex V8

def edgeContains (a b : V8) (e : E8) : Prop :=
  a ∈ e.1 ∧ b ∈ e.1

def redProjection (e : E8) : Prop :=
  edgeContains 0 1 e ∨ edgeContains 2 3 e

def blueProjection (e : E8) : Prop :=
  edgeContains 0 3 e ∨ edgeContains 1 2 e

def fixed02Projection (e : E8) : Prop := edgeContains 0 2 e

def fixed13Projection (e : E8) : Prop := edgeContains 1 3 e

def outsideCompleteProjection (e : E8) : Prop :=
  ∃ a b : V8, 4 ≤ a ∧ 4 ≤ b ∧ a < b ∧ edgeContains a b e

def evenOutsideProjection (e : E8) : Prop :=
  ∃ a b : V8, (a = 0 ∨ a = 2) ∧ 4 ≤ b ∧ edgeContains a b e

def oddOutsideProjection (e : E8) : Prop :=
  ∃ a b : V8, (a = 1 ∨ a = 3) ∧ 4 ≤ b ∧ edgeContains a b e

def componentHasLeftProjection
    (π : PointedLocalPermutations V8) (c : Γ8) (p : E8 → Prop) : Prop :=
  ∀ e : E8, GammaConnected π (Sum.inl e) c ↔ p e

def componentHasRightProjection
    (π : PointedLocalPermutations V8) (c : Γ8) (p : E8 → Prop) : Prop :=
  ∀ e : E8, GammaConnected π (Sum.inr e) c ↔ p e

def exactAlternatingSquareRegime
    (π : PointedLocalPermutations V8) : Prop :=
  ∃ (cR cS c02 c13 c45 cEven cOdd : Γ8),
    componentHasLeftProjection π cR redProjection ∧
      componentHasRightProjection π cR blueProjection ∧
      componentHasLeftProjection π cS blueProjection ∧
      componentHasRightProjection π cS redProjection ∧
      componentHasLeftProjection π c02 fixed02Projection ∧
      componentHasRightProjection π c02 fixed02Projection ∧
      componentHasLeftProjection π c13 fixed13Projection ∧
      componentHasRightProjection π c13 fixed13Projection ∧
      componentHasLeftProjection π c45 outsideCompleteProjection ∧
      componentHasRightProjection π c45 outsideCompleteProjection ∧
      componentHasLeftProjection π cEven evenOutsideProjection ∧
      componentHasRightProjection π cEven evenOutsideProjection ∧
      componentHasLeftProjection π cOdd oddOutsideProjection ∧
      componentHasRightProjection π cOdd oddOutsideProjection ∧
      ∀ u : Γ8,
        GammaConnected π u cR ∨ GammaConnected π u cS ∨
          GammaConnected π u c02 ∨ GammaConnected π u c13 ∨
            GammaConnected π u c45 ∨ GammaConnected π u cEven ∨
              GammaConnected π u cOdd

def globalPairing
    (π : PointedLocalPermutations V8) (σ : Equiv.Perm V8) : Prop :=
  ∀ e : E8,
    GammaConnected π (Sum.inl e) (Sum.inr (edgeImage σ e))

def involutiveFixedIndexCocycle
    (π : PointedLocalPermutations V8) : Prop :=
  ∀ i : V8, Function.Involutive (π.1 i)

def tableFamily (π : PointedLocalPermutations V8) : Prop :=
  ∀ i x : V8, π.1 i x = explicitTransportTables i x

/-- Claim 17072: an exact alternating-square witness glues every prescribed
map while every prescribed map lies outside its transport subgroup. -/
def claim17072_transportMembershipNotNecessary : Prop :=
  ∃ π : PointedLocalPermutations V8,
    involutiveFixedIndexCocycle π ∧
      tableFamily π ∧
        exactAlternatingSquareRegime π ∧
          ∀ j : V8,
            globalPairing π (π.1 j) ∧
              π.1 j ∉ prescribedTransportSubgroup π.1 j

end MathlibPlus.Open.ResearchFormalization
