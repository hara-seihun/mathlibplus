import Mathlib
namespace MathlibPlus.Open.RelativeDerivative

/-- Right regular permutations used in the relative-derivative construction. -/
def rightRegular {G : Type} [Group G] (g : G) : Equiv.Perm G :=
  Equiv.mulRight g

def relativeK {G : Type} [Group G] (f : Equiv.Perm G) : Subgroup (Equiv.Perm G) :=
  Subgroup.closure
    (Set.range (rightRegular (G := G)) ∪
      Set.range (fun g : G => f⁻¹ * rightRegular g * f))

def pointStabilizer {G : Type} [Group G] (H : Subgroup (Equiv.Perm G)) :
    Subgroup (Equiv.Perm G) where
  carrier := {p | p ∈ H ∧ p 1 = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    exact ⟨H.mul_mem ha.1 hb.1, by simp [ha.2, hb.2]⟩
  inv_mem' := by
    intro a ha
    refine ⟨H.inv_mem ha.1, ?_⟩
    have h := congrArg (fun x : G => (a⁻¹) x) ha.2
    calc
      (a⁻¹) 1 = (a⁻¹) (a 1) := h.symm
      _ = 1 := by simp

def subgroupOrbit {G : Type} (H : Subgroup (Equiv.Perm G)) (x : G) : Set G :=
  {y | ∃ h : H, h.1 x = y}

def basicSetFamily {G : Type} (H : Subgroup (Equiv.Perm G)) : Set (Set G) :=
  {S | ∃ x : G, S = subgroupOrbit H x}

def relativeDerivative {G : Type} [Group G] (f : Equiv.Perm G) (g : G) : Equiv.Perm G :=
  f⁻¹ * rightRegular ((f g)⁻¹) * f * rightRegular g

def relativeDelta {G : Type} [Group G] (f : Equiv.Perm G) : Subgroup (Equiv.Perm G) :=
  Subgroup.closure (Set.range (relativeDerivative f))

/-- Basic sets of `V(G,(K_f)_1)` are precisely the `Delta_f`-orbits. -/
def claim_27268 {G : Type} [Fintype G] [DecidableEq G] [Group G]
    (f : Equiv.Perm G) : Prop :=
  f 1 = 1 →
    basicSetFamily (pointStabilizer (relativeK f)) = basicSetFamily (relativeDelta f)

end MathlibPlus.Open.RelativeDerivative
