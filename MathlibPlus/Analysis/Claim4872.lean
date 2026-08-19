import Mathlib

namespace MathlibPlus.Analysis.Claim4872

noncomputable section

open scoped BigOperators ComplexConjugate

/-- The reflection paired with the finite zero packet in claim 4872. -/
def tau (s : ℂ) : ℂ := 1 - conj s

/-- A finite zero packet records multiplicity and the involutive zero reflection. -/
structure FiniteZeroPacket where
  Index : Type*
  root : Index → ℂ
  reflect : Index → Index
  reflect_involutive : Function.Involutive reflect
  root_reflect : ∀ index, root (reflect index) = tau (root index)

def reflectEquiv (packet : FiniteZeroPacket) : packet.Index ≃ packet.Index where
  toFun := packet.reflect
  invFun := packet.reflect
  left_inv := packet.reflect_involutive
  right_inv := packet.reflect_involutive

/-- The finite Weil form on Mellin-side values from claim 4872. -/
def finiteWeilForm
    (packet : FiniteZeroPacket) [Fintype packet.Index]
    (F G : ℂ → ℂ) : ℂ :=
  ∑ index, F (packet.root index) * conj (G (tau (packet.root index)))

theorem finiteWeilForm_conj_swap_claim4872
    (packet : FiniteZeroPacket) [Fintype packet.Index]
    (F G : ℂ → ℂ) :
    finiteWeilForm packet F G = conj (finiteWeilForm packet G F) := by
  unfold finiteWeilForm
  calc
    (∑ index, F (packet.root index) * conj (G (tau (packet.root index))))
        = ∑ index, conj (G (packet.root index)) * F (packet.root (packet.reflect index)) := by
            apply Fintype.sum_equiv (reflectEquiv packet)
            intro index
            change F (packet.root index) * conj (G (tau (packet.root index)))
              = conj (G (packet.root (packet.reflect index)))
                  * F (packet.root (packet.reflect (packet.reflect index)))
            rw [packet.root_reflect, packet.reflect_involutive]
            ring
    _ = conj (∑ index, G (packet.root index) * conj (F (tau (packet.root index)))) := by
          simp [packet.root_reflect]

theorem finiteWeilForm_quadratic_expansion_claim4872
    (packet : FiniteZeroPacket) [Fintype packet.Index]
    (F G : ℂ → ℂ) :
    finiteWeilForm packet (F + G) (F + G)
      = finiteWeilForm packet F F
        + finiteWeilForm packet F G
        + finiteWeilForm packet G F
        + finiteWeilForm packet G G := by
  unfold finiteWeilForm
  simp only [Pi.add_apply, map_add, add_mul, mul_add]
  simp only [Finset.sum_add_distrib]
  ring

end

end MathlibPlus.Analysis.Claim4872
