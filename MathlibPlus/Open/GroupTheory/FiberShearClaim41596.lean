import Mathlib

namespace MathlibPlus.Open.GroupTheory.FiberShearClaim41596

noncomputable section

/-- Claim 41596: every normalized fibre shear on `F₅ × F₅⁴` conjugates the
translation group to another regular copy of `C₅⁵`. -/
def claim41596 : Prop :=
  ∀ (f : (Fin 4 → ZMod 5) → ZMod 5),
    f 0 = 0 →
      ∃ q : Equiv.Perm (ZMod 5 × (Fin 4 → ZMod 5)),
        (∀ (z : ZMod 5) (v : Fin 4 → ZMod 5),
          q (z, v) = (z + f v, v)) ∧
          let R : Subgroup
              (Equiv.Perm (ZMod 5 × (Fin 4 → ZMod 5))) :=
            Subgroup.closure
              (Set.range (fun a : ZMod 5 × (Fin 4 → ZMod 5) =>
                Equiv.addRight a))
          let T : Subgroup
              (Equiv.Perm (ZMod 5 × (Fin 4 → ZMod 5))) :=
            R.map (MulAut.conj q⁻¹)
          Nonempty
              (R ≃* Multiplicative (Fin 5 → ZMod 5)) ∧
            Nonempty
              (T ≃* Multiplicative (Fin 5 → ZMod 5)) ∧
              (∀ x y : ZMod 5 × (Fin 4 → ZMod 5),
                ∃! h : R, h.1 x = y) ∧
              (∀ x y : ZMod 5 × (Fin 4 → ZMod 5),
                ∃! h : T, h.1 x = y)

end

end MathlibPlus.Open.GroupTheory.FiberShearClaim41596
