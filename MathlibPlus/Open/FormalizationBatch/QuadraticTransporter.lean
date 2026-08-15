import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.QuadraticTransporter

private structure F3Five where
  i : ZMod 3
  j : ZMod 3
  a : ZMod 3
  b : ZMod 3
  c : ZMod 3

private abbrev H := F3Five
private abbrev E := ZMod 3 × F3Five

/-- The specified quadratic transporter on the five-coordinate `F₃`-space. -/
def fixedQuadraticTransporterOnH : Prop :=
  ∃! g : H → H, ∀ h : H,
    g h =
      { i := h.i
        j := h.j
        a := h.a + h.i * (h.i - 1)
        b := h.b + (2 * h.i - 1) * h.j
        c := h.c + h.j ^ 2 }

/-- The same transporter and its `φ`-corrected lift on `F₃ ⊕ H`. -/
def fixedQuadraticTransporterLift : Prop :=
  ∀ φ : H → ZMod 3,
    ∃! g : H → H,
      (∀ h : H,
        g h =
          { i := h.i
            j := h.j
            a := h.a + h.i * (h.i - 1)
            b := h.b + (2 * h.i - 1) * h.j
            c := h.c + h.j ^ 2 }) ∧
        ∃! q : E → E, ∀ z : ZMod 3, ∀ h : H,
          q (z, h) = (z + φ h, g h)

end MathlibPlus.Open.FormalizationBatch.QuadraticTransporter
