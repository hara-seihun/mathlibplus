import MathlibPlus.Basic

namespace MathlibPlus.Algebra

/--
The rectangle identity in admitted claim 31223.  The displayed functional is
kept as `P ↦ Φ (z * P)`, so the four-term trade is not replaced by an
unrelated scalar identity.
-/
theorem claim31223_equatorial_coalescence
    {R S : Type*} [CommRing R] [AddCommGroup S]
    (Φ : R →+ S) (z C D E F : R) :
    let equatorial : R → S := fun P => Φ (z * P)
    equatorial (C * E) + equatorial (D * F) -
          equatorial (C * F) - equatorial (D * E) =
      Φ (z * (C - D) * (E - F)) := by
  dsimp
  calc
    Φ (z * (C * E)) + Φ (z * (D * F)) -
          Φ (z * (C * F)) - Φ (z * (D * E)) =
        Φ (z * (C * E) + z * (D * F) -
          (z * (C * F) + z * (D * E))) := by
            simp only [map_sub, map_add]
            abel
    _ = Φ (z * (C - D) * (E - F)) := by
      congr 1
      ring

end MathlibPlus.Algebra
