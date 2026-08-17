import MathlibPlus.Open.Research.ScalarConormalClaims26426_26428

namespace MathlibPlus.Open.ResearchFormalization.BatchR0628Claim26423

open MathlibPlus.Open.ResearchFormalizationBatch

noncomputable section

abbrev ConductorBase := Polynomial ℚ
abbrev ConductorPlane := MvPolynomial (Fin 2) ℚ
abbrev ScalarAQuotient := (scalarA : Type) ⧸ scalarKInA
abbrev ScalarRQuotient := ScalarR ⧸ scalarK

def scalarAtoRQuotient : scalarA →ₐ[ℚ] ScalarRQuotient :=
  (Ideal.Quotient.mkₐ ℚ scalarK).comp scalarA.val

def conductorQuotientMap : ScalarAQuotient →ₐ[ℚ] ScalarRQuotient :=
  Ideal.Quotient.liftₐ (R₁ := ℚ) scalarKInA scalarAtoRQuotient
    (fun _a ha => (Ideal.Quotient.eq_zero_iff_mem).2 ha)

def conductorSpecMap : PrimeSpectrum ScalarRQuotient → PrimeSpectrum ScalarAQuotient :=
  PrimeSpectrum.comap conductorQuotientMap.toRingHom

def conductorProjection : ConductorBase →ₐ[ℚ] ConductorPlane :=
  Polynomial.aeval (MvPolynomial.X (0 : Fin 2))

def coordinateConductorSpecMap : PrimeSpectrum ConductorPlane → PrimeSpectrum ConductorBase :=
  PrimeSpectrum.comap conductorProjection.toRingHom

def scalarPlaneToRQuotient : ConductorPlane →ₐ[ℚ] ScalarRQuotient :=
  MvPolynomial.aeval (fun i : Fin 2 =>
    if i = (0 : Fin 2) then
      Ideal.Quotient.mk scalarK scalarS
    else
      Ideal.Quotient.mk scalarK scalarZ)

def scalarConductorProjection26423 : Prop :=
  ∃ (eA : ScalarAQuotient ≃ₐ[ℚ] ConductorBase)
    (eR : ScalarRQuotient ≃ₐ[ℚ] ConductorPlane),
    eA.symm.toAlgHom = scalarPolyToAQuotient ∧
    eR.symm.toAlgHom = scalarPlaneToRQuotient ∧
    eR (Ideal.Quotient.mk scalarK scalarS) = MvPolynomial.X (0 : Fin 2) ∧
    eR (Ideal.Quotient.mk scalarK scalarZ) = MvPolynomial.X (1 : Fin 2) ∧
    eR.toAlgHom.comp conductorQuotientMap =
      conductorProjection.comp eA.toAlgHom ∧
    conductorSpecMap.comp (PrimeSpectrum.comap eR.toRingHom) =
      (PrimeSpectrum.comap eA.toRingHom).comp coordinateConductorSpecMap

end
end MathlibPlus.Open.ResearchFormalization.BatchR0628Claim26423
