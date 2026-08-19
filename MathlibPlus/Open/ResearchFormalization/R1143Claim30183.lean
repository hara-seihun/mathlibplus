import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1143Claim30183

/-- The binary balanced-edge marker, viewed in the lower-marker coefficient
ring. -/
def balancedEdgeBit {R : Type*} [CommRing R] (kappa : Fin 2) : R :=
  (kappa.1 : R)

/-- The exact quadratic central-marker collar for an active denominator.  The
indeterminate `Polynomial.X` is the central marker `c_J`. -/
noncomputable def activeDenominatorCentralCollar {R : Type*} [CommRing R]
    (B Xi : R) (t : R) (kappa : Fin 2) : Polynomial R :=
  Polynomial.C B +
    Polynomial.X * Polynomial.C (t * Xi) +
      Polynomial.X ^ 2 * Polynomial.C (t ^ 2 * balancedEdgeBit kappa)

/-- The exact active-difference collar, with all coefficients other than the
central marker in the lower-marker coefficient ring. -/
noncomputable def activeDifferenceCentralCollar {R : Type*} [CommRing R]
    (A XiX XiY : R) (t : R) (kappaX kappaY : Fin 2) : Polynomial R :=
  Polynomial.C A +
    Polynomial.X * Polynomial.C (XiX - XiY) +
      Polynomial.X ^ 2 *
        Polynomial.C (t * (balancedEdgeBit kappaX - balancedEdgeBit kappaY))

/-- Claim 30180's exact denominator collar for all active classes. -/
def exactActiveDenominatorCollar_claim30180
    {R Active : Type*} [CommRing R]
    (B Xi : Active → R) (t : R) (kappa : Active → Fin 2)
    (Q : Active → Polynomial R) : Prop :=
  ∀ X : Active,
    Q X = activeDenominatorCentralCollar (B X) (Xi X) t (kappa X)

/-- Claim 30181's exact active-difference collar for all ordered pairs. -/
def exactActiveDifferenceCollar_claim30181
    {R Active : Type*} [CommRing R]
    (A : Active → Active → R) (Xi : Active → R) (t : R)
    (kappa : Active → Fin 2)
    (Delta : Active → Active → Polynomial R) : Prop :=
  ∀ X Y : Active,
    Delta X Y =
      activeDifferenceCentralCollar
        (A X Y) (Xi X) (Xi Y) t (kappa X) (kappa Y)

/-- Claim 30183.  Under the exact central collars, three distinct active
classes with distinct denominators cannot share a genuinely quadratic
central-marker prime.  The nonconstant-degree and degree-at-most-two clauses
are the exact consequences supplied by the source's dependence and common-
difference hypotheses; the conclusion records both the exclusion of degree
two and the resulting linear degree. -/
def noGenuinelyQuadraticCommonCentralPrime_claim30183 : Prop :=
  ∀ {R Active : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R]
    (B Xi : Active → R) (t : R)
    (kappa : Active → Fin 2)
    (A : Active → Active → R)
    (Q : Active → Polynomial R)
    (Delta : Active → Active → Polynomial R)
    (S Rclass T : Active) (p : Polynomial R),
    S ≠ Rclass → S ≠ T → Rclass ≠ T →
      Q S ≠ Q Rclass → Q S ≠ Q T → Q Rclass ≠ Q T →
        exactActiveDenominatorCollar_claim30180 B Xi t kappa Q →
          exactActiveDifferenceCollar_claim30181 A Xi t kappa Delta →
            (∀ X Y : Active, Delta X Y = Q X - Q Y) →
              Irreducible p →
                0 < p.natDegree →
                  p.natDegree ≤ 2 →
                    p ∣ Delta S T →
                      p ∣ Delta Rclass T →
                        p.natDegree ≠ 2 ∧ p.natDegree = 1

end MathlibPlus.Open.ResearchFormalization.R1143Claim30183
