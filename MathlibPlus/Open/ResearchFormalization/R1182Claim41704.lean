import MathlibPlus.Open.ResearchFormalization.R1182.Claim41710

namespace MathlibPlus.Open.ResearchFormalization.R1182.Claim41704

open MathlibPlus.Open.ResearchFormalization.R1182.Claim41710

noncomputable section

/-- The actual relative derivative d_(f,g)(x)=f(xg)f(g)^(-1) in the
prime-block semidirect coordinates. -/
def relativeDerivative41704
    (p : ℕ) (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p)
    (x g : PrimeBlock p) : PrimeBlock p :=
  primeBlockMul p
    (affineLiftMap p false lam tau (primeBlockMul p x g))
    (primeBlockInv p (affineLiftMap p false lam tau g))

/-- The coefficient of the varying top coordinate y in the actual relative
derivative at connection base h and vertex base k. -/
def varyingTopCoefficient41704
    (p : ℕ) (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p)
    (h k : Q12) : ZMod p :=
  (relativeDerivative41704 p lam tau (0, h) (1, k)).1 -
    (relativeDerivative41704 p lam tau (0, h) (0, k)).1

/-- Claim 41704: the displayed coefficient belongs to the normalized affine
lift's actual relative derivative, and its vanishing profile is exactly the
left stabilizer condition for a(k)=lambda(k) chi(k)/chi(sigma(k)). -/
def claim41704 : Prop :=
  ∀ p : ℕ,
    Nat.Prime p →
      3 < p →
        ∀ (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p),
          normalizedAffineFunctions lam tau →
            (∀ h k : Q12,
              varyingTopCoefficient41704 p lam tau h k =
                relativeCoefficient p false lam h k) ∧
            (∀ h : Q12,
              ((∀ k : Q12,
                varyingTopCoefficient41704 p lam tau h k = 0) ↔
                (∀ k : Q12,
                  scalarProfile p false lam (q12Mul h k) =
                    scalarProfile p false lam k)))

end

end MathlibPlus.Open.ResearchFormalization.R1182.Claim41704
