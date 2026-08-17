import MathlibPlus.Open.ResearchFormalization.R0913RootedContextChannels

namespace MathlibPlus.Open.ResearchFormalization.R0913

/-- Claim 25578: grafting a local jet with an aggregate rooted-context jet and
composing two aggregate context jets have the displayed commutative-ring laws. -/
def claim25578 : Prop :=
  ∀ {R : Type*} [CommRing R] (j : Jet R)
    (context context' : RootedContext),
    let c := aggregateJet (R := R) context
    let c' := aggregateJet (R := R) context'
    graftedJet j c =
        (j.1 + c.1, j.2.1 + c.2.1 + j.1 * c.1,
          j.2.2 + c.2.2) ∧
      rootJetProduct c c' =
        (c.1 + c'.1, c.2.1 + c'.2.1 + c.1 * c'.1,
          c.2.2 + c'.2.2)

end MathlibPlus.Open.ResearchFormalization.R0913
