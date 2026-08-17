import MathlibPlus.Open.Combinatorics.Claim5604

namespace MathlibPlus.Open.ResearchFormalization.RootJet5598

abbrev RootJet := MathlibPlus.Open.Combinatorics.Claim5604.RootJet

/-- The displayed root-jet product on `(d,b,q)` triples. -/
def rootJetProduct (x y : RootJet) : RootJet :=
  (x.1 + y.1,
    (x.2.1 + y.2.1 + x.1 * y.1, x.2.2 + y.2.2))

/-- The displayed root-jet identity. -/
def rootJetIdentity : RootJet :=
  (0, (0, 0))

/-- Claim 5598: the root-jet product is associative and commutative with the
specified identity. -/
def rootJetProductCommutativeMonoid_claim5598 : Prop :=
  (∀ x y z : RootJet,
    rootJetProduct (rootJetProduct x y) z =
      rootJetProduct x (rootJetProduct y z)) ∧
    (∀ x y : RootJet,
      rootJetProduct x y = rootJetProduct y x) ∧
    (∀ x : RootJet,
      rootJetProduct rootJetIdentity x = x ∧
        rootJetProduct x rootJetIdentity = x)

end MathlibPlus.Open.ResearchFormalization.RootJet5598
