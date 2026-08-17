import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.C4TimesC2SharpCounterexample29806

noncomputable section

abbrev C4TimesC2 := ZMod 4 × ZMod 2

/-- The normalized profile with values `(0,0,1,1)` on `C₄`. -/
def c4Profile (x : ZMod 4) : ZMod 2 :=
  if x.val < 2 then 0 else 1

/-- The exact linearity locus of the Boolean/C₂ profile. -/
def c4LinearityLocus : Set (ZMod 4) :=
  {x | ∀ u : ZMod 4,
    c4Profile (x + u) = c4Profile x + c4Profile u}

/-- The normalized fibre switch `f_b(x,e)=(x,e+b(x))`. -/
def c4Switch : C4TimesC2 → C4TimesC2 :=
  fun z => (z.1, z.2 + c4Profile z.1)

/-- The two connection sets in the counterexample. -/
def c4Source : Set C4TimesC2 :=
  {(2, 0)}

def c4Target : Set C4TimesC2 :=
  {(2, 1)}

/-- Inverse-closedness in the additive model of `C₄ × C₂`. -/
def c4InverseClosed (S : Set C4TimesC2) : Prop :=
  ∀ x, x ∈ S → -x ∈ S

/-- Identity-freeness of an ordinary Cayley connection set. -/
def c4IdentityFree (S : Set C4TimesC2) : Prop :=
  (0, 0) ∉ S

/-- Squares in the additive model are doubles. -/
def c4Square (x : C4TimesC2) : Prop :=
  ∃ y : C4TimesC2, (2 : ℕ) • y = x

/-- Explicit ordinary undirected Cayley-graph transport. -/
def c4CayleyGraphTransport
    (S T : Set C4TimesC2) (f : C4TimesC2 → C4TimesC2) : Prop :=
  Function.Bijective f ∧
    ∀ x y : C4TimesC2,
      (SimpleGraph.addCayley S).Adj x y ↔
        (SimpleGraph.addCayley T).Adj (f x) (f y)

/-- Transport of a connection set by a group automorphism. -/
def c4AutomorphismTransports
    (S T : Set C4TimesC2) : Prop :=
  ∃ α : C4TimesC2 ≃+ C4TimesC2, Set.image α S = T

/-- The ordinary undirected Cayley-CI defect carried by the displayed
connection-set transport and the absence of an automorphism shadow. -/
def c4OrdinaryUndirectedCIDefect : Prop :=
  c4CayleyGraphTransport c4Source c4Target c4Switch ∧
    ¬ c4AutomorphismTransports c4Source c4Target

/-- Claim 29806: the normalized period set, character obstruction, exact
switch of the inverse-closed singleton, and its ordinary non-CI Cayley
witness on `C₄ × C₂`. -/
def claim29806 : Prop :=
  c4Profile 0 = 0 ∧
    c4Profile 1 = 0 ∧
      c4Profile 2 = 1 ∧
        c4Profile 3 = 1 ∧
          (∀ x : ZMod 4,
            x ∈ c4LinearityLocus ↔ x = 0 ∨ x = 2) ∧
            c4Profile 2 = 1 ∧
              (∀ χ : ZMod 4 →+ ZMod 2, χ 2 = 0) ∧
                c4InverseClosed c4Source ∧
                  c4IdentityFree c4Source ∧
                    Set.image c4Switch c4Source = c4Target ∧
                      c4Square (2, 0) ∧
                        ¬ c4Square (2, 1) ∧
                          c4OrdinaryUndirectedCIDefect

end

end MathlibPlus.Open.ResearchFormalization.C4TimesC2SharpCounterexample29806
