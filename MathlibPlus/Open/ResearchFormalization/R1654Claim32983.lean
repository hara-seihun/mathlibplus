import MathlibPlus.Open.ResearchFormalization.R1654Claim32991

namespace MathlibPlus.Open.ResearchFormalization.R1654Claim32983

open MathlibPlus.Open.ResearchFormalization.R1654

noncomputable section

def exactlyThreeBlockChart_claim32983 : Prop :=
  ∀ (alpha sigma tau : Local7) (i j k : ZMod 8),
    alpha ≠ 1 →
      affineLocal alpha →
        ¬ affineLocal sigma →
          psl32Type sigma →
            ¬ affineLocal tau →
              a7Type tau →
                i ≠ j → i ≠ k → j ≠ k →
                  let F := threeBlockChart alpha sigma tau i j k
                  let R := standardRegularCopy
                  let T := conjugateCopy F R
                  let X := generatedCopy R T
                  (∀ x : ZMod 7,
                    F (x, i) = (alpha x, i) ∧
                      F (x, j) = (sigma x, j) ∧
                        F (x, k) = (tau x, k)) ∧
                    (∀ x : ZMod 7, ∀ h : ZMod 8,
                      h ≠ i → h ≠ j → h ≠ k →
                        F (x, h) = (x, h)) ∧
                      R = standardRegularCopy ∧
                        T = conjugateCopy F R ∧
                          X = generatedCopy R T

end

end MathlibPlus.Open.ResearchFormalization.R1654Claim32983
