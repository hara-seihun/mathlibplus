import Mathlib

namespace MathlibPlus.Open.Combinatorics

/--
The admitted 16-cell Cayley-CI family theorem, with the Cayley graph
isomorphism relation written out explicitly so that the open node is
proof-free.
-/
def ciMixedAbelianResidualValency13 : Prop :=
  let V := Fin 3 → ZMod 3
  let G := ZMod 4 × V
  let family : Set (Set G) :=
    {S : Set G |
      ∃ (W : Submodule (ZMod 3) V) (u v : V),
        Module.finrank (ZMod 3) W = 2 ∧
        u ∈ W ∧
        v ∈ W ∧
        LinearIndependent (ZMod 3) ![u, v] ∧
        S =
          ((AddSubgroup.prod (AddSubgroup.zmultiples (2 : ZMod 4))
              W.toAddSubgroup : AddSubgroup G) : Set G) \
            ({(0, 0)} ∪ {(0, u), (0, -u), (0, v), (0, -v)})}
  (Set.ncard
      {W : Submodule (ZMod 3) V |
        Module.finrank (ZMod 3) W = 2} = 13) ∧
    (∀ W : Submodule (ZMod 3) V,
      Module.finrank (ZMod 3) W = 2 →
        Set.ncard
            {P : Set (Submodule (ZMod 3) V) |
              P.Finite ∧
                P.ncard = 2 ∧
                ∀ L ∈ P,
                  L ≤ W ∧ Module.finrank (ZMod 3) L = 1} = 6) ∧
    (Set.ncard family = 78) ∧
    (∀ S ∈ family, S.ncard = 13) ∧
    (∀ (W : Submodule (ZMod 3) V) (u v : V),
      Module.finrank (ZMod 3) W = 2 →
      u ∈ W →
      v ∈ W →
      LinearIndependent (ZMod 3) ![u, v] →
      let E_W : AddSubgroup G :=
        AddSubgroup.prod (AddSubgroup.zmultiples (2 : ZMod 4))
          W.toAddSubgroup
      let R_W_u_v : Set G :=
        {(0, u), (0, -u), (0, v), (0, -v)}
      let S_W_u_v : Set G :=
        (E_W : Set G) \ ({(0, 0)} ∪ R_W_u_v)
      S_W_u_v.ncard = 13 ∧
        S_W_u_v ⊆ {x : G | x ≠ (0, 0)} ∧
        (∀ x : G, x ∈ S_W_u_v → -x ∈ S_W_u_v) ∧
        (∀ T : Set G,
          T ⊆ {x : G | x ≠ (0, 0)} →
          (∀ x : G, x ∈ T → -x ∈ T) →
          (∃ e : G ≃ G,
            ∀ x y : G,
              (x ≠ y ∧ y - x ∈ S_W_u_v) ↔
                (e x ≠ e y ∧ e y - e x ∈ T)) →
          ∃ α : G ≃+ G, Set.image (fun x => α x) S_W_u_v = T))

end MathlibPlus.Open.Combinatorics
