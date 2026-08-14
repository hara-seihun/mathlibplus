import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BlockLayers

/- The following predicates isolate the binary vector-space layer of the
   admitted block-coordinate claims. -/

def claim35684
    (V W : Type*)
    [Fintype V] [Fintype W]
    [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W]
    (M : Submodule (ZMod 2) (V × W)) : Prop :=
  (∀ x : V, ∃ y : W, (x, y) ∈ M) →
    (∀ y : W, ∃ x : V, (x, y) ∈ M) →
      let K : Submodule (ZMod 2) V :=
        M.comap (LinearMap.inl (ZMod 2) V W)
      ∃ β : W →ₗ[ZMod 2] (V ⧸ K),
        Function.Surjective (Submodule.mkQ K) ∧
          Function.Surjective β ∧
          (∀ x : V, ∀ y : W,
            (x, y) ∈ M ↔ Submodule.mkQ K x = β y) ∧
          (Subsingleton (V ⧸ K) ↔ M = ⊤)


def cell
    (V W Q : Type*)
    [AddCommGroup V] [AddCommGroup W] [AddCommGroup Q]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Module (ZMod 2) Q]
    (α : V →ₗ[ZMod 2] Q) (β : W →ₗ[ZMod 2] Q) (q : Q) : Set (V × W) :=
  {p | α p.1 + β p.2 = q}


def additiveOrbit
    (V W : Type*)
    [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W]
    (M : Submodule (ZMod 2) (V × W)) (p : V × W) : Set (V × W) :=
  {z | ∃ m : M, z = p + (m : V × W)}


def claim35685
    (V W Q : Type*)
    [AddCommGroup V] [AddCommGroup W] [AddCommGroup Q]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Module (ZMod 2) Q]
    (M : Submodule (ZMod 2) (V × W))
    (α : V →ₗ[ZMod 2] Q) (β : W →ₗ[ZMod 2] Q) : Prop :=
  Function.Surjective α →
    Function.Surjective β →
      (∀ x : V, ∀ y : W,
        (x, y) ∈ M ↔ α x + β y = 0) →
        Set.range (cell V W Q α β) = Set.range (additiveOrbit V W M) ∧
          cell V W Q α β 0 = (M : Set (V × W))


def claim35686
    (V W V' W' Q Q' : Type*)
    [AddCommGroup V] [AddCommGroup W] [AddCommGroup V'] [AddCommGroup W']
    [AddCommGroup Q] [AddCommGroup Q']
    [Module (ZMod 2) V] [Module (ZMod 2) W]
    [Module (ZMod 2) V'] [Module (ZMod 2) W']
    [Module (ZMod 2) Q] [Module (ZMod 2) Q']
    (α : V →ₗ[ZMod 2] Q) (β : W →ₗ[ZMod 2] Q)
    (α' : V' →ₗ[ZMod 2] Q') (β' : W' →ₗ[ZMod 2] Q')
    (u : V ≃ V') (v : W ≃ W')
    (η : Q ≃ Q') (L : Q →ₗ[ZMod 2] Q') (c : Q') (q : Q) : Prop :=
  (∀ x : V, α' (u x) = η (α x)) →
    (∀ y : W, β' (v y) = η (β y)) →
      (∀ a : Q, η a = L a + c) →
        Set.image (fun p : V × W => (u p.1, v p.2)) (cell V W Q α β q) =
          cell V' W' Q' α' β' (L q)

end MathlibPlus.Open.ResearchFormalization.BlockLayers
