import StrategyCompression
import SurvivorEnvelope

/-! Set-operator composition and Cartesian-product lifting.
No geometric compression is assumed optimal; the only hypotheses are the
explicit monotonicity and neighborhood-inclusion properties. Cardinal
preservation is a separate exact fiber sum, usable with arbitrary finite
factors. -/
namespace Princess.ProductCompression

open Princess.CaptureRecurrence Princess.LadderCardinality
open Princess.SurvivorEnvelope

structure Operator {V : Type} (adj : V → V → Prop) where
  map : Region V → Region V
  mono : ∀ A B, Subset A B → Subset (map A) (map B)
  neighbors : ∀ A, Subset (move adj (map A)) (map (move adj A))

def ofCompression {n : Nat} {adj : Fin n → Fin n → Prop}
    (C : Princess.StrategyCompression.Compression adj) : Operator adj :=
  ⟨C.map, C.mono, C.neighbors⟩

def identity {V : Type} (adj : V → V → Prop) : Operator adj where
  map := fun A => A
  mono := fun _ _ h => h
  neighbors := fun _ _ h => h

def compose {V : Type} {adj : V → V → Prop}
    (C D : Operator adj) : Operator adj where
  map := fun A => C.map (D.map A)
  mono := fun A B h => C.mono _ _ (D.mono A B h)
  neighbors := by
    intro A v hv
    exact C.mono _ _ (D.neighbors A) v (C.neighbors (D.map A) v hv)

def lift {V W : Type} {left : V → V → Prop}
    (C : Operator left) (right : W → W → Prop) : Operator (productAdj left right) where
  map := fun S x => C.map (fiber S x.2) x.1
  mono := by
    intro A B h x hx
    exact C.mono _ _ (fun v hv => h (v,x.2) hv) x.1 hx
  neighbors := by
    intro A x hx
    rcases (move_fiber left right _ x.1 x.2).mp hx with hleft | ⟨j,hj,hA⟩
    · apply C.mono (move left (fiber A x.2)) (fiber (move (productAdj left right) A) x.2)
      · intro v hv
        exact (move_fiber left right A v x.2).mpr (Or.inl hv)
      · exact C.neighbors (fiber A x.2) x.1 hleft
    · apply C.mono (fiber A j) (fiber (move (productAdj left right) A) x.2)
      · intro v hv
        exact (move_fiber left right A v x.2).mpr (Or.inr ⟨j,hj,hv⟩)
      · exact hA

theorem compose_card {V : Type} {adj : V → V → Prop} (C D : Operator adj)
    (measure : Region V → Nat) (hC : ∀ A, measure (C.map A) = measure A)
    (hD : ∀ A, measure (D.map A) = measure A) (A : Region V) :
    measure ((compose C D).map A) = measure A := by
  change measure (C.map (D.map A)) = measure A
  rw [hC,hD]

theorem lift_card {a b : Nat} {left : Fin a → Fin a → Prop}
    (C : Operator left) (right : Fin b → Fin b → Prop)
    (size : ∀ A, card (C.map A) = card A) (S : Region (Fin a × Fin b)) :
    productCard ((lift C right).map S) = productCard S := by
  rw [productCard_fibers, productCard_fibers]
  congr 1
  apply List.map_congr_left
  intro j hj
  exact size (fiber S j)

theorem lift_idempotent {V W : Type} {left : V → V → Prop}
    (C : Operator left) (right : W → W → Prop)
    (idem : ∀ A, C.map (C.map A) = C.map A) (S : Region (V × W)) :
    (lift C right).map ((lift C right).map S) = (lift C right).map S := by
  funext x
  exact congrFun (idem (fiber S x.2)) x.1

theorem lifted_composition {V W : Type} {left : V → V → Prop}
    (C D : Operator left) (right : W → W → Prop) (S : Region (V × W)) :
    (lift (compose C D) right).map S =
      (compose (lift C right) (lift D right)).map S := rfl

end Princess.ProductCompression

#print axioms Princess.ProductCompression.lift
#print axioms Princess.ProductCompression.lift_card
#print axioms Princess.ProductCompression.lift_idempotent
