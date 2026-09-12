import ProductCompressionEnergy

/-! Relabelling a compression along an explicit graph isomorphism. -/
namespace Princess.ProductCompression
open Princess.CaptureRecurrence Princess.LadderCardinality

structure Relabel {V W : Type} (left : V → V → Prop) (right : W → W → Prop) where
  toLeft : W → V
  toRight : V → W
  left_inv : ∀ v, toLeft (toRight v) = v
  right_inv : ∀ w, toRight (toLeft w) = w
  edges : ∀ u v, left (toLeft u) (toLeft v) ↔ right u v

theorem relabel_move {V W : Type} {left : V → V → Prop} {right : W → W → Prop}
    (E : Relabel left right) (A : Region W) (v : V) :
    move left (fun u => A (E.toRight u)) v ↔ move right A (E.toRight v) := by
  constructor
  · rintro ⟨u,hu,he⟩
    refine ⟨E.toRight u,hu,?_⟩
    apply (E.edges _ _).mp
    simpa only [E.left_inv] using he
  · rintro ⟨u,hu,he⟩
    refine ⟨E.toLeft u,?_,?_⟩
    · simpa only [E.right_inv] using hu
    · have h := (E.edges u (E.toRight v)).mpr he
      simpa only [E.left_inv] using h

def relabel {V W : Type} {left : V → V → Prop} {right : W → W → Prop}
    (E : Relabel left right) (C : Operator left) : Operator right where
  map := fun A w => C.map (fun v => A (E.toRight v)) (E.toLeft w)
  mono := fun A B h w hw => C.mono _ _ (fun v hv => h _ hv) _ hw
  neighbors := by
    intro A w hw
    obtain ⟨u,hu,he⟩ := hw
    have h := C.neighbors (fun v => A (E.toRight v)) (E.toLeft w)
      ⟨E.toLeft u,hu,(E.edges u w).mpr he⟩
    have eq : move left (fun v => A (E.toRight v)) =
        (fun v => move right A (E.toRight v)) := by
      funext v; exact propext (relabel_move E A v)
    rwa [eq] at h

theorem relabel_pull_map {V W : Type} {left : V → V → Prop} {right : W → W → Prop}
    (E : Relabel left right) (C : Operator left) (A : Region W) :
    (fun v => (relabel E C).map A (E.toRight v)) = C.map (fun v => A (E.toRight v)) := by
  funext v
  change C.map (fun v => A (E.toRight v)) (E.toLeft (E.toRight v)) = _
  rw [E.left_inv]

theorem relabel_measure {V W : Type} {left : V → V → Prop} {right : W → W → Prop}
    (E : Relabel left right) (C : Operator left)
    (small : Region V → Nat) (large : Region W → Nat)
    (bridge : ∀ A, large A = small (fun v => A (E.toRight v)))
    (size : ∀ A, small (C.map A) = small A) (A : Region W) :
    large ((relabel E C).map A) = large A := by
  rw [bridge,bridge,relabel_pull_map,size]

theorem relabel_energy {V W : Type} {left : V → V → Prop} {right : W → W → Prop}
    (E : Relabel left right) (C : Operator left)
    (small : Region V → Nat) (large : Region W → Nat)
    (bridge : ∀ A, large A = small (fun v => A (E.toRight v)))
    (good : EnergyGood C small) : EnergyGood (relabel E C) large := by
  intro A
  have h := good (fun v => A (E.toRight v))
  constructor
  · rw [bridge,bridge,relabel_pull_map]
    exact h.1
  · intro he
    rw [bridge,bridge,relabel_pull_map] at he
    have fix := h.2 he
    funext w
    have point := congrFun fix (E.toLeft w)
    simpa only [E.right_inv,relabel] using point

theorem cardOn_relabel {V W : Type} {left : V → V → Prop} {right : W → W → Prop}
    (E : Relabel left right) (xs : List W) (ys : List V)
    (perm : (ys.map E.toRight).Perm xs) (A : Region W) :
    cardOn xs A = cardOn ys (fun v => A (E.toRight v)) := by
  classical
  calc
    cardOn xs A = cardOn (ys.map E.toRight) A := by
      unfold cardOn
      exact List.Perm.countP_eq _ perm.symm
    _ = cardOn ys (fun v => A (E.toRight v)) := cardOn_map ys E.toRight A

end Princess.ProductCompression
#print axioms Princess.ProductCompression.relabel
#print axioms Princess.ProductCompression.relabel_energy
