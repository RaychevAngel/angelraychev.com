import SquareCompressionFourEnergy
import ProductCompressionRelabel

/-! Six verified diagonal compressions on the actual 64-room cube. -/
namespace Princess.FourCubeCompression
open Princess.CaptureRecurrence Princess.LadderCardinality Princess.SurvivorEnvelope
open Princess.ProductCompression

abbrev Room := Fin 64
abbrev Coord := Fin 4

def x (v : Room) : Coord := ⟨v.val/16,by have := v.isLt; omega⟩
def y (v : Room) : Coord := ⟨v.val/4%4,by omega⟩
def z (v : Room) : Coord := ⟨v.val%4,by omega⟩
def room (a b c : Coord) : Room := ⟨16*a.val+4*b.val+c.val,by
  have := a.isLt; have := b.isLt; have := c.isLt; omega⟩
def square (a b : Coord) : Fin 16 := ⟨4*a.val+b.val,by
  have := a.isLt; have := b.isLt; omega⟩
def first (v : Fin 16) : Coord := ⟨v.val/4,by have := v.isLt; omega⟩
def second (v : Fin 16) : Coord := ⟨v.val%4,by omega⟩
def pathAdj (u v : Coord) : Prop := u.val+1=v.val ∨ v.val+1=u.val
instance (u v : Coord) : Decidable (pathAdj u v) := inferInstanceAs (Decidable (_ ∨ _))
def adj (u v : Room) : Prop :=
  (pathAdj (x u) (x v) ∧ y u=y v ∧ z u=z v) ∨
  (x u=x v ∧ pathAdj (y u) (y v) ∧ z u=z v) ∨
  (x u=x v ∧ y u=y v ∧ pathAdj (z u) (z v))
instance (u v : Room) : Decidable (adj u v) := inferInstanceAs (Decidable (_ ∨ _ ∨ _))

def toPair (pair : Fin 3) (v : Room) : Fin 16 × Coord :=
  if pair.val=0 then (square (x v) (y v),z v)
  else if pair.val=1 then (square (x v) (z v),y v)
  else (square (y v) (z v),x v)
def fromPair (pair : Fin 3) (v : Fin 16 × Coord) : Room :=
  if pair.val=0 then room (first v.1) (second v.1) v.2
  else if pair.val=1 then room (first v.1) v.2 (second v.1)
  else room v.2 (first v.1) (second v.1)

theorem inverse_left : ∀ pair : Fin 3, ∀ v : Fin 16 × Coord,
    toPair pair (fromPair pair v)=v := by
  have h : ∀ pair : Fin 3, ∀ a : Fin 16, ∀ b : Coord,
      toPair pair (fromPair pair (a,b)) = (a,b) := by decide
  rintro pair ⟨a,b⟩; exact h pair a b

theorem inverse_right : ∀ pair : Fin 3, ∀ v : Room,
    fromPair pair (toPair pair v)=v := by decide

instance (u v : Fin 16 × Coord) : Decidable (productAdj SquareCompressionFour.adj pathAdj u v) :=
  inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))

set_option maxHeartbeats 2000000 in
theorem pair_edges : ∀ pair : Fin 3, ∀ u v : Room,
    productAdj SquareCompressionFour.adj pathAdj (toPair pair u) (toPair pair v) ↔ adj u v := by
  decide +kernel

def pairing (pair : Fin 3) : Relabel (productAdj SquareCompressionFour.adj pathAdj) adj where
  toLeft := toPair pair
  toRight := fromPair pair
  left_inv := inverse_left pair
  right_inv := inverse_right pair
  edges := pair_edges pair

theorem pair_enumeration : ∀ pair : Fin 3,
    ((productList 16 4).map (fromPair pair)).Perm (List.finRange 64) := by decide

def op (pair : Fin 3) (dir : Bool) : Operator adj :=
  relabel (pairing pair) (lift (ofCompression (SquareCompressionFour.compression dir)) pathAdj)

theorem pair_card (pair : Fin 3) (A : Region Room) :
    card A = productCard (fun v => A (fromPair pair v)) :=
  cardOn_relabel (pairing pair) (List.finRange 64) (productList 16 4) (pair_enumeration pair) A

theorem op_size (pair : Fin 3) (dir : Bool) (A : Region Room) : card ((op pair dir).map A)=card A := by
  apply relabel_measure (pairing pair) _ productCard card (pair_card pair)
  intro B
  exact lift_card (ofCompression (SquareCompressionFour.compression dir)) pathAdj
    (SquareCompressionFour.cmap_size dir) B

def weight (v : Room) : Nat := (x v).val+2*(y v).val+3*(z v).val
noncomputable def energy (A : Region Room) : Nat := weightedOn (List.finRange 64) weight A

def restWeight (pair : Fin 3) (j : Coord) : Nat :=
  if pair.val=0 then 3*j.val else if pair.val=1 then 2*j.val else j.val

theorem weight_pair : ∀ pair : Fin 3, ∀ v : Fin 16 × Coord,
    weight (fromPair pair v) = SquareCompressionFour.pairWeight pair v.1 + restWeight pair v.2 := by
  have h : ∀ pair : Fin 3, ∀ a : Fin 16, ∀ b : Coord,
      weight (fromPair pair (a,b)) = SquareCompressionFour.pairWeight pair a + restWeight pair b := by decide
  rintro pair ⟨a,b⟩; exact h pair a b

theorem pair_energy (pair : Fin 3) (A : Region Room) :
    energy A = fiberEnergy (SquareCompressionFour.energy pair) (restWeight pair)
      (fun v => A (fromPair pair v)) := by
  unfold energy
  rw [← weightedOn_perm _ _ weight A (pair_enumeration pair),weightedOn_map]
  have heq : (fun v => weight (fromPair pair v)) =
      (fun v => SquareCompressionFour.pairWeight pair v.1 + restWeight pair v.2) := by
    funext v; exact weight_pair pair v
  rw [heq,product_energy]
  rfl

theorem op_energy (pair : Fin 3) (dir : Bool) : EnergyGood (op pair dir) energy := by
  apply relabel_energy (pairing pair) _
    (fiberEnergy (SquareCompressionFour.energy pair) (restWeight pair)) energy (pair_energy pair)
  exact lift_energy (ofCompression (SquareCompressionFour.compression dir)) pathAdj
    (SquareCompressionFour.energy pair) (restWeight pair)
    (SquareCompressionFour.cmap_energy dir pair) (SquareCompressionFour.cmap_size dir)

theorem energy_bound (A : Region Room) : energy A ≤ 1152 := by
  have hb : ∀ v : Room, weight v ≤ 18 := by decide
  exact weightedOn_bound (List.finRange 64) weight A 18 (fun v _ => hb v)

end Princess.FourCubeCompression
#print axioms Princess.FourCubeCompression.op_size
#print axioms Princess.FourCubeCompression.op_energy
