import FiniteExclusionFastBounds

/-! Complete reflected upper-bound trees with cached bitset certificates.
External data is accepted only through the ordinary Lean kernel. -/
namespace Delivery.FiniteExclusion.BoundTreeRows
open FiniteGame Bounds PrefixBounds FastBounds

structure RowTable where
  r0 : Nat
  r1 : Nat
  r2 : Nat
  r3 : Nat
  r4 : Nat
  r5 : Nat
  r6 : Nat
  r7 : Nat
  r8 : Nat

def rows (table : RowTable) (x : Fin 9) : Nat :=
  match x.val with
  | 0 => table.r0
  | 1 => table.r1
  | 2 => table.r2
  | 3 => table.r3
  | 4 => table.r4
  | 5 => table.r5
  | 6 => table.r6
  | 7 => table.r7
  | _ => table.r8

structure Loss where
  target : Fin 9
  region : Nat
  good : RowTable

structure Leaf where
  allowed : RowTable
  sources : List SourceWitness
  recipients : List RecipientWitness
  upper : RowTable
  lower : RowTable
  losses : List Loss

def Leaf.masks (leaf : Leaf) : List (Fin 9 × Nat) :=
  leaf.losses.map fun loss => (loss.target,loss.region)

def LeafOK (a : Assignment 9) (p : List (Fin 9)) (bound : Nat) (leaf : Leaf) : Prop :=
  (∀ w ∈ leaf.sources, SourceOK a p w) ∧
  (∀ w ∈ leaf.recipients, RecipientOK a p w) ∧
  (∀ r z, Legal (upperEdge a p) r z → Bitset.graph (rows leaf.upper) r z) ∧
  (∀ c z, Bitset.graph (rows leaf.lower) c z → lowerLegal a p c z) ∧
  (∀ loss ∈ leaf.losses, Bitset.FastRegionOK (rows leaf.upper) (rows leaf.lower)
    (rows loss.good) loss.target loss.region) ∧
  CoverOK a p (rows leaf.allowed) leaf.sources leaf.recipients leaf.masks ∧
  allowedCount (rows leaf.allowed) ≤ bound
instance (a : Assignment 9) (p : List (Fin 9)) (bound : Nat) (leaf : Leaf) :
    Decidable (LeafOK a p bound leaf) := inferInstanceAs (Decidable (_ ∧ _))

theorem leaf_sound (a : Assignment 9) (p : List (Fin 9)) (bound : Nat) (leaf : Leaf)
    (checked : LeafOK a p bound leaf) : UpperPrefix a p bound := by
  apply FastBounds.upper a p bound (rows leaf.allowed) leaf.sources leaf.recipients leaf.masks
    checked.1 checked.2.1 ?_ checked.2.2.2.2.2.1 checked.2.2.2.2.2.2
  intro tm member
  obtain ⟨loss,listed,equal⟩ := List.mem_map.mp member
  subst tm
  exact Bitset.prefix_ok a p (rows leaf.upper) (rows leaf.lower) checked.2.2.1 checked.2.2.2.1
    loss.target loss.region (Bitset.fast_sound _ _ _ _ _ (checked.2.2.2.2.1 loss listed))

structure Local where
  allowed : RowTable
  sources : List SourceWitness
  recipients : List RecipientWitness

def LocalOK (a : Assignment 9) (p : List (Fin 9)) (bound : Nat) (cert : Local) : Prop :=
  (∀ w ∈ cert.sources, SourceOK a p w) ∧
  (∀ w ∈ cert.recipients, RecipientOK a p w) ∧
  CoverOK a p (rows cert.allowed) cert.sources cert.recipients [] ∧
  allowedCount (rows cert.allowed) ≤ bound
instance (a : Assignment 9) (p : List (Fin 9)) (bound : Nat) (cert : Local) :
    Decidable (LocalOK a p bound cert) := inferInstanceAs (Decidable (_ ∧ _))

theorem local_sound (a : Assignment 9) (p : List (Fin 9)) (bound : Nat) (cert : Local)
    (checked : LocalOK a p bound cert) : UpperPrefix a p bound :=
  FastBounds.upper a p bound (rows cert.allowed) cert.sources cert.recipients []
    checked.1 checked.2.1 (by simp) checked.2.2.1 checked.2.2.2

inductive Tree where
  | invalid
  | leaf (certificate : Leaf)
  | camp (certificate : Local)
  | branch (children : Fin 9 → Tree)

def check (a : Assignment 9) (p : List (Fin 9)) (bound : Nat) : Tree → Bool
  | .invalid => decide (¬PrefixOK a p)
  | .leaf leaf => decide (LeafOK a p bound leaf)
  | .camp cert => decide (LocalOK a p bound cert)
  | .branch children => decide (p.length < 9) &&
      (List.finRange 9).all (fun v => check a (p++[v]) bound (children v))

theorem sound (a : Assignment 9) (p : List (Fin 9)) (bound : Nat) (tree : Tree)
    (checked : check a p bound tree = true) : UpperPrefix a p bound := by
  induction tree generalizing p with
  | invalid => exact invalid_upper a p bound (of_decide_eq_true checked)
  | leaf certificate => exact leaf_sound a p bound certificate (of_decide_eq_true checked)
  | camp certificate => exact local_sound a p bound certificate (of_decide_eq_true checked)
  | branch children ih =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at checked
    exact branch_upper a p bound checked.1
      (fun v => ih v (p++[v]) (checked.2 v (List.mem_finRange v)))

#print axioms leaf_sound
#print axioms sound
end Delivery.FiniteExclusion.BoundTreeRows
