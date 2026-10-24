import ConstructionCounts
import FiniteHall

/-! Exact size of the periodic modulo-four circle envelope. -/
namespace Delivery.CircleCounting
open DenseCombinatorics ConstructionCounts

def periodic {n : Nat} (d : Fin n) : Prop := d.val%4=0 ∨ d.val%4=1

def enumerate {n : Nat} (multiple : n%4=0) (i : Fin (n/2)) : Fin n :=
  ⟨4*(i.val/2)+i.val%2,by have := i.isLt; omega⟩

theorem periodic_count {n : Nat} (multiple : n%4=0) : card (@periodic n)=n/2 := by
  apply card_image (enumerate multiple)
  · intro x y same
    have eq := congrArg Fin.val same
    dsimp [enumerate] at eq
    apply Fin.ext
    omega
  · intro d
    constructor
    · intro hp
      let i : Fin (n/2) := ⟨2*(d.val/4)+d.val%4,by have := d.isLt; unfold periodic at hp; omega⟩
      refine ⟨i,?_⟩
      apply Fin.ext
      dsimp [enumerate,i]
      unfold periodic at hp
      omega
    · rintro ⟨i,rfl⟩
      change (4*(i.val/2)+i.val%2)%4=0 ∨ (4*(i.val/2)+i.val%2)%4=1
      omega

def allowed {n : Nat} (h : Nat) (d : Fin n) : Prop :=
  (periodic d ∨ d.val=h) ∧ d.val≠2*h-1

theorem singleton_count {n h : Nat} (small : h<n) :
    card (fun d : Fin n => d.val=h)=1 := by
  have same := card_congr (P := fun d : Fin n => d.val=h) (Q := fun d => d=⟨h,small⟩)
    (fun _ => ⟨fun eq => Fin.ext eq,fun eq => congrArg Fin.val eq⟩)
  rw [same]
  exact FiniteHall.card_singleton _

theorem allowed_count {n h : Nat} (multiple : n%4=0) (large : 7≤h)
    (residue : h%4=3) (room : 2*h+2≤n) : card (@allowed n h)=n/2 := by
  have period := periodic_count multiple
  have point := singleton_count (n := n) (h := h) (by omega)
  have disjoint : ∀ d : Fin n, periodic d → d.val=h → False := by
    intro d hp eq
    unfold periodic at hp
    omega
  have union := card_disjoint_union disjoint
  have cut := singleton_count (n := n) (h := 2*h-1) (by omega)
  have split := card_partition (fun d : Fin n => periodic d ∨ d.val=h)
    (fun d => d.val=2*h-1)
  have removed : card (fun d : Fin n => (periodic d ∨ d.val=h) ∧ d.val=2*h-1)=1 := by
    rw [card_congr (Q := fun d : Fin n => d.val=2*h-1)]
    · exact cut
    · intro d
      constructor
      · exact And.right
      · intro eq
        refine ⟨Or.inl ?_,eq⟩
        unfold periodic
        omega
  change _ + card (allowed h) = _ at split
  omega

#print axioms periodic_count
#print axioms allowed_count
end Delivery.CircleCounting
