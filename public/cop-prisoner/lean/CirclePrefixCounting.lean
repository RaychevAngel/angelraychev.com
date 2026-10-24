import CircleCounting

/-! Closed cardinality for truncated modulo-four envelopes. -/
namespace Delivery.CirclePrefixCounting
open DenseCombinatorics ConstructionCounts CircleCounting

def count (length : Nat) : Nat := 2*(length/4)+min (length%4) 2

def enumeratePrefix {n length : Nat} (range : length≤n) (i : Fin (count length)) : Fin n :=
  ⟨4*(i.val/2)+i.val%2,by have := i.isLt; unfold count at this; omega⟩

theorem periodic_prefix {n length : Nat} (range : length≤n) :
    card (fun d : Fin n => periodic d ∧ d.val<length)=count length := by
  apply card_image (enumeratePrefix range)
  · intro x y same
    have eq := congrArg Fin.val same
    dsimp [enumeratePrefix] at eq
    apply Fin.ext
    omega
  · intro d
    constructor
    · rintro ⟨hp,small⟩
      let i : Fin (count length) := ⟨2*(d.val/4)+d.val%4,by unfold periodic at hp; unfold count; omega⟩
      refine ⟨i,?_⟩
      apply Fin.ext
      dsimp [enumeratePrefix,i]
      unfold periodic at hp
      omega
    · rintro ⟨i,rfl⟩
      change ((4*(i.val/2)+i.val%2)%4=0 ∨ (4*(i.val/2)+i.val%2)%4=1) ∧
        4*(i.val/2)+i.val%2<length
      have := i.isLt
      unfold count at this
      omega

def allowed {n : Nat} (h : Nat) (d : Fin n) : Prop :=
  d.val≤n-h ∧ (periodic d ∨ d.val=h) ∧ d.val≠2*h-1

theorem allowed_count {n h : Nat} (large : 7≤h) (residue : h%4=3)
    (room : 2*h+2≤n) :
    card (@allowed n h)=count (n-h+1)+1-(if 2*h-1≤n-h then 1 else 0) := by
  let P : Fin n → Prop := fun d => periodic d ∧ d.val<n-h+1
  let Q : Fin n → Prop := fun d => d.val=h
  let U : Fin n → Prop := fun d => d.val≤n-h ∧ (periodic d ∨ d.val=h)
  have period := periodic_prefix (n := n) (length := n-h+1) (by omega)
  have point := CircleCounting.singleton_count (n := n) (h := h) (by omega)
  have separate : ∀ d, P d → Q d → False := by
    intro d hp hq
    dsimp [P,Q] at hp hq
    unfold periodic at hp
    omega
  have united := card_disjoint_union separate
  have equal : card U=card (fun d => P d ∨ Q d) := by
    apply card_congr
    intro d
    dsimp [P,Q,U]
    constructor
    · rintro ⟨small,hp | eq⟩
      · exact Or.inl ⟨hp,by omega⟩
      · exact Or.inr eq
    · rintro (⟨hp,small⟩ | eq)
      · exact ⟨by omega,Or.inl hp⟩
      · exact ⟨by omega,Or.inr eq⟩
  have total : card U=count (n-h+1)+1 := by
    change card P=count (n-h+1) at period
    change card Q=1 at point
    omega
  have split := card_partition U (fun d => d.val=2*h-1)
  have retained : card (fun d => U d ∧ ¬ d.val=2*h-1)=card (@allowed n h) := by
    apply card_congr
    intro d
    dsimp [U,allowed]
    exact ⟨fun h => ⟨h.1.1,h.1.2,h.2⟩,fun h => ⟨⟨h.1,h.2.1⟩,h.2.2⟩⟩
  rw [retained,total] at split
  by_cases kept : 2*h-1≤n-h
  · have removed : card (fun d => U d ∧ d.val=2*h-1)=1 := by
      rw [card_congr (Q := fun d : Fin n => d.val=2*h-1)]
      · exact CircleCounting.singleton_count (by omega)
      · intro d
        constructor
        · exact And.right
        · intro eq
          refine ⟨⟨by omega,?_⟩,eq⟩
          apply Or.inl
          unfold periodic
          omega
    rw [if_pos kept]
    omega
  · have removed : card (fun d => U d ∧ d.val=2*h-1)=0 := by
      apply card_eq_zero.mpr
      intro d hd
      dsimp [U] at hd
      omega
    rw [if_neg kept]
    omega

#print axioms periodic_prefix
#print axioms allowed_count
end Delivery.CirclePrefixCounting
