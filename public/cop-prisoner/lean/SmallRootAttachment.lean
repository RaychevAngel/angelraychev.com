import RootAttachment
import ConstructionCounts

/-! A concrete attachment recipe for 11≤r and at most nine added vertices.
The added missing rows are distinct pairs drawn from the five roots 2,4,6,8,10.
All parameters and all adjacencies are determined by r,k. -/
namespace Delivery.SmallRootAttachment
open FiniteGame Extremal FunctionalEndpoint
open DenseCombinatorics ConstructionCounts

def left (i : Fin 9) : Fin 5 :=
  if i.val < 4 then ⟨0,by decide⟩
  else if i.val < 7 then ⟨1,by decide⟩ else ⟨2,by decide⟩

def right (i : Fin 9) : Fin 5 :=
  if h : i.val < 4 then ⟨i.val+1,by omega⟩
  else if h' : i.val < 7 then ⟨i.val-2,by omega⟩
  else ⟨i.val-4,by have := i.isLt; omega⟩

theorem pair_distinct : ∀ i : Fin 9, left i ≠ right i := by decide

theorem pair_separate : ∀ i j : Fin 9, j ≠ i →
    ∃ u : Fin 5, (u = left j ∨ u = right j) ∧ u ≠ left i ∧ u ≠ right i := by decide

def root (r k : Nat) (hr : 11 ≤ r) (i : Fin 5) : Fin (r+k) :=
  ⟨2*i.val+2,by have := i.isLt; omega⟩

theorem root_injective {r k : Nat} {hr : 11 ≤ r} {i j : Fin 5}
    (same : root r k hr i = root r k hr j) : i = j := by
  apply Fin.ext
  have := congrArg Fin.val same
  simp only [root] at this
  omega

def code {r k : Nat} (s : Fin (r+k)) : Fin 9 := ⟨(s.val-r)%9,Nat.mod_lt _ (by decide)⟩

theorem code_injective_new {r k : Nat} (hk : k ≤ 9) {s c : Fin (r+k)}
    (hs : ¬ s.val < r) (hc : ¬ c.val < r) (same : code s = code c) : s = c := by
  apply Fin.ext
  have := congrArg Fin.val same
  have := s.isLt
  have := c.isLt
  simp only [code] at *
  omega

def f (r k : Nat) (hr : 11 ≤ r) (s : Fin (r+k)) : Fin (r+k) :=
  if hs : s.val < r then
    ⟨(partner r (by omega) ⟨s.val,hs⟩).val,by
      have := (partner r (by omega) ⟨s.val,hs⟩).isLt; omega⟩
  else ⟨0,by omega⟩

def roots {r k : Nat} (s : Fin (r+k)) : Prop :=
  s.val < r ∧ 2 ≤ s.val ∧ s.val%2 = 0

def pair (r k : Nat) (hr : 11 ≤ r) (s t : Fin (r+k)) : Prop :=
  t = root r k hr (left (code s)) ∨ t = root r k hr (right (code s))

theorem f_old {r k : Nat} (hr : 11 ≤ r) (s : Fin (r+k)) : (f r k hr s).val < r := by
  unfold f
  split <;> dsimp
  · exact (partner r (by omega) _).isLt
  · omega

theorem f_fixed {r k : Nat} (hr : 11 ≤ r) (s : Fin (r+k)) (hs : s.val < r) :
    f r k hr s ≠ s := by
  intro eq
  have val := congrArg Fin.val eq
  simp only [f,dif_pos hs] at val
  exact partner_fixed (by omega) ⟨s.val,hs⟩ (Fin.ext val)

theorem root_is_root {r k : Nat} (hr : 11 ≤ r) (i : Fin 5) :
    roots (root r k hr i) := by
  have := i.isLt
  simp only [roots,root]
  omega

theorem roots_absent {r k : Nat} (hr : 11 ≤ r) (c u : Fin (r+k))
    (hc : c.val < r) (hu : roots u) : f r k hr c ≠ u := by
  intro same
  have val := congrArg Fin.val same
  simp only [f,dif_pos hc] at val
  unfold partner at val
  rcases hu with ⟨_,low,even⟩
  split at val <;> try dsimp only at val
  · omega
  · split at val <;> try dsimp only at val <;> omega

def data (r k : Nat) (hr : 11 ≤ r) (hk : k ≤ 9) : RootAttachment.Data (Fin (r+k)) where
  old s := s.val < r
  f := f r k hr
  roots := roots
  pair := pair r k hr
  core_closed := fun c _ => f_old hr c
  core_fixed := f_fixed hr
  roots_old := fun _ h => h.1
  roots_absent := fun c hc u hu => roots_absent hr c u hc hu
  pair_roots := by
    intro c _ u pair
    rcases pair with rfl | rfl <;> exact root_is_root hr _
  separate := by
    intro s c hs hc initial
    obtain ⟨u,member,notLeft,notRight⟩ := pair_separate (code s) (code c)
      (fun same => initial (code_injective_new hk hc hs same))
    refine ⟨root r k hr u,?_,?_⟩
    · rcases member with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro pair
      rcases pair with eq | eq
      · exact notLeft (root_injective eq)
      · exact notRight (root_injective eq)
  spare := by
    intro c _ s _
    by_cases equal : root r k hr (left (code c)) = s
    · refine ⟨root r k hr (right (code c)),Or.inr rfl,?_⟩
      intro same
      exact pair_distinct (code c) (root_injective (equal.trans same.symm))
    · exact ⟨root r k hr (left (code c)),Or.inl rfl,equal⟩

def good {r k : Nat} (s : Fin (r+k)) : Prop :=
  2 ≤ s.val ∧ s.val%2 = 0 ∧ s.val+1 < r

instance {r k : Nat} (s : Fin (r+k)) : Decidable (good s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem good_unique {r k : Nat} (hr : 11 ≤ r) {s c : Fin (r+k)}
    (hs : good s) (hc : c.val < r) (same : f r k hr c = f r k hr s) : c = s := by
  have oldS : s.val < r := by have := hs.2.2; omega
  have paired : Paired (⟨s.val,oldS⟩ : Fin r) := hs
  have unique := ((partner_root (by omega) ⟨s.val,oldS⟩).mpr paired).2
  have val := congrArg Fin.val same
  simp only [f,dif_pos hc,dif_pos oldS] at val
  have eq := unique ⟨c.val,hc⟩ (Fin.ext val)
  exact Fin.ext (congrArg (fun x : Fin r => x.val) eq)

theorem good_indirect {r k : Nat} (hr : 11 ≤ r) (hk : k ≤ 9) {s : Fin (r+k)}
    (hs : good s) : Indirect (data r k hr hk).edge s (f r k hr s) := by
  apply RootAttachment.Data.old_indirect
  · exact ⟨by have := hs.2.2; omega,hs.1,hs.2.1⟩
  · exact fun c hc h => good_unique hr hs hc h

theorem added_indirect {r k : Nat} (hr : 11 ≤ r) (hk : k ≤ 9) {s t : Fin (r+k)}
    (hs : ¬ s.val < r) (ht : pair r k hr s t) :
    Indirect (data r k hr hk).edge s t :=
  RootAttachment.Data.new_indirect _ hs ht

theorem good_count (r k : Nat) : card (@good r k) = (r-2)/2 := by
  let image : Fin ((r-2)/2) → Fin (r+k) :=
    fun i => ⟨(rootVertex r i).val,by have := (rootVertex r i).isLt; omega⟩
  apply card_image image
  · intro i j same
    apply rootVertex_injective
    exact Fin.ext (congrArg (fun x : Fin (r+k) => x.val) same)
  · intro s
    constructor
    · rintro ⟨low,even,room⟩
      refine ⟨⟨(s.val-2)/2,by omega⟩,?_⟩
      apply Fin.ext
      dsimp [image,rootVertex]
      omega
    · rintro ⟨i,rfl⟩
      have := i.isLt
      dsimp [good,image,rootVertex]
      omega

theorem new_count (r k : Nat) : card (fun s : Fin (r+k) => ¬ s.val < r) = k := by
  let image : Fin k → Fin (r+k) := fun i => ⟨r+i.val,by have := i.isLt; omega⟩
  apply card_image image
  · intro i j same
    apply Fin.ext
    have := congrArg Fin.val same
    dsimp [image] at this
    omega
  · intro s
    constructor
    · intro hs
      refine ⟨⟨s.val-r,by have := s.isLt; omega⟩,?_⟩
      apply Fin.ext
      dsimp [image]
      omega
    · rintro ⟨i,rfl⟩
      dsimp [image]
      omega

theorem pair_card {r k : Nat} (hr : 11 ≤ r) (s : Fin (r+k)) :
    card (pair r k hr s) = 2 := by
  have distinct : root r k hr (left (code s)) ≠ root r k hr (right (code s)) :=
    fun same => pair_distinct (code s) (root_injective same)
  have perm := (List.perm_ext_iff_of_nodup (elems_nodup (pair r k hr s))
    (show [root r k hr (left (code s)),root r k hr (right (code s))].Nodup by
      simp [distinct])).mpr (fun t => by simp [pair])
  change (elems (pair r k hr s)).length = 2
  exact perm.length_eq

theorem singleton_card {n : Nat} (t : Fin n) : card (fun u => u = t) = 1 := by
  classical
  rw [card_eq]
  exact singleton_count t

theorem missing_iff {r k : Nat} (hr : 11 ≤ r) (hk : k ≤ 9) (s t : Fin (r+k)) :
    (s ≠ t ∧ ¬ (data r k hr hk).edge s t) ↔ (data r k hr hk).missing s t := by
  classical
  constructor
  · intro h
    exact Classical.byContradiction (fun notMissing => h.2 ⟨h.1,notMissing⟩)
  · intro h
    exact ⟨fun same => (data r k hr hk).missing_loopless s (same ▸ h),fun edge => edge.2 h⟩

theorem missing_row {r k : Nat} (hr : 11 ≤ r) (hk : k ≤ 9) (s : Fin (r+k)) :
    card (fun t => s ≠ t ∧ ¬ (data r k hr hk).edge s t) =
      if ¬ s.val < r then 2 else 1 := by
  classical
  rw [card_congr (missing_iff hr hk s)]
  by_cases hs : s.val < r
  · rw [if_neg (fun h => h hs)]
    have same : card ((data r k hr hk).missing s) = card (fun t => t = f r k hr s) := by
      apply card_congr
      intro t
      simp [RootAttachment.Data.missing,data,hs,eq_comm]
    rw [same,singleton_card]
  · rw [if_pos hs]
    have same : card ((data r k hr hk).missing s) = card (pair r k hr s) := by
      apply card_congr
      intro t
      simp [RootAttachment.Data.missing,data,hs]
    rw [same,pair_card]

theorem missing_count {r k : Nat} (hr : 11 ≤ r) (hk : k ≤ 9) :
    missingCount (data r k hr hk).edge = r+2*k := by
  classical
  rw [missing_rows]
  simp only [missing_row hr hk]
  rw [one_or_two,List.length_finRange]
  have count := new_count r k
  rw [card_eq] at count
  omega

theorem score_row_lower {r k : Nat} (hr : 11 ≤ r) (hk : k ≤ 9) (s : Fin (r+k)) :
    (if good s then 1 else 0) + (if ¬ s.val < r then 2 else 0) ≤
      card (Indirect (data r k hr hk).edge s) := by
  classical
  by_cases hs : s.val < r
  · simp only [hs,not_true_eq_false,if_false,Nat.add_zero]
    by_cases goodS : good s
    · rw [if_pos goodS]
      have bound := card_mono (P := fun t => t = f r k hr s)
        (Q := Indirect (data r k hr hk).edge s)
        (fun t ht => ht ▸ good_indirect hr hk goodS)
      rw [singleton_card] at bound
      exact bound
    · simp [goodS]
  · have notGood : ¬ good s := fun h => hs (by have := h.2.2; omega)
    simp only [notGood,if_false,hs,Nat.zero_add]
    have bound := card_mono (P := pair r k hr s)
      (fun t ht => added_indirect hr hk hs ht)
    rw [pair_card] at bound
    exact bound

theorem score_lower {r k : Nat} (hr : 11 ≤ r) (hk : k ≤ 9) :
    (r-2)/2+2*k ≤ score (data r k hr hk).edge := by
  classical
  rw [score_rows]
  have bound := sum_mono (List.finRange (r+k)) (score_row_lower hr hk)
  rw [weighted_indicators] at bound
  have goodCount := good_count r k
  have newCount := new_count r k
  rw [card_eq] at goodCount newCount
  simpa only [Nat.one_mul,goodCount,newCount] using bound

theorem arc_count {r k : Nat} (hr : 11 ≤ r) (hk : k ≤ 9) :
    arcCount (data r k hr hk).edge = (r+k)*(r+k-3)+r := by
  have total := arcCount_add_missingCount (data r k hr hk).edge (data r k hr hk).loopless
  rw [missing_count hr hk] at total
  have identity : (r+k)*(r+k-1) = (r+k)*(r+k-3)+2*(r+k) := by
    have eq : r+k-1 = (r+k-3)+2 := by omega
    rw [eq,Nat.mul_add,Nat.mul_comm (r+k) 2]
  omega

theorem score_exact {r k : Nat} (hr : 11 ≤ r) (hk : k ≤ 9) :
    score (data r k hr hk).edge = (r-2)/2+2*k := by
  have lower := score_lower hr hk
  have upper := DenseStaircase.bound_at_offset (data r k hr hk).edge
    (data r k hr hk).loopless (by omega) (by omega) (by omega) (arc_count hr hk)
  unfold DenseCounting.ceilHalf at upper
  omega

theorem maximum {r k : Nat} (hr : 11 ≤ r) (hk : k ≤ 9) :
    IsMaximum (r+k) ((r+k)*(r+k-3)+r) ((r-2)/2+2*k) := by
  constructor
  · intro E noLoops arrows
    have upper := DenseStaircase.bound_at_offset E noLoops (by omega)
      (by omega) (by omega) arrows
    unfold DenseCounting.ceilHalf at upper
    omega
  · exact ⟨(data r k hr hk).edge,(data r k hr hk).loopless,
      arc_count hr hk,score_exact hr hk⟩

#print axioms data
#print axioms good_indirect
#print axioms added_indirect
#print axioms maximum
end Delivery.SmallRootAttachment
