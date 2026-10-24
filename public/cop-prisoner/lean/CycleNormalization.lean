import FiniteHall
import CyclicArithmetic
import FiniteExclusionConjugacy

/-! Finite permutation normalization by disjoint orbit lists. -/
namespace Delivery.CycleNormalization
open DenseCombinatorics FiniteHall CyclicArithmetic

def iterate {V : Type} (f : V → V) : Nat → V → V
  | 0, x => x
  | k+1, x => f (iterate f k x)

@[simp] theorem iterate_zero {V : Type} (f : V → V) (x : V) : iterate f 0 x = x := rfl
@[simp] theorem iterate_succ {V : Type} (f : V → V) (k : Nat) (x : V) :
    iterate f (k+1) x = f (iterate f k x) := rfl

theorem iterate_add {V : Type} (f : V → V) (a b : Nat) (x : V) :
    iterate f (a+b) x = iterate f a (iterate f b x) := by
  induction a with
  | zero => simp only [Nat.zero_add,iterate_zero]
  | succ a ih => simpa only [Nat.succ_add,iterate_succ] using congrArg f ih

theorem iterate_injective {V : Type} {f : V → V}
    (injective : ∀ x y, f x = f y → x = y) (k : Nat) :
    ∀ x y, iterate f k x = iterate f k y → x = y := by
  induction k with
  | zero => exact fun _ _ h => h
  | succ k ih =>
    intro x y same
    exact ih x y (injective _ _ same)

theorem return_from_repeat {V : Type} {f : V → V}
    (injective : ∀ x y, f x = f y → x = y) (x : V) {a b : Nat}
    (ordered : a ≤ b) (same : iterate f a x = iterate f b x) :
    iterate f (b-a) x = x := by
  apply Eq.symm
  apply iterate_injective injective a
  rw [← iterate_add,show a + (b-a) = b by omega]
  exact same

theorem exists_return {n : Nat} (f : Fin n → Fin n)
    (injective : ∀ x y, f x = f y → x = y) (x : Fin n) :
    ∃ p, 0 < p ∧ iterate f p x = x := by
  classical
  apply Classical.byContradiction
  intro absent
  have orbitInj : ∀ i j : Fin (n+1), iterate f i.val x = iterate f j.val x → i = j := by
    intro i j same
    apply Fin.ext
    by_cases ordered : i.val ≤ j.val
    · have returned := return_from_repeat injective x ordered same
      apply Classical.byContradiction
      intro different
      exact absent ⟨j.val-i.val,by omega,returned⟩
    · have returned := return_from_repeat injective x (by omega) same.symm
      exact False.elim (absent ⟨i.val-j.val,by omega,returned⟩)
  have bound := card_injection (P := fun _ : Fin (n+1) => True)
    (Q := fun _ : Fin n => True) (fun i => iterate f i.val x)
    (fun _ _ => trivial) (fun i j _ _ same => orbitInj i j same)
  rw [card_true,card_true] at bound
  omega

theorem exists_minimal {P : Nat → Prop} (inhabited : ∃ p, P p) :
    ∃ p, P p ∧ ∀ q, q < p → ¬ P q := by
  classical
  obtain ⟨p,hp⟩ := inhabited
  induction p using Nat.strongRecOn with
  | ind p ih =>
    by_cases earlier : ∃ q, q < p ∧ P q
    · obtain ⟨q,less,hq⟩ := earlier
      exact ih q less hq
    · exact ⟨p,hp,fun q less hq => earlier ⟨q,less,hq⟩⟩

structure Cycle {n : Nat} (f : Fin n → Fin n) where
  size : Nat
  positive : 0 < size
  vertex : Fin size → Fin n
  injective : ∀ i j, vertex i = vertex j → i = j
  successor : ∀ i, f (vertex i) = vertex (shift i 1)

namespace Cycle
variable {n : Nat} {f : Fin n → Fin n}

def entries (c : Cycle f) : List (Fin n) := (List.finRange c.size).map c.vertex

def support (c : Cycle f) (x : Fin n) : Prop := ∃ i, c.vertex i = x

@[simp] theorem mem_entries (c : Cycle f) (x : Fin n) : x ∈ c.entries ↔ c.support x := by
  simp [entries,support]

@[simp] theorem length_entries (c : Cycle f) : c.entries.length = c.size := by
  simp [entries]

theorem nodup_entries (c : Cycle f) : c.entries.Nodup := by
  apply List.pairwise_map.mpr
  exact (List.nodup_finRange c.size).imp (fun h equal => h (c.injective _ _ equal))

theorem card_support (c : Cycle f) : card c.support = c.size := by
  have perm := (List.perm_ext_iff_of_nodup (elems_nodup c.support) c.nodup_entries).mpr
    (fun x => by simp)
  change (elems c.support).length = c.size
  rw [perm.length_eq,c.length_entries]

theorem backward (c : Cycle f) (injective : ∀ x y, f x = f y → x = y)
    {x : Fin n} (inside : c.support (f x)) : c.support x := by
  obtain ⟨i,hi⟩ := inside
  have previous : f (c.vertex (prev i)) = f x := by
    rw [c.successor,shift_prev]
    exact hi
  exact ⟨prev i,injective _ _ previous⟩

theorem size_two (c : Cycle f) (fixed : ∀ x, f x ≠ x) : 2 ≤ c.size := by
  apply Classical.byContradiction
  intro small
  have one : c.size = 1 := by have := c.positive; omega
  let i : Fin c.size := ⟨0,c.positive⟩
  have same : shift i 1 = i := by
    apply Fin.ext
    simp [shift,one,i]
  exact fixed (c.vertex i) (by simpa only [same] using c.successor i)

end Cycle

/-- The minimal positive return gives one simple cycle within a closed set. -/
theorem cycle_inside {n : Nat} (f : Fin n → Fin n)
    (injective : ∀ x y, f x = f y → x = y)
    (P : Fin n → Prop) (closed : ∀ x, P x → P (f x)) {x : Fin n} (hx : P x) :
    ∃ c : Cycle f, ∀ y, c.support y → P y := by
  obtain ⟨p,⟨positive,returned⟩,minimal⟩ := exists_minimal (exists_return f injective x)
  have inside : ∀ k, P (iterate f k x) := by
    intro k
    induction k with
    | zero => exact hx
    | succ k ih => exact closed _ ih
  let vertex (i : Fin p) := iterate f i.val x
  have orbitInj : ∀ i j : Fin p, vertex i = vertex j → i = j := by
    intro i j same
    apply Fin.ext
    by_cases ordered : i.val ≤ j.val
    · apply Classical.byContradiction
      intro different
      have ret := return_from_repeat injective x ordered same
      exact minimal (j.val-i.val) (by have := j.isLt; omega) ⟨by omega,ret⟩
    · have ret := return_from_repeat injective x (by omega) same.symm
      exact False.elim (minimal (i.val-j.val) (by have := i.isLt; omega) ⟨by omega,ret⟩)
  have successor : ∀ i : Fin p, f (vertex i) = vertex (shift i 1) := by
    intro i
    change iterate f (i.val+1) x = iterate f ((i.val+1)%p) x
    by_cases before : i.val+1 < p
    · rw [Nat.mod_eq_of_lt before]
    · have last : i.val+1 = p := by have := i.isLt; omega
      rw [last,Nat.mod_self,iterate_zero]
      exact returned
  let c : Cycle f := ⟨p,positive,vertex,orbitInj,successor⟩
  refine ⟨c,?_⟩
  intro y hy
  obtain ⟨i,rfl⟩ := hy
  exact inside i.val

/-- Every closed finite source set decomposes into disjoint simple cycles. -/
theorem cycle_decomposition {n : Nat} (f : Fin n → Fin n)
    (injective : ∀ x y, f x = f y → x = y) (P : Fin n → Prop)
    (closed : ∀ x, P x → P (f x)) :
    ∃ cs : List (Cycle f), (cs.flatMap Cycle.entries).Nodup ∧
      ∀ x, x ∈ cs.flatMap Cycle.entries ↔ P x := by
  classical
  have main : ∀ m : Nat, ∀ P : Fin n → Prop, card P = m →
      (∀ x, P x → P (f x)) →
      ∃ cs : List (Cycle f), (cs.flatMap Cycle.entries).Nodup ∧
        ∀ x, x ∈ cs.flatMap Cycle.entries ↔ P x := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro P size closed
      by_cases empty : card P = 0
      · refine ⟨[],by simp,?_⟩
        intro x
        simp [card_eq_zero.mp empty x]
      · obtain ⟨x,hx⟩ := (card_positive (P := P)).mp (by omega)
        obtain ⟨c,inside⟩ := cycle_inside f injective P closed hx
        let Q := fun y => P y ∧ ¬ c.support y
        have qclosed : ∀ y, Q y → Q (f y) := by
          intro y hy
          exact ⟨closed y hy.1,fun h => hy.2 (c.backward injective h)⟩
        have split := card_difference inside
        rw [c.card_support] at split
        have smaller : card Q < m := by
          have positive := c.positive
          change card Q + c.size = card P at split
          omega
        obtain ⟨cs,nd,members⟩ := ih (card Q) smaller Q rfl qclosed
        refine ⟨c :: cs,?_,?_⟩
        · rw [List.flatMap_cons,List.nodup_append]
          refine ⟨c.nodup_entries,nd,?_⟩
          intro y hy z hz same
          have hyc := (c.mem_entries y).mp hy
          exact ((members z).mp hz).2 (same ▸ hyc)
        · intro y
          simp only [List.flatMap_cons,List.mem_append,c.mem_entries,members]
          exact ⟨fun h => h.elim (inside y) And.left,
            fun h => by by_cases hc : c.support y; exact Or.inl hc; exact Or.inr ⟨h,hc⟩⟩
  exact main (card P) P rfl closed

/-- Sorting cycle records gives a complete vertex enumeration with ordered
cycle lengths. No choice of canonical labels has yet been assumed. -/
theorem sorted_decomposition {n : Nat} (f : Fin n → Fin n)
    (injective : ∀ x y, f x = f y → x = y) :
    ∃ cs : List (Cycle f), (cs.flatMap Cycle.entries).Nodup ∧
      (∀ x, x ∈ cs.flatMap Cycle.entries) ∧
      (cs.flatMap Cycle.entries).length = n ∧
      cs.Pairwise (fun a b => a.size ≤ b.size) := by
  obtain ⟨raw,nd,members⟩ := cycle_decomposition f injective (fun _ => True)
    (fun _ _ => trivial)
  let cs := raw.mergeSort (fun a b => decide (a.size ≤ b.size))
  have perm := List.mergeSort_perm raw (fun a b : Cycle f => decide (a.size ≤ b.size))
  have flatPerm := perm.flatMap_right Cycle.entries
  have nd' : (cs.flatMap Cycle.entries).Nodup := flatPerm.symm.nodup nd
  have members' : ∀ x, x ∈ cs.flatMap Cycle.entries := by
    intro x
    exact flatPerm.mem_iff.mpr ((members x).mpr trivial)
  have total := (List.perm_ext_iff_of_nodup nd' (List.nodup_finRange n)).mpr
    (fun x => ⟨fun _ => List.mem_finRange x,fun _ => members' x⟩)
  refine ⟨cs,nd',members',?_,?_⟩
  · simpa using total.length_eq
  · have sorted := List.pairwise_mergeSort
      (le := fun a b : Cycle f => decide (a.size ≤ b.size))
      (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
      (by intro a b; simp only [Bool.or_eq_true,decide_eq_true_eq]; omega) raw
    simpa only [decide_eq_true_eq] using sorted

/-- Exactly the eight sorted partitions of nine into cycle lengths at least two. -/
theorem nine_partitions (xs : List Nat) (large : ∀ x, x ∈ xs → 2 ≤ x)
    (sorted : xs.Pairwise (· ≤ ·)) (total : xs.sum = 9) :
    xs = [2,2,2,3] ∨ xs = [2,2,5] ∨ xs = [2,3,4] ∨ xs = [2,7] ∨
    xs = [3,3,3] ∨ xs = [3,6] ∨ xs = [4,5] ∨ xs = [9] := by
  cases xs with
  | nil => simp at total
  | cons a xs =>
    have ha := large a (by simp)
    cases xs with
    | nil => simp_all
    | cons b xs =>
      have hb := large b (by simp)
      have ab : a ≤ b := (List.pairwise_cons.mp sorted).1 b (by simp)
      cases xs with
      | nil =>
        simp only [List.sum_cons,List.sum_nil,Nat.add_zero] at total
        have cases : (a = 2 ∧ b = 7) ∨ (a = 3 ∧ b = 6) ∨ (a = 4 ∧ b = 5) := by omega
        rcases cases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp
      | cons c xs =>
        have hc := large c (by simp)
        have bc : b ≤ c := (List.pairwise_cons.mp (List.pairwise_cons.mp sorted).2).1 c (by simp)
        cases xs with
        | nil =>
          simp only [List.sum_cons,List.sum_nil,Nat.add_zero] at total
          have cases : (a = 2 ∧ b = 2 ∧ c = 5) ∨ (a = 2 ∧ b = 3 ∧ c = 4) ∨
              (a = 3 ∧ b = 3 ∧ c = 3) := by omega
          rcases cases with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;> simp
        | cons d xs =>
          have hd := large d (by simp)
          have cd : c ≤ d := (List.pairwise_cons.mp
            (List.pairwise_cons.mp (List.pairwise_cons.mp sorted).2).2).1 d (by simp)
          cases xs with
          | nil =>
            simp only [List.sum_cons,List.sum_nil,Nat.add_zero] at total
            have values : a = 2 ∧ b = 2 ∧ c = 2 ∧ d = 3 := by omega
            rcases values with ⟨rfl,rfl,rfl,rfl⟩
            simp
          | cons e xs =>
            have he := large e (by simp)
            simp only [List.sum_cons] at total
            omega

/-- Successor positions in contiguous cycle blocks. Positions past the full
list are left unchanged, which makes the optional-index identity uniform. -/
def blockNext : List Nat → Nat → Nat
  | [], i => i
  | d :: ds, i => if i < d then (i+1) % d else d + blockNext ds (i-d)

theorem blockNext_bound (ds : List Nat) (positive : ∀ d, d ∈ ds → 0 < d)
    {i : Nat} (inside : i < ds.sum) : blockNext ds i < ds.sum := by
  induction ds generalizing i with
  | nil => simp at inside
  | cons d ds ih =>
    have hd := positive d (by simp)
    simp only [List.sum_cons] at inside ⊢
    by_cases first : i < d
    · simp only [blockNext,first,if_true]
      have := Nat.mod_lt (i+1) hd
      omega
    · simp only [blockNext,first,if_false]
      have tail := ih (fun e he => positive e (by simp [he])) (i := i-d) (by omega)
      omega

theorem entries_get {n : Nat} {f : Fin n → Fin n} (c : Cycle f) (i : Nat)
    (inside : i < c.size) : c.entries[i]'(by simpa using inside) = c.vertex ⟨i,inside⟩ := by
  simp [Cycle.entries]

theorem entries_successor {n : Nat} {f : Fin n → Fin n} (c : Cycle f) (i : Nat)
    (inside : i < c.size) :
    (c.entries[i]?).map f = c.entries[(i+1)%c.size]? := by
  have nextInside := Nat.mod_lt (i+1) c.positive
  rw [List.getElem?_eq_getElem (by simpa using inside),
    List.getElem?_eq_getElem (by simpa using nextInside)]
  simp only [Option.map_some,Option.some.injEq]
  rw [entries_get,entries_get]
  exact c.successor ⟨i,inside⟩

/-- Flattening orbit lists conjugates their successor to the block successor. -/
theorem flatten_successor {n : Nat} {f : Fin n → Fin n} (cs : List (Cycle f)) (i : Nat) :
    ((cs.flatMap Cycle.entries)[i]?).map f =
      (cs.flatMap Cycle.entries)[blockNext (cs.map Cycle.size) i]? := by
  induction cs generalizing i with
  | nil => simp [blockNext]
  | cons c cs ih =>
    simp only [List.flatMap_cons,List.map_cons]
    by_cases first : i < c.size
    · have nextInside := Nat.mod_lt (i+1) c.positive
      simp only [blockNext,first,if_true,List.getElem?_append,Cycle.length_entries,
        nextInside]
      exact entries_successor c i first
    · have notFirst : ¬ c.size + blockNext (cs.map Cycle.size) (i-c.size) < c.size := by omega
      simp only [blockNext,first,if_false,List.getElem?_append,Cycle.length_entries,
        notFirst,Nat.add_sub_cancel_left]
      exact ih (i-c.size)

/-- Any table agreeing with the successor of a complete cycle enumeration
is conjugate to the original permutation. -/
theorem conjugacy_of_table {n : Nat} (f d : Fin n → Fin n) (cs : List (Cycle f))
    (nd : (cs.flatMap Cycle.entries).Nodup)
    (size : (cs.flatMap Cycle.entries).length = n)
    (table : ∀ i : Fin n, (d i).val = blockNext (cs.map Cycle.size) i.val) :
    Nonempty (FiniteExclusion.Conjugacy f d) := by
  classical
  let xs := cs.flatMap Cycle.entries
  let order (i : Fin n) : Fin n := xs[i.val]'(by dsimp [xs]; rw [size]; exact i.isLt)
  have orderInj : ∀ i j, order i = order j → i = j := by
    intro i j same
    apply Fin.ext
    exact (List.getElem_inj nd).mp same
  have onto := injective_surjective order orderInj
  let inverse (x : Fin n) : Fin n := Classical.choose (onto x)
  have right (x : Fin n) : order (inverse x) = x := Classical.choose_spec (onto x)
  have left (i : Fin n) : inverse (order i) = i := orderInj _ _ (right (order i))
  have follow (i : Fin n) : f (order i) = order (d i) := by
    have h := flatten_successor cs i.val
    rw [← table i] at h
    rw [List.getElem?_eq_getElem (by rw [size]; exact i.isLt),
      List.getElem?_eq_getElem (by rw [size]; exact (d i).isLt)] at h
    exact Option.some.inj h
  refine ⟨⟨inverse,order,right,left,?_⟩⟩
  intro x
  apply orderInj
  rw [right,← follow,right]

#print axioms cycle_decomposition
#print axioms sorted_decomposition
#print axioms nine_partitions
#print axioms conjugacy_of_table
end Delivery.CycleNormalization
