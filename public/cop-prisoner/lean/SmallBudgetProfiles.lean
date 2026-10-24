import DegreeProfileRelabeling
import RowPrefixCutLoss
import Init.Data.List.Sort.Lemmas

/-! Complete sorted joint-degree catalogues with prescribed sums. -/
namespace Delivery.SmallBudgetProfiles
open FiniteGame Extremal DenseCombinatorics ConstructionCounts SparseSupport

theorem perm_sum {xs ys : List Nat} (p : xs.Perm ys) : xs.sum=ys.sum := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp only [List.sum_cons]; omega
  | swap a b xs => simp only [List.sum_cons]; omega
  | trans _ _ ih1 ih2 => omega

def regular (zeroTwo : Bool) (a : Nat) : Prop :=
  (0<a/16 ∧ 0<a%16) ∨ (zeroTwo=true ∧ a/16+a%16=2)
instance (zeroTwo : Bool) (a : Nat) : Decidable (regular zeroTwo a) :=
  inferInstanceAs (Decidable (_∨_))

/-- Base-sixteen labels cover every support order at most sixteen. -/
def alphabet (n : Nat) (zeroTwo : Bool) : List Nat :=
  (List.range (16*n)).filter fun a => decide (a%16<n ∧ 2≤a/16+a%16 ∧ regular zeroTwo a)

def profiles (n : Nat) (zeroTwo : Bool) : Nat → Nat → Nat → Nat → List (List Nat)
  | 0,_,d,r => if d=0 ∧ r=0 then [[]] else []
  | slots+1,lo,d,r => if 2*(slots+1)≤d+r then (alphabet n zeroTwo).flatMap fun a =>
      if lo≤a ∧ a/16≤d ∧ a%16≤r then
        (profiles n zeroTwo slots a (d-a/16) (r-a%16)).map (a::·)
      else []
    else []

theorem total_minimum (n : Nat) (zeroTwo : Bool) (xs : List Nat)
    (members : ∀a∈xs,a∈alphabet n zeroTwo) :
    2*xs.length≤(xs.map (·/16)).sum+(xs.map (·%16)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := members a (by simp)
    have rest := ih (fun b hb => members b (by simp [hb]))
    simp only [alphabet,List.mem_filter,decide_eq_true_eq] at ha
    simp only [List.length_cons,List.map_cons,List.sum_cons]
    omega

theorem profiles_complete (n : Nat) (zeroTwo : Bool) (xs : List Nat) (lo d r : Nat)
    (members : ∀a∈xs,a∈alphabet n zeroTwo) (sorted : xs.Pairwise (·≤·))
    (lower : ∀a∈xs,lo≤a) (outSum : (xs.map (·/16)).sum=d)
    (inSum : (xs.map (·%16)).sum=r) : xs∈profiles n zeroTwo xs.length lo d r := by
  induction xs generalizing lo d r with
  | nil =>
    have hd : d=0 := by simpa using outSum.symm
    have hr : r=0 := by simpa using inSum.symm
    subst d; subst r; simp [profiles]
  | cons a xs ih =>
    have pair := List.pairwise_cons.mp sorted
    simp only [List.map_cons,List.sum_cons] at outSum inSum
    have step : lo≤a ∧ a/16≤d ∧ a%16≤r := ⟨lower a (by simp),by omega,by omega⟩
    have enough : 2*(xs.length+1)≤d+r := by
      have h := total_minimum n zeroTwo (a::xs) members
      simp only [List.length_cons,List.map_cons,List.sum_cons] at h
      omega
    simp only [List.length_cons,profiles,if_pos enough,List.mem_flatMap]
    refine ⟨a,members a (by simp),?_⟩
    rw [if_pos step]
    apply List.mem_map.mpr
    refine ⟨xs,ih a (d-a/16) (r-a%16) (fun b hb => members b (by simp [hb])) pair.2 pair.1 (by omega) (by omega),rfl⟩

def label (d e : Fin n → Nat) (x : Fin n) : Nat := 16*d x+e x

def sorted (d e : Fin n → Nat) : List Nat :=
  ((List.finRange n).map (label d e)).mergeSort (fun a b => a≤b)

theorem sorted_perm (d e : Fin n → Nat) :
    (sorted d e).Perm ((List.finRange n).map (label d e)) := List.mergeSort_perm _ _

theorem sorted_length (d e : Fin n → Nat) : (sorted d e).length=n := by
  simpa using (sorted_perm d e).length_eq

def value (xs : List Nat) (i : Fin n) : Nat := xs[i.val]?.getD 0
def D (xs : List Nat) (i : Fin n) : Nat := value xs i/16
def R (xs : List Nat) (i : Fin n) : Nat := value xs i%16

theorem values_eq (xs : List Nat) (length : xs.length=n) :
    (List.finRange n).map (value xs)=xs := by
  apply List.ext_getElem
  · simp [length]
  · intro i h1 h2
    simp only [List.getElem_map,List.getElem_finRange,value]
    exact Option.getD_some (a:=xs[i]) (b:=0) ▸ congrArg (fun o => o.getD 0) (List.getElem?_eq_getElem h2)

theorem sorted_member {n m : Nat} (d e : Fin n → Nat) (zeroTwo : Bool) (small : n≤16)
    (pd : ∀x,d x<n) (pe : ∀x,e x<n) (total : ∀x,2≤d x+e x)
    (regularity : ∀x,(0<d x ∧ 0<e x) ∨ (zeroTwo=true ∧ d x+e x=2))
    (td : ((List.finRange n).map d).sum=m) (te : ((List.finRange n).map e).sum=m) :
    sorted d e∈profiles n zeroTwo n 0 m m := by
  have perm := sorted_perm d e
  have len := sorted_length d e
  have result : sorted d e∈profiles n zeroTwo (sorted d e).length 0 m m := by
    apply profiles_complete
    · intro a ha
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp (perm.mem_iff.mp ha)
      have hd := pd x; have he := pe x; have ht := total x; have good := regularity x
      simp only [alphabet,List.mem_filter,List.mem_range,label,regular]
      constructor
      · omega
      · apply decide_eq_true
        have q : (16*d x+e x)/16=d x := by omega
        have r : (16*d x+e x)%16=e x := by omega
        rw [q,r]
        exact ⟨he,ht,good⟩
    · have h := List.pairwise_mergeSort (le:=fun a b : Nat => a≤b)
        (by intro a b c h1 h2; exact decide_eq_true (Nat.le_trans (of_decide_eq_true h1) (of_decide_eq_true h2)))
        (by intro a b; simp only [Bool.or_eq_true,decide_eq_true_eq]; omega)
        ((List.finRange n).map (label d e))
      exact h.imp (fun h => of_decide_eq_true h)
    · intro a _; omega
    · have eq := perm_sum (perm.map (·/16))
      rw [List.map_map] at eq
      have vals : (fun x => label d e x/16)=d := by
        funext x; have he := pe x; dsimp [label]; omega
      simpa only [Function.comp_def,vals,td] using eq
    · have eq := perm_sum (perm.map (·%16))
      rw [List.map_map] at eq
      have vals : (fun x => label d e x%16)=e := by
        funext x; have he := pe x; dsimp [label]; omega
      simpa only [Function.comp_def,vals,te] using eq
  simpa only [len] using result

theorem relabel_reversed (E : Graph (Fin n)) (loops : Loopless E)
    (inSmall : ∀x,indegree E x<16) :
    ∃F : Graph (Fin n), Nonempty (GraphRelabeling.Iso F E) ∧
      RowPrefix.Prescribed (D (sorted (outdegree E) (indegree E)).reverse)
        (R (sorted (outdegree E) (indegree E)).reverse) F := by
  classical
  let d := outdegree E
  let e := indegree E
  let xs := (sorted d e).reverse
  have values : (List.finRange n).map (value xs)=xs := values_eq xs (by simp only [xs,List.length_reverse,sorted_length])
  have counts (a : Nat) : card (fun x => label d e x=a)=card (fun x : Fin n => value xs x=a) := by
    rw [card_eq,card_eq]
    have eq := (((List.reverse_perm (sorted d e)).trans (sorted_perm d e)).filter (fun b => decide (b=a))).length_eq
    change (xs.filter (fun b => decide (b=a))).length=((List.finRange n).map (label d e) |>.filter (fun b => decide (b=a))).length at eq
    rw [←values,List.filter_map,List.filter_map,List.length_map,List.length_map] at eq
    exact eq.symm
  obtain ⟨f,g,left,right,labels⟩ := DegreeProfileRelabeling.labelled_bijection (label d e) (value xs) counts
  let F : Graph (Fin n) := fun s t => E (f s) (f t)
  let iso : GraphRelabeling.Iso F E := ⟨f,g,left,right,fun _ _ => Iff.rfl⟩
  refine ⟨F,⟨iso⟩,iso.symm.loopless loops,?_,?_⟩
  · intro x
    have equal : outdegree F x=outdegree E (f x) :=
      IrregularTenProfile.card_pullback f g left right (E (f x))
    have labs := labels x; have bound := inSmall (f x)
    change 16*outdegree E (f x)+indegree E (f x)=value xs x at labs
    change outdegree F x=value xs x/16
    omega
  · intro x
    have equal : indegree F x=indegree E (f x) :=
      IrregularTenProfile.card_pullback f g left right (fun s => E s (f x))
    have labs := labels x; have bound := inSmall (f x)
    change 16*outdegree E (f x)+indegree E (f x)=value xs x at labs
    change indegree F x=value xs x%16
    omega


open RowPrefix

def hard (n bound : Nat) (xs : List Nat) : Prop :=
  bound < eligibleCount (D (n:=n) xs.reverse) (R xs.reverse) ∧
  bound + degreeSum (D (n:=n) xs.reverse) <
    eligibleCount (D (n:=n) xs.reverse) (R xs.reverse) +
      lowSum (D (n:=n) xs.reverse) + lowSum (R (n:=n) xs.reverse)
instance (n bound : Nat) (xs : List Nat) : Decidable (hard n bound xs) :=
  inferInstanceAs (Decidable (_∧_))

def hardProfiles (n m bound : Nat) (zeroTwo : Bool) : List (List Nat) :=
  (profiles n zeroTwo n 0 m m).filter (fun xs => decide (hard n bound xs))

theorem active_only {n : Nat} (D R : Fin n → Nat) (bound : Nat)
    (numeric : eligibleCount D R≤bound) : Upper D R [] bound := by
  intro E valid agrees
  have subset := arcs_mono (E:=Indirect E) (F:=fun s t => 2≤D s ∧ 2≤R t ∧ s≠t) (by
    intro s t pair
    have a := live_outdegree valid.1 pair
    have b := live_indegree pair
    rw [valid.2.1] at a
    rw [valid.2.2] at b
    exact ⟨a,b,pair.1⟩)
  have count : arcCount (fun s t => 2≤D s ∧ 2≤R t ∧ s≠t)=eligibleCount D R := arcCount_eq _
  change score E≤_ at subset
  omega


theorem cut_only {n : Nat} (D R : Fin n → Nat) (bound : Nat)
    (numeric : eligibleCount D R + lowSum D + lowSum R ≤ bound+degreeSum D) :
    Upper D R [] bound := by
  apply cut_count_sound D R [] bound (fun _ => 0)
  · intro s t h; simp [bit] at h
  · intro E valid agrees s t h; simp [bit] at h
  · have zero : allowedCount (fun _ : Fin n => 0)=0 := by
      simp [allowedCount,bit]
    rw [zero]
    omega

theorem upper_of_hard {n m bound : Nat} {zeroTwo : Bool}
    (checked : ∀xs∈hardProfiles n m bound zeroTwo, Upper (D (n:=n) xs.reverse) (R xs.reverse) [] bound)
    (xs : List Nat) (member : xs∈profiles n zeroTwo n 0 m m) :
    Upper (D (n:=n) xs.reverse) (R xs.reverse) [] bound := by
  by_cases difficult : hard n bound xs
  · apply checked xs
    apply List.mem_filter.mpr
    refine ⟨member,?_⟩
    simpa only [decide_eq_true_eq] using difficult
  · by_cases small : eligibleCount (D (n:=n) xs.reverse) (R xs.reverse)≤bound
    · exact active_only _ _ _ small
    · apply cut_only
      dsimp [hard] at difficult
      omega

#print axioms sorted_member
#print axioms relabel_reversed
#print axioms upper_of_hard
end Delivery.SmallBudgetProfiles
