import SmallBudgetProfiles

/-! Budget-aware complete degree catalogues. The finite alphabet is a recursive
parameter, and necessary lower/upper sum bounds cut impossible tails before
enumeration. No equality to the older, slower catalogue is assumed. -/
namespace Delivery.SmallBudgetProfilesFast
open FiniteGame Extremal DenseCombinatorics ConstructionCounts SparseSupport
open SmallBudgetProfiles RowPrefix

def enumerate (n : Nat) (letters : List Nat) : Nat → Nat → Nat → Nat → List (List Nat)
  | 0,_,d,r => if d=0 ∧ r=0 then [[]] else []
  | slots+1,lo,d,r =>
    if 2*(slots+1)≤d+r ∧ (slots+1)*(lo/16)≤d ∧
        d≤(slots+1)*(n-1) ∧ r≤(slots+1)*(n-1) then
      letters.flatMap fun a =>
        if lo≤a ∧ a/16≤d ∧ a%16≤r then
          (enumerate n letters slots a (d-a/16) (r-a%16)).map (a::·)
        else []
    else []

def profiles (n : Nat) (zeroTwo : Bool) (slots lo d r : Nat) : List (List Nat) :=
  enumerate n (alphabet n zeroTwo) slots lo d r

theorem sum_lower (xs : List Nat) (f : Nat → Nat) (b : Nat)
    (bounds : ∀a∈xs,b≤f a) : xs.length*b≤(xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have first := bounds a (by simp)
    have rest := ih (fun x hx => bounds x (by simp [hx]))
    simp only [List.length_cons,List.map_cons,List.sum_cons,Nat.succ_mul]
    omega

theorem sum_upper (xs : List Nat) (f : Nat → Nat) (b : Nat)
    (bounds : ∀a∈xs,f a≤b) : (xs.map f).sum≤xs.length*b := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have first := bounds a (by simp)
    have rest := ih (fun x hx => bounds x (by simp [hx]))
    simp only [List.length_cons,List.map_cons,List.sum_cons,Nat.succ_mul]
    omega

theorem enumerate_complete (n : Nat) (zeroTwo : Bool) (xs : List Nat) (lo d r : Nat)
    (members : ∀a∈xs,a∈alphabet n zeroTwo) (sorted : xs.Pairwise (·≤·))
    (lower : ∀a∈xs,lo≤a) (outSum : (xs.map (·/16)).sum=d)
    (inSum : (xs.map (·%16)).sum=r) :
    xs∈enumerate n (alphabet n zeroTwo) xs.length lo d r := by
  induction xs generalizing lo d r with
  | nil =>
    have hd : d=0 := by simpa using outSum.symm
    have hr : r=0 := by simpa using inSum.symm
    subst d; subst r; simp [enumerate]
  | cons a xs ih =>
    have minimum := total_minimum n zeroTwo (a::xs) members
    have outgoing := sum_lower (a::xs) (·/16) (lo/16) (by
      intro b hb; have bound := lower b hb; omega)
    have maxOut := sum_upper (a::xs) (·/16) (n-1) (by
      intro b hb
      have member := members b hb
      simp only [alphabet,List.mem_filter,List.mem_range,decide_eq_true_eq] at member
      omega)
    have maxIn := sum_upper (a::xs) (·%16) (n-1) (by
      intro b hb
      have member := members b hb
      simp only [alphabet,List.mem_filter,List.mem_range,decide_eq_true_eq] at member
      omega)
    rw [outSum,inSum] at minimum
    rw [outSum] at outgoing maxOut
    rw [inSum] at maxIn
    have guard : 2*(xs.length+1)≤d+r ∧ (xs.length+1)*(lo/16)≤d ∧
        d≤(xs.length+1)*(n-1) ∧ r≤(xs.length+1)*(n-1) :=
      ⟨minimum,outgoing,maxOut,maxIn⟩
    have pair := List.pairwise_cons.mp sorted
    simp only [List.map_cons,List.sum_cons] at outSum inSum
    have step : lo≤a ∧ a/16≤d ∧ a%16≤r := ⟨lower a (by simp),by omega,by omega⟩
    simp only [List.length_cons,enumerate,if_pos guard,List.mem_flatMap]
    refine ⟨a,members a (by simp),?_⟩
    rw [if_pos step]
    apply List.mem_map.mpr
    refine ⟨xs,ih a (d-a/16) (r-a%16) (fun b hb => members b (by simp [hb]))
      pair.2 pair.1 (by omega) (by omega),rfl⟩

theorem profiles_complete (n : Nat) (zeroTwo : Bool) (xs : List Nat) (lo d r : Nat)
    (members : ∀a∈xs,a∈alphabet n zeroTwo) (sorted : xs.Pairwise (·≤·))
    (lower : ∀a∈xs,lo≤a) (outSum : (xs.map (·/16)).sum=d)
    (inSum : (xs.map (·%16)).sum=r) : xs∈profiles n zeroTwo xs.length lo d r :=
  enumerate_complete n zeroTwo xs lo d r members sorted lower outSum inSum

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

def hardProfiles (n m bound : Nat) (zeroTwo : Bool) : List (List Nat) :=
  (profiles n zeroTwo n 0 m m).filter (fun xs => decide (hard n bound xs))

theorem upper_of_hard {n m bound : Nat} {zeroTwo : Bool}
    (checked : ∀xs∈hardProfiles n m bound zeroTwo,
      Upper (D (n:=n) xs.reverse) (R xs.reverse) [] bound)
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

#print axioms enumerate_complete
#print axioms sorted_member
#print axioms upper_of_hard
end Delivery.SmallBudgetProfilesFast
