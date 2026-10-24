import DegreeProfileRelabeling
import RowPrefixKernel
import Init.Data.List.Sort.Lemmas

/-! Complete sorted joint-degree catalogues with prescribed sums. -/
namespace Delivery.SmallDegreeProfiles
open FiniteGame Extremal DenseCombinatorics ConstructionCounts SparseSupport

theorem perm_sum {xs ys : List Nat} (p : xs.Perm ys) : xs.sum=ys.sum := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp only [List.sum_cons]; omega
  | swap a b xs => simp only [List.sum_cons]; omega
  | trans _ _ ih1 ih2 => omega

/-- Base-eight labels are sufficient for the orders at most seven below. -/
def alphabet (n : Nat) : List Nat :=
  (List.range (8*n)).filter fun a => decide (a%8<n ∧ 2≤a/8+a%8)

def profiles (n : Nat) : Nat → Nat → Nat → Nat → List (List Nat)
  | 0,_,d,r => if d=0 ∧ r=0 then [[]] else []
  | slots+1,lo,d,r => (alphabet n).flatMap fun a =>
      if lo≤a ∧ a/8≤d ∧ a%8≤r then
        (profiles n slots a (d-a/8) (r-a%8)).map (a::·)
      else []

theorem profiles_complete (n : Nat) (xs : List Nat) (lo d r : Nat)
    (members : ∀a∈xs,a∈alphabet n) (sorted : xs.Pairwise (·≤·))
    (lower : ∀a∈xs,lo≤a) (outSum : (xs.map (·/8)).sum=d)
    (inSum : (xs.map (·%8)).sum=r) : xs∈profiles n xs.length lo d r := by
  induction xs generalizing lo d r with
  | nil =>
    have hd : d=0 := by simpa using outSum.symm
    have hr : r=0 := by simpa using inSum.symm
    subst d; subst r; simp [profiles]
  | cons a xs ih =>
    have pair := List.pairwise_cons.mp sorted
    simp only [List.map_cons,List.sum_cons] at outSum inSum
    have step : lo≤a ∧ a/8≤d ∧ a%8≤r := ⟨lower a (by simp),by omega,by omega⟩
    simp only [List.length_cons,profiles,List.mem_flatMap]
    refine ⟨a,members a (by simp),?_⟩
    rw [if_pos step]
    apply List.mem_map.mpr
    refine ⟨xs,ih a (d-a/8) (r-a%8) (fun b hb => members b (by simp [hb])) pair.2 pair.1 (by omega) (by omega),rfl⟩

def label (d e : Fin n → Nat) (x : Fin n) : Nat := 8*d x+e x

def sorted (d e : Fin n → Nat) : List Nat :=
  ((List.finRange n).map (label d e)).mergeSort (fun a b => a≤b)

theorem sorted_perm (d e : Fin n → Nat) :
    (sorted d e).Perm ((List.finRange n).map (label d e)) := List.mergeSort_perm _ _

theorem sorted_length (d e : Fin n → Nat) : (sorted d e).length=n := by
  simpa using (sorted_perm d e).length_eq

def value (xs : List Nat) (i : Fin n) : Nat := xs[i.val]?.getD 0
def D (xs : List Nat) (i : Fin n) : Nat := value xs i/8
def R (xs : List Nat) (i : Fin n) : Nat := value xs i%8

theorem values_eq (xs : List Nat) (length : xs.length=n) :
    (List.finRange n).map (value xs)=xs := by
  apply List.ext_getElem
  · simp [length]
  · intro i h1 h2
    simp only [List.getElem_map,List.getElem_finRange,value]
    exact Option.getD_some (a:=xs[i]) (b:=0) ▸ congrArg (fun o => o.getD 0) (List.getElem?_eq_getElem h2)

theorem sorted_member {n m : Nat} (d e : Fin n → Nat) (small : n≤7)
    (pd : ∀x,d x<n) (pe : ∀x,e x<n) (total : ∀x,2≤d x+e x)
    (td : ((List.finRange n).map d).sum=m) (te : ((List.finRange n).map e).sum=m) :
    sorted d e∈profiles n n 0 m m := by
  have perm := sorted_perm d e
  have len := sorted_length d e
  have result : sorted d e∈profiles n (sorted d e).length 0 m m := by
    apply profiles_complete
    · intro a ha
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp (perm.mem_iff.mp ha)
      have hd := pd x; have he := pe x; have ht := total x
      simp only [alphabet,List.mem_filter,List.mem_range,decide_eq_true_eq,label]
      omega
    · have h := List.pairwise_mergeSort (le:=fun a b : Nat => a≤b)
        (by intro a b c h1 h2; exact decide_eq_true (Nat.le_trans (of_decide_eq_true h1) (of_decide_eq_true h2)))
        (by intro a b; simp only [Bool.or_eq_true,decide_eq_true_eq]; omega)
        ((List.finRange n).map (label d e))
      exact h.imp (fun h => of_decide_eq_true h)
    · intro a _; omega
    · have eq := perm_sum (perm.map (·/8))
      rw [List.map_map] at eq
      have vals : (fun x => label d e x/8)=d := by
        funext x; have he := pe x; dsimp [label]; omega
      simpa only [Function.comp_def,vals,td] using eq
    · have eq := perm_sum (perm.map (·%8))
      rw [List.map_map] at eq
      have vals : (fun x => label d e x%8)=e := by
        funext x; have he := pe x; dsimp [label]; omega
      simpa only [Function.comp_def,vals,te] using eq
  simpa only [len] using result

theorem relabel (E : Graph (Fin n)) (loops : Loopless E)
    (inSmall : ∀x,indegree E x<8) :
    ∃F : Graph (Fin n), Nonempty (GraphRelabeling.Iso F E) ∧
      RowPrefix.Prescribed (D (sorted (outdegree E) (indegree E)))
        (R (sorted (outdegree E) (indegree E))) F := by
  classical
  let d := outdegree E
  let e := indegree E
  let xs := sorted d e
  have values : (List.finRange n).map (value xs)=xs := values_eq xs (sorted_length d e)
  have counts (a : Nat) : card (fun x => label d e x=a)=card (fun x : Fin n => value xs x=a) := by
    rw [card_eq,card_eq]
    have eq := ((sorted_perm d e).filter (fun b => decide (b=a))).length_eq
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
    change 8*outdegree E (f x)+indegree E (f x)=value xs x at labs
    change outdegree F x=value xs x/8
    omega
  · intro x
    have equal : indegree F x=indegree E (f x) :=
      IrregularTenProfile.card_pullback f g left right (fun s => E s (f x))
    have labs := labels x; have bound := inSmall (f x)
    change 8*outdegree E (f x)+indegree E (f x)=value xs x at labs
    change indegree F x=value xs x%8
    omega

end Delivery.SmallDegreeProfiles
