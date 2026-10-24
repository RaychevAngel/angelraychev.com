import ProtectedCircle

/-! The prescribed finite greedy extension of protected offsets. Each residue
is scanned once in increasing order; only six modular equalities per existing
offset are tested. No game or graph search is involved. -/
namespace Delivery.ProtectedGrowth
open CyclicArithmetic DenseCombinatorics ProtectedCircle

def pairs (a : Nat) : List (Nat × Nat) :=
  [(1,a),(1,2*a+1),(a,1),(a,2*a+1),(2*a+1,1),(2*a+1,a)]

def Listed {n : Nat} (xs : List (Fin n)) (d : Nat) : Prop := ∃ x∈xs, x.val=d

@[simp] theorem listed_val {n : Nat} (xs : List (Fin n)) (x : Fin n) :
    Listed xs x.val ↔ x∈xs := by
  constructor
  · rintro ⟨y,hy,same⟩
    have equal : y=x := Fin.ext same
    exact equal ▸ hy
  · exact fun h => ⟨x,h,rfl⟩

theorem pair_membership {a u v : Nat} (large : 3≤a) :
    (u,v)∈pairs a ↔ Core a u ∧ Core a v ∧ u≠v := by
  simp only [pairs,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq,Core]
  omega

def Blocked {n : Nat} (a : Nat) (xs : List (Fin n)) (z : Fin n) : Prop :=
  z∈xs ∨ ∃ y∈xs, ∃ p∈pairs a, (p.1+y.val)%n=(p.2+z.val)%n

def blocked {n : Nat} (a : Nat) (xs : List (Fin n)) (z : Fin n) : Bool :=
  decide (z∈xs) || xs.any (fun y => (pairs a).any fun p =>
    decide ((p.1+y.val)%n=(p.2+z.val)%n))

@[simp] theorem blocked_eq {n : Nat} {a : Nat} {xs : List (Fin n)} {z : Fin n} :
    blocked a xs z=true ↔ Blocked a xs z := by
  simp [blocked,Blocked]

theorem blocked_mono {n a : Nat} {xs ys : List (Fin n)} (subset : xs⊆ys)
    {z : Fin n} (hz : Blocked a xs z) : Blocked a ys z := by
  rcases hz with hz | ⟨y,hy,p,hp,eq⟩
  · exact Or.inl (subset hz)
  · exact Or.inr ⟨y,subset hy,p,hp,eq⟩

def grow {n : Nat} (a : Nat) (todo xs : List (Fin n)) : List (Fin n) :=
  match todo with
  | [] => xs
  | z::zs => grow a zs (if blocked a xs z then xs else z::xs)

theorem grow_contains {n a : Nat} (todo xs : List (Fin n)) : xs⊆grow a todo xs := by
  induction todo generalizing xs with
  | nil => exact fun _ h => h
  | cons z zs ih =>
    simp only [grow]
    by_cases hb : blocked a xs z=true
    · simp only [hb,ite_true]
      exact ih xs
    · have falseB : blocked a xs z=false := Bool.eq_false_iff.mpr hb
      simp only [falseB,Bool.false_eq_true,ite_false]
      exact fun _ h => ih (z::xs) (List.mem_cons_of_mem z h)

theorem grow_blocks {n a : Nat} (todo xs : List (Fin n)) :
    ∀ z∈todo, Blocked a (grow a todo xs) z := by
  induction todo generalizing xs with
  | nil => simp
  | cons x rest ih =>
    intro z hz
    rcases List.mem_cons.mp hz with same | hz
    · subst z
      simp only [grow]
      by_cases hb : blocked a xs x=true
      · simp only [hb,ite_true]
        exact blocked_mono (grow_contains rest xs) (blocked_eq.mp hb)
      · have falseB : blocked a xs x=false := Bool.eq_false_iff.mpr hb
        simp only [falseB,Bool.false_eq_true,ite_false]
        exact Or.inl (grow_contains rest (x::xs) (by simp))
    · exact ih _ z hz

theorem add_protected {n a : Nat} (large : 3≤a) (room : 2*a+1<n)
    {xs : List (Fin n)} {z : Fin n} (protection : Protected n a (Listed xs))
    (free : ¬ Blocked a xs z) : Protected n a (Listed (z::xs)) := by
  intro u v hu hv ne x y hx hy same
  obtain ⟨xx,hxx,rfl⟩ := hx
  obtain ⟨yy,hyy,rfl⟩ := hy
  rcases List.mem_cons.mp hxx with ex | hxx
  · subst xx
    rcases List.mem_cons.mp hyy with ey | hyy
    · subst yy
      have ub : u<n := by rcases hu with rfl | rfl | rfl <;> omega
      have vb : v<n := by rcases hv with rfl | rfl | rfl <;> omega
      have sameFin : shift (⟨u,ub⟩ : Fin n) z.val=shift (⟨v,vb⟩ : Fin n) z.val := Fin.ext same
      have eq := congrArg Fin.val (shift_injective sameFin)
      exact False.elim (ne eq)
    · exact False.elim (free (Or.inr ⟨yy,hyy,(u,v),pair_membership large |>.mpr ⟨hu,hv,ne⟩,same⟩))
  · rcases List.mem_cons.mp hyy with ey | hyy
    · subst yy
      exact False.elim (free (Or.inr ⟨xx,hxx,(v,u),pair_membership large |>.mpr ⟨hv,hu,Ne.symm ne⟩,same.symm⟩))
    · exact protection u v hu hv ne xx.val yy.val ⟨xx,hxx,rfl⟩ ⟨yy,hyy,rfl⟩ same

theorem grow_protected {n a : Nat} (large : 3≤a) (room : 2*a+1<n)
    (todo xs : List (Fin n)) (protection : Protected n a (Listed xs)) :
    Protected n a (Listed (grow a todo xs)) := by
  induction todo generalizing xs with
  | nil => exact protection
  | cons z zs ih =>
    simp only [grow]
    by_cases hb : blocked a xs z=true
    · simp only [hb,ite_true]
      exact ih xs protection
    · have falseB : blocked a xs z=false := Bool.eq_false_iff.mpr hb
      simp only [falseB,Bool.false_eq_true,ite_false]
      exact ih (z::xs) (add_protected large room protection (fun h => hb (blocked_eq.mpr h)))

theorem grow_nodup {n a : Nat} (todo xs : List (Fin n)) (nodup : xs.Nodup) :
    (grow a todo xs).Nodup := by
  induction todo generalizing xs with
  | nil => exact nodup
  | cons z zs ih =>
    simp only [grow]
    by_cases hb : blocked a xs z=true
    · simp only [hb,ite_true]; exact ih xs nodup
    · have falseB : blocked a xs z=false := Bool.eq_false_iff.mpr hb
      simp only [falseB,Bool.false_eq_true,ite_false]
      apply ih
      exact List.nodup_cons.mpr ⟨fun hz => hb (blocked_eq.mpr (Or.inl hz)),nodup⟩

theorem card_union_le {n : Nat} (P Q : Fin n → Prop) :
    card (fun x => P x ∨ Q x)≤card P+card Q := by
  have partition := card_partition (fun x => P x ∨ Q x) P
  have left := card_mono (P := fun x => (P x ∨ Q x) ∧ P x) (Q := P) (fun _ h => h.2)
  have right := card_mono (P := fun x => (P x ∨ Q x) ∧ ¬ P x) (Q := Q)
    (fun _ h => h.1.resolve_left h.2)
  omega

theorem card_list_union_le {n b : Nat} {α : Type} (xs : List α) (R : α → Fin n → Prop)
    (bound : ∀ x∈xs, card (R x)≤b) :
    card (fun z => ∃ x∈xs, R x z)≤xs.length*b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := bound x (by simp)
    have rest := ih (fun y hy => bound y (by simp [hy]))
    have equal : card (fun z => ∃ y∈x::xs, R y z)=card (fun z => R x z ∨ ∃ y∈xs, R y z) := by
      apply card_congr
      intro z
      simp only [List.mem_cons,exists_eq_or_imp]
    rw [equal]
    have union := card_union_le (R x) (fun z => ∃ y∈xs, R y z)
    simp only [List.length_cons,Nat.add_mul]
    omega

theorem equation_count {n : Nat} (y : Fin n) (u v : Nat) :
    card (fun z : Fin n => (u+y.val)%n=(v+z.val)%n)≤1 := by
  have bound := card_injection (P := fun z : Fin n => (u+y.val)%n=(v+z.val)%n)
    (Q := fun _ : Fin 1 => True) (fun _ => ⟨0,by decide⟩) (fun _ _ => True.intro)
    (by
      intro x z hx hz _
      apply shift_injective (d := v)
      apply Fin.ext
      change (x.val+v)%n=(z.val+v)%n
      simpa only [Nat.add_comm] using hx.symm.trans hz)
  simpa only [card_true] using bound

theorem blocked_count {n a : Nat} (xs : List (Fin n)) :
    card (Blocked a xs)≤7*xs.length := by
  have each (y : Fin n) :
      card (fun z : Fin n => ∃ p∈pairs a, (p.1+y.val)%n=(p.2+z.val)%n)≤6 := by
    have count := card_list_union_le (b := 1) (pairs a)
      (fun p z => (p.1+y.val)%n=(p.2+z.val)%n)
      (fun p _ => equation_count y p.1 p.2)
    simpa only [pairs,List.length_cons,List.length_nil,Nat.mul_one] using count
  have sums := card_list_union_le (b := 6) xs
    (fun y z => ∃ p∈pairs a, (p.1+y.val)%n=(p.2+z.val)%n) (fun y _ => each y)
  have members : card (fun z => z∈xs)≤xs.length :=
    (elems_nodup (fun z => z∈xs)).length_le_of_subset (fun _ h => mem_elems.mp h)
  have union := card_union_le (fun z => z∈xs)
    (fun z => ∃ y∈xs, ∃ p∈pairs a, (p.1+y.val)%n=(p.2+z.val)%n)
  change card (Blocked a xs)≤_ at union
  omega

theorem grown_size {n a : Nat} (xs : List (Fin n)) :
    (n+6)/7≤(grow a (List.finRange n) xs).length := by
  have total : card (Blocked a (grow a (List.finRange n) xs))=n := by
    rw [card_congr (Q := fun _ => True)]
    · exact card_true n
    · intro z
      exact ⟨fun _ => True.intro,fun _ => grow_blocks _ _ z (List.mem_finRange z)⟩
  have count := blocked_count (a := a) (grow a (List.finRange n) xs)
  omega

#print axioms grow_protected
#print axioms grown_size
end Delivery.ProtectedGrowth
