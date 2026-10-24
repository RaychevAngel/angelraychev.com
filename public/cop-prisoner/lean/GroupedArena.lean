import LocalArena

/-! Grouped finite cop masks. Literal checks are independent of the chosen
Data: the semantic adapter selects a minimum-rank group for each state. -/
namespace Delivery.GroupedArena
open LocalArena

structure Group (m n : Nat) where
  rank : Nat
  move : Fin m
  cops : List (Fin n)
  mask : Nat

def Has {n : Nat} (mask : Nat) (c : Fin n) : Prop := mask.testBit c.val=true
instance {n : Nat} (mask : Nat) (c : Fin n) : Decidable (Has mask c) := inferInstanceAs (Decidable (_=true))

def maskOf {n : Nat} : List (Fin n) → Nat
  | [] => 0
  | c::cs => 2^c.val ||| maskOf cs

def replyUnion {n : Nat} (replyMasks : Fin n → Nat) : List (Fin n) → Nat
  | [] => 0
  | c::cs => replyMasks c ||| replyUnion replyMasks cs

def lowerMask {m n : Nat} : List (Group m n) → Nat → Nat
  | [], _ => 0
  | g::gs, k => if g.rank<k then g.mask ||| lowerMask gs k else lowerMask gs k

theorem has_or {n : Nat} (a b : Nat) (c : Fin n) :
    Has (a ||| b) c ↔ Has a c ∨ Has b c := by
  simp only [Has,Nat.testBit_or,Bool.or_eq_true]

theorem has_power {n : Nat} (d c : Fin n) : Has (2^d.val) c ↔ c=d := by
  simp only [Has,Nat.testBit_two_pow,decide_eq_true_eq]
  exact ⟨fun h => Fin.ext h.symm,fun h => congrArg Fin.val h.symm⟩

theorem has_maskOf {n : Nat} (cs : List (Fin n)) (c : Fin n) : Has (maskOf cs) c ↔ c∈cs := by
  induction cs with
  | nil => simp [Has,maskOf]
  | cons d cs ih => simp only [maskOf,has_or,has_power,ih,List.mem_cons]

theorem has_replyUnion {n : Nat} (replyMasks : Fin n → Nat) {cs : List (Fin n)}
    {c d : Fin n} (member : c∈cs) (reply : Has (replyMasks c) d) :
    Has (replyUnion replyMasks cs) d := by
  induction cs with
  | nil => simp at member
  | cons a cs ih =>
    rcases List.mem_cons.mp member with same|tail
    · subst a; exact (has_or _ _ d).mpr (Or.inl reply)
    · exact (has_or _ _ d).mpr (Or.inr (ih tail))

theorem has_lowerMask {m n : Nat} (gs : List (Group m n)) (k : Nat) (c : Fin n) :
    Has (lowerMask gs k) c ↔ ∃ g∈gs, g.rank<k ∧ Has g.mask c := by
  induction gs with
  | nil => simp [Has,lowerMask]
  | cons g gs ih =>
    by_cases small : g.rank<k
    · simp [lowerMask,small,has_or,ih]
    · simp [lowerMask,small,ih]

theorem has_subset {n : Nat} {a b : Nat} {c : Fin n} (subset : a &&& b=a)
    (yes : Has a c) : Has b c := by
  have eq := congrArg (fun x => x.testBit c.val) subset
  simpa [Has,Nat.testBit_and,show a.testBit c.val=true from yes] using eq

theorem has_disjoint {n : Nat} {a b : Nat} {c : Fin n} (disjoint : a &&& b=0)
    (yes : Has a c) : ¬Has b c := by
  intro no
  have eq := congrArg (fun x => x.testBit c.val) disjoint
  simp [show a.testBit c.val=true from yes,show b.testBit c.val=true from no] at eq

def Active {m n : Nat} (gs : List (Group m n)) (c : Fin n) : Prop :=
  ∃ g∈gs, Has g.mask c

theorem exists_min {m n : Nat} (gs : List (Group m n)) (c : Fin n)
    (active : Active gs c) :
    ∃ g∈gs, Has g.mask c ∧ ∀ h∈gs, Has h.mask c → g.rank≤h.rank := by
  induction gs with
  | nil => simp [Active] at active
  | cons a gs ih =>
    by_cases yes : Has a.mask c
    · by_cases tail : Active gs c
      · obtain ⟨b,bmem,byes,bmin⟩ := ih tail
        by_cases le : a.rank≤b.rank
        · refine ⟨a,by simp,yes,?_⟩
          intro h hm hh
          rcases List.mem_cons.mp hm with same|mem
          · subst h; exact Nat.le_refl _
          · exact Nat.le_trans le (bmin h mem hh)
        · refine ⟨b,by simp [bmem],byes,?_⟩
          intro h hm hh
          rcases List.mem_cons.mp hm with same|mem
          · subst h; omega
          · exact bmin h mem hh
      · refine ⟨a,by simp,yes,?_⟩
        intro h hm hh
        rcases List.mem_cons.mp hm with same|mem
        · subst h; exact Nat.le_refl _
        · exact False.elim (tail ⟨h,mem,hh⟩)
    · have tail : Active gs c := by
        obtain ⟨g,gm,gh⟩ := active
        rcases List.mem_cons.mp gm with same|mem
        · subst g; exact False.elim (yes gh)
        · exact ⟨g,mem,gh⟩
      obtain ⟨b,bmem,byes,bmin⟩ := ih tail
      refine ⟨b,by simp [bmem],byes,?_⟩
      intro h hm hh
      rcases List.mem_cons.mp hm with same|mem
      · subst h; exact False.elim (yes hh)
      · exact bmin h mem hh

noncomputable def selected {m n : Nat} (gs : List (Group m n)) (c : Fin n)
    (active : Active gs c) : Group m n := Classical.choose (exists_min gs c active)

theorem selected_spec {m n : Nat} (gs : List (Group m n)) (c : Fin n) (active : Active gs c) :
    selected gs c active∈gs ∧ Has (selected gs c active).mask c ∧
      ∀ h∈gs, Has h.mask c → (selected gs c active).rank≤h.rank :=
  Classical.choose_spec (exists_min gs c active)

noncomputable def data {m n : Nat} (rows : Fin m → List (Group m n)) : Data (Fin m) (Fin n) := by
  classical
  exact {
    region r c := Active (rows r) c
    rank r c := if h : Active (rows r) c then (selected (rows r) c h).rank else 0
    move r c := if h : Active (rows r) c then (selected (rows r) c h).move else r }

theorem rank_selected {m n : Nat} (rows : Fin m → List (Group m n)) (r : Fin m) (c : Fin n)
    (h : Active (rows r) c) : (data rows).rank r c=(selected (rows r) c h).rank := by
  simp [data,h]
theorem move_selected {m n : Nat} (rows : Fin m → List (Group m n)) (r : Fin m) (c : Fin n)
    (h : Active (rows r) c) : (data rows).move r c=(selected (rows r) c h).move := by
  simp [data,h]

theorem below {m n : Nat} (rows : Fin m → List (Group m n)) (r : Fin m) (c : Fin n) (k : Nat)
    (inside : Has (lowerMask (rows r) k) c) :
    (data rows).region r c ∧ (data rows).rank r c<k := by
  obtain ⟨g,member,small,yes⟩ := (has_lowerMask (rows r) k c).mp inside
  have active : Active (rows r) c := ⟨g,member,yes⟩
  refine ⟨active,?_⟩
  rw [rank_selected rows r c active]
  exact Nat.lt_of_le_of_lt ((selected_spec (rows r) c active).2.2 g member yes) small

theorem bounded {m n : Nat} (rows : Fin m → List (Group m n)) (r : Fin m) (c : Fin n) (bound : Nat)
    (inside : Has (lowerMask (rows r) (bound+1)) c) :
    (data rows).region r c ∧ (data rows).rank r c≤bound := by
  obtain ⟨active,small⟩ := below rows r c (bound+1) inside
  exact ⟨active,by omega⟩

def Good {m n : Nat} (delivery : Bool) (A : Arena (Fin m) (Fin n)) (Goal : Fin m → Prop)
    (replyMasks : Fin n → Nat) (collisionMasks : Fin m → Nat)
    (rows : Fin m → List (Group m n)) (r : Fin m) (g : Group m n) : Prop :=
  g.mask=maskOf g.cops ∧ g.mask &&& collisionMasks r=0 ∧
    (Goal r ∨ (0<g.rank ∧ A.messenger r g.move ∧
      ((delivery=true ∧ Goal g.move) ∨
        (g.mask &&& collisionMasks g.move=0 ∧
          replyUnion replyMasks g.cops &&& lowerMask (rows g.move) g.rank = replyUnion replyMasks g.cops))))

instance {m n : Nat} (delivery : Bool) (A : Arena (Fin m) (Fin n)) (Goal : Fin m → Prop)
    [DecidableRel A.messenger] [DecidablePred Goal]
    (replyMasks : Fin n → Nat) (collisionMasks : Fin m → Nat)
    (rows : Fin m → List (Group m n)) (r : Fin m) (g : Group m n) :
    Decidable (Good delivery A Goal replyMasks collisionMasks rows r g) :=
  inferInstanceAs (Decidable (_∧_∧(_∨(_∧_∧(_∨_)))))

def Checked {m n : Nat} (delivery : Bool) (A : Arena (Fin m) (Fin n)) (Goal : Fin m → Prop)
    [DecidableRel A.messenger] [DecidablePred Goal]
    (replyMasks : Fin n → Nat) (collisionMasks : Fin m → Nat)
    (rows : Fin m → List (Group m n)) : Prop :=
  ∀ r, (rows r).all (fun g => decide (Good delivery A Goal replyMasks collisionMasks rows r g))=true

theorem group_good {m n : Nat} {delivery : Bool} {A : Arena (Fin m) (Fin n)} {Goal : Fin m → Prop}
    [DecidableRel A.messenger] [DecidablePred Goal]
    {replyMasks : Fin n → Nat} {collisionMasks : Fin m → Nat}
    {rows : Fin m → List (Group m n)} (checked : Checked delivery A Goal replyMasks collisionMasks rows)
    {r : Fin m} {g : Group m n} (member : g∈rows r) : Good delivery A Goal replyMasks collisionMasks rows r g :=
  of_decide_eq_true ((List.all_eq_true.mp (checked r)) g member)

theorem region_safe {m n : Nat} {delivery : Bool} {A : Arena (Fin m) (Fin n)} {Goal : Fin m → Prop}
    [DecidableRel A.messenger] [DecidablePred Goal]
    {replyMasks : Fin n → Nat} {collisionMasks : Fin m → Nat}
    {rows : Fin m → List (Group m n)}
    (collision_covered : ∀ r c, A.collision r c → Has (collisionMasks r) c)
    (checked : Checked delivery A Goal replyMasks collisionMasks rows)
    {r : Fin m} {c : Fin n} (active : (data rows).region r c) : ¬A.collision r c := by
  obtain ⟨g,member,yes⟩ := active
  have good := group_good checked member
  exact fun h => has_disjoint good.2.1 yes (collision_covered r c h)

theorem safe_checked {m n : Nat} (A : Arena (Fin m) (Fin n)) (Goal : Fin m → Prop)
    [DecidableRel A.messenger] [DecidablePred Goal]
    (replyMasks : Fin n → Nat) (collisionMasks : Fin m → Nat)
    (rows : Fin m → List (Group m n))
    (reply_covered : ∀ c d, A.pursuer c d → Has (replyMasks c) d)
    (collision_covered : ∀ r c, A.collision r c → Has (collisionMasks r) c)
    (checked : Checked false A Goal replyMasks collisionMasks rows) : SafeChecked A Goal (data rows) := by
  constructor
  intro r c active
  let g := selected (rows r) c active
  have spec := selected_spec (rows r) c active
  have good := group_good checked spec.1
  have safe := region_safe collision_covered checked active
  rcases good.2.2 with goal | ⟨positive,move,finish|⟨safeNow,future⟩⟩
  · exact Or.inl ⟨goal,safe⟩
  · cases finish.1
  · apply Or.inr
    rw [rank_selected rows r c active,move_selected rows r c active]
    refine ⟨positive,safe,move,?_,?_⟩
    · exact fun hit => has_disjoint safeNow spec.2.1 (collision_covered _ c hit)
    · intro d legal
      have cop : c∈(selected (rows r) c active).cops :=
        (has_maskOf _ c).mp (by rw [←good.1]; exact spec.2.1)
      have reply := has_replyUnion replyMasks cop (reply_covered c d legal)
      have lower := below rows _ d _ (has_subset future reply)
      exact ⟨region_safe collision_covered checked lower.1,lower.1,lower.2⟩

theorem delivery_checked {m n : Nat} (A : Arena (Fin m) (Fin n)) (Goal : Fin m → Prop)
    [DecidableRel A.messenger] [DecidablePred Goal]
    (replyMasks : Fin n → Nat) (collisionMasks : Fin m → Nat)
    (rows : Fin m → List (Group m n))
    (reply_covered : ∀ c d, A.pursuer c d → Has (replyMasks c) d)
    (collision_covered : ∀ r c, A.collision r c → Has (collisionMasks r) c)
    (checked : Checked true A Goal replyMasks collisionMasks rows) : DeliveryChecked A Goal (data rows) := by
  constructor
  intro r c active
  have spec := selected_spec (rows r) c active
  have good := group_good checked spec.1
  have safe := region_safe collision_covered checked active
  rcases good.2.2 with goal | ⟨positive,move,finish|⟨safeNow,future⟩⟩
  · exact Or.inl goal
  · apply Or.inr
    rw [rank_selected rows r c active,move_selected rows r c active]
    exact ⟨positive,safe,move,Or.inl finish.2⟩
  · apply Or.inr
    rw [rank_selected rows r c active,move_selected rows r c active]
    refine ⟨positive,safe,move,Or.inr ⟨?_,?_⟩⟩
    · exact fun hit => has_disjoint safeNow spec.2.1 (collision_covered _ c hit)
    · intro d legal
      have cop : c∈(selected (rows r) c active).cops :=
        (has_maskOf _ c).mp (by rw [←good.1]; exact spec.2.1)
      have reply := has_replyUnion replyMasks cop (reply_covered c d legal)
      have lower := below rows _ d _ (has_subset future reply)
      exact ⟨region_safe collision_covered checked lower.1,lower.1,lower.2⟩

#print axioms safe_checked
#print axioms delivery_checked
#print axioms bounded
end Delivery.GroupedArena
