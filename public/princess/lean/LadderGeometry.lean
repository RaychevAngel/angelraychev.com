import Std

/-!
Set-level geometry of the ordinary two-row ladder.

Both encodings below have a finite column coordinate and a Boolean second
coordinate. For `rowAdj`, that Boolean is the physical row. For `colorAdj`,
it is the checkerboard color. The explicit involution `recolor` relates them.
No cardinality theorem or probe-budget correspondence is claimed here.
-/

namespace Princess.LadderGeometry

abbrev Room (n : Nat) := Fin n × Bool

def columnParity {n : Nat} (c : Fin n) : Bool := decide (c.val % 2 = 1)

def rowAdj {n : Nat} (x y : Room n) : Prop :=
  (x.1 = y.1 ∧ x.2 ≠ y.2) ∨
  (x.2 = y.2 ∧ (x.1.val + 1 = y.1.val ∨ y.1.val + 1 = x.1.val))

def closedPathAdj {n : Nat} (a b : Fin n) : Prop :=
  a = b ∨ a.val + 1 = b.val ∨ b.val + 1 = a.val

def colorAdj {n : Nat} (x y : Room n) : Prop :=
  x.2 ≠ y.2 ∧ closedPathAdj x.1 y.1

def recolor {n : Nat} (x : Room n) : Room n :=
  (x.1, Bool.xor x.2 (columnParity x.1))

theorem recolor_involutive {n : Nat} (x : Room n) : recolor (recolor x) = x := by
  rcases x with ⟨c, r⟩
  unfold recolor
  cases r <;> cases columnParity c <;> rfl

theorem physical_no_dead_ends {n : Nat} (x : Room n) : ∃ y, rowAdj x y := by
  rcases x with ⟨c, r⟩
  refine ⟨(c, !r), Or.inl ⟨rfl, ?_⟩⟩
  change r ≠ !r
  cases r <;> decide

theorem adjacent_parities {n : Nat} {a b : Fin n}
    (neighbor : a.val + 1 = b.val ∨ b.val + 1 = a.val) :
    columnParity a ≠ columnParity b := by
  unfold columnParity
  by_cases ha : a.val % 2 = 1
  · have hb : ¬ b.val % 2 = 1 := by omega
    simp only [ha, hb, decide_true, decide_false]
    decide
  · have hb : b.val % 2 = 1 := by omega
    simp only [ha, hb, decide_true, decide_false]
    decide

/-- The checkerboard encoding preserves exactly the ordinary ladder edges. -/
theorem rowAdj_iff_colorAdj {n : Nat} (x y : Room n) :
    rowAdj x y ↔ colorAdj (recolor x) (recolor y) := by
  rcases x with ⟨a, r⟩
  rcases y with ⟨b, s⟩
  by_cases same : a = b
  · subst b
    have notForward : ¬ a.val + 1 = a.val := by omega
    unfold rowAdj colorAdj closedPathAdj recolor
    simp only [notForward, or_self, true_and, and_false, or_false]
    cases r <;> cases s <;> cases columnParity a <;> decide
  · by_cases neighbor : a.val + 1 = b.val ∨ b.val + 1 = a.val
    · have parity := adjacent_parities neighbor
      unfold rowAdj colorAdj closedPathAdj recolor
      simp only [same, neighbor, false_and, false_or, and_true]
      cases r <;> cases s <;> cases ha : columnParity a <;> cases hb : columnParity b
      all_goals simp_all
    · unfold rowAdj colorAdj closedPathAdj recolor
      simp only [same, neighbor, false_and, false_or, and_false]

abbrev ColumnSet (n : Nat) := Fin n → Prop
abbrev RoomSet (n : Nat) := Room n → Prop

def fiber {n : Nat} (color : Bool) (B : ColumnSet n) : RoomSet n :=
  fun x => x.2 = color ∧ B x.1

def probeColumns {n : Nat} (S : RoomSet n) (color : Bool) : ColumnSet n :=
  fun j => S (j, color)

def columnStep {n : Nat} (B S : ColumnSet n) : ColumnSet n :=
  fun j => ∃ i, (B i ∧ ¬ S i) ∧ closedPathAdj i j

def roomStep {n : Nat} (B S : RoomSet n) : RoomSet n :=
  fun y => ∃ x, B x ∧ ¬ S x ∧ colorAdj x y

def physicalStep {n : Nat} (B S : RoomSet n) : RoomSet n :=
  fun y => ∃ x, B x ∧ ¬ S x ∧ rowAdj x y

theorem flip_of_ne {a b : Bool} (h : a ≠ b) : b = !a := by
  cases a <;> cases b <;> simp_all

theorem ne_of_flip {a b : Bool} (h : b = !a) : a ≠ b := by
  cases a <;> cases b <;> simp_all

/-- A physical inspection/move step is carried exactly to the checkerboard
encoding, with both beliefs and probe sets transported by the same bijection. -/
theorem physicalStep_iff_recolored {n : Nat} (B S : RoomSet n) (y : Room n) :
    physicalStep B S y ↔
      roomStep (fun x => B (recolor x)) (fun x => S (recolor x)) (recolor y) := by
  constructor
  · intro h
    obtain ⟨x, hx, hm, he⟩ := h
    refine ⟨recolor x, ?_, ?_, (rowAdj_iff_colorAdj x y).mp he⟩
    · simpa only [recolor_involutive] using hx
    · simpa only [recolor_involutive] using hm
  · intro h
    obtain ⟨x, hx, hm, he⟩ := h
    refine ⟨recolor x, hx, hm, (rowAdj_iff_colorAdj (recolor x) y).mpr ?_⟩
    simpa only [recolor_involutive] using he

/-- Exact one-step column projection of one checkerboard cohort. Horizontal
room moves become adjacent columns and a vertical room move becomes a column
stay. Staying in the same physical room is never introduced. -/
theorem step_fiber {n : Nat} (color : Bool) (B : ColumnSet n) (S : RoomSet n)
    (y : Room n) :
    roomStep (fiber color B) S y ↔
      fiber (!color) (columnStep B (probeColumns S color)) y := by
  constructor
  · intro h
    obtain ⟨⟨j, r⟩, ⟨hr, hB⟩, hS, he⟩ := h
    change r = color at hr
    subst r
    exact ⟨flip_of_ne he.1, ⟨j, ⟨hB, hS⟩, he.2⟩⟩
  · intro h
    obtain ⟨hy, j, ⟨hB, hS⟩, he⟩ := h
    exact ⟨(j, color), ⟨rfl, hB⟩, hS, ⟨ne_of_flip hy, he⟩⟩

theorem fiber_rooms_injective {n : Nat} (color : Bool) (a b : Fin n) :
    (a, color) = (b, color) ↔ a = b := by
  constructor
  · intro h
    exact congrArg Prod.fst h
  · intro h
    subst b
    rfl

def colorAt (color : Bool) : Nat → Bool
  | 0 => color
  | t + 1 => !(colorAt color t)

def roomBelief {n : Nat} (initial : RoomSet n) (probes : Nat → RoomSet n) :
    Nat → RoomSet n
  | 0 => initial
  | t + 1 => roomStep (roomBelief initial probes t) (probes t)

def columnBelief {n : Nat} (color : Bool) (initial : ColumnSet n)
    (probes : Nat → RoomSet n) : Nat → ColumnSet n
  | 0 => initial
  | t + 1 => columnStep (columnBelief color initial probes t)
      (probeColumns (probes t) (colorAt color t))

/-- Projection is exact for every finite time and every sequence of room
probe sets, not merely for specially chosen suffix strategies. -/
theorem cohort_projection {n : Nat} (color : Bool) (initial : ColumnSet n)
    (probes : Nat → RoomSet n) (t : Nat) (x : Room n) :
    roomBelief (fiber color initial) probes t x ↔
      fiber (colorAt color t) (columnBelief color initial probes t) x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
      have congr : roomStep (roomBelief (fiber color initial) probes t) (probes t) x ↔
          roomStep (fiber (colorAt color t) (columnBelief color initial probes t)) (probes t) x := by
        constructor
        · intro h
          obtain ⟨y, hy, hm, he⟩ := h
          exact ⟨y, (ih y).mp hy, hm, he⟩
        · intro h
          obtain ⟨y, hy, hm, he⟩ := h
          exact ⟨y, (ih y).mpr hy, hm, he⟩
      exact congr.trans (step_fiber _ _ _ _)

end Princess.LadderGeometry

#print axioms Princess.LadderGeometry.recolor_involutive
#print axioms Princess.LadderGeometry.physical_no_dead_ends
#print axioms Princess.LadderGeometry.rowAdj_iff_colorAdj
#print axioms Princess.LadderGeometry.physicalStep_iff_recolored
#print axioms Princess.LadderGeometry.step_fiber
#print axioms Princess.LadderGeometry.cohort_projection
