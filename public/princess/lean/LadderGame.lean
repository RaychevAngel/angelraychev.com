import LadderCardinality
import BeliefSemantics

namespace Princess.LadderGame

open Princess.LadderGeometry Princess.LadderCardinality

def pair {n : Nat} (color : Bool) (A C : ColumnSet n) : RoomSet n :=
  fun x => if x.2 = color then A x.1 else C x.1

theorem pair_step {n : Nat} (color : Bool) (A C U V : ColumnSet n) (y : Room n) :
    roomStep (pair color A C) (pair color U V) y ↔
      pair (!color) (columnStep A U) (columnStep C V) y := by
  rcases y with ⟨j, r⟩
  cases color <;> cases r
  all_goals simp [roomStep, pair, columnStep, colorAdj, Prod.exists, Bool.exists_bool, and_assoc]

theorem pair_probe_left {n : Nat} (color : Bool) (U V : ColumnSet n) :
    probeColumns (pair color U V) color = U := by
  funext i
  apply propext
  simp [probeColumns, pair]

theorem pair_probe_right {n : Nat} (color : Bool) (U V : ColumnSet n) :
    probeColumns (pair color U V) (!color) = V := by
  funext i
  apply propext
  cases color <;> simp [probeColumns, pair]

theorem pair_decompose {n : Nat} (color : Bool) (B : RoomSet n) :
    pair color (probeColumns B color) (probeColumns B (!color)) = B := by
  funext x
  apply propext
  rcases x with ⟨i, r⟩
  cases color <;> cases r <;> simp [pair, probeColumns]

theorem pair_card {n : Nat} (color : Bool) (U V : ColumnSet n) :
    roomCard (pair color U V) = card U + card V := by
  have h := budget_split (pair color U V) color
  rw [pair_probe_left, pair_probe_right] at h
  exact h.symm

inductive RoomClears (n m : Nat) : RoomSet n → Nat → Prop
  | done {B} : (∀ x, ¬ B x) → RoomClears n m B 0
  | step {B S t} : roomCard S ≤ m → RoomClears n m (roomStep B S) t →
      RoomClears n m B (t + 1)

theorem room_clears_mono {n m : Nat} {A B : RoomSet n} {t : Nat}
    (run : RoomClears n m B t) (included : ∀ x, A x → B x) : RoomClears n m A t := by
  induction run generalizing A with
  | done empty => exact RoomClears.done (fun x hx => empty x (included x hx))
  | @step B S t budget rest ih =>
      apply RoomClears.step (S := S) budget
      apply ih
      intro y hy
      obtain ⟨x, hx, hm, he⟩ := hy
      exact ⟨x, included x hx, hm, he⟩

theorem counters_mono {n m b c d e t : Nat} (run : Princess.Ladder.Clears n m d e t)
    (hb : b ≤ d) (hc : c ≤ e) : Princess.Ladder.Clears n m b c t := by
  induction run generalizing b c with
  | done =>
      have hb0 : b = 0 := by omega
      have hc0 : c = 0 := by omega
      rw [hb0, hc0]
      exact Princess.Ladder.Clears.done
  | step budget rest ih =>
      exact Princess.Ladder.Clears.step budget
        (ih (Princess.Ladder.next_mono hb) (Princess.Ladder.next_mono hc))

theorem room_run_to_counters {n m : Nat} {B : RoomSet n} {t : Nat}
    (run : RoomClears n m B t) (color : Bool) :
    Princess.Ladder.Clears n m (card (probeColumns B color))
      (card (probeColumns B (!color))) t := by
  induction run generalizing color with
  | @done B empty =>
      have zero : ∀ c, card (probeColumns B c) = 0 := by
        intro c
        apply Nat.eq_zero_of_not_pos
        intro positive
        obtain ⟨i, hi⟩ := (card_pos (probeColumns B c)).mp positive
        exact empty (i, c) hi
      rw [zero, zero]
      exact Princess.Ladder.Clears.done
  | @step B S t budget rest ih =>
      let A := probeColumns B color
      let C := probeColumns B (!color)
      let U := probeColumns S color
      let V := probeColumns S (!color)
      have after : roomStep B S = pair (!color) (columnStep A U) (columnStep C V) := by
        have oldB : pair color A C = B := pair_decompose color B
        have oldS : pair color U V = S := pair_decompose color S
        calc
          roomStep B S = roomStep (pair color A C) (pair color U V) := by rw [oldB, oldS]
          _ = pair (!color) (columnStep A U) (columnStep C V) := by
            funext y
            exact propext (pair_step color A C U V y)
      have later := ih (!color)
      rw [after, pair_probe_left, pair_probe_right] at later
      have actualBudget : card U + card V ≤ m := by
        have split := budget_split S color
        change card U + card V = roomCard S at split
        omega
      exact Princess.Ladder.Clears.step actualBudget
        (counters_mono later (column_count_lower A U) (column_count_lower C V))

theorem counters_to_room_run {n m b c t : Nat}
    (run : Princess.Ladder.Clears n m b c t) (hb : b ≤ n) (hc : c ≤ n)
    (color : Bool) : RoomClears n m (pair color (suffix b) (suffix c)) t := by
  induction run generalizing color with
  | done =>
      apply RoomClears.done
      intro x hx
      unfold pair suffix at hx
      have bound := x.1.isLt
      split at hx <;> omega
  | @step b c p q t budget rest ih =>
      let S := pair color (cut (n := n) b p) (cut c q)
      have roomBudget : roomCard S ≤ m := by
        have a := cut_card_le (n := n) (b := b) (p := p)
        have d := cut_card_le (n := n) (b := c) (p := q)
        have split := pair_card color (cut (n := n) b p) (cut c q)
        change roomCard S = _ at split
        omega
      apply RoomClears.step (S := S) roomBudget
      have after : roomStep (pair color (suffix b) (suffix c)) S =
          pair (!color) (suffix (Princess.Ladder.next n b p)) (suffix (Princess.Ladder.next n c q)) := by
        funext y
        apply propext
        rw [pair_step]
        unfold pair
        split
        · exact suffix_step hb y.1
        · exact suffix_step hc y.1
      rw [after]
      exact ih (Princess.Ladder.next_le n b p) (Princess.Ladder.next_le n c q) (!color)

def full {n : Nat} : RoomSet n := fun _ => True

theorem full_card {n : Nat} (color : Bool) : card (probeColumns (full (n := n)) color) = n := by
  exact (card_full_iff _).mpr (fun _ => True.intro)

/-- Complete exact classification for the explicitly defined checkerboard
room game. The physical coordinate transfer is given separately below. -/
theorem colored_game_classification (n m : Nat) (hn : 2 ≤ n) (hm : 2 ≤ m) :
    RoomClears n m full (Princess.Ladder.optimalTurns n m) ∧
      ∀ t, RoomClears n m full t → Princess.Ladder.optimalTurns n m ≤ t := by
  have main := Princess.Ladder.counter_classification n m hn hm
  constructor
  · have witness := counters_to_room_run main.1 (Nat.le_refl n) (Nat.le_refl n) false
    apply room_clears_mono witness
    intro x hx
    unfold pair suffix
    split <;> omega
  · intro t run
    have reduced := room_run_to_counters run false
    rw [full_card, full_card] at reduced
    exact main.2 t reduced

theorem colored_one_probe_impossible (n t : Nat) (hn : 2 ≤ n) :
    ¬ RoomClears n 1 full t := by
  intro run
  have reduced := room_run_to_counters run false
  rw [full_card, full_card] at reduced
  exact Princess.Ladder.one_probe_no_clears n t hn reduced

inductive PhysicalClears (n m : Nat) : RoomSet n → Nat → Prop
  | done {B} : (∀ x, ¬ B x) → PhysicalClears n m B 0
  | step {B S t} : roomCard S ≤ m → PhysicalClears n m (physicalStep B S) t →
      PhysicalClears n m B (t + 1)

theorem physical_to_colored {n m : Nat} {B : RoomSet n} {t : Nat}
    (run : PhysicalClears n m B t) : RoomClears n m (fun x => B (recolor x)) t := by
  induction run with
  | done empty => exact RoomClears.done (fun x => empty (recolor x))
  | @step B S t budget rest ih =>
      apply RoomClears.step (S := fun x => S (recolor x))
      · simpa only [recolor_roomCard] using budget
      · have after : (fun x => physicalStep B S (recolor x)) =
            roomStep (fun x => B (recolor x)) (fun x => S (recolor x)) := by
          funext x
          apply propext
          simpa only [recolor_involutive] using physicalStep_iff_recolored B S (recolor x)
        rw [← after]
        exact ih

theorem colored_to_physical {n m : Nat} {B : RoomSet n} {t : Nat}
    (run : RoomClears n m B t) : PhysicalClears n m (fun x => B (recolor x)) t := by
  induction run with
  | done empty => exact PhysicalClears.done (fun x => empty (recolor x))
  | @step B S t budget rest ih =>
      apply PhysicalClears.step (S := fun x => S (recolor x))
      · simpa only [recolor_roomCard] using budget
      · have after : physicalStep (fun x => B (recolor x)) (fun x => S (recolor x)) =
            (fun x => roomStep B S (recolor x)) := by
          funext x
          apply propext
          simpa only [recolor_involutive] using
            physicalStep_iff_recolored (fun x => B (recolor x)) (fun x => S (recolor x)) x
        rw [after]
        exact ih

/-- Complete classification for the ordinary physical row-edge game. -/
theorem physical_game_classification (n m : Nat) (hn : 2 ≤ n) (hm : 2 ≤ m) :
    PhysicalClears n m full (Princess.Ladder.optimalTurns n m) ∧
      ∀ t, PhysicalClears n m full t → Princess.Ladder.optimalTurns n m ≤ t := by
  have main := colored_game_classification n m hn hm
  exact ⟨colored_to_physical main.1, fun t run => main.2 t (physical_to_colored run)⟩

theorem physical_one_probe_impossible (n t : Nat) (hn : 2 ≤ n) :
    ¬ PhysicalClears n 1 full t := by
  intro run
  exact colored_one_probe_impossible n t hn (physical_to_colored run)

theorem possible_shift_one {n : Nat} (B : RoomSet n) (probes : Nat → RoomSet n)
    (t : Nat) (x : Room n) :
    Princess.possible rowAdj B probes (t + 1) x ↔
      Princess.possible rowAdj (physicalStep B (probes 0)) (fun i => probes (i + 1)) t x := by
  induction t generalizing x with
  | zero => simp [Princess.possible, Princess.move, physicalStep, and_assoc]
  | succ t ih =>
      constructor
      · intro h
        obtain ⟨y, ⟨hy, hm⟩, he⟩ := h
        exact ⟨y, ⟨(ih y).mp hy, hm⟩, he⟩
      · intro h
        obtain ⟨y, ⟨hy, hm⟩, he⟩ := h
        exact ⟨y, ⟨(ih y).mpr hy, hm⟩, he⟩

theorem empty_possible_to_physical_run {n m : Nat} (B : RoomSet n)
    (probes : Nat → RoomSet n) (budget : ∀ i, roomCard (probes i) ≤ m)
    (t : Nat) (empty : ∀ x, ¬ Princess.possible rowAdj B probes t x) :
    PhysicalClears n m B t := by
  induction t generalizing B probes with
  | zero => exact PhysicalClears.done empty
  | succ t ih =>
      apply PhysicalClears.step (S := probes 0) (budget 0)
      apply ih (physicalStep B (probes 0)) (fun i => probes (i + 1)) (fun i => budget (i + 1))
      intro x hx
      exact empty x ((possible_shift_one B probes t x).mpr hx)

theorem physical_run_to_empty_possible {n m : Nat} {B : RoomSet n} {t : Nat}
    (run : PhysicalClears n m B t) :
    ∃ probes : Nat → RoomSet n, (∀ i, roomCard (probes i) ≤ m) ∧
      ∀ x, ¬ Princess.possible rowAdj B probes t x := by
  classical
  induction run with
  | done empty =>
      refine ⟨fun _ _ => False, ?_, empty⟩
      intro i
      have zero : card (fun _ : Fin n => False) = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro positive
        obtain ⟨x, hx⟩ := (card_pos (fun _ : Fin n => False)).mp positive
        exact hx
      change card (fun _ : Fin n => False) + card (fun _ : Fin n => False) ≤ m
      rw [zero]
      omega
  | @step B S t budget rest ih =>
      obtain ⟨tail, tailBudget, tailEmpty⟩ := ih
      let probes : Nat → RoomSet n := fun i => match i with
        | 0 => S
        | j + 1 => tail j
      refine ⟨probes, ?_, ?_⟩
      · intro i
        cases i with
        | zero => exact budget
        | succ i => exact tailBudget i
      · intro x hx
        exact tailEmpty x ((possible_shift_one B probes t x).mp hx)

/-- The exact optimum for arbitrary actual physical probe sequences.
`possible` is the general belief computation already proved equivalent to
actual legal avoiding trajectories in `BeliefSemantics.lean`. -/
theorem actual_ladder_classification (n m : Nat) (hn : 2 ≤ n) (hm : 2 ≤ m) :
    (∃ probes : Nat → RoomSet n, (∀ i, roomCard (probes i) ≤ m) ∧
      ∀ x, ¬ Princess.possible rowAdj full probes (Princess.Ladder.optimalTurns n m) x) ∧
    (∀ probes : Nat → RoomSet n, (∀ i, roomCard (probes i) ≤ m) → ∀ t,
      (∀ x, ¬ Princess.possible rowAdj full probes t x) → Princess.Ladder.optimalTurns n m ≤ t) := by
  have main := physical_game_classification n m hn hm
  constructor
  · exact physical_run_to_empty_possible main.1
  · intro probes budget t empty
    exact main.2 t (empty_possible_to_physical_run full probes budget t empty)

theorem actual_one_probe_impossible (n : Nat) (hn : 2 ≤ n)
    (probes : Nat → RoomSet n) (budget : ∀ i, roomCard (probes i) ≤ 1) (t : Nat) :
    ¬ (∀ x, ¬ Princess.possible rowAdj full probes t x) := by
  intro empty
  exact physical_one_probe_impossible n t hn (empty_possible_to_physical_run full probes budget t empty)

/-- Empty next belief means guaranteed capture, using a proved physical
neighbor for every room rather than assuming that a surviving target dies. -/
theorem empty_iff_guaranteed_capture {n : Nat} (B : RoomSet n) (probes : Nat → RoomSet n)
    (t : Nat) :
    (∀ x, ¬ Princess.possible rowAdj B probes (t + 1) x) ↔
      Princess.GuaranteesAt rowAdj B probes t := by
  exact (Princess.guarantees_iff_next_empty rowAdj B probes physical_no_dead_ends t).symm

theorem zero_run_counters {n m b c : Nat} (run : Princess.Ladder.Clears n m b c 0) :
    b = 0 ∧ c = 0 := by
  cases run
  exact ⟨rfl, rfl⟩

theorem single_edge_counter_upper (m : Nat) (hm : 1 ≤ m) :
    Princess.Ladder.Clears 1 m 1 1 (if 2 ≤ m then 1 else 2) := by
  by_cases enough : 2 ≤ m
  · rw [if_pos enough]
    apply Princess.Ladder.Clears.step (p := 1) (q := 1) (by omega)
    exact Princess.Ladder.Clears.done
  · rw [if_neg enough]
    apply Princess.Ladder.Clears.step (p := 1) (q := 0) (by omega)
    apply Princess.Ladder.Clears.step (p := 0) (q := 1) (by omega)
    exact Princess.Ladder.Clears.done

theorem single_edge_counter_lower {m t : Nat} (hm : 1 ≤ m)
    (run : Princess.Ladder.Clears 1 m 1 1 t) : (if 2 ≤ m then 1 else 2) ≤ t := by
  cases t with
  | zero =>
      have h := zero_run_counters run
      omega
  | succ t =>
      by_cases enough : 2 ≤ m
      · rw [if_pos enough]
        omega
      · rw [if_neg enough]
        cases t with
        | zero =>
            cases run with
            | @step b c p q t budget rest =>
                have gone := zero_run_counters rest
                have hp := (Princess.Ladder.next_eq_zero_iff (n := 1) (by omega)).mp gone.1
                have hq := (Princess.Ladder.next_eq_zero_iff (n := 1) (by omega)).mp gone.2
                omega
        | succ t => omega

/-- The omitted n=1 ladder is a single physical edge: two rounds for one
probe, and one round for two or more probes. -/
theorem actual_single_edge_classification (m : Nat) (hm : 1 ≤ m) :
    (∃ probes : Nat → RoomSet 1, (∀ i, roomCard (probes i) ≤ m) ∧
      ∀ x, ¬ Princess.possible rowAdj full probes (if 2 ≤ m then 1 else 2) x) ∧
    (∀ probes : Nat → RoomSet 1, (∀ i, roomCard (probes i) ≤ m) → ∀ t,
      (∀ x, ¬ Princess.possible rowAdj full probes t x) → (if 2 ≤ m then 1 else 2) ≤ t) := by
  constructor
  · have witness := counters_to_room_run (single_edge_counter_upper m hm)
      (Nat.le_refl 1) (Nat.le_refl 1) false
    have fullRun : RoomClears 1 m full (if 2 ≤ m then 1 else 2) := by
      apply room_clears_mono witness
      intro x hx
      unfold pair suffix
      split <;> omega
    exact physical_run_to_empty_possible (colored_to_physical fullRun)
  · intro probes budget t empty
    have physical := empty_possible_to_physical_run full probes budget t empty
    have colored : RoomClears 1 m full t := physical_to_colored physical
    have reduced := room_run_to_counters colored false
    rw [full_card, full_card] at reduced
    exact single_edge_counter_lower hm reduced

end Princess.LadderGame

#print axioms Princess.LadderGame.pair_step
#print axioms Princess.LadderGame.colored_game_classification
#print axioms Princess.LadderGame.actual_ladder_classification
#print axioms Princess.LadderGame.actual_one_probe_impossible
#print axioms Princess.LadderGame.empty_iff_guaranteed_capture
#print axioms Princess.LadderGame.actual_single_edge_classification
