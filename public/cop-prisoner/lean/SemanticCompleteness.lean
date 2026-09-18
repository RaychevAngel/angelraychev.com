import FiniteGame

/-! Eventual delivery against arbitrary history-dependent legal policies is
equivalent, on finite graphs, to a finite winning tree. No a priori horizon
is built into the eventual-delivery definition. -/
namespace Delivery.SemanticCompleteness
open FiniteGame

universe u
variable {V : Type u}

abbrev MessengerPolicy (V : Type u) := History V → V → V → V

def LegalMessenger (E : Graph V) (messenger : MessengerPolicy V) : Prop :=
  ∀ h r c, Legal E r (messenger h r c)

/-- A finite observation of play under two fixed policies. The policies do
not receive the observation horizon; timeout is not a successful outcome. -/
def playAgainst [DecidableEq V] (t : V) (messenger : MessengerPolicy V)
    (cop : PursuerPolicy V) : Nat → History V → V → V → Outcome
  | 0, _, r, c =>
      if r = t then .delivered else if r = c then .captured else .timeout
  | k+1, h, r, c =>
      if r = t then .delivered else if r = c then .captured else
      let z := messenger h r c
      if z = t then .delivered else if z = c then .captured else
      let c' := cop h r c z
      if z = c' then .captured else playAgainst t messenger cop k ((r,c)::h) z c'

def EventuallyWinning [DecidableEq V] (E : Graph V) (t r c : V) : Prop :=
  ∃ messenger : MessengerPolicy V, LegalMessenger E messenger ∧
    ∀ cop : PursuerPolicy V, LegalPursuer E cop →
      ∃ k, playAgainst t messenger cop k [] r c = .delivered

theorem selectedMove_legal (E : Graph V) (t : V) (k : Nat) (r c : V) :
    Legal E r (selectedMove E t k r c) := by
  classical
  by_cases existsMove : ∃ z, GoodMove E t k r c z
  · simp only [selectedMove, dif_pos existsMove]
    exact (Classical.choose_spec existsMove).1
  · simp only [selectedMove, dif_neg existsMove]
    exact legal_wait E r

/-- A winning finite bound is built into the policy once, and the observed
history determines its remaining budget; no future cop response is observed. -/
noncomputable def clockMessenger (E : Graph V) (t : V) (bound : Nat) :
    MessengerPolicy V := fun h r c => selectedMove E t (bound - h.length - 1) r c

theorem clockMessenger_legal (E : Graph V) (t : V) (bound : Nat) :
    LegalMessenger E (clockMessenger E t bound) :=
  fun _h r c => selectedMove_legal E t _ r c

theorem clock_play_eq [DecidableEq V] (E : Graph V) (t : V) (bound : Nat)
    (cop : PursuerPolicy V) (k : Nat) (h : History V) (r c : V)
    (clock : k + h.length = bound) :
    playAgainst t (clockMessenger E t bound) cop k h r c = play E t cop k h r c := by
  induction k generalizing h r c with
  | zero => rfl
  | succ k ih =>
      have budget : bound - h.length - 1 = k := by omega
      have nextClock : k + ((r,c)::h).length = bound := by simp; omega
      simp only [playAgainst, play, clockMessenger, budget]
      split <;> try rfl
      split <;> try rfl
      split <;> try rfl
      split <;> try rfl
      split <;> try rfl
      exact ih _ _ _ nextClock

theorem winning_eventually [DecidableEq V] {E : Graph V} {t r c : V} {k : Nat}
    (win : Winning E t k r c) : EventuallyWinning E t r c := by
  refine ⟨clockMessenger E t k, clockMessenger_legal E t k, ?_⟩
  intro cop legal
  refine ⟨k, ?_⟩
  rw [clock_play_eq E t k cop k [] r c (by simp)]
  exact winning_play_delivers win cop legal []

/-- Finitely many individually bounded obligations admit a common bound. -/
theorem finite_uniform_bound {n : Nat} (P : Nat → Fin n → Prop)
    (mono : ∀ k l c, k ≤ l → P k c → P l c)
    (individual : ∀ c, ∃ k, P k c) : ∃ k, ∀ c, P k c := by
  have aux : ∀ xs : List (Fin n), ∃ k, ∀ c, c ∈ xs → P k c := by
    intro xs
    induction xs with
    | nil => exact ⟨0,fun _ h => False.elim (List.not_mem_nil h)⟩
    | cons c xs ih =>
        obtain ⟨a,ha⟩ := individual c
        obtain ⟨b,hb⟩ := ih
        refine ⟨max a b, ?_⟩
        intro d member
        rcases List.mem_cons.mp member with same | tail
        · subst d; exact mono a _ c (Nat.le_max_left _ _) ha
        · exact mono b _ d (Nat.le_max_right _ _) (hb d tail)
  obtain ⟨k,hk⟩ := aux (List.finRange n)
  exact ⟨k, fun c => hk c (List.mem_finRange c)⟩

/-- The complement of finite winning is closed against every legal messenger
move. Finiteness is used only to combine the possible cop-reply horizons. -/
noncomputable def nonwinningRegion {n : Nat} (E : Graph (Fin n)) (t : Fin n) :
    LosingRegion E t where
  region := fun r c => ¬ ∃ k, Winning E t k r c
  nonterminal := by
    intro r c outside same
    subst r
    exact outside ⟨0,Winning.delivered⟩
  closed := by
    classical
    intro r c outside distinct z moveLegal
    have notTarget : z ≠ t := by
      intro same
      subst z
      exact outside ⟨1,Winning.finish distinct moveLegal⟩
    refine ⟨notTarget, ?_⟩
    by_cases immediate : z = c
    · exact Or.inl immediate
    · right
      apply Classical.byContradiction
      intro noReply
      have safe : ∀ c', Legal E c c' → z ≠ c' := by
        intro c' legal same
        exact noReply ⟨c',legal,Or.inl same⟩
      have individual : ∀ c', ∃ k, Legal E c c' → Winning E t k z c' := by
        intro c'
        by_cases legal : Legal E c c'
        · have someWin : ∃ k, Winning E t k z c' := by
            apply Classical.byContradiction
            intro none
            exact noReply ⟨c',legal,Or.inr none⟩
          obtain ⟨k,win⟩ := someWin
          exact ⟨k,fun _ => win⟩
        · exact ⟨0,fun h => False.elim (legal h)⟩
      obtain ⟨k,allWin⟩ := finite_uniform_bound
        (fun k c' => Legal E c c' → Winning E t k z c')
        (fun a b _ hab win legal => winning_mono (win legal) hab) individual
      exact outside ⟨k+1,Winning.step distinct moveLegal immediate safe allWin⟩

noncomputable def regionCop {E : Graph V} {t : V} (cert : LosingRegion E t) :
    PursuerPolicy V := fun _ r c z => by
  classical
  exact if reply : ∃ c', Legal E c c' ∧ (z = c' ∨ cert.region z c')
    then Classical.choose reply else c

theorem regionCop_legal {E : Graph V} {t : V} (cert : LosingRegion E t) :
    LegalPursuer E (regionCop cert) := by
  classical
  intro h r c z
  by_cases reply : ∃ c', Legal E c c' ∧ (z = c' ∨ cert.region z c')
  · simp only [regionCop, dif_pos reply]
    exact (Classical.choose_spec reply).1
  · simp only [regionCop, dif_neg reply]
    exact legal_wait E c

theorem regionCop_preserves {E : Graph V} {t : V} (cert : LosingRegion E t)
    (h : History V) {r c z : V} (inside : cert.region r c) (distinct : r ≠ c)
    (moveLegal : Legal E r z) (notCaptured : z ≠ c) :
    z = regionCop cert h r c z ∨ cert.region z (regionCop cert h r c z) := by
  classical
  have reply : ∃ c', Legal E c c' ∧ (z = c' ∨ cert.region z c') := by
    rcases (cert.closed r c inside distinct z moveLegal).2 with immediate | reply
    · exact False.elim (notCaptured immediate)
    · exact reply
  simp only [regionCop, dif_pos reply]
  exact (Classical.choose_spec reply).2

theorem losingRegion_never_delivers [DecidableEq V] {E : Graph V} {t : V}
    (cert : LosingRegion E t) (messenger : MessengerPolicy V)
    (legal : LegalMessenger E messenger) (k : Nat) (h : History V) (r c : V)
    (inside : cert.region r c) :
    playAgainst t messenger (regionCop cert) k h r c ≠ .delivered := by
  induction k generalizing h r c with
  | zero =>
      have notTarget := cert.nonterminal r c inside
      simp only [playAgainst, if_neg notTarget]
      split <;> simp
  | succ k ih =>
      have notTarget := cert.nonterminal r c inside
      by_cases captured : r = c
      · simp only [playAgainst, if_neg notTarget, if_pos captured]
        simp
      · have moveLegal := legal h r c
        have notFinish := (cert.closed r c inside captured _ moveLegal).1
        by_cases immediate : messenger h r c = c
        · simp only [playAgainst, if_neg notTarget, if_neg captured,
            if_neg notFinish, if_pos immediate]
          simp
        · have next := regionCop_preserves cert h inside captured moveLegal immediate
          by_cases collision : messenger h r c = regionCop cert h r c (messenger h r c)
          · simp only [playAgainst, if_neg notTarget, if_neg captured,
              if_neg notFinish, if_neg immediate, if_pos collision]
            simp
          · have nextInside := next.resolve_left collision
            simp only [playAgainst, if_neg notTarget, if_neg captured, if_neg notFinish,
              if_neg immediate, if_neg collision]
            exact ih _ _ _ nextInside

theorem eventual_iff_finite {n : Nat} (E : Graph (Fin n)) (t r c : Fin n) :
    EventuallyWinning E t r c ↔ ∃ k, Winning E t k r c := by
  constructor
  · intro eventual
    apply Classical.byContradiction
    intro outside
    obtain ⟨messenger, legal, wins⟩ := eventual
    let cert := nonwinningRegion E t
    obtain ⟨k,delivers⟩ := wins (regionCop cert) (regionCop_legal cert)
    exact losingRegion_never_delivers cert messenger legal k [] r c outside delivers
  · rintro ⟨k,win⟩
    exact winning_eventually win

theorem guaranteed_iff_eventual {n : Nat} (E : Graph (Fin n)) (s t : Fin n) :
    Guaranteed E s t ↔ ∀ c, c ≠ s → EventuallyWinning E t s c := by
  constructor
  · intro guaranteed c initial
    exact (eventual_iff_finite E t s c).mpr (guaranteed c initial)
  · intro eventual c initial
    exact (eventual_iff_finite E t s c).mp (eventual c initial)

/-- There is also one finite bound working for all permitted initial cops. -/
theorem guaranteed_uniform_bound {n : Nat} {E : Graph (Fin n)} {s t : Fin n}
    (guaranteed : Guaranteed E s t) : ∃ k, Universal E t k s := by
  classical
  apply finite_uniform_bound (fun k c => c ≠ s → Winning E t k s c)
    (fun a b _ hab win initial => winning_mono (win initial) hab)
  intro c
  by_cases initial : c ≠ s
  · obtain ⟨k,win⟩ := guaranteed c initial
    exact ⟨k,fun _ => win⟩
  · exact ⟨0,fun h => False.elim (initial h)⟩

/-- A single fixed messenger policy suffices for every initial cop and every
cop policy. The messenger may observe the initial cop through the state. -/
def ActualGuaranteed {n : Nat} (E : Graph (Fin n)) (s t : Fin n) : Prop :=
  ∃ messenger : MessengerPolicy (Fin n), LegalMessenger E messenger ∧
    ∀ c, c ≠ s → ∀ cop, LegalPursuer E cop →
      ∃ k, playAgainst t messenger cop k [] s c = .delivered

theorem guaranteed_iff_actual {n : Nat} (E : Graph (Fin n)) (s t : Fin n) :
    Guaranteed E s t ↔ ActualGuaranteed E s t := by
  constructor
  · intro guaranteed
    obtain ⟨k,win⟩ := guaranteed_uniform_bound guaranteed
    refine ⟨clockMessenger E t k, clockMessenger_legal E t k, ?_⟩
    intro c initial cop legal
    refine ⟨k, ?_⟩
    rw [clock_play_eq E t k cop k [] s c (by simp)]
    exact winning_play_delivers (win c initial) cop legal []
  · rintro ⟨messenger,legal,wins⟩ c initial
    exact (eventual_iff_finite E t s c).mp ⟨messenger,legal,wins c initial⟩

#print axioms winning_eventually
#print axioms losingRegion_never_delivers
#print axioms eventual_iff_finite
#print axioms guaranteed_iff_eventual
#print axioms guaranteed_iff_actual
end Delivery.SemanticCompleteness
