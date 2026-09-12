import Std

/-!
Actual visible, alternating messenger/pursuer game.
Both players may wait; messenger moves first; receipt ends play before
collision is checked at the recipient. Infinite non-delivery is not success.
No external graph-game interface or classification theorem is assumed.
-/
namespace Delivery

universe u
variable {V : Type u}

abbrev Graph (V : Type u) := V → V → Prop

def Legal (E : Graph V) (x y : V) : Prop := x = y ∨ E x y

theorem legal_wait (E : Graph V) (x : V) : Legal E x x := Or.inl rfl

/-- A finite contingent strategy tree, counting messenger moves. Every
pursuer reply is quantified; both kinds of nonterminal collision are excluded. -/
inductive Winning (E : Graph V) (t : V) : Nat → V → V → Prop
  | delivered {k c} : Winning E t k t c
  | finish {k r c} : r ≠ c → Legal E r t → Winning E t (k+1) r c
  | step {k r c z} : r ≠ c → Legal E r z → z ≠ c →
      (∀ c', Legal E c c' → z ≠ c') →
      (∀ c', Legal E c c' → Winning E t k z c') →
      Winning E t (k+1) r c

/-- The universal initial-position quantifier. -/
def Universal (E : Graph V) (t : V) (k : Nat) (r : V) : Prop :=
  ∀ c, c ≠ r → Winning E t k r c

theorem winning_mono {E : Graph V} {t r c : V} {k l : Nat}
    (h : Winning E t k r c) (hle : k ≤ l) : Winning E t l r c := by
  induction h generalizing l with
  | delivered => exact Winning.delivered
  | finish hrc he =>
      cases l with
      | zero => omega
      | succ l => exact Winning.finish hrc he
  | @step k r c z hrc he hzc hsafe hnext ih =>
      cases l with
      | zero => omega
      | succ l =>
          exact Winning.step hrc he hzc hsafe (fun c' hc' =>
            ih c' hc' (by omega))

theorem direct_delivery {E : Graph V} {r t c : V}
    (hrc : r ≠ c) (edge : E r t) : Winning E t 1 r c :=
  Winning.finish hrc (Or.inr edge)

theorem occupied_recipient_delivery {E : Graph V} {r t : V}
    (hrt : r ≠ t) (edge : E r t) : Winning E t 1 r t :=
  direct_delivery hrt edge

/-- The exact one-round requirement used to select a move from a winning tree. -/
def GoodMove (E : Graph V) (t : V) (k : Nat) (r c z : V) : Prop :=
  Legal E r z ∧ (z = t ∨
    (z ≠ c ∧ ∀ c', Legal E c c' → z ≠ c' ∧ Winning E t k z c'))

theorem winning_has_move {E : Graph V} {t r c : V} {k : Nat}
    (h : Winning E t (k+1) r c) (hrt : r ≠ t) :
    r ≠ c ∧ ∃ z, GoodMove E t k r c z := by
  cases h with
  | delivered => exact False.elim (hrt rfl)
  | finish hrc he => exact ⟨hrc,t,he,Or.inl rfl⟩
  | step hrc he hzc hsafe hnext =>
      exact ⟨hrc,_,he,Or.inr ⟨hzc,fun c' hc' => ⟨hsafe c' hc',hnext c' hc'⟩⟩⟩

/-- A single budget-dependent policy obtained from the strategy-tree relation.
It observes positions; it never sees a future pursuer response. -/
noncomputable def selectedMove (E : Graph V) (t : V) (k : Nat) (r c : V) : V := by
  classical
  exact if h : ∃ z, GoodMove E t k r c z then Classical.choose h else r

theorem selectedMove_spec {E : Graph V} {t r c : V} {k : Nat}
    (h : Winning E t (k+1) r c) (hrt : r ≠ t) :
    r ≠ c ∧ GoodMove E t k r c (selectedMove E t k r c) := by
  obtain ⟨hrc,hm⟩ := winning_has_move h hrt
  exact ⟨hrc, by simp only [selectedMove, dif_pos hm]; exact Classical.choose_spec hm⟩

abbrev History (V : Type u) := List (V × V)
abbrev PursuerPolicy (V : Type u) := History V → V → V → V → V

/-- A pursuer may use the entire observed history and current messenger move. -/
def LegalPursuer (E : Graph V) (cop : PursuerPolicy V) : Prop :=
  ∀ h r c z, Legal E c (cop h r c z)

inductive Outcome where
  | delivered
  | captured
  | timeout
  deriving DecidableEq, Repr

/-- Concrete play of the actual game. Success is checked before collision at
the recipient. Timeout means no delivery within the supplied finite budget. -/
noncomputable def play [DecidableEq V] (E : Graph V) (t : V)
    (cop : PursuerPolicy V) : Nat → History V → V → V → Outcome
  | 0, _, r, c =>
      if r = t then .delivered else if r = c then .captured else .timeout
  | k+1, h, r, c =>
      if r = t then .delivered else if r = c then .captured else
      let z := selectedMove E t k r c
      if z = t then .delivered else if z = c then .captured else
      let c' := cop h r c z
      if z = c' then .captured else play E t cop k ((r,c)::h) z c'

/-- Semantic bridge: every legal, history-dependent pursuer produces actual
terminal delivery under the selected messenger policy, within the tree bound. -/
theorem winning_play_delivers [DecidableEq V] {E : Graph V} {t r c : V}
    {k : Nat} (win : Winning E t k r c) (cop : PursuerPolicy V)
    (hc : LegalPursuer E cop) (h : History V) :
    play E t cop k h r c = .delivered := by
  induction k generalizing h r c with
  | zero =>
      cases win
      simp [play]
  | succ k ih =>
      by_cases hrt : r = t
      · simp [play,hrt]
      · obtain ⟨hrc,hm⟩ := selectedMove_spec win hrt
        obtain ⟨_,ht | ⟨hzc,hnext⟩⟩ := hm
        · simp [play,hrt,hrc,ht]
        · by_cases hzt : selectedMove E t k r c = t
          · simp [play,hrt,hrc,hzt]
          · have hn := hnext (cop h r c (selectedMove E t k r c))
                (hc h r c (selectedMove E t k r c))
            simp only [play, if_neg hrt, if_neg hrc, if_neg hzt, if_neg hzc,
              if_neg hn.1]
            exact ih hn.2 ((r,c)::h)

/-- There is no nonterminal collision in any finite winning state. -/
theorem winning_noncaptured {E : Graph V} {t r c : V} {k : Nat}
    (h : Winning E t k r c) : r = t ∨ r ≠ c := by
  cases h with
  | delivered => exact Or.inl rfl
  | finish hn _ => exact Or.inr hn
  | step hn _ _ _ _ => exact Or.inr hn

/-- A concrete finite-rank strategy certificate. Its obligations refer directly
to the actual legal waits, arcs, next pursuer response, and collision checks. -/
structure RankCertificate (E : Graph V) (t : V) where
  rank : V → V → Nat
  move : V → V → V
  valid : ∀ r c, r ≠ t → r ≠ c →
    Legal E r (move r c) ∧ (move r c = t ∨
      (move r c ≠ c ∧ ∀ c', Legal E c c' →
        move r c ≠ c' ∧ rank (move r c) c' < rank r c))

/-- A checked finite-rank certificate yields actual finite strategy trees. -/
theorem rankCertificate_winning {E : Graph V} {t : V}
    (cert : RankCertificate E t) (r c : V) (hrc : r ≠ c) :
    Winning E t (cert.rank r c + 1) r c := by
  generalize hk : cert.rank r c = k
  induction k using Nat.strongRecOn generalizing r c with
  | ind k ih =>
      by_cases hrt : r = t
      · subst r; exact Winning.delivered
      · obtain ⟨he,ht | ⟨hzc,hnext⟩⟩ := cert.valid r c hrt hrc
        · rw [ht] at he
          exact Winning.finish hrc he
        · apply Winning.step hrc he hzc (fun c' hc' => (hnext c' hc').1)
          intro c' hc'
          obtain ⟨hn,hl⟩ := hnext c' hc'
          have hklt : cert.rank (cert.move r c) c' < k := by omega
          have child := ih _ hklt (cert.move r c) c' hn rfl
          exact winning_mono child (by omega)

theorem rankCertificate_actual_delivery [DecidableEq V] {E : Graph V} {t : V}
    (cert : RankCertificate E t) (r c : V) (hrc : r ≠ c)
    (cop : PursuerPolicy V) (legal : LegalPursuer E cop) (history : History V) :
    play E t cop (cert.rank r c + 1) history r c = .delivered :=
  winning_play_delivers (rankCertificate_winning cert r c hrc) cop legal history

end Delivery
