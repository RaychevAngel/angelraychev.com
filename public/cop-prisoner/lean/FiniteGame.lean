import DeliveryGame

/-! Partial winning certificates and closed losing regions for the actual game.
Unlike RankCertificate, a winning region need not contain every safe state.
The losing closure permits immediate capture and capture on the cop's reply.
Receipt still precedes either collision test. -/
namespace Delivery.FiniteGame

universe u
variable {V : Type u}

structure WinningRegion (E : Graph V) (t : V) where
  region : V → V → Prop
  rank : V → V → Nat
  move : V → V → V
  valid : ∀ r c, region r c → r ≠ t → r ≠ c →
    Legal E r (move r c) ∧ (move r c = t ∨
      (move r c ≠ c ∧ ∀ c', Legal E c c' →
        move r c ≠ c' ∧ region (move r c) c' ∧
        rank (move r c) c' < rank r c))

theorem winningRegion_winning {E : Graph V} {t : V}
    (cert : WinningRegion E t) (r c : V)
    (inside : cert.region r c) (safe : r ≠ c) :
    Winning E t (cert.rank r c + 1) r c := by
  generalize hk : cert.rank r c = k
  induction k using Nat.strongRecOn generalizing r c with
  | ind k ih =>
      by_cases terminal : r = t
      · subst r; exact Winning.delivered
      · obtain ⟨moveLegal, finish | ⟨safeNow, future⟩⟩ :=
          cert.valid r c inside terminal safe
        · rw [finish] at moveLegal
          exact Winning.finish safe moveLegal
        · apply Winning.step safe moveLegal safeNow (fun c' hc' => (future c' hc').1)
          intro c' reply
          obtain ⟨nextSafe, nextInside, smaller⟩ := future c' reply
          have child := ih (cert.rank (cert.move r c) c') (by omega)
            (cert.move r c) c' nextInside nextSafe rfl
          exact winning_mono child (by omega)

theorem winningRegion_actual_delivery [DecidableEq V] {E : Graph V} {t : V}
    (cert : WinningRegion E t) (r c : V)
    (inside : cert.region r c) (safe : r ≠ c)
    (cop : PursuerPolicy V) (legal : LegalPursuer E cop) (history : History V) :
    play E t cop (cert.rank r c + 1) history r c = .delivered :=
  winning_play_delivers (winningRegion_winning cert r c inside safe) cop legal history

structure LosingRegion (E : Graph V) (t : V) where
  region : V → V → Prop
  nonterminal : ∀ r c, region r c → r ≠ t
  closed : ∀ r c, region r c → r ≠ c → ∀ z, Legal E r z →
    z ≠ t ∧ (z = c ∨ ∃ c', Legal E c c' ∧ (z = c' ∨ region z c'))

/-- No finite contingent winning strategy starts in a checked losing region. -/
theorem losingRegion_not_winning {E : Graph V} {t : V}
    (cert : LosingRegion E t) {k : Nat} {r c : V}
    (win : Winning E t k r c) : ¬ cert.region r c := by
  induction win with
  | delivered => exact fun inside => cert.nonterminal _ _ inside rfl
  | @finish k r c distinct moveLegal =>
      intro inside
      exact (cert.closed r c inside distinct t moveLegal).1 rfl
  | @step k r c z distinct moveLegal safeNow safeReply next ih =>
      intro inside
      obtain ⟨_, immediate | ⟨c', reply, capture | remains⟩⟩ :=
        cert.closed r c inside distinct z moveLegal
      · exact safeNow immediate
      · exact safeReply c' reply capture
      · exact ih c' reply remains

/-- The source is guaranteed only when every permitted initial cop has a
finite winning strategy. Different initial cop states may have different ranks. -/
def Guaranteed (E : Graph V) (s t : V) : Prop :=
  ∀ c, c ≠ s → ∃ k, Winning E t k s c

theorem universal_guaranteed {E : Graph V} {s t : V} {k : Nat}
    (win : Universal E t k s) : Guaranteed E s t :=
  fun c distinct => ⟨k, win c distinct⟩

theorem losingRegion_not_guaranteed {E : Graph V} {s t c : V}
    (cert : LosingRegion E t) (inside : cert.region s c) (initial : c ≠ s) :
    ¬ Guaranteed E s t := by
  intro guaranteed
  obtain ⟨k, win⟩ := guaranteed c initial
  exact losingRegion_not_winning cert win inside

#print axioms winningRegion_actual_delivery
#print axioms losingRegion_not_winning
#print axioms losingRegion_not_guaranteed
end Delivery.FiniteGame
