import ExactScoreCertificates

/-! Exact mixed graph scores from literal signed rank tables.
Negative ranks designate a closed losing region; nonnegative ranks have
checked legal moves and strict descent. Table producers need not be trusted. -/
namespace Delivery.SignedRankCertificate
open FiniteGame ExactScoreCertificates

structure Data (n : Nat) where
  signed : Fin n → Fin n → Fin n → Int
  move : Fin n → Fin n → Fin n → Fin n

def win {n : Nat} (D : Data n) (t r c : Fin n) : Prop := 0 ≤ D.signed t r c
def lose {n : Nat} (D : Data n) (t r c : Fin n) : Prop := D.signed t r c < 0
def rank {n : Nat} (D : Data n) (t r c : Fin n) : Nat := (D.signed t r c).toNat
instance {n : Nat} (D : Data n) (t r c : Fin n) : Decidable (win D t r c) :=
  inferInstanceAs (Decidable (0 ≤ _))
instance {n : Nat} (D : Data n) (t r c : Fin n) : Decidable (lose D t r c) :=
  inferInstanceAs (Decidable (_ < 0))

structure Checked {n : Nat} (E : Graph (Fin n)) (D : Data n) : Prop where
  valid : ∀ t r c, win D t r c → r ≠ t → r ≠ c →
    Legal E r (D.move t r c) ∧ (D.move t r c = t ∨
      (D.move t r c ≠ c ∧ ∀ c', Legal E c c' →
        D.move t r c ≠ c' ∧ win D t (D.move t r c) c' ∧
        rank D t (D.move t r c) c' < rank D t r c))
  nonterminal : ∀ t r c, lose D t r c → r ≠ t
  closed : ∀ t r c, lose D t r c → r ≠ c →
    ∀ z, Legal E r z → z ≠ t ∧
      (z = c ∨ ∃ c', Legal E c c' ∧ (z = c' ∨ lose D t z c'))

def accepted {n : Nat} (D : Data n) (s t : Fin n) : Bool :=
  decide (∀ c, c ≠ s → win D t s c)

def classification {n : Nat} {E : Graph (Fin n)} {D : Data n}
    (check : Checked E D) : Classification E where
  accepted := accepted D
  winning t := { region := win D t, rank := rank D t, move := D.move t, valid := check.valid t }
  losing t := { region := lose D t, nonterminal := check.nonterminal t, closed := check.closed t }
  yes _ _ _ _ yes := by
    simpa only [accepted,decide_eq_true_eq] using yes
  no s t _ _ no := by
    apply Classical.byContradiction
    intro absent
    have all : ∀ c, c ≠ s → win D t s c := by
      intro c initial
      have notLose : ¬ lose D t s c := fun lost => absent ⟨c,initial,lost⟩
      unfold lose at notLose
      unfold win
      omega
    have yes : accepted D s t = true := by
      simpa only [accepted,decide_eq_true_eq] using all
    rw [yes] at no
    contradiction

#print axioms classification
end Delivery.SignedRankCertificate
