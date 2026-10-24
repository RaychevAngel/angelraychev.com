import RowPrefixCampingNine

/-! Sparse lists of certified losing pairs. Counting the list once replaces
an exhaustive scan of an otherwise mostly empty pair mask. -/
namespace Delivery.RowPrefix
open FiniteGame Extremal DenseCombinatorics SparseSupport

def pairRows : List (Fin n × Fin n) → Rows n
  | [] => fun _ => 0
  | (a,b)::pairs => fun s => (if a=s then 2^b.val else 0) ||| pairRows pairs s

theorem pairRows_bit (pairs : List (Fin n × Fin n)) (s t : Fin n) :
    bit (pairRows pairs s) t ↔ (s,t)∈pairs := by
  induction pairs with
  | nil => simp [pairRows,bit]
  | cons ab pairs ih =>
    obtain ⟨a,b⟩ := ab
    simp only [pairRows,bit,Nat.testBit_or,Bool.or_eq_true,List.mem_cons]
    change ((if a=s then 2^b.val else 0).testBit t.val=true ∨ bit (pairRows pairs s) t) ↔ _
    rw [ih]
    by_cases same : a=s
    · subst a
      rw [if_pos rfl]
      have power := bit_power b t
      change (Nat.testBit (2^b.val) t.val=true ↔ b=t) at power
      rw [power]
      simp [Prod.mk.injEq,eq_comm]
    · rw [if_neg same]
      simp only [Nat.zero_testBit,Bool.false_eq_true,false_or]
      have different : (s,t)≠(a,b) := fun eq => same (congrArg Prod.fst eq).symm
      simp [different]

theorem pairRows_count (pairs : List (Fin n × Fin n)) (nodup : pairs.Nodup) :
    allowedCount (pairRows pairs)=pairs.length := by
  have count : arcCount (fun s t => (s,t)∈pairs)=pairs.length := by
    rw [arcCount_eq]
    have perm : ((allPairs n).filter fun st => decide (st∈pairs)).Perm pairs := by
      apply (List.perm_ext_iff_of_nodup ((DenseZero.allPairs_nodup n).filter _) nodup).mpr
      intro st
      simp only [List.mem_filter,GraphRelabeling.allPairs_mem,true_and,decide_eq_true_eq]
    exact perm.length_eq
  have equal : arcCount (fun s t => bit (pairRows pairs s) t)=arcCount (fun s t => (s,t)∈pairs) :=
    arcs_congr (pairRows_bit pairs)
  have counted : arcCount (fun s t => bit (pairRows pairs s) t)=allowedCount (pairRows pairs) := arcCount_eq _
  omega

structure PairBound (n : Nat) where
  pairs : List (Fin n × Fin n)
  upper : Rows n
  lower : Rows n
  available : Nat
  camps : List (CampLoss n)
  losses : List (Loss n)

def PairBoundOK (D R : Fin n → Nat) (p : List Nat) (bound left total : Nat) (cert : PairBound n) : Prop :=
  FastEnvelopeOK R p cert.upper cert.lower cert.available ∧
  (∀ loss∈cert.camps,CampRegionOK cert.upper cert.lower loss) ∧
  (∀ loss∈cert.losses,RegionOK cert.upper cert.lower loss.good loss.region loss.target) ∧
  cert.pairs.Nodup ∧
  (∀ st∈cert.pairs,2≤D st.1 ∧ 2≤R st.2 ∧ st.1≠st.2 ∧
    (CampExists cert.camps st.1 st.2 ∨ LossExists cert.losses st.1 st.2)) ∧
  left ≤ bound + cert.pairs.length + total + cornerCount D R p

instance (D R : Fin n → Nat) (p : List Nat) (bound left total : Nat) (cert : PairBound n) :
    Decidable (PairBoundOK D R p bound left total cert) := inferInstanceAs (Decidable (_ ∧ _))

theorem pair_bound_sound (D R : Fin n → Nat) (p : List Nat) (bound left total : Nat)
    (cert : PairBound n)
    (left_eq : eligibleCount D R + lowSum D + lowSum R=left)
    (total_eq : degreeSum D=total)
    (checked : PairBoundOK D R p bound left total cert) : Upper D R p bound := by
  apply cut_count_sound D R p bound (pairRows cert.pairs)
  · intro s t h
    have yes := checked.2.2.2.2.1 (s,t) ((pairRows_bit _ _ _).mp h)
    exact ⟨yes.1,yes.2.1,yes.2.2.1⟩
  · intro E valid agrees s t h
    have env := fast_envelope_sound R p cert.upper cert.lower cert.available checked.1
    have yes := checked.2.2.2.2.1 (s,t) ((pairRows_bit _ _ _).mp h)
    rcases yes.2.2.2 with camp | game
    · exact camp_loss_sound valid agrees cert.upper cert.lower env cert.camps checked.2.1 camp
    · exact loss_sound valid agrees cert.upper cert.lower cert.losses env checked.2.2.1 game
  · rw [left_eq,total_eq,pairRows_count cert.pairs checked.2.2.2.1]
    exact checked.2.2.2.2.2

namespace PairNine
open BooleanNine CampingNine

def check (D R : Fin 9 → Nat) (p : List Nat) (bound left total : Nat) (cert : PairBound 9) : Bool :=
  fastEnvelopeCheck R p cert.upper cert.lower cert.available &&
  cert.camps.all (campCheck cert.upper cert.lower) &&
  cert.losses.all (fun loss => regionCheck cert.upper cert.lower loss.good loss.region loss.target) &&
  decide cert.pairs.Nodup &&
  cert.pairs.all (fun st => decide (2≤D st.1 ∧ 2≤R st.2 ∧ st.1≠st.2 ∧
    (CampExists cert.camps st.1 st.2 ∨ LossExists cert.losses st.1 st.2))) &&
  decide (left ≤ bound + cert.pairs.length + total + cornerCount D R p)

theorem check_true (D R : Fin 9 → Nat) (p : List Nat) (bound left total : Nat) (cert : PairBound 9) :
    check D R p bound left total cert=true ↔ PairBoundOK D R p bound left total cert := by
  simp only [check,Bool.and_eq_true,fastEnvelopeCheck_true,List.all_eq_true,campCheck_true,
    regionCheck_true,decide_eq_true_eq,PairBoundOK,and_assoc]

theorem sound (D R : Fin 9 → Nat) (p : List Nat) (bound left total : Nat)
    (cert : PairBound 9)
    (left_eq : eligibleCount D R + lowSum D + lowSum R=left)
    (total_eq : degreeSum D=total)
    (checked : check D R p bound left total cert=true) : Upper D R p bound :=
  pair_bound_sound D R p bound left total cert left_eq total_eq
    ((check_true D R p bound left total cert).mp checked)

end PairNine
#print axioms pair_bound_sound
end Delivery.RowPrefix
