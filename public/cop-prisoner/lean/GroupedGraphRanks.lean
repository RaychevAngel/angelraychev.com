import GroupedArena
import GuaranteedPrefix
import StagedEnvelopes
import WinningScoreRows

/-! Grouped cop certificates for actual finite graphs and asymmetric graph
envelopes. Messenger moves use the lower graph, while every legal cop reply
in the upper graph is covered. Initial cops range over every c ≠ s, including
the recipient. Receipt ends the game before either arrival collision test.

The supplied group rank bounds the number of messenger moves directly. To
convert a MainStageRows table, whose bound is raw rank + 1, add one to each
nonterminal raw rank before grouping; no rank conversion is assumed here. -/
namespace Delivery.GroupedGraphRanks
open FiniteGame Extremal RobustTwoMove LocalArena GroupedArena

abbrev Rows (n : Nat) := Fin n → Fin n → List (Group n n)

def arena {n : Nat} (B U : Graph (Fin n)) : Arena (Fin n) (Fin n) where
  messenger := Legal B
  pursuer := Legal U
  collision r c := r=c

instance {n : Nat} (B U : Graph (Fin n)) [DecidableRel B] :
    DecidableRel (arena B U).messenger :=
  fun r z => inferInstanceAs (Decidable (r=z ∨ B r z))

def collisionMasks {n : Nat} (r : Fin n) : Nat := 2^r.val

def initialMask {n : Nat} (s : Fin n) : Nat := (2^n-1) ^^^ 2^s.val

theorem has_initialMask {n : Nat} (s c : Fin n) : Has (initialMask s) c ↔ c≠s := by
  by_cases same : c=s
  · subst c
    simp [Has,initialMask,Nat.testBit_xor,s.isLt]
  · have different : s.val≠c.val := fun eq => same (Fin.ext eq.symm)
    simp [Has,initialMask,Nat.testBit_xor,c.isLt,different,same]

def activeMask {n : Nat} : List (Group n n) → Nat
  | [] => 0
  | g::gs => g.mask ||| activeMask gs

theorem has_activeMask {n : Nat} (gs : List (Group n n)) (c : Fin n) :
    Has (activeMask gs) c ↔ Active gs c := by
  induction gs with
  | nil => simp [activeMask,Has,Active]
  | cons g gs ih => simp [activeMask,has_or,ih,Active]

/-- One mask inclusion per missing source/recipient pair covers every
eligible initial cop, without a separate finite check for each cop. -/
theorem entries_of_masks {n : Nat} (B : Graph (Fin n)) (rows : Rows n)
    (included : ∀ s t, s≠t → ¬B s t →
      initialMask s &&& activeMask (rows t s)=initialMask s) :
    ∀ s t, s≠t → ¬B s t → ∀ c, c≠s → Active (rows t s) c := by
  intro s t distinct missing c initial
  exact (has_activeMask _ c).mp
    (has_subset (included s t distinct missing) ((has_initialMask s c).mpr initial))

theorem collision_covered {n : Nat} (B U : Graph (Fin n)) (r c : Fin n)
    (collision : (arena B U).collision r c) : Has (collisionMasks r) c :=
  (has_power r c).mpr collision.symm

def Checked {n : Nat} (B U : Graph (Fin n)) [DecidableRel B]
    (replyMasks : Fin n → Nat) (rows : Rows n) : Prop :=
  ∀ t, GroupedArena.Checked true (arena B U) (fun r => r=t)
    replyMasks collisionMasks (rows t)

/-- Sparse upper-graph reply lists may be checked once and reused for every
recipient. Masks may contain additional replies; omitting an actual reply
is forbidden. -/
theorem reply_masks_covered {n : Nat} (U : Graph (Fin n))
    (replies : Fin n → List (Fin n)) (replyMasks : Fin n → Nat)
    (coverage : ∀ c d, Legal U c d → d∈replies c)
    (masks : ∀ c d, d∈replies c → Has (replyMasks c) d) :
    ∀ c d, Legal U c d → Has (replyMasks c) d :=
  fun c d legal => masks c d (coverage c d legal)

def simulation {n : Nat} {B U G : Graph (Fin n)}
    (lower : Subgraph B G) (upper : Subgraph G U) : Simulation G (arena B U) where
  embed := id
  project := id
  messenger_sound := fun _ _ move => StagedEnvelopes.legal_subgraph lower move
  pursuer_complete := fun _ _ reply => StagedEnvelopes.legal_subgraph upper reply
  collision_complete := fun _ _ collision => collision

/-- Every active cop receives an actual finite strategy, at the chosen
minimum group rank, in every intermediate optional subset. -/
theorem winning {n : Nat} {B U G : Graph (Fin n)} [DecidableRel B]
    (replyMasks : Fin n → Nat) (rows : Rows n)
    (coverage : ∀ c d, Legal U c d → Has (replyMasks c) d)
    (checked : Checked B U replyMasks rows)
    (lower : Subgraph B G) (upper : Subgraph G U) (t r c : Fin n)
    (inside : Active (rows t r) c) :
    Winning G t ((data (rows t)).rank r c) r c := by
  have certificate := delivery_checked (arena B U) (fun r => r=t)
    replyMasks collisionMasks (rows t) coverage (collision_covered B U) (checked t)
  exact delivery_projection (simulation lower upper) certificate
    (fun _ same => same) r c inside

theorem winning_bounded {n : Nat} {B U G : Graph (Fin n)} [DecidableRel B]
    (replyMasks : Fin n → Nat) (rows : Rows n)
    (coverage : ∀ c d, Legal U c d → Has (replyMasks c) d)
    (checked : Checked B U replyMasks rows)
    (lower : Subgraph B G) (upper : Subgraph G U) (t r c : Fin n) (bound : Nat)
    (inside : Has (lowerMask (rows t r) (bound+1)) c) : Winning G t bound r c := by
  obtain ⟨active,rankBound⟩ := bounded (rows t) r c bound inside
  exact winning_mono (winning replyMasks rows coverage checked lower upper t r c active) rankBound

/-- Only missing off-diagonal pairs require saved entries. Direct lower
arrows deliver immediately, even when the cop starts at the recipient. -/
theorem delivers {n : Nat} (B U : Graph (Fin n)) [DecidableRel B]
    (replyMasks : Fin n → Nat) (rows : Rows n)
    (coverage : ∀ c d, Legal U c d → Has (replyMasks c) d)
    (checked : Checked B U replyMasks rows)
    (entries : ∀ s t, s≠t → ¬B s t → ∀ c, c≠s → Active (rows t s) c) :
    GuaranteedPrefix.Delivers B U := by
  intro G lower upper s t c initial
  by_cases terminal : s=t
  · subst s
    exact ⟨0,Winning.delivered⟩
  by_cases direct : B s t
  · exact ⟨1,Winning.finish (Ne.symm initial) (Or.inr (lower s t direct))⟩
  exact ⟨_,winning replyMasks rows coverage checked lower upper t s c
    (entries s t terminal direct c initial)⟩

theorem maximum {n m : Nat} (B U : Graph (Fin n)) [DecidableRel B]
    (replyMasks : Fin n → Nat) (rows : Rows n)
    (subset : Subgraph B U) (loopless : Loopless U)
    (coverage : ∀ c d, Legal U c d → Has (replyMasks c) d)
    (checked : Checked B U replyMasks rows)
    (entries : ∀ s t, s≠t → ¬B s t → ∀ c, c≠s → Active (rows t s) c)
    (low : arcCount B≤m) (high : m≤arcCount U) : IsMaximum n m (n*(n-1)-m) :=
  GuaranteedPrefix.maximum B U subset loopless
    (delivers B U replyMasks rows coverage checked entries) low high

/-- A partial certificate can instead count just selected missing pairs of
one graph. Exactness still requires an independent upper bound. -/
theorem lower_bound {n : Nat} (E : Graph (Fin n)) [DecidableRel E]
    (replyMasks : Fin n → Nat) (rows : Rows n) (accepted : Fin n → Fin n → Bool)
    (coverage : ∀ c d, Legal E c d → Has (replyMasks c) d)
    (checked : Checked E E replyMasks rows)
    (entries : ∀ s t, s≠t → ¬E s t → accepted s t=true →
      ∀ c, c≠s → Active (rows t s) c) :
    WinningScoreRows.acceptedCount E accepted≤score E := by
  classical
  apply filter_length_mono
  intro pair yes
  have facts := of_decide_eq_true yes
  apply decide_eq_true
  refine ⟨facts.1,facts.2.1,?_⟩
  intro c initial
  exact ⟨_,winning replyMasks rows coverage checked (fun _ _ edge => edge)
    (fun _ _ edge => edge) pair.2 pair.1 c
    (entries pair.1 pair.2 facts.1 facts.2.1 facts.2.2 c initial)⟩

#print axioms winning
#print axioms winning_bounded
#print axioms entries_of_masks
#print axioms delivers
#print axioms maximum
#print axioms lower_bound
end Delivery.GroupedGraphRanks
