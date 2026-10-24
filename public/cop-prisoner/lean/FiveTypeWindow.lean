import GroupedArena
import SafeProgress
import GuaranteedPrefix
import StagedEnvelopes

/-! Finite charts for the retained five-type local strategies. The chart
obligations include the full upper-graph cop turn and collision reflection
in both directions, so every permitted actual initial cop is covered. -/
namespace Delivery.FiveTypeWindow
open FiniteGame LocalArena RobustTwoMove
abbrev R := Fin 35
def transferGoal (r : R) : Prop := r.val/5=3
def deliveryGoal (t : Fin 5) (r : R) : Prop := r.val=15+t.val
instance (r : R) : Decidable (transferGoal r) := inferInstanceAs (Decidable (_=_))
instance (t : Fin 5) (r : R) : Decidable (deliveryGoal t r) := inferInstanceAs (Decidable (_=_))
def transferStart (j : Fin 5) : R := ⟨20+j.val,by have:=j.isLt;omega⟩
def deliveryStart (j : Fin 5) : R := ⟨25+j.val,by have:=j.isLt;omega⟩

structure Certificates {C : Type} (A : Arena R C) (D : Nat) where
  transfer : Data R C
  transfer_checked : SafeChecked A transferGoal transfer
  transfer_entries : ∀ r c, r.val/5=4 → ¬A.collision r c →
    transfer.region r c ∧ transfer.rank r c≤8
  delivery : Fin 5 → Data R C
  delivery_checked : ∀ t, DeliveryChecked A (deliveryGoal t) (delivery t)
  delivery_entries : ∀ t r c, r.val/5=5 → ¬A.collision r c →
    (delivery t).region r c ∧ (delivery t).rank r c≤D

structure Charts {n k : Nat} {C : Type} (B U : Graph (Fin n)) (A : Arena R C) where
  embed : Fin k → R → Fin n
  project : Fin k → Fin n → C
  messenger : ∀ a r z, A.messenger r z → Legal B (embed a r) (embed a z)
  pursuer : ∀ a c d, Legal U c d → A.pursuer (project a c) (project a d)
  collision : ∀ a r c, A.collision r (project a c) ↔ embed a r=c
  typ : Fin n → Fin 5
  transferCenter : Fin n → Fin k
  deliveryCenter : Fin n → Fin k
  measure : Fin n → Fin n → Nat
  transfer_start : ∀ s, embed (transferCenter s) (transferStart (typ s))=s
  delivery_start : ∀ t s, measure t s=0 →
    embed (deliveryCenter t) (deliveryStart (typ s))=s
  progress : ∀ t s r, 0<measure t s → transferGoal r →
    measure t (embed (transferCenter s) r)<measure t s
  recipient : ∀ t r, deliveryGoal (typ t) r → embed (deliveryCenter t) r=t

def simulation {n k C} {B U G : Graph (Fin n)} {A : Arena R C}
    (chart : Charts (k:=k) B U A) (lower : Subgraph B G) (upper : Subgraph G U)
    (a : Fin k) : Simulation G A where
  embed := chart.embed a
  project := chart.project a
  messenger_sound r z move := StagedEnvelopes.legal_subgraph lower (chart.messenger a r z move)
  pursuer_complete c d reply := chart.pursuer a c d (StagedEnvelopes.legal_subgraph upper reply)
  collision_complete r c same := (chart.collision a r c).mpr same

theorem winning {n k C D} {B U G : Graph (Fin n)} {A : Arena R C}
    (cert : Certificates A D) (chart : Charts (k:=k) B U A)
    (lower : Subgraph B G) (upper : Subgraph G U) (t s c : Fin n) (safe : s≠c) :
    Winning G t (chart.measure t s*8+D) s c := by
  apply SafeProgress.winning (fun _ => True) (chart.measure t) 8 D t
    (r:=s) (c:=c) (eligible:=True.intro) (safe:=safe)
  · intro r c _ distinct positive
    let a := chart.transferCenter r
    let z := transferStart (chart.typ r)
    have start : chart.embed a z=r := chart.transfer_start r
    have noncollision : ¬A.collision z (chart.project a c) := by
      intro bad; exact distinct (start.symm.trans ((chart.collision a z c).mp bad))
    have entry : z.val/5=4 := by dsimp [z,transferStart];have:=(chart.typ r).isLt;omega
    obtain ⟨inside,bound⟩ := cert.transfer_entries z (chart.project a c) entry noncollision
    have projected := safe_projection (simulation chart lower upper a) cert.transfer_checked
      (P:=fun v => True ∧ chart.measure t v<chart.measure t r)
      (fun x goal => ⟨True.intro,chart.progress t r x positive goal⟩) z c inside
    have result := safe_mono projected bound
    simpa only [simulation,start] using result
  · intro r c _ distinct zero
    let a := chart.deliveryCenter t
    let z := deliveryStart (chart.typ r)
    have start : chart.embed a z=r := chart.delivery_start t r zero
    have noncollision : ¬A.collision z (chart.project a c) := by
      intro bad;exact distinct (start.symm.trans ((chart.collision a z c).mp bad))
    have entry : z.val/5=5 := by dsimp [z,deliveryStart];have:=(chart.typ r).isLt;omega
    obtain ⟨inside,bound⟩ := cert.delivery_entries (chart.typ t) z (chart.project a c) entry noncollision
    have projected := delivery_projection (simulation chart lower upper a)
      (cert.delivery_checked (chart.typ t)) (chart.recipient t) z c inside
    have result := winning_mono projected bound
    simpa only [simulation,start] using result

theorem delivers {n k C D} {B U : Graph (Fin n)} {A : Arena R C}
    (cert : Certificates A D) (chart : Charts (k:=k) B U A) : GuaranteedPrefix.Delivers B U := by
  intro G lower upper s t c distinct
  exact ⟨_,winning cert chart lower upper t s c distinct.symm⟩

#print axioms winning
#print axioms delivers
end Delivery.FiveTypeWindow
