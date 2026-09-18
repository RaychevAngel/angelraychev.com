import RobustLayers

/-! Antichain guide attachment. The finite hub-interface strategy and the
concrete neighborhood tests are explicit premises. This file proves the
four safe-entry cases and their composition with that strategy, including
actual delivery against history-dependent pursuers. It does not instantiate
the paper's hub lists, count arrows, or prove the classification. -/
namespace Delivery.GuideAttachment
universe u
variable {V : Type u}

/-- The structural entry premises supplied by a concrete guide construction.
`twoGuides` is the pointwise form of having at least two assigned guides;
`incomparable` is the directed difference supplied by distinct antichain codes.
All safety statements refer to the full optional envelope, including waits. -/
structure EntryData (B E : Graph V) where
  hub : V → Prop
  guide : V → Prop
  bulk : V → Prop
  outlet : V → Prop
  assigned : V → V → Prop
  cover : ∀ c, hub c ∨ guide c ∨ bulk c
  outsideBulk : ∀ x, ¬ (hub x ∨ guide x) → bulk x
  assignedGuide : ∀ x z, bulk x → assigned x z → guide z
  assignedMove : ∀ x z, bulk x → assigned x z → B x z
  twoGuides : ∀ x, bulk x → ∀ c, ∃ z, assigned x z ∧ z ≠ c
  incomparable : ∀ x c, bulk x → bulk c → x ≠ c →
    ∃ z, assigned x z ∧ ¬ assigned c z
  outletEntry : ∀ x c, bulk x → hub c → outlet c →
    ∃ z, hub z ∧ B x z ∧ ¬ Legal E c z
  otherHubSafe : ∀ c z, hub c → ¬ outlet c → guide z → ¬ Legal E c z
  otherGuideSafe : ∀ c z, guide c → guide z → z ≠ c → ¬ Legal E c z
  bulkGuide : ∀ c z, bulk c → guide z → Legal E c z → assigned c z

/-- One compulsory move safely enters the interface from any bulk source. -/
theorem safe_entry {B E : Graph V} (data : EntryData B E)
    {x c : V} (outside : ¬ (data.hub x ∨ data.guide x)) (distinct : c ≠ x) :
    ∃ z, (data.hub z ∨ data.guide z) ∧ B x z ∧ ¬ Legal E c z := by
  have hx := data.outsideBulk x outside
  rcases data.cover c with hc | hc | hc
  · by_cases ho : data.outlet c
    · obtain ⟨z, hz, move, safe⟩ := data.outletEntry x c hx hc ho
      exact ⟨z, Or.inl hz, move, safe⟩
    · obtain ⟨z, assigned, _⟩ := data.twoGuides x hx c
      have hz := data.assignedGuide x z hx assigned
      exact ⟨z, Or.inr hz, data.assignedMove x z hx assigned,
        data.otherHubSafe c z hc ho hz⟩
  · obtain ⟨z, assigned, different⟩ := data.twoGuides x hx c
    have hz := data.assignedGuide x z hx assigned
    exact ⟨z, Or.inr hz, data.assignedMove x z hx assigned,
      data.otherGuideSafe c z hc hz different⟩
  · obtain ⟨z, assigned, absent⟩ := data.incomparable x c hx hc (Ne.symm distinct)
    have hz := data.assignedGuide x z hx assigned
    refine ⟨z, Or.inr hz, data.assignedMove x z hx assigned, ?_⟩
    intro reachable
    exact absent (data.bulkGuide c z hc hz reachable)

/-- Every optional subset preserves the interface bound plus one entry move. -/
theorem attachment_universal {B E G : Graph V} {t : V} {k : Nat}
    (data : EntryData B E)
    (lower : RobustTwoMove.Subgraph B G) (upper : RobustTwoMove.Subgraph G E)
    (inside : ∀ z, data.hub z ∨ data.guide z → Universal G t k z)
    (s : V) : Universal G t (k + 1) s := by
  apply RobustLayers.safe_routing_layer lower upper inside
  intro x outside c distinct
  exact safe_entry data outside distinct

/-- The bound concerns actual terminal receipt, not only safe movement. -/
theorem attachment_actual_delivery [DecidableEq V]
    {B E G : Graph V} {t s c : V} {k : Nat}
    (data : EntryData B E)
    (lower : RobustTwoMove.Subgraph B G) (upper : RobustTwoMove.Subgraph G E)
    (inside : ∀ z, data.hub z ∨ data.guide z → Universal G t k z)
    (initial : c ≠ s) (cop : PursuerPolicy V) (legal : LegalPursuer G cop)
    (history : History V) : play G t cop (k + 1) history s c = .delivered := by
  exact winning_play_delivers
    (attachment_universal data lower upper inside s c initial) cop legal history

#print axioms safe_entry
#print axioms attachment_universal
#print axioms attachment_actual_delivery
end Delivery.GuideAttachment
