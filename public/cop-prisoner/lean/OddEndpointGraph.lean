import OddEndpointStrip
import CyclicSigned
import Extremal

/-! Actual cyclic odd-endpoint graphs. Integer smoothing is projected only
after proving that no removed vertex, loop, parallel arrow, or exceptional
recipient can acquire a second cyclic lift. -/
namespace Delivery.OddEndpointGraph
open CyclicSigned
abbrev Raw (k : Nat) := Fin k × Fin 6
abbrev Case := Fin 6

def view {k : Nat} (v : Raw k) : OddEndpointStrip.Vertex := (representative v.1,v.2)
def project {k : Nat} (hk : 15≤k) (v : OddEndpointStrip.Vertex) : Raw k :=
  (wrap (by omega : 0<k) v.1,v.2)

@[simp] theorem project_view {k : Nat} (hk : 15≤k) (v : Raw k) : project hk (view v)=v := by
  apply Prod.ext
  · exact wrap_representative (by omega) _
  · rfl

theorem view_project {k : Nat} (hk : 15≤k) (v : OddEndpointStrip.Vertex)
    (low : -2≤v.1) (high : v.1≤(k : Int)-3) : view (project hk v)=v := by
  apply Prod.ext
  · exact representative_wrap (by omega) v.1 low high
  · rfl

theorem project_injective_of_gap {k : Nat} (hk : 15≤k) {v w : OddEndpointStrip.Vertex}
    (right : v.1<w.1+(k : Int)) (left : w.1<v.1+(k : Int))
    (same : project hk v=project hk w) : v=w := by
  apply Prod.ext
  · exact injective_of_gap (by omega) right left (congrArg Prod.fst same)
  · simpa only [project] using congrArg (fun x : Raw k => x.2) same

def Present {k : Nat} (hk : 15≤k) (r : Case) (v : Raw k) : Prop :=
  v∉(OddEndpointStrip.holes r).map (project hk)
instance {k : Nat} (hk : 15≤k) (r : Case) (v : Raw k) : Decidable (Present hk r v) :=
  inferInstanceAs (Decidable (_∉_))
abbrev Vertex {k : Nat} (hk : 15≤k) (r : Case) := {v : Raw k // Present hk r v}

theorem present_iff {k : Nat} (hk : 15≤k) (r : Case) (v : Raw k) :
    Present hk r v ↔ view v∉OddEndpointStrip.holes r := by
  constructor
  · intro present gone
    apply present
    exact List.mem_map.mpr ⟨view v,gone,project_view hk v⟩
  · intro present gone
    obtain ⟨w,member,same⟩ := List.mem_map.mp gone
    have bounds := OddEndpointStrip.holes_bounds r member
    have lifted := congrArg view same
    rw [view_project hk w (by omega) (by omega)] at lifted
    exact present (lifted ▸ member)

theorem present_project {k : Nat} (hk : 15≤k) (r : Case) (v : OddEndpointStrip.Vertex)
    (present : v∉OddEndpointStrip.holes r) (low : -3≤v.1) (high : v.1≤(k : Int)-2) :
    Present hk r (project hk v) := by
  intro gone
  obtain ⟨w,member,same⟩ := List.mem_map.mp gone
  have bounds := OddEndpointStrip.holes_bounds r member
  have equal := project_injective_of_gap hk (v:=v) (w:=w) (by omega) (by omega) same.symm
  exact present (equal ▸ member)

def rawMove {k : Nat} (hk : 15≤k) (r : Case) (b : Bool) (v : Raw k) : Raw k :=
  project hk (OddEndpointStrip.smooth r b (view v))

theorem rawMove_present {k : Nat} (hk : 15≤k) (r : Case) (b : Bool) (v : Raw k)
    (present : Present hk r v) : Present hk r (rawMove hk r b v) := by
  have inside := (present_iff hk r v).mp present
  have good := OddEndpointStrip.good r (view v) inside
  have bounds := representative_bounds (by omega : 3≤k) v.1
  have output := OddEndpointStrip.output_bounds hk r b (view v) inside bounds.1 bounds.2
  exact present_project hk r _ (good.1 b).1 output.1 output.2

def move {k : Nat} (hk : 15≤k) (r : Case) (b : Bool) (v : Vertex hk r) : Vertex hk r :=
  ⟨rawMove hk r b v.val,rawMove_present hk r b v.val v.property⟩

def lowSource {k : Nat} (hk : 15≤k) (r : Case) : Vertex hk r :=
  ⟨project hk (OddEndpointStrip.source r),
    present_project hk r _ (OddEndpointStrip.defect_valid r).1
      (by have := OddEndpointStrip.source_bounds r; omega)
      (by have := OddEndpointStrip.source_bounds r; omega)⟩

def lowTarget {k : Nat} (hk : 15≤k) (r : Case) : Vertex hk r :=
  ⟨project hk (OddEndpointStrip.target r),
    present_project hk r _ (OddEndpointStrip.defect_valid r).2.1
      (by have := OddEndpointStrip.target_bounds r; omega)
      (by have := OddEndpointStrip.target_bounds r; omega)⟩

theorem source_iff {k : Nat} (hk : 15≤k) (r : Case) (s : Vertex hk r) :
    s=lowSource hk r ↔ view s.val=OddEndpointStrip.source r := by
  constructor
  · intro same
    rw [same]
    have bounds := OddEndpointStrip.source_bounds r
    exact view_project hk _ (by omega) (by omega)
  · intro same
    apply Subtype.ext
    have lifted := congrArg (project hk) same
    change s.val=project hk (OddEndpointStrip.source r)
    simpa only [project_view] using lifted

def edge {k : Nat} (hk : 15≤k) (r : Case) : Graph (Vertex hk r) :=
  fun s t => ∃ b : Bool, (s≠lowSource hk r ∨ b≠OddEndpointStrip.deletedChoice r) ∧ t=move hk r b s
instance {k : Nat} (hk : 15≤k) (r : Case) : DecidableRel (edge hk r) :=
  fun _ _ => inferInstanceAs (Decidable (∃ _ : Bool, _∧_))

theorem move_ne_self {k : Nat} (hk : 15≤k) (r : Case) (b : Bool) (s : Vertex hk r) :
    move hk r b s≠s := by
  intro same
  have inside := (present_iff hk r s.val).mp s.property
  have good := (OddEndpointStrip.good r (view s.val) inside).1 b
  have projected := congrArg Subtype.val same
  change project hk (OddEndpointStrip.smooth r b (view s.val))=s.val at projected
  have projected' := projected.trans (project_view hk s.val).symm
  have equal := project_injective_of_gap hk (by omega) (by omega) projected'
  exact good.2.1 equal

theorem moves_distinct {k : Nat} (hk : 15≤k) (r : Case) (s : Vertex hk r) :
    move hk r false s≠move hk r true s := by
  intro same
  have inside := (present_iff hk r s.val).mp s.property
  have good := OddEndpointStrip.good r (view s.val) inside
  have one := good.1 false
  have two := good.1 true
  have projected := congrArg Subtype.val same
  change project hk (OddEndpointStrip.smooth r false (view s.val))=
    project hk (OddEndpointStrip.smooth r true (view s.val)) at projected
  exact good.2 (project_injective_of_gap hk (by omega) (by omega) projected)

theorem loopless {k : Nat} (hk : 15≤k) (r : Case) : Extremal.Loopless (edge hk r) := by
  rintro s ⟨b,_,same⟩
  exact move_ne_self hk r b s same.symm

theorem permitted_iff {k : Nat} (hk : 15≤k) (r : Case) (s : Vertex hk r) (b : Bool) :
    (s≠lowSource hk r ∨ b≠OddEndpointStrip.deletedChoice r) ↔
      OddEndpointStrip.permitted r (view s.val) b := by
  simp only [ne_eq,source_iff,OddEndpointStrip.permitted]

def predecessor {k : Nat} (hk : 15≤k) (r : Case) : Vertex hk r :=
  ⟨project hk (OddEndpointStrip.uniquePredecessor r),
    present_project hk r _ ((OddEndpointStrip.incoming r _).mpr rfl).1
      (by have := OddEndpointStrip.predecessor_bounds r; omega)
      (by have := OddEndpointStrip.predecessor_bounds r; omega)⟩

/-- The exceptional recipient does not acquire a second incoming arrow by
wrapping a different integer lift onto the same cyclic vertex. -/
theorem target_edge_iff {k : Nat} (hk : 15≤k) (r : Case) (s : Vertex hk r) :
    edge hk r s (lowTarget hk r) ↔
      OddEndpointStrip.edge r (view s.val) (OddEndpointStrip.target r) := by
  have inside := (present_iff hk r s.val).mp s.property
  constructor
  · rintro ⟨b,allowed,same⟩
    have bounds := representative_bounds (by omega : 3≤k) s.val.1
    have output := OddEndpointStrip.output_bounds hk r b (view s.val) inside bounds.1 bounds.2
    have targetBounds := OddEndpointStrip.target_bounds r
    have rawSame := congrArg Subtype.val same
    change project hk (OddEndpointStrip.target r)=
      project hk (OddEndpointStrip.smooth r b (view s.val)) at rawSame
    have equal := project_injective_of_gap hk (by omega) (by omega) rawSame
    exact ⟨inside,b,(permitted_iff hk r s b).mp allowed,equal⟩
  · rintro ⟨_,b,allowed,same⟩
    refine ⟨b,(permitted_iff hk r s b).mpr allowed,?_⟩
    apply Subtype.ext
    exact congrArg (project hk) same

theorem incoming {k : Nat} (hk : 15≤k) (r : Case) (s : Vertex hk r) :
    edge hk r s (lowTarget hk r) ↔ s=predecessor hk r := by
  rw [target_edge_iff,OddEndpointStrip.incoming]
  constructor
  · intro same
    apply Subtype.ext
    have lifted := congrArg (project hk) same
    change s.val=project hk (OddEndpointStrip.uniquePredecessor r)
    simpa only [project_view] using lifted
  · intro same
    rw [same]
    have bounds := OddEndpointStrip.predecessor_bounds r
    exact view_project hk _ (by omega) (by omega)

theorem defect_distinct {k : Nat} (hk : 15≤k) (r : Case) : lowSource hk r≠lowTarget hk r := by
  intro same
  have sourceBounds := OddEndpointStrip.source_bounds r
  have targetBounds := OddEndpointStrip.target_bounds r
  have rawSame := congrArg Subtype.val same
  exact (OddEndpointStrip.defect_valid r).2.2.1
    (project_injective_of_gap hk (by omega) (by omega) rawSame)

theorem defect_missing {k : Nat} (hk : 15≤k) (r : Case) :
    ¬edge hk r (lowSource hk r) (lowTarget hk r) := by
  rw [target_edge_iff]
  have source := (source_iff hk r (lowSource hk r)).mp rfl
  rw [source]
  exact (OddEndpointStrip.defect_valid r).2.2.2

theorem ordinary_row {k : Nat} (hk : 15≤k) (r : Case) (s t : Vertex hk r)
    (ordinary : s≠lowSource hk r) :
    edge hk r s t ↔ t=move hk r false s ∨ t=move hk r true s := by
  constructor
  · rintro ⟨b,_,same⟩
    cases b with
    | false => exact Or.inl same
    | true => exact Or.inr same
  · rintro (first|second)
    · exact ⟨false,Or.inl ordinary,first⟩
    · exact ⟨true,Or.inl ordinary,second⟩

theorem source_row {k : Nat} (hk : 15≤k) (r : Case) (t : Vertex hk r) :
    edge hk r (lowSource hk r) t ↔
      t=move hk r (!(OddEndpointStrip.deletedChoice r)) (lowSource hk r) := by
  constructor
  · rintro ⟨b,allowed,same⟩
    have other : b≠OddEndpointStrip.deletedChoice r := allowed.resolve_left (fun h => h rfl)
    have choice : b=!(OddEndpointStrip.deletedChoice r) := by
      cases b <;> cases h : OddEndpointStrip.deletedChoice r <;> simp_all
    simpa only [choice] using same
  · intro same
    refine ⟨!(OddEndpointStrip.deletedChoice r),Or.inr ?_,same⟩
    cases OddEndpointStrip.deletedChoice r <;> decide

#print axioms incoming
#print axioms defect_missing

#print axioms rawMove_present
#print axioms moves_distinct
#print axioms loopless
end Delivery.OddEndpointGraph
