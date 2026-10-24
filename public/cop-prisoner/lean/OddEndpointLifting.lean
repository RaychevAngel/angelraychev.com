import OddEndpointGraph
import CyclicWindow

/-! A single supported-patch lifting argument for all six odd graphs.
The strict lift interval excludes a second periodic copy of the patch;
all remaining rows are ordinary translation-invariant permutation rows. -/
namespace Delivery.OddEndpointLifting
open OddEndpointGraph CyclicSigned CyclicArithmetic

def InSupport (r : Case) (v : OddEndpointStrip.Vertex) : Prop :=
  OddEndpointStrip.supportLow r≤v.1 ∧ v.1≤OddEndpointStrip.supportHigh r
instance (r : Case) (v : OddEndpointStrip.Vertex) : Decidable (InSupport r v) :=
  inferInstanceAs (Decidable (_≤_ ∧ _≤_))

theorem holes_support (r : Case) {v : OddEndpointStrip.Vertex}
    (member : v∈OddEndpointStrip.holes r) : InSupport r v := by
  have finite : ∀ r, (OddEndpointStrip.holes r).all (fun v => decide (InSupport r v))=true := by
    unfold InSupport
    decide +kernel
  exact of_decide_eq_true ((List.all_eq_true.mp (finite r)) v member)

theorem source_support (r : Case) : InSupport r (OddEndpointStrip.source r) := by
  have finite : ∀ r, InSupport r (OddEndpointStrip.source r) := by
    unfold InSupport
    decide +kernel
  exact finite r

def GoodLift (k : Nat) (r : Case) (v : OddEndpointStrip.Vertex) : Prop :=
  OddEndpointStrip.supportHigh r-(k : Int)<v.1 ∧
    v.1<OddEndpointStrip.supportLow r+(k : Int)

theorem project_eq_support {k : Nat} (hk : 15≤k) (r : Case)
    {v w : OddEndpointStrip.Vertex} (lift : GoodLift k r v)
    (support : InSupport r w) (same : project hk v=project hk w) : v=w := by
  unfold GoodLift at lift
  unfold InSupport at support
  exact project_injective_of_gap hk (by omega) (by omega) same

theorem present_project_iff {k : Nat} (hk : 15≤k) (r : Case)
    (v : OddEndpointStrip.Vertex) (lift : GoodLift k r v) :
    Present hk r (project hk v) ↔ v∉OddEndpointStrip.holes r := by
  constructor
  · intro present gone
    exact present (List.mem_map.mpr ⟨v,gone,rfl⟩)
  · intro present gone
    obtain ⟨w,member,same⟩ := List.mem_map.mp gone
    exact present ((project_eq_support hk r lift (holes_support r member) same.symm) ▸ member)

theorem raw_project_congr {k : Nat} (hk : 15≤k) (r : Case) (b : Bool)
    {v w : OddEndpointStrip.Vertex} (same : project hk v=project hk w) :
    project hk (OddEndpointStrip.raw r b v)=project hk (OddEndpointStrip.raw r b w) := by
  rcases v with ⟨x,i⟩
  rcases w with ⟨y,j⟩
  have types : i=j := congrArg Prod.snd same
  subst j
  apply Prod.ext
  · have cols := (wrap_eq_iff (by omega : 0<k) x y).mp (congrArg Prod.fst same)
    apply (wrap_eq_iff (by omega : 0<k) _ _).mpr
    change (x+(OddEndpointStrip.stepSpec r b i).1)%(k : Int)=
      (y+(OddEndpointStrip.stepSpec r b i).1)%(k : Int)
    calc
      (x+(OddEndpointStrip.stepSpec r b i).1)%(k : Int) =
        (x%(k : Int)+(OddEndpointStrip.stepSpec r b i).1%(k : Int))%(k : Int) := Int.add_emod _ _ _
      _ = (y%(k : Int)+(OddEndpointStrip.stepSpec r b i).1%(k : Int))%(k : Int) := by rw [cols]
      _ = (y+(OddEndpointStrip.stepSpec r b i).1)%(k : Int) := (Int.add_emod _ _ _).symm
  · rfl

/-- Exact smoothing commutes with cyclic projection throughout the unique
patch lift. This proves all exceptional and ordinary smoothing cases together. -/
theorem smooth_project {k : Nat} (hk : 15≤k) (r : Case) (b : Bool)
    (v : OddEndpointStrip.Vertex) (lift : GoodLift k r v) :
    rawMove hk r b (project hk v)=project hk (OddEndpointStrip.smooth r b v) := by
  by_cases supported : InSupport r v
  · have bounds := OddEndpointStrip.support_bounds r
    have range : -2≤v.1 ∧ v.1≤(k : Int)-3 := by
      unfold InSupport at supported
      omega
    simp only [rawMove,view_project hk v range.1 range.2]
  · have outside : v.1<OddEndpointStrip.supportLow r ∨
        OddEndpointStrip.supportHigh r<v.1 := by
      unfold InSupport at supported
      omega
    have normalizedOutside : ¬InSupport r (view (project hk v)) := by
      intro hit
      have equal := project_eq_support hk r lift hit (project_view hk (project hk v)).symm
      exact supported (equal ▸ hit)
    have outside' : (view (project hk v)).1<OddEndpointStrip.supportLow r ∨
        OddEndpointStrip.supportHigh r<(view (project hk v)).1 := by
      unfold InSupport at normalizedOutside
      omega
    rw [rawMove,(OddEndpointStrip.outside_support r _ outside').2.2 b,
      (OddEndpointStrip.outside_support r _ outside).2.2 b]
    exact raw_project_congr hk r b (project_view hk (project hk v))

theorem source_project_iff {k : Nat} (hk : 15≤k) (r : Case)
    (v : OddEndpointStrip.Vertex) (lift : GoodLift k r v) :
    project hk v=project hk (OddEndpointStrip.source r) ↔ v=OddEndpointStrip.source r :=
  ⟨project_eq_support hk r lift (source_support r),congrArg (project hk)⟩

theorem project_short {k J : Nat} (hk : 15≤k)
    (v w : OddEndpointStrip.Vertex)
    (low : -(J : Int)≤w.1-v.1) (high : w.1-v.1≤(J : Int)) :
    CyclicWindow.ShortMove J (project hk v).1 (project hk w).1 := by
  by_cases forward : v.1≤w.1
  · let d := (w.1-v.1).toNat
    have distance : (d : Int)=w.1-v.1 := by dsimp [d]; omega
    refine ⟨d,by omega,Or.inl ?_⟩
    change wrap (by omega : 0<k) w.1=shift (wrap (by omega : 0<k) v.1) d
    rw [←wrap_shift]
    congr 1
    omega
  · let d := (v.1-w.1).toNat
    have distance : (d : Int)=v.1-w.1 := by dsimp [d]; omega
    refine ⟨d,by omega,Or.inr ?_⟩
    change wrap (by omega : 0<k) v.1=shift (wrap (by omega : 0<k) w.1) d
    rw [←wrap_shift]
    congr 1
    omega

/-- Every actual arrow, including every smoothed arrow, obeys the precise
residue-dependent jump bound used for outside cop entries. -/
theorem edge_short {k : Nat} (hk : 15≤k) (r : Case) {s t : Vertex hk r}
    (arrow : edge hk r s t) :
    CyclicWindow.ShortMove (OddEndpointParameters.jump r) s.val.1 t.val.1 := by
  obtain ⟨b,allowed,rfl⟩ := arrow
  have inside := (present_iff hk r s.val).mp s.property
  have bounds := ((OddEndpointStrip.good r (view s.val) inside).1 b).2.2.2.2
    ((permitted_iff hk r s b).mp allowed)
  have result := project_short hk (view s.val) (OddEndpointStrip.smooth r b (view s.val))
    bounds.1 bounds.2
  simpa only [project_view,move,rawMove] using result

theorem legal_short {k : Nat} (hk : 15≤k) (r : Case) {s t : Vertex hk r}
    (legal : Legal (edge hk r) s t) :
    CyclicWindow.ShortMove (OddEndpointParameters.jump r) s.val.1 t.val.1 := by
  rcases legal with same|arrow
  · subst t
    exact ⟨0,by omega,Or.inl (shift_zero _).symm⟩
  · exact edge_short hk r arrow

theorem translated_good {k : Nat} (r : Case) (radius : Nat) (h x : Int)
    (small : 2*radius+OddEndpointParameters.span r<k)
    (anchorLow : -(radius : Int)-OddEndpointStrip.supportHigh r≤h)
    (anchorHigh : h≤(radius : Int)-OddEndpointStrip.supportLow r)
    (windowLow : -(radius : Int)≤x) (windowHigh : x≤(radius : Int)) (j : Fin 6) :
    GoodLift k r (x-h,j) := by
  have width : (OddEndpointParameters.span r : Int)=
      OddEndpointStrip.supportHigh r-OddEndpointStrip.supportLow r := by
    have finite : ∀ r, (OddEndpointParameters.span r : Int)=
        OddEndpointStrip.supportHigh r-OddEndpointStrip.supportLow r := by decide +kernel
    exact finite r
  unfold GoodLift
  dsimp
  omega

#print axioms smooth_project
#print axioms legal_short
#print axioms translated_good
end Delivery.OddEndpointLifting
