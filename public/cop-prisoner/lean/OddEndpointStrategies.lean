import OddEndpointProjection
import OddEndpointCertificatesSpec

/-! Exact local certificate interfaces projected into the actual cyclic game.
The finite certificates remain explicit premises in this module. -/
set_option maxRecDepth 4096

namespace Delivery.OddEndpointStrategies
open OddEndpointGraph OddEndpointLocal OddEndpointWindow OddEndpointProjection
open OddEndpointCertificatesSpec CyclicSigned LocalArena FiniteGame

 def index (d : Int) (j : Fin 6) (low : -5≤d) (high : d≤5) : R :=
  ⟨6*(d+5).toNat+j.val,by have := j.isLt; omega⟩

 theorem index_vertex (d : Int) (j : Fin 6) (low : -5≤d) (high : d≤5) :
    rvertex (index d j low high)=(d,j) := by
  apply Prod.ext
  · dsimp [rvertex,index]
    have h := j.isLt
    omega
  · apply Fin.ext
    dsimp [rvertex,index]
    have h := j.isLt
    omega

 theorem catalogued {k : Nat} (r : Case) (origin : Int) :
    Catalogued r (anchor k r origin) := by
  have h := anchor_coherent k r origin
  cases eq : anchor k r origin with
  | none => trivial
  | some a =>
    rw [eq] at h
    exact anchor_covered r origin a h

section
variable {k : Nat} (hk : 15≤k) (r : Case) (origin : Int) (a : Option Int)
variable (small : 2*OddEndpointParameters.radius r+OddEndpointParameters.span r<k)
variable (short : 2*OddEndpointParameters.radius r+OddEndpointParameters.jump r<k)
variable (coherent : Coherent k r origin a)

 theorem lift_coordinates (d : Int) (s : Vertex hk r)
    (column : s.val.1=wrap (by omega : 0<k) (d+origin)) :
    lift hk origin (d,s.val.2)=s.val := by
  apply Prod.ext
  · exact column.symm
  · rfl

 theorem represented (s : Vertex hk r) (d : Int)
    (inside : inWindow (messengerRadius r) (d,s.val.2))
    (column : s.val.1=wrap (by omega : 0<k) (d+origin))
    (ordinary : s≠lowSource hk r) :
    ∃ x : R, presentR r a x ∧ eligible r a (rvertex x) ∧
      rvertex x=(d,s.val.2) ∧ embed hk r origin a small coherent x=s := by
  have radius : messengerRadius r≤5 := by
    unfold messengerRadius OddEndpointParameters.radius; split <;> omega
  have low : -5≤d := by have := inside.1; omega
  have high : d≤5 := by have := inside.2; omega
  let x := index d s.val.2 low high
  have coord : rvertex x=(d,s.val.2) := index_vertex d s.val.2 low high
  have bigger : inWindow (OddEndpointParameters.radius r) (d,s.val.2) := by
    have lower := inside.1; have upper := inside.2
    unfold messengerRadius at lower upper
    constructor <;> omega
  have lifted := lift_coordinates hk r origin d s column
  have available : presentR r a x := by
    refine ⟨?_,?_⟩
    · simpa only [coord] using inside
    · rw [coord]
      apply (present_lift hk r origin a small coherent _ bigger).mp
      rw [lifted]
      exact s.property
  have equal : embed hk r origin a small coherent x=s := by
    apply Subtype.ext
    rw [embed_raw hk r origin a small coherent x available,coord,lifted]
  refine ⟨x,available,?_,coord,equal⟩
  rw [coord]
  apply (source_lift hk r origin a small coherent _ bigger).mp
  rw [lifted]
  exact fun h => ordinary (Subtype.ext h)

 include small short coherent in
 theorem transfer (certificate : Transfer r a) (s c : Vertex hk r)
    (ordinary : s≠lowSource hk r) (safe : s≠c)
    (column : s.val.1=wrap (by omega : 0<k) (entryColumn r+origin)) :
    SafeReach (edge hk r) (fun z => z≠lowSource hk r ∧
      (z.val.1=wrap (by omega : 0<k) origin ∨
        (r.val=5 ∧ z.val.1=wrap (by omega : 0<k) (origin-1))))
      (transferBound r) s c := by
  have inside : inWindow (messengerRadius r) (entryColumn r,s.val.2) := by
    have finite : ∀ r, -(messengerRadius r : Int)≤entryColumn r ∧
        entryColumn r≤(messengerRadius r : Int) := by decide +kernel
    exact finite r
  obtain ⟨x,available,eligible,coord,equal⟩ :=
    represented hk r origin a small coherent s (entryColumn r) inside column ordinary
  have entry : transferEntry r a x := ⟨available,eligible,congrArg Prod.fst coord⟩
  have starts := certificate.starts x (projectRaw hk r origin c.val) entry
    (project_present hk r origin a small coherent c)
    (fun h => safe (equal.symm.trans ((collision_iff hk r origin a small short coherent x c available).mp h)))
  have sound : ∀ y, safeGoal r a y →
      (embed hk r origin a small coherent y≠lowSource hk r ∧
        ((embed hk r origin a small coherent y).val.1=wrap (by omega : 0<k) origin ∨
          (r.val=5 ∧ (embed hk r origin a small coherent y).val.1=
            wrap (by omega : 0<k) (origin-1)))) := by
    intro y goal
    have raw := embed_raw hk r origin a small coherent y goal.1
    refine ⟨?_,?_⟩
    · intro same
      have nonSource := (source_lift hk r origin a small coherent _
        (messenger_inside r a y goal.1)).mpr goal.2.1
      exact nonSource (raw.symm.trans (congrArg Subtype.val same))
    · rw [raw]
      change wrap (by omega : 0<k) ((rvertex y).1+origin)=_ ∨ _
      rcases goal.2.2 with col|⟨five,col⟩
      · exact Or.inl (by rw [col,Int.zero_add])
      · exact Or.inr ⟨five,by change wrap (by omega : 0<k) ((rvertex y).1+origin)=_; rw [col]; congr 1; omega⟩
  have result := safe_projection (P := fun z : Vertex hk r => z≠lowSource hk r ∧
      (z.val.1=wrap (by omega : 0<k) origin ∨
        (r.val=5 ∧ z.val.1=wrap (by omega : 0<k) (origin-1))))
    (simulation hk r origin a small short coherent) certificate.checked sound x c starts.1
  change SafeReach _ _ _ (embed hk r origin a small coherent x) c at result
  rw [equal] at result
  exact safe_mono result starts.2

 include small short coherent in
 theorem deliver (certificates : Certificates r a) (s t c : Vertex hk r)
    (ordinary : s≠lowSource hk r) (recipient : t≠lowTarget hk r) (safe : s≠c)
    (targetColumn : t.val.1=wrap (by omega : 0<k) origin)
    (d : Int) (entry : d=2*entryColumn r ∨ (r.val=5 ∧ d=3))
    (column : s.val.1=wrap (by omega : 0<k) (d+origin)) :
    Winning (edge hk r) t (deliveryBound r) s c := by
  have bounds : -3≤d ∧ d≤3 := by
    have finite : ∀ r, -1≤entryColumn r ∧ entryColumn r≤1 := by decide +kernel
    have := finite r
    rcases entry with h|⟨_,h⟩ <;> omega
  have radius : 4≤messengerRadius r := by
    unfold messengerRadius OddEndpointParameters.radius; split <;> omega
  have inside : inWindow (messengerRadius r) (d,s.val.2) := by constructor <;> omega
  obtain ⟨x,available,eligible,coord,equal⟩ :=
    represented hk r origin a small coherent s d inside column ordinary
  have entry' : deliveryEntry r a x := by
    refine ⟨available,eligible,?_⟩
    simpa only [coord] using entry
  have targetLift : lift hk origin (0,t.val.2)=t.val := by
    apply lift_coordinates hk r origin 0 t
    simpa only [Int.zero_add] using targetColumn
  have targetInside : inWindow (OddEndpointParameters.radius r) (0,t.val.2) := by
    constructor <;> omega
  have allowed : targetAllowed r a t.val.2 := by
    refine ⟨?_,?_⟩
    · apply (present_lift hk r origin a small coherent _ targetInside).mp
      rw [targetLift]; exact t.property
    · cases a with
      | none => trivial
      | some h =>
        intro bad
        apply recipient
        apply Subtype.ext
        rw [←targetLift,lift_some hk r origin h coherent _,bad]
        rfl
  let certificate := certificates.delivery t.val.2 allowed
  have starts := certificate.starts x (projectRaw hk r origin c.val) entry'
    (project_present hk r origin a small coherent c)
    (fun h => safe (equal.symm.trans ((collision_iff hk r origin a small short coherent x c available).mp h)))
  have sound : ∀ y, deliveryGoal r a t.val.2 y → embed hk r origin a small coherent y=t := by
    intro y goal
    apply Subtype.ext
    rw [embed_raw hk r origin a small coherent y goal.1,goal.2,targetLift]
  have result := delivery_projection (simulation hk r origin a small short coherent)
    certificate.checked sound x c starts.1
  change Winning _ t _ (embed hk r origin a small coherent x) c at result
  rw [equal] at result
  exact winning_mono result starts.2
end
#print axioms transfer
#print axioms deliver
end Delivery.OddEndpointStrategies
