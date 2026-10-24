import OddEndpointStrategies
import CyclicProgress
import SafeProgress

/-! The six saved local interfaces imply delivery for every eligible pair.
The final catalogue is an explicit premise; no finite witness is assumed. -/
namespace Delivery.OddEndpointComposition
open OddEndpointGraph OddEndpointLocal OddEndpointWindow OddEndpointStrategies
open OddEndpointCertificatesSpec CyclicSigned CyclicArithmetic SinglePatchWindow
open LocalArena FiniteGame

 theorem safe_imp {V : Type} {E : Graph V} {P Q : V → Prop} {n : Nat} {s c : V}
    (first : SafeReach E P n s c) (implies : ∀ z, P z → Q z) : SafeReach E Q n s c := by
  have next : ∀ z d, P z → z≠d → SafeReach E Q 0 z d :=
    fun z _ goal safe => SafeReach.done (implies z goal) safe
  simpa only [Nat.add_zero] using safe_compose first next

section
variable {k : Nat} (hk : 15≤k) (r : Case)
variable (small : 2*OddEndpointParameters.radius r+OddEndpointParameters.span r<k)
variable (short : 2*OddEndpointParameters.radius r+OddEndpointParameters.jump r<k)
variable (certificates : ∀ a, Catalogued r a → Certificates r a)

include small short certificates in
 theorem transfer_forward (direction : r.val≠2 ∧ r.val≠5) (s c : Vertex hk r)
    (ordinary : s≠lowSource hk r) (safe : s≠c) :
    SafeReach (edge hk r) (fun z => z≠lowSource hk r ∧ z.val.1=shift s.val.1 1)
      (transferBound r) s c := by
  let origin : Int := (s.val.1.val : Int)+1
  let a := anchor k r origin
  have coh := anchor_coherent k r origin
  have column : s.val.1=wrap (by omega : 0<k) (entryColumn r+origin) := by
    simp only [entryColumn,direction.1,direction.2,false_or,ite_false]
    have eq : -1+origin=(s.val.1.val : Int) := by dsimp [origin]; omega
    rw [eq,wrap_fin]
  have reach := OddEndpointStrategies.transfer hk r origin a small short coh
    (certificates a (catalogued r origin)).transfer s c ordinary safe column
  apply safe_imp reach
  intro z goal
  refine ⟨goal.1,?_⟩
  rcases goal.2 with col|⟨five,_⟩
  · rw [col]
    dsimp [origin]
    have shifted := wrap_shift (by omega : 0<k) (s.val.1.val : Int) 1
    rw [wrap_fin (by omega : 0<k) s.val.1] at shifted
    exact shifted
  · exact False.elim (direction.2 five)

include small short certificates in
 theorem transfer_backward (direction : r.val=2 ∨ r.val=5) (s c : Vertex hk r)
    (ordinary : s≠lowSource hk r) (safe : s≠c) :
    SafeReach (edge hk r) (fun z => z≠lowSource hk r ∧
      (z.val.1=wrap (by omega : 0<k) ((s.val.1.val : Int)-1) ∨
       (r.val=5 ∧ z.val.1=wrap (by omega : 0<k) ((s.val.1.val : Int)-2))))
      (transferBound r) s c := by
  let origin : Int := (s.val.1.val : Int)-1
  let a := anchor k r origin
  have coh := anchor_coherent k r origin
  have column : s.val.1=wrap (by omega : 0<k) (entryColumn r+origin) := by
    simp only [entryColumn,direction,ite_true]
    have eq : 1+origin=(s.val.1.val : Int) := by dsimp [origin]; omega
    rw [eq,wrap_fin]
  have reach := OddEndpointStrategies.transfer hk r origin a small short coh
    (certificates a (catalogued r origin)).transfer s c ordinary safe column
  apply safe_imp reach
  intro z goal
  refine ⟨goal.1,?_⟩
  rcases goal.2 with col|⟨five,col⟩
  · exact Or.inl col
  · refine Or.inr ⟨five,?_⟩
    rw [col]
    congr 1
    dsimp [origin]
    omega

 def entryTarget (t : Vertex hk r) : Fin k :=
  wrap (by omega : 0<k) ((t.val.1.val : Int)+2*entryColumn r)

 def measure (t s : Vertex hk r) : Nat :=
  if r.val=2 ∨ r.val=5 then
    if r.val=5 then (offset (entryTarget hk r t) s.val.1).val-1
    else (offset (entryTarget hk r t) s.val.1).val
  else (offset s.val.1 (entryTarget hk r t)).val

 theorem measure_lt (t s : Vertex hk r) : measure hk r t s<k := by
  unfold measure
  have := (offset (entryTarget hk r t) s.val.1).isLt
  have := (offset s.val.1 (entryTarget hk r t)).isLt
  split <;> (try split) <;> omega

include small short certificates in
 theorem progress (t s c : Vertex hk r) (ordinary : s≠lowSource hk r) (safe : s≠c)
    (positive : 0<measure hk r t s) :
    SafeReach (edge hk r) (fun z => z≠lowSource hk r ∧ measure hk r t z<measure hk r t s)
      (transferBound r) s c := by
  by_cases direction : r.val=2 ∨ r.val=5
  · have reach := transfer_backward hk r small short certificates direction s c ordinary safe
    apply safe_imp reach
    intro z goal
    refine ⟨goal.1,?_⟩
    by_cases five : r.val=5
    · simp only [measure,if_pos direction,if_pos five] at positive ⊢
      rcases goal.2 with col|⟨_,col⟩
      · have step := CyclicProgress.backward (by omega : 0<k) (entryTarget hk r t) s.val.1 1 (by omega)
        change (offset (entryTarget hk r t)
          (wrap (by omega : 0<k) ((s.val.1.val : Int)-1))).val=
            (offset (entryTarget hk r t) s.val.1).val-1 at step
        rw [col,step]
        omega
      · have step := CyclicProgress.backward (by omega : 0<k) (entryTarget hk r t) s.val.1 2 (by omega)
        change (offset (entryTarget hk r t)
          (wrap (by omega : 0<k) ((s.val.1.val : Int)-2))).val=
            (offset (entryTarget hk r t) s.val.1).val-2 at step
        rw [col,step]
        omega
    · simp only [measure,if_pos direction,if_neg five] at positive ⊢
      rcases goal.2 with col|⟨bad,_⟩
      · have step := CyclicProgress.backward (by omega : 0<k) (entryTarget hk r t) s.val.1 1 (by omega)
        change (offset (entryTarget hk r t)
          (wrap (by omega : 0<k) ((s.val.1.val : Int)-1))).val=
            (offset (entryTarget hk r t) s.val.1).val-1 at step
        rw [col,step]
        omega
      · exact False.elim (five bad)
  · have forward : r.val≠2 ∧ r.val≠5 := not_or.mp direction
    have reach := transfer_forward hk r small short certificates forward s c ordinary safe
    apply safe_imp reach
    intro z goal
    refine ⟨goal.1,?_⟩
    simp only [measure,direction,ite_false] at positive ⊢
    have step := CyclicProgress.forward s.val.1 (entryTarget hk r t) 1 (by omega)
    rw [goal.2,step]
    omega

 theorem offset_zero {x y : Fin k} (zero : (offset x y).val=0) : x=y := by
  have h := shift_offset x y
  simpa only [zero,shift_zero] using h

include small short certificates in
 theorem finish (t s c : Vertex hk r) (ordinary : s≠lowSource hk r)
    (recipient : t≠lowTarget hk r) (safe : s≠c) (zero : measure hk r t s=0) :
    Winning (edge hk r) t (deliveryBound r) s c := by
  let origin : Int := (t.val.1.val : Int)
  let a := anchor k r origin
  have coh := anchor_coherent k r origin
  have targetColumn : t.val.1=wrap (by omega : 0<k) origin := (wrap_fin _ _).symm
  have entryEqual : entryTarget hk r t=wrap (by omega : 0<k) (2*entryColumn r+origin) := by
    unfold entryTarget
    congr 1
    dsimp [origin]
    omega
  by_cases direction : r.val=2 ∨ r.val=5
  · by_cases five : r.val=5
    · rw [measure,if_pos direction,if_pos five] at zero
      have distance : (offset (entryTarget hk r t) s.val.1).val=0 ∨
          (offset (entryTarget hk r t) s.val.1).val=1 := by omega
      rcases distance with distance|distance
      · have column := (offset_zero distance).symm.trans entryEqual
        exact OddEndpointStrategies.deliver hk r origin a small short coh
          (certificates a (catalogued r origin)) s t c ordinary recipient safe targetColumn
          (2*entryColumn r) (Or.inl rfl) column
      · have column : s.val.1=wrap (by omega : 0<k) (3+origin) := by
          have h := shift_offset (entryTarget hk r t) s.val.1
          rw [distance,entryEqual,←wrap_shift] at h
          have e : entryColumn r=1 := by simp [entryColumn,five]
          rw [e] at h
          have eq : 2*1+origin+(1 : Int)=3+origin := by omega
          change wrap (by omega : 0<k) (2*1+origin+1)=s.val.1 at h
          rw [eq] at h
          exact h.symm
        exact OddEndpointStrategies.deliver hk r origin a small short coh
          (certificates a (catalogued r origin)) s t c ordinary recipient safe targetColumn
          3 (Or.inr ⟨five,rfl⟩) column
    · rw [measure,if_pos direction,if_neg five] at zero
      have column := (offset_zero zero).symm.trans entryEqual
      exact OddEndpointStrategies.deliver hk r origin a small short coh
        (certificates a (catalogued r origin)) s t c ordinary recipient safe targetColumn
        (2*entryColumn r) (Or.inl rfl) column
  · simp only [measure,direction,ite_false] at zero
    have column := (offset_zero zero).trans entryEqual
    exact OddEndpointStrategies.deliver hk r origin a small short coh
      (certificates a (catalogued r origin)) s t c ordinary recipient safe targetColumn
      (2*entryColumn r) (Or.inl rfl) column

include small short certificates in
 theorem winning (t s c : Vertex hk r) (ordinary : s≠lowSource hk r)
    (recipient : t≠lowTarget hk r) (safe : s≠c) :
    Winning (edge hk r) t (measure hk r t s*transferBound r+deliveryBound r) s c := by
  apply SafeProgress.winning (fun z => z≠lowSource hk r) (measure hk r t)
    (transferBound r) (deliveryBound r) t
  · exact fun s c hs hc hp => progress hk r small short certificates t s c hs hc hp
  · exact fun s c hs hc hz => finish hk r small short certificates t s c hs recipient hc hz
  · exact ordinary
  · exact safe

include small short certificates in
 theorem guaranteed (t s : Vertex hk r) (ordinary : s≠lowSource hk r)
    (recipient : t≠lowTarget hk r) : Guaranteed (edge hk r) s t := by
  intro c safe
  exact ⟨_,winning hk r small short certificates t s c ordinary recipient (Ne.symm safe)⟩

include small short certificates in
 theorem uniform_winning (t s c : Vertex hk r) (ordinary : s≠lowSource hk r)
    (recipient : t≠lowTarget hk r) (safe : s≠c) :
    Winning (edge hk r) t (34*(k-1)+27) s c := by
  have result := winning hk r small short certificates t s c ordinary recipient safe
  have distance := measure_lt hk r t s
  have bounds := uniform_bounds r
  have budget := Nat.mul_le_mul (show measure hk r t s≤k-1 by omega) bounds.1
  rw [Nat.mul_comm (k-1)] at budget
  exact winning_mono result (by omega)
end
#print axioms guaranteed
#print axioms uniform_winning
end Delivery.OddEndpointComposition
