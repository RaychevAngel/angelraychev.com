import FourCubePotentialSemantics

namespace Princess.FourCubeCompression
open Princess.CaptureRecurrence Princess.LadderCardinality Princess.FiniteSubsetProfiles

attribute [local irreducible] Princess.ProductCompression.iterateMap

def part (A : Region Room) (p : Bool) : Region Room :=
  fun v => A v ∧ color v=(if p then 1 else 0)

theorem encode_all_correct (p : Bool) (A : Region Room) : decoded (encodeColor p A)=part A p := by
  classical
  funext v
  apply propext
  unfold decoded encodeColor
  rw [selectedMask_bit]
  simp only [Nat.testBit_two_pow,decide_eq_true_eq]
  constructor
  · rintro ⟨u,hu,hA,heq⟩
    have huv : u=v := Fin.ext heq
    subst u
    exact ⟨hA,(colorRooms_mem p v).mp hu⟩
  · rintro ⟨hA,hp⟩
    exact ⟨v,(colorRooms_mem p v).mpr hp,hA,rfl⟩

theorem encode_part (p : Bool) (A : Region Room) : encodeColor p (part A p)=encodeColor p A := by
  apply decoded_injective _ _ (encoded_bounded _ _) (encoded_bounded _ _)
  rw [encode_all_correct,encode_all_correct]
  funext v; apply propext
  simp only [part,and_assoc,and_self]

theorem encode_empty (p : Bool) (A : Region Room) (empty : Empty A) : encodeColor p A=0 := by
  apply decoded_injective _ _ (encoded_bounded _ _) (by intro j hj; simp at hj)
  rw [encode_all_correct]
  funext v; apply propext
  constructor
  · intro h; exact False.elim (empty v h.1)
  · intro h; simp [decoded] at h

def fullMask (p : Bool) : Nat := if p then 11936045732788001370 else 6510698340921550245

theorem fullMask_bounded (p : Bool) : BoundedMask (fullMask p) := by
  have h : fullMask p &&& 18446744073709551615=fullMask p := by cases p <;> decide
  simpa only [h] using cap_bounded (fullMask p)

theorem fullMask_color : ∀ p : Bool, ∀ v : Room,
    (fullMask p).testBit v.val=true ↔ color v=(if p then 1 else 0) := by decide

theorem encode_full (p : Bool) : encodeColor p (fun _ => True)=fullMask p := by
  apply decoded_injective _ _ (encoded_bounded _ _) (fullMask_bounded p)
  rw [encode_all_correct]
  funext v; apply propext
  simp only [part,true_and,decoded,fullMask_color]

theorem color_bound : ∀ v : Room, color v<2 := by decide

theorem adj_flips : ∀ u v : Room, adj u v → color u≠color v := by decide

theorem move_part (p : Bool) (A : Region Room) : part (move adj A) (!p)=move adj (part A p) := by
  funext v; apply propext
  have hc := color_bound v
  constructor
  · rintro ⟨⟨u,hu,he⟩,hv⟩
    have hcu := color_bound u
    have unequal := adj_flips u v he
    refine ⟨u,⟨hu,?_⟩,he⟩
    cases p <;> simp_all <;> omega
  · rintro ⟨u,⟨hu,hp⟩,he⟩
    have hcu := color_bound u
    have unequal := adj_flips u v he
    refine ⟨⟨u,hu,he⟩,?_⟩
    cases p <;> simp_all <;> omega

theorem rawHood_encode (p : Bool) (A : Region Room) :
    rawHood (encodeColor p A)=encodeColor (!p) (move adj A) := by
  apply decoded_injective _ _ (rawHood_bounded _) (encoded_bounded _ _)
  rw [rawHood_correct,encode_all_correct,encode_all_correct,move_part]

theorem closed_part (p : Bool) (A : Region Room) (closed : Closed A) : Closed (part A p) := by
  intro u v hu hv
  exact ⟨closed u v hu hv.1,(down_color u v hu).trans hv.2⟩

theorem card_parts (A : Region Room) : card A=card (part A false)+card (part A true) := by
  have h := cardOn_split (List.finRange 64) A (fun v => color v=0)
  have other : card (fun v => A v ∧ ¬color v=0)=card (part A true) := by
    apply cardOn_congr
    intro v _
    have hc := color_bound v
    change (A v ∧ ¬color v=0) ↔ (A v ∧ color v=1)
    constructor
    · intro hv; exact ⟨hv.1,by omega⟩
    · intro hv; exact ⟨hv.1,by omega⟩
  change card A=card (part A false)+card (fun v => A v ∧ ¬color v=0) at h
  rwa [other] at h

theorem part_survivors (p : Bool) (A S : Region Room) :
    part (fun v => A v ∧ ¬S v) p = (fun v => part A p v ∧ ¬part S p v) := by
  funext v; apply propext
  simp only [part]
  constructor
  · rintro ⟨⟨ha,hs⟩,hp⟩; exact ⟨⟨ha,hp⟩,fun h => hs h.1⟩
  · rintro ⟨⟨ha,hp⟩,hs⟩; exact ⟨⟨ha,fun h => hs ⟨h,hp⟩⟩,hp⟩

theorem part_probe_bound (p : Bool) (A S : Region Room) :
    card (part A p)-card (part (fun v => A v ∧ ¬S v) p) ≤ card (part S p) := by
  have h := probes_remove_at_most (part A p) (part S p)
  rw [← part_survivors] at h
  omega

noncomputable def statePotential (A : Region Room) : Nat :=
  potential (encodeColor false A)+potential (encodeColor true A)

theorem state_empty (A : Region Room) (empty : Empty A) : statePotential A=0 := by
  simp only [statePotential,encode_empty _ A empty,potential_empty,Nat.zero_add]

theorem state_full : statePotential (fun _ => True)=80 := by
  rw [statePotential,encode_full,encode_full]
  exact (by decide)

theorem state_step (A S : Region Room) (aclosed : Closed A)
    (rclosed : Closed (fun v => A v ∧ ¬S v)) (budget : card S≤8) :
    statePotential A ≤ 2+statePotential (next adj A S) := by
  let R : Region Room := fun v => A v ∧ ¬S v
  let c0 := card (part A false)-card (part R false)
  let c1 := card (part A true)-card (part R true)
  have h0 := part_probe_bound false A S
  have h1 := part_probe_bound true A S
  have hs := card_parts S
  have sumcost : c0+c1≤8 := by dsimp [c0,c1,R]; omega
  have cone (p : Bool) :
      potential (encodeColor p A) ≤ charge (card (part A p)-card (part R p)) +
        potential (encodeColor (!p) (next adj A S)) := by
    have hp : card (part A p)-card (part R p)≤8 := by
      cases p <;> dsimp [c0,c1] at sumcost <;> omega
    have h := encoded_transition p (part A p) (part R p)
      (fun _ h => h.2) (fun _ h => h.2) (closed_part p A aclosed) (closed_part p R rclosed)
      (fun _ h => ⟨h.1.1,h.2⟩) hp
    rw [encode_part,encode_part,rawHood_encode] at h
    exact h
  have hfalse := cone false
  have htrue := cone true
  have hc := charge_budget c0 c1 sumcost
  change potential (encodeColor false A)+potential (encodeColor true A) ≤
    2+(potential (encodeColor false (next adj A S))+potential (encodeColor true (next adj A S)))
  simp only [Bool.not_false,Bool.not_true] at hfalse htrue
  change potential (encodeColor false A) ≤ charge c0+_ at hfalse
  change potential (encodeColor true A) ≤ charge c1+_ at htrue
  omega

end Princess.FourCubeCompression
#print axioms Princess.FourCubeCompression.state_step
