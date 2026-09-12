import FourCubePotentialSemantics

/-! Direct 40-round physical replay, independent of the lower certificate. -/
namespace Princess.FourCubeCompression
open Princess.CaptureRecurrence Princess.LadderCardinality

def scheduleMasks : List Nat := [5188292457229484032, 2630172551204063232, 1317343024254025728, 2508873287680, 1317338075377968256, 1146000966156288, 1315051091196912768, 10153200212508672, 1297036692720985216, 82210794183327744, 17486587008, 82210759286718536, 154925540352, 82210484408812104, 1254437167104, 82190693199778376, 5067804017426432, 8609075784, 5067786531504420, 281552305061906, 9223451203914975232, 5188151719606887552, 70369356550728, 5188186902943498240, 2630102182921245256, 40132481122308, 2630102491622019648, 39582725308452, 2630104690645275136, 35184678797604, 2630122282831577088, 20266198629351716, 2594093485814710272, 164381386701013284, 2305863109679775744, 1317302908185739556, 20066106343442, 1317304145136451584, 82190701808320530, 5067790827520001]

def stepMask (belief shots : Nat) : Nat := rawHood (belief &&& (shots ^^^ 18446744073709551615))
def runMasks : Nat → List Nat → Nat
  | belief, [] => belief
  | belief, shots::rest => runMasks (stepMask belief shots) rest

theorem cap_bit : ∀ v : Room, (18446744073709551615 : Nat).testBit v.val=true := by decide

theorem stepMask_correct (B S : Nat) : decoded (stepMask B S)=next adj (decoded B) (decoded S) := by
  rw [stepMask,rawHood_correct]
  apply congrArg (move adj)
  funext v; apply propext
  simp only [decoded,Nat.testBit_and,Nat.testBit_xor,cap_bit]
  cases hb : B.testBit v.val <;> cases hs : S.testBit v.val <;> simp

theorem schedule_length : scheduleMasks.length=40 := by decide

theorem schedule_budget : ∀ S∈scheduleMasks, Princess.FiniteSubsetProfiles.countBits 64 S≤8 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem schedule_clears : runMasks 18446744073709551615 scheduleMasks=0 := by decide +kernel

theorem runMasks_winning (shots : List Nat) (B : Nat)
    (budget : ∀ S∈shots, Princess.FiniteSubsetProfiles.countBits 64 S≤8)
    (clears : runMasks B shots=0) :
    winning adj (fun S => card S≤8) shots.length (decoded B) := by
  induction shots generalizing B with
  | nil =>
      change B=0 at clears
      subst B
      intro v hv; simp [decoded] at hv
  | cons S shots ih =>
      have tail := ih (stepMask B S) (fun Q hQ => budget Q (List.mem_cons_of_mem S hQ)) clears
      rw [stepMask_correct] at tail
      refine ⟨decoded S,?_,tail⟩
      change card (decoded S)≤8
      rw [decoded_card]
      exact budget S List.mem_cons_self

theorem actual_upper_40 : ∃ shots : Nat → Region Room,
    (∀ t, t<40 → card (shots t)≤8) ∧ GuaranteesAt adj (fun _ => True) shots 39 := by
  have win := runMasks_winning scheduleMasks 18446744073709551615 schedule_budget schedule_clears
  rw [schedule_length] at win
  have full : decoded 18446744073709551615=(fun _ => True) := by
    funext v; exact propext ⟨fun _ => trivial,fun _ => cap_bit v⟩
  rw [full] at win
  exact (winning_iff_guarantees adj (fun S => card S≤8) no_dead_ends 39 (fun _ => True)).mp win

end Princess.FourCubeCompression
#print axioms Princess.FourCubeCompression.actual_upper_40
