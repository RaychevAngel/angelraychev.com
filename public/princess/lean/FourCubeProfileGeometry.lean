import FourCubeTimeCounterData

namespace Princess.FourCubeCompression
open Princess.CaptureRecurrence Princess.LadderCardinality Princess.FiniteSubsetProfiles
open Princess.FiniteIdealCertificates

attribute [local irreducible] Princess.ProductCompression.iterateMap

theorem profile_lower (p : Bool) (A : Region Room)
    (support : ∀ v, A v → color v=(if p then 1 else 0)) (closed : Closed A) :
    FourCubeTimeCounter.profile (card A)≤card (move adj A) := by
  have checked : check down FourCubeTimeCounter.profileCheck ((colorRooms p).map Fin.val) 0=true := by
    cases p
    · exact FourCubeTimeCounter.profile_even_checked
    · exact FourCubeTimeCounter.profile_odd_checked
  have h := checker_sound p A FourCubeTimeCounter.profileCheck support closed checked
  have bound : FourCubeTimeCounter.profile (sizeTable (encodeColor p A))≤
      countBits 64 (hoodTable (encodeColor p A)) := by
    simpa only [FourCubeTimeCounter.profileCheck,decide_eq_true_eq] using h
  rw [(tables_correct p A support closed).1,(tables_correct p A support closed).2,
    ← decoded_card,rawHood_correct,encodeColor_correct p A support] at bound
  exact bound

theorem full_part_card (p : Bool) : card (part (fun _ => True) p)=32 := by
  have eq : part (fun _ => True) p=decoded (fullMask p) := by
    rw [← encode_all_correct,encode_full]
  rw [eq,decoded_card]
  cases p <;> decide

theorem part_card_bound (p : Bool) (A : Region Room) : card (part A p)≤32 := by
  have h := card_mono (part A p) (part (fun _ => True) p) (fun _ hv => ⟨trivial,hv.2⟩)
  rwa [full_part_card] at h

theorem part_card_empty (p : Bool) (A : Region Room) (empty : Empty A) : card (part A p)=0 := by
  classical
  have eq : part A p=(fun _ => False) := by
    funext v; apply propext
    exact ⟨fun h => empty v h.1,False.elim⟩
  rw [eq]
  simp [card,cardOn]

end Princess.FourCubeCompression
