import LowBandLocal
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandPattern058
open LocalArena LocalArenaRows LowBandLocal
def pattern : List Nat := [2,14]
def messengerMasks (r : Nat) : Nat := (if r < 33 then (if r < 16 then (if r < 8 then (if r < 4 then (if r < 2 then (if r < 1 then 35 else 1030) else (if r < 3 then 140 else 24)) else (if r < 6 then (if r < 5 then 304 else 96) else (if r < 7 then 2240 else 65920))) else (if r < 12 then (if r < 10 then (if r < 9 then 8960 else 1537) else (if r < 11 then 19456 else 6152)) else (if r < 14 then (if r < 13 then 143360 else 4218880) else (if r < 15 then 573440 else 98368)))) else (if r < 24 then (if r < 20 then (if r < 18 then (if r < 17 then 1245184 else 393728) else (if r < 19 then 9175040 else 270008320)) else (if r < 22 then (if r < 21 then 36700160 else 6295552) else (if r < 23 then 79691776 else 25198592))) else (if r < 28 then (if r < 26 then (if r < 25 then 587202560 else 17280532480) else (if r < 27 then 2348810240 else 402915328)) else (if r < 30 then (if r < 29 then 5100273664 else 1612709888) else (if r < 31 then 37580963840 else (if r < 32 then 1105954078720 else 150323855360)))))) else (if r < 49 then (if r < 41 then (if r < 37 then (if r < 35 then (if r < 34 then 25786580992 else 326417514496) else (if r < 36 then 103213432832 else 2405181685760)) else (if r < 39 then (if r < 38 then 70781061038080 else 9620726743040) else (if r < 40 then 1650341183488 else 20890720927744))) else (if r < 45 then (if r < 43 then (if r < 42 then 6605659701248 else 153931627888640) else (if r < 44 then 4529987906437120 else 615726511554560)) else (if r < 47 then (if r < 46 then 105621835743232 else 1337006139375616) else (if r < 48 then 422762220879872 else 9851624184872960)))) else (if r < 57 then (if r < 53 then (if r < 51 then (if r < 50 then 289919226011975680 else 39406496739491840) else (if r < 52 then 6759797487566848 else 85568392920039424)) else (if r < 55 then (if r < 54 then 27056782136311808 else 630503947831869440) else (if r < 56 then 18554830464766443520 else 2522015791327477760))) else (if r < 61 then (if r < 59 then (if r < 58 then 432627039204278272 else 5476377146882523136) else (if r < 60 then 1731634056723955712 else 40352252661239644160)) else (if r < 63 then (if r < 62 then 6917529027641081856 else 13835058055282163712) else (if r < 64 then 27688130509073809408 else (if r < 65 then 55340232221128654848 else 37037603335494959104)))))))
def replyRows (r : Nat) : List C := (if r < 51 then (if r < 25 then (if r < 12 then (if r < 6 then (if r < 3 then (if r < 1 then [0,1,5] else (if r < 2 then [1,2,10,102] else [2,3,7,18])) else (if r < 4 then [3,4,18,102] else (if r < 5 then [4,5,8,19,102] else [5,6,102]))) else (if r < 9 then (if r < 7 then [6,7,11] else (if r < 8 then [7,8,20,102] else [8,9,13,24])) else (if r < 10 then [0,9,10,24,102] else (if r < 11 then [10,11,14,25,102] else [3,11,12,102])))) else (if r < 18 then (if r < 15 then (if r < 13 then [12,13,17] else (if r < 14 then [13,14,22] else [14,15,19,30])) else (if r < 16 then [6,15,17,30,102] else (if r < 17 then [] else [0,9,17,18]))) else (if r < 21 then (if r < 19 then [18,19,23] else (if r < 20 then [19,20,28] else [20,21,25,36])) else (if r < 23 then (if r < 22 then [0,12,21,22] else [0,22,23,26,37]) else (if r < 24 then [6,15,23,24] else [24,25,29]))))) else (if r < 38 then (if r < 31 then (if r < 28 then (if r < 26 then [11,25,26,34] else (if r < 27 then [26,27,31,42] else [6,18,27,28,42])) else (if r < 29 then [28,29,32,43] else (if r < 30 then [12,21,29,30] else [30,31,35]))) else (if r < 34 then (if r < 32 then [17,31,32,40] else (if r < 33 then [32,33,37,48] else [12,17,24,33,34,48])) else (if r < 36 then (if r < 35 then [12,34,35,38,49] else [18,27,35,36]) else (if r < 37 then [36,37,41] else [23,37,38,46])))) else (if r < 44 then (if r < 41 then (if r < 39 then [38,39,43,54] else (if r < 40 then [18,23,30,39,40,54] else [18,40,41,44,55])) else (if r < 42 then [24,33,41,42] else (if r < 43 then [42,43,47] else [29,43,44,52]))) else (if r < 47 then (if r < 45 then [44,45,49,60] else (if r < 46 then [24,29,36,45,46,60] else [24,46,47,50,61])) else (if r < 49 then (if r < 48 then [30,39,47,48] else [48,49,53]) else (if r < 50 then [35,49,50,58] else [50,51,55,66])))))) else (if r < 77 then (if r < 64 then (if r < 57 then (if r < 54 then (if r < 52 then [30,35,42,51,52,66] else (if r < 53 then [30,52,53,56,67] else [36,45,53,54])) else (if r < 55 then [54,55,59] else (if r < 56 then [41,55,56,64] else [56,57,61,72]))) else (if r < 60 then (if r < 58 then [36,41,48,57,58,72] else (if r < 59 then [36,58,59,62,73] else [42,51,59,60])) else (if r < 62 then (if r < 61 then [60,61,65] else [47,61,62,70]) else (if r < 63 then [62,63,67,78] else [42,47,54,63,64,78])))) else (if r < 70 then (if r < 67 then (if r < 65 then [42,64,65,68,79] else (if r < 66 then [48,57,65,66] else [66,67,71])) else (if r < 68 then [53,67,68,76] else (if r < 69 then [68,69,73,84] else [48,53,60,69,70,84]))) else (if r < 73 then (if r < 71 then [48,70,71,74,85] else (if r < 72 then [54,63,71,72] else [72,73,77])) else (if r < 75 then (if r < 74 then [59,73,74,82] else [74,75,79,90]) else (if r < 76 then [54,59,66,75,76,90] else [54,76,77,80,91]))))) else (if r < 90 then (if r < 83 then (if r < 80 then (if r < 78 then [60,69,77,78] else (if r < 79 then [78,79,83] else [65,79,80,92])) else (if r < 81 then [80,81,85,96] else (if r < 82 then [60,65,72,81,82,96] else [60,82,83,86,97]))) else (if r < 86 then (if r < 84 then [66,75,83,84] else (if r < 85 then [84,85,89] else [85,86,94])) else (if r < 88 then (if r < 87 then [86,87,91,102] else [66,78,87,89,102]) else (if r < 89 then [] else [72,81,89,90])))) else (if r < 96 then (if r < 93 then (if r < 91 then [90,91,95] else (if r < 92 then [91,92,100] else [92,93,97,102])) else (if r < 94 then [72,84,93,94] else (if r < 95 then [72,94,95,98,102] else [78,87,95,96]))) else (if r < 99 then (if r < 97 then [96,97,101] else (if r < 98 then [83,97,98,102] else [98,99,102])) else (if r < 101 then (if r < 100 then [78,90,99,100,102] else [100,101,102]) else (if r < 102 then [84,93,101,102] else [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,17,84,85,86,87,89,90,91,92,93,94,95,96,97,98,99,100,101,102])))))))
def frozenReplies (c : C) : List C := replyRows c.val
def frozenArena : Arena R C where
  messenger r z := (messengerMasks r.val).testBit z.val = true
  pursuer c d := d ∈ frozenReplies c
  collision r c := ¬presentR pattern r ∨ rcop r=c
instance (r z : R) : Decidable (frozenArena.messenger r z) :=
  inferInstanceAs (Decidable (_ = true))
instance (c d : C) : Decidable (frozenArena.pursuer c d) :=
  inferInstanceAs (Decidable (_ ∈ _))
instance (r : R) (c : C) : Decidable (frozenArena.collision r c) :=
  inferInstanceAs (Decidable (_ ∨ _))
theorem messenger_agrees : ∀ r z, frozenArena.messenger r z ↔ (arena pattern).messenger r z := by
  decide +kernel
def sameReplies (c : C) : Bool :=
  (frozenReplies c).all (fun d => decide (d ∈ replies pattern c)) &&
  (replies pattern c).all (fun d => decide (d ∈ frozenReplies c))
theorem reply_rows : ∀ c, sameReplies c=true := by
  decide +kernel
theorem pursuer_agrees : ∀ c d, frozenArena.pursuer c d ↔ (arena pattern).pursuer c d := by
  intro c d
  have both := Bool.and_eq_true_iff.mp (reply_rows c)
  exact ⟨fun h => of_decide_eq_true ((List.all_eq_true.mp both.1) d h),
    fun h => of_decide_eq_true ((List.all_eq_true.mp both.2) d h)⟩
theorem arena_eq : frozenArena = arena pattern := by
  have hm : frozenArena.messenger = (arena pattern).messenger :=
    funext fun r => funext fun z => propext (messenger_agrees r z)
  have hp : frozenArena.pursuer = (arena pattern).pursuer :=
    funext fun c => funext fun d => propext (pursuer_agrees c d)
  change Arena.mk frozenArena.messenger frozenArena.pursuer frozenArena.collision =
    Arena.mk (arena pattern).messenger (arena pattern).pursuer (arena pattern).collision
  rw [hm, hp]
  rfl
#print axioms arena_eq
end Delivery.LowBandPattern058
