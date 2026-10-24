import SixTypeLocal
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypePattern64
open LocalArena LocalArenaRows SixTypeLocal
def pattern : List Nat := [4,7]
def messengerMasks (r : Nat) : Nat := (if r < 27 then (if r < 13 then (if r < 6 then (if r < 3 then (if r < 1 then 35 else (if r < 2 then 1030 else 140)) else (if r < 4 then 24 else (if r < 5 then 304 else 96))) else (if r < 9 then (if r < 7 then 2240 else (if r < 8 then 1048960 else 8960)) else (if r < 11 then (if r < 10 then 1537 else 19456) else (if r < 12 then 6152 else 143360)))) else (if r < 20 then (if r < 16 then (if r < 14 then 4218880 else (if r < 15 then 573440 else 163904)) else (if r < 18 then (if r < 17 then 0 else 393728) else (if r < 19 then 9175040 else 270008320))) else (if r < 23 then (if r < 21 then 36700160 else (if r < 22 then 6295552 else 79691776)) else (if r < 25 then (if r < 24 then 25198592 else 587202560) else (if r < 26 then 274978570240 else 2348810240))))) else (if r < 40 then (if r < 33 then (if r < 30 then (if r < 28 then 402915328 else (if r < 29 then 5100273664 else 1612709888)) else (if r < 31 then 37580963840 else (if r < 32 then 1105954078720 else 150323855360))) else (if r < 36 then (if r < 34 then 42966450176 else (if r < 35 then 0 else 103213432832)) else (if r < 38 then (if r < 37 then 2405181685760 else 70781061038080) else (if r < 39 then 9620726743040 else 1650341183488)))) else (if r < 47 then (if r < 43 then (if r < 41 then 20890720927744 else (if r < 42 then 6605659701248 else 153931627888640)) else (if r < 45 then (if r < 44 then 4529987906437120 else 615726511554560) else (if r < 46 then 105621835743232 else 1337006139375616))) else (if r < 50 then (if r < 48 then 422762220879872 else (if r < 49 then 9851624184872960 else 1688849860263936)) else (if r < 52 then (if r < 51 then 3377699720527872 else 6759797487566848) else (if r < 53 then 13510798882111488 else 9042383626829824))))))
def replyRows (r : Nat) : List C := (if r < 39 then (if r < 19 then (if r < 9 then (if r < 4 then (if r < 2 then (if r < 1 then [0,1,5] else [1,2,10]) else (if r < 3 then [2,3,7] else [3,4,78])) else (if r < 6 then (if r < 5 then [4,5,8] else [5,6,78]) else (if r < 7 then [6,7,11] else (if r < 8 then [7,8,16] else [8,9,13])))) else (if r < 14 then (if r < 11 then (if r < 10 then [0,9,10] else [10,11,14]) else (if r < 12 then [3,11,12] else (if r < 13 then [12,13,17] else [13,14,22]))) else (if r < 16 then (if r < 15 then [14,15,19] else [6,15,16]) else (if r < 17 then [16,17,20] else (if r < 18 then [9,17,18] else [18,19,23]))))) else (if r < 29 then (if r < 24 then (if r < 21 then (if r < 20 then [19,20,32] else [20,21,25]) else (if r < 22 then [12,21,22] else (if r < 23 then [22,23,26] else [15,23,24]))) else (if r < 26 then (if r < 25 then [24,25,29] else [25,26,34]) else (if r < 27 then [26,27,31] else (if r < 28 then [18,27,29] else [])))) else (if r < 34 then (if r < 31 then (if r < 30 then [21,29,30] else [30,31,35]) else (if r < 32 then [31,32,40] else (if r < 33 then [32,33,37] else [24,33,34]))) else (if r < 36 then (if r < 35 then [34,35,38] else [27,35,36]) else (if r < 37 then [36,37,41] else (if r < 38 then [37,38,50] else [38,39,43])))))) else (if r < 59 then (if r < 49 then (if r < 44 then (if r < 41 then (if r < 40 then [30,39,40] else [40,41,44]) else (if r < 42 then [33,41,42] else (if r < 43 then [42,43,47] else [43,44,52]))) else (if r < 46 then (if r < 45 then [44,45,49] else [36,45,47]) else (if r < 47 then [] else (if r < 48 then [39,47,48] else [48,49,53])))) else (if r < 54 then (if r < 51 then (if r < 50 then [49,50,58] else [50,51,55]) else (if r < 52 then [42,51,52] else (if r < 53 then [52,53,56] else [45,53,54]))) else (if r < 56 then (if r < 55 then [54,55,59] else [55,56,64]) else (if r < 57 then [56,57,61] else (if r < 58 then [48,57,58] else [58,59,62]))))) else (if r < 69 then (if r < 64 then (if r < 61 then (if r < 60 then [51,59,60] else [60,61,65]) else (if r < 62 then [61,62,70] else (if r < 63 then [62,63,67] else [54,63,64]))) else (if r < 66 then (if r < 65 then [64,65,68] else [57,65,66]) else (if r < 67 then [66,67,71] else (if r < 68 then [67,68,76] else [68,69,73])))) else (if r < 74 then (if r < 71 then (if r < 70 then [60,69,70] else [70,71,74]) else (if r < 72 then [63,71,72] else (if r < 73 then [72,73,77] else [73,74,78]))) else (if r < 76 then (if r < 75 then [74,75,78] else [66,75,76]) else (if r < 77 then [76,77,78] else (if r < 78 then [69,77,78] else [0,1,2,3,4,5,6,7,8,9,10,11,66,67,68,69,70,71,72,73,74,75,76,77,78])))))))
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
theorem pursuer_agrees : ∀ c d, frozenArena.pursuer c d ↔ (arena pattern).pursuer c d := by
  decide +kernel
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
end Delivery.SixTypePattern64
