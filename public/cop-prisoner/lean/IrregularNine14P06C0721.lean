import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0650
import IrregularNine14P06C0651
import IrregularNine14P06C0652
import IrregularNine14P06C0653
import IrregularNine14P06C0654

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m43260_12 : Upper (D 6) (R 6) [34,384,66,5,12] 13 :=
  permutation_upper _ _ _ [34,384,66,5,9] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39048

theorem m43260_65 : Upper (D 6) (R 6) [34,384,66,5,65] 13 :=
  permutation_upper _ _ _ [34,384,66,5,36] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39050

theorem m43260_68 : Upper (D 6) (R 6) [34,384,66,5,68] 13 :=
  permutation_upper _ _ _ [34,384,66,5,33] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39049

theorem m43260_72 : Upper (D 6) (R 6) [34,384,66,5,72] 13 :=
  permutation_upper _ _ _ [34,384,66,5,40] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39051

def r43260 : Route 9 := (fun mask => (mask,id))

def c43260 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43260 : Upper (D 6) (R 6) [34,384,66,5] 13 := by
  apply FastRouting.sound _ _ [34,384,66,5] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r43260 c43260
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39047
  · exact u39048
  · exact m43260_12
  · exact u39049
  · exact u39050
  · exact u39051
  · exact m43260_65
  · exact m43260_68
  · exact m43260_72
  · exact u39052

theorem m43261_5 : Upper (D 6) (R 6) [34,384,66,17,5] 13 :=
  permutation_upper _ _ _ [34,384,66,5,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39048

def r43261 : Route 9 := (fun mask => (mask,id))

def c43261 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43261 : Upper (D 6) (R 6) [34,384,66,17] 13 := by
  apply FastRouting.sound _ _ [34,384,66,17] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r43261 c43261
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43261_5
  · exact u39053
  · exact u39054
  · exact u39055
  · exact u39056
  · exact u39057
  · exact u39058
  · exact u39059
  · exact u39060
  · exact u39061

def b43262 : PairBound 9 := { available := 93, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 386 70 41 93 125 93 221 349), lower := (rows 35 386 70 41 16 32 64 128 256), losses := [] }

theorem u43262 : Upper (D 6) (R 6) [34,384,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43262 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43263_5 : Upper (D 6) (R 6) [34,384,66,36,5] 13 :=
  permutation_upper _ _ _ [34,384,66,5,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39050

theorem m43263_9 : Upper (D 6) (R 6) [34,384,66,36,9] 13 :=
  permutation_upper _ _ _ [34,384,66,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39056

theorem m43263_12 : Upper (D 6) (R 6) [34,384,66,36,12] 13 :=
  permutation_upper _ _ _ [34,384,66,17,65] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39058

theorem m43263_68 : Upper (D 6) (R 6) [34,384,66,36,68] 13 :=
  permutation_upper _ _ _ [34,384,66,33,65] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39062

def r43263 : Route 9 := (fun mask => (mask,id))

def c43263 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43263 : Upper (D 6) (R 6) [34,384,66,36] 13 := by
  apply FastRouting.sound _ _ [34,384,66,36] 13 (by decide) (choices 2) [5,9,12,65,68,72] r43263 c43263
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43263_5
  · exact m43263_9
  · exact m43263_12
  · exact u39064
  · exact m43263_68
  · exact u39065

theorem m43264_5 : Upper (D 6) (R 6) [34,384,66,48,5] 13 :=
  permutation_upper _ _ _ [34,384,66,5,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39051

theorem m43264_9 : Upper (D 6) (R 6) [34,384,66,48,9] 13 :=
  permutation_upper _ _ _ [34,384,66,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39057

theorem m43264_12 : Upper (D 6) (R 6) [34,384,66,48,12] 13 :=
  permutation_upper _ _ _ [34,384,66,17,72] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39060

theorem m43264_65 : Upper (D 6) (R 6) [34,384,66,48,65] 13 :=
  permutation_upper _ _ _ [34,384,66,36,72] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39065

theorem m43264_68 : Upper (D 6) (R 6) [34,384,66,48,68] 13 :=
  permutation_upper _ _ _ [34,384,66,33,72] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39063

def r43264 : Route 9 := (fun mask => (mask,id))

def c43264 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43264 : Upper (D 6) (R 6) [34,384,66,48] 13 := by
  apply FastRouting.sound _ _ [34,384,66,48] 13 (by decide) (choices 2) [5,9,12,65,68,72] r43264 c43264
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43264_5
  · exact m43264_9
  · exact m43264_12
  · exact m43264_65
  · exact m43264_68
  · exact u39066

theorem m43265_5 : Upper (D 6) (R 6) [34,384,66,96,5] 13 :=
  permutation_upper _ _ _ [34,384,66,5,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39052

theorem m43265_9 : Upper (D 6) (R 6) [34,384,66,96,9] 13 :=
  permutation_upper _ _ _ [34,384,66,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39061

theorem m43265_12 : Upper (D 6) (R 6) [34,384,66,96,12] 13 :=
  permutation_upper _ _ _ [34,384,66,17,96] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39061

def r43265 : Route 9 := (fun mask => (mask,id))

def c43265 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43265 : Upper (D 6) (R 6) [34,384,66,96] 13 := by
  apply FastRouting.sound _ _ [34,384,66,96] 13 (by decide) (choices 2) [5,9,12] r43265 c43265
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m43265_5
  · exact m43265_9
  · exact m43265_12

def b43266 : PairBound 9 := { available := 117, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 386 76 11 117 117 117 245 373), lower := (rows 35 386 76 11 16 32 64 128 256), losses := [] }

theorem u43266 : Upper (D 6) (R 6) [34,384,72,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43266 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43267 : Route 9 := (fun mask => (mask,id))

def c43267 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43267 : Upper (D 6) (R 6) [34,384,72,5] 13 := by
  apply FastRouting.sound _ _ [34,384,72,5] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43267 c43267
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39067
  · exact u39068
  · exact u39069
  · exact u39070
  · exact u39071
  · exact u39072
  · exact u39073
  · exact u39074
  · exact u39075
  · exact u39076

def r43268 : Route 9 := (fun mask => (mask,id))

def c43268 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43268 : Upper (D 6) (R 6) [34,384,72,6] 13 := by
  apply FastRouting.sound _ _ [34,384,72,6] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43268 c43268
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39077
  · exact u39078
  · exact u39079
  · exact u39080
  · exact u39081
  · exact u39082

def r43269 : Route 9 := (fun mask => (mask,id))

def c43269 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43269 : Upper (D 6) (R 6) [34,384,72,17] 13 := by
  apply FastRouting.sound _ _ [34,384,72,17] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43269 c43269
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39083
  · exact u39084
  · exact u39085
  · exact u39086
  · exact u39087
  · exact u39088
  · exact u39089
  · exact u39090
  · exact u39091
  · exact u39092

def r43270 : Route 9 := (fun mask => (mask,id))

def c43270 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43270 : Upper (D 6) (R 6) [34,384,72,18] 13 := by
  apply FastRouting.sound _ _ [34,384,72,18] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43270 c43270
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39093
  · exact u39094
  · exact u39095
  · exact u39096
  · exact u39097
  · exact u39098

def r43271 : Route 9 := (fun mask => (mask,id))

def c43271 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43271 : Upper (D 6) (R 6) [34,384,72,20] 13 := by
  apply FastRouting.sound _ _ [34,384,72,20] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43271 c43271
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39099
  · exact u39100
  · exact u39101
  · exact u39102
  · exact u39103
  · exact u39104
  · exact u39105
  · exact u39106
  · exact u39107
  · exact u39108

def b43272 : PairBound 9 := { available := 87, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 386 76 41 87 119 87 215 343), lower := (rows 35 386 76 41 16 32 64 128 256), losses := [] }

theorem u43272 : Upper (D 6) (R 6) [34,384,72,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43272 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43273 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 386 76 42 85 117 85 213 341), lower := (rows 35 386 76 42 16 32 64 128 256), losses := [] }

theorem u43273 : Upper (D 6) (R 6) [34,384,72,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43273 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43274 : Route 9 := (fun mask => (mask,id))

def c43274 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43274 : Upper (D 6) (R 6) [34,384,72,36] 13 := by
  apply FastRouting.sound _ _ [34,384,72,36] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43274 c43274
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39109
  · exact u39110
  · exact u39111
  · exact u39112
  · exact u39113
  · exact u39114

def r43275 : Route 9 := (fun mask => (mask,id))

def c43275 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43275 : Upper (D 6) (R 6) [34,384,72,48] 13 := by
  apply FastRouting.sound _ _ [34,384,72,48] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43275 c43275
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39115
  · exact u39116
  · exact u39117
  · exact u39118
  · exact u39119
  · exact u39120

def b43276 : PairBound 9 := { available := 55, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 386 76 73 55 55 119 183 311), lower := (rows 35 386 76 73 16 32 64 128 256), losses := [] }

theorem u43276 : Upper (D 6) (R 6) [34,384,72,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43276 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43277 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 386 76 74 53 53 117 181 309), lower := (rows 35 386 76 74 16 32 64 128 256), losses := [] }

theorem u43277 : Upper (D 6) (R 6) [34,384,72,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43278 : PairBound 9 := { available := 55, camps := [{ cop := 6, region := 12, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 386 76 76 55 55 119 183 311), lower := (rows 35 386 76 76 16 32 64 128 256), losses := [] }

theorem u43278 : Upper (D 6) (R 6) [34,384,72,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43278 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43279 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 386 76 88 55 39 103 167 295), lower := (rows 35 386 76 88 16 32 64 128 256), losses := [] }

theorem u43279 : Upper (D 6) (R 6) [34,384,72,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43280 : PairBound 9 := { available := 23, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 386 76 104 23 55 87 151 279), lower := (rows 35 386 76 104 16 32 64 128 256), losses := [] }

theorem u43280 : Upper (D 6) (R 6) [34,384,72,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43280 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43281 : PairBound 9 := { available := 93, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 386 100 11 93 125 93 221 349), lower := (rows 35 386 100 11 16 32 64 128 256), losses := [] }

theorem u43281 : Upper (D 6) (R 6) [34,384,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43281 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43282_3 : Upper (D 6) (R 6) [34,384,96,5,3] 13 :=
  permutation_upper _ _ _ [34,384,96,3,5] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39121

def r43282 : Route 9 := (fun mask => (mask,id))

def c43282 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43282 : Upper (D 6) (R 6) [34,384,96,5] 13 := by
  apply FastRouting.sound _ _ [34,384,96,5] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r43282 c43282
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43282_3
  · exact u39126
  · exact u39127
  · exact u39128
  · exact u39129
  · exact u39130
  · exact u39131
  · exact u39132
  · exact u39133
  · exact u39134

theorem m43283_5 : Upper (D 6) (R 6) [34,384,96,6,5] 13 :=
  permutation_upper _ _ _ [34,384,96,5,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39127

def r43283 : Route 9 := (fun mask => (mask,id))

def c43283 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43283 : Upper (D 6) (R 6) [34,384,96,6] 13 := by
  apply FastRouting.sound _ _ [34,384,96,6] 13 (by decide) (choices 2) [5,9,12,65,68,72] r43283 c43283
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43283_5
  · exact u39135
  · exact u39136
  · exact u39137
  · exact u39138
  · exact u39139

theorem m43284_3 : Upper (D 6) (R 6) [34,384,96,17,3] 13 :=
  permutation_upper _ _ _ [34,384,96,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39122

theorem m43284_5 : Upper (D 6) (R 6) [34,384,96,17,5] 13 :=
  permutation_upper _ _ _ [34,384,96,5,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39128

theorem m43284_6 : Upper (D 6) (R 6) [34,384,96,17,6] 13 :=
  permutation_upper _ _ _ [34,384,96,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39135

def r43284 : Route 9 := (fun mask => (mask,id))

def c43284 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43284 : Upper (D 6) (R 6) [34,384,96,17] 13 := by
  apply FastRouting.sound _ _ [34,384,96,17] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r43284 c43284
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43284_3
  · exact m43284_5
  · exact m43284_6
  · exact u39140
  · exact u39141
  · exact u39142
  · exact u39143
  · exact u39144
  · exact u39145
  · exact u39146

theorem m43285_5 : Upper (D 6) (R 6) [34,384,96,18,5] 13 :=
  permutation_upper _ _ _ [34,384,96,5,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39129

theorem m43285_9 : Upper (D 6) (R 6) [34,384,96,18,9] 13 :=
  permutation_upper _ _ _ [34,384,96,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39141

def r43285 : Route 9 := (fun mask => (mask,id))

def c43285 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43285 : Upper (D 6) (R 6) [34,384,96,18] 13 := by
  apply FastRouting.sound _ _ [34,384,96,18] 13 (by decide) (choices 2) [5,9,12,65,68,72] r43285 c43285
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43285_5
  · exact m43285_9
  · exact u39147
  · exact u39148
  · exact u39149
  · exact u39150

theorem m43286_3 : Upper (D 6) (R 6) [34,384,96,20,3] 13 :=
  permutation_upper _ _ _ [34,384,96,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39123

theorem m43286_5 : Upper (D 6) (R 6) [34,384,96,20,5] 13 :=
  permutation_upper _ _ _ [34,384,96,5,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39130

theorem m43286_6 : Upper (D 6) (R 6) [34,384,96,20,6] 13 :=
  permutation_upper _ _ _ [34,384,96,6,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39136

theorem m43286_9 : Upper (D 6) (R 6) [34,384,96,20,9] 13 :=
  permutation_upper _ _ _ [34,384,96,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39142

theorem m43286_10 : Upper (D 6) (R 6) [34,384,96,20,10] 13 :=
  permutation_upper _ _ _ [34,384,96,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39147

def r43286 : Route 9 := (fun mask => (mask,id))

def c43286 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43286 : Upper (D 6) (R 6) [34,384,96,20] 13 := by
  apply FastRouting.sound _ _ [34,384,96,20] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r43286 c43286
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43286_3
  · exact m43286_5
  · exact m43286_6
  · exact m43286_9
  · exact m43286_10
  · exact u39151
  · exact u39152
  · exact u39153
  · exact u39154
  · exact u39155

theorem m43287_3 : Upper (D 6) (R 6) [34,384,96,65,3] 13 :=
  permutation_upper _ _ _ [34,384,96,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39124

theorem m43287_5 : Upper (D 6) (R 6) [34,384,96,65,5] 13 :=
  permutation_upper _ _ _ [34,384,96,5,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39131

theorem m43287_6 : Upper (D 6) (R 6) [34,384,96,65,6] 13 :=
  permutation_upper _ _ _ [34,384,96,6,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39137

theorem m43287_9 : Upper (D 6) (R 6) [34,384,96,65,9] 13 :=
  permutation_upper _ _ _ [34,384,96,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39143

theorem m43287_10 : Upper (D 6) (R 6) [34,384,96,65,10] 13 :=
  permutation_upper _ _ _ [34,384,96,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39148

theorem m43287_12 : Upper (D 6) (R 6) [34,384,96,65,12] 13 :=
  permutation_upper _ _ _ [34,384,96,20,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39152

def r43287 : Route 9 := (fun mask => (mask,id))

def c43287 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43287 : Upper (D 6) (R 6) [34,384,96,65] 13 := by
  apply FastRouting.sound _ _ [34,384,96,65] 13 (by decide) (choices 2) [3,5,6,9,10,12] r43287 c43287
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43287_3
  · exact m43287_5
  · exact m43287_6
  · exact m43287_9
  · exact m43287_10
  · exact m43287_12

theorem m43288_5 : Upper (D 6) (R 6) [34,384,96,66,5] 13 :=
  permutation_upper _ _ _ [34,384,96,5,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39132

theorem m43288_9 : Upper (D 6) (R 6) [34,384,96,66,9] 13 :=
  permutation_upper _ _ _ [34,384,96,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39144

theorem m43288_12 : Upper (D 6) (R 6) [34,384,96,66,12] 13 :=
  permutation_upper _ _ _ [34,384,96,20,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39153

def r43288 : Route 9 := (fun mask => (mask,id))

def c43288 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43288 : Upper (D 6) (R 6) [34,384,96,66] 13 := by
  apply FastRouting.sound _ _ [34,384,96,66] 13 (by decide) (choices 2) [5,9,12] r43288 c43288
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m43288_5
  · exact m43288_9
  · exact m43288_12

def b43289 : PairBound 9 := { available := 31, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 386 100 76 31 63 95 159 287), lower := (rows 35 386 100 76 16 32 64 128 256), losses := [] }

theorem u43289 : Upper (D 6) (R 6) [34,384,96,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43289 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43290_3 : Upper (D 6) (R 6) [34,384,96,80,3] 13 :=
  permutation_upper _ _ _ [34,384,96,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39125

theorem m43290_5 : Upper (D 6) (R 6) [34,384,96,80,5] 13 :=
  permutation_upper _ _ _ [34,384,96,5,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39134

theorem m43290_6 : Upper (D 6) (R 6) [34,384,96,80,6] 13 :=
  permutation_upper _ _ _ [34,384,96,6,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39139

theorem m43290_9 : Upper (D 6) (R 6) [34,384,96,80,9] 13 :=
  permutation_upper _ _ _ [34,384,96,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39146

theorem m43290_10 : Upper (D 6) (R 6) [34,384,96,80,10] 13 :=
  permutation_upper _ _ _ [34,384,96,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39150

theorem m43290_12 : Upper (D 6) (R 6) [34,384,96,80,12] 13 :=
  permutation_upper _ _ _ [34,384,96,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39155

def r43290 : Route 9 := (fun mask => (mask,id))

def c43290 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43290 : Upper (D 6) (R 6) [34,384,96,80] 13 := by
  apply FastRouting.sound _ _ [34,384,96,80] 13 (by decide) (choices 2) [3,5,6,9,10,12] r43290 c43290
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43290_3
  · exact m43290_5
  · exact m43290_6
  · exact m43290_9
  · exact m43290_10
  · exact m43290_12

def b43291 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 50 133 11 342 358 326 454 326), lower := (rows 41 50 133 11 16 32 64 128 256), losses := [] }

theorem u43291 : Upper (D 6) (R 6) [40,48,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43291 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43292 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 41 50 133 13 342 358 326 454 326), lower := (rows 41 50 133 13 16 32 64 128 256), losses := [] }

theorem u43292 : Upper (D 6) (R 6) [40,48,129,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43293 : Route 9 := (fun mask => (mask,id))

def c43293 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43293 : Upper (D 6) (R 6) [40,48,129,6] 13 := by
  apply FastRouting.sound _ _ [40,48,129,6] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43293 c43293
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39156
  · exact u39157
  · exact u39158
  · exact u39159
  · exact u39160
  · exact u39161
  · exact u39162
  · exact u39163
  · exact u39164
  · exact u39165

def r43294 : Route 9 := (fun mask => (mask,id))

def c43294 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43294 : Upper (D 6) (R 6) [40,48,129,65] 13 := by
  apply FastRouting.sound _ _ [40,48,129,65] 13 (by decide) (choices 2) [6,66,68,258,260,320] r43294 c43294
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39166
  · exact u39167
  · exact u39168
  · exact u39169
  · exact u39170
  · exact u39171

def r43295 : Route 9 := (fun mask => (mask,id))

def c43295 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43295 : Upper (D 6) (R 6) [40,48,129,66] 13 := by
  apply FastRouting.sound _ _ [40,48,129,66] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43295 c43295
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39172
  · exact u39173
  · exact u39174
  · exact u39175
  · exact u39176
  · exact u39177
  · exact u39178
  · exact u39179
  · exact u39180
  · exact u39181

def r43296 : Route 9 := (fun mask => (mask,id))

def c43296 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43296 : Upper (D 6) (R 6) [40,48,129,68] 13 := by
  apply FastRouting.sound _ _ [40,48,129,68] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43296 c43296
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39182
  · exact u39183
  · exact u39184
  · exact u39185
  · exact u39186
  · exact u39187
  · exact u39188
  · exact u39189
  · exact u39190
  · exact u39191

def r43297 : Route 9 := (fun mask => (mask,id))

def c43297 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43297 : Upper (D 6) (R 6) [40,48,129,257] 13 := by
  apply FastRouting.sound _ _ [40,48,129,257] 13 (by decide) (choices 2) [6,66,68] r43297 c43297
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u39192
  · exact u39193
  · exact u39194

def r43298 : Route 9 := (fun mask => (mask,id))

def c43298 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43298 : Upper (D 6) (R 6) [40,48,129,258] 13 := by
  apply FastRouting.sound _ _ [40,48,129,258] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43298 c43298
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39195
  · exact u39196
  · exact u39197
  · exact u39198
  · exact u39199
  · exact u39200

def r43299 : Route 9 := (fun mask => (mask,id))

def c43299 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43299 : Upper (D 6) (R 6) [40,48,129,260] 13 := by
  apply FastRouting.sound _ _ [40,48,129,260] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43299 c43299
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39201
  · exact u39202
  · exact u39203
  · exact u39204
  · exact u39205
  · exact u39206

def r43300 : Route 9 := (fun mask => (mask,id))

def c43300 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43300 : Upper (D 6) (R 6) [40,48,129,320] 13 := by
  apply FastRouting.sound _ _ [40,48,129,320] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43300 c43300
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39207
  · exact u39208
  · exact u39209
  · exact u39210
  · exact u39211
  · exact u39212

def b43301 : PairBound 9 := { available := 327, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 50 196 11 343 359 327 455 327), lower := (rows 41 50 196 11 16 32 64 128 256), losses := [] }

theorem u43301 : Upper (D 6) (R 6) [40,48,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43301 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43302_3 : Upper (D 6) (R 6) [40,48,192,5,3] 13 :=
  permutation_upper _ _ _ [40,48,192,3,6] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39214

def r43302 : Route 9 := (fun mask => (mask,id))

def c43302 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43302 : Upper (D 6) (R 6) [40,48,192,5] 13 := by
  apply FastRouting.sound _ _ [40,48,192,5] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43302 c43302
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43302_3
  · exact u39221
  · exact u39222
  · exact u39223
  · exact u39224
  · exact u39225
  · exact u39226
  · exact u39227
  · exact u39228
  · exact u39229

theorem m43303_3 : Upper (D 6) (R 6) [40,48,192,6,3] 13 :=
  permutation_upper _ _ _ [40,48,192,3,5] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39213

theorem m43303_6 : Upper (D 6) (R 6) [40,48,192,6,6] 13 :=
  permutation_upper _ _ _ [40,48,192,5,5] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39221

def r43303 : Route 9 := (fun mask => (mask,id))

def c43303 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43303 : Upper (D 6) (R 6) [40,48,192,6] 13 := by
  apply FastRouting.sound _ _ [40,48,192,6] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43303 c43303
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43303_3
  · exact u39230
  · exact m43303_6
  · exact u39231
  · exact u39232
  · exact u39233
  · exact u39234
  · exact u39235
  · exact u39236
  · exact u39237

theorem m43304_3 : Upper (D 6) (R 6) [40,48,192,65,3] 13 :=
  permutation_upper _ _ _ [40,48,192,3,66] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39216

theorem m43304_5 : Upper (D 6) (R 6) [40,48,192,65,5] 13 :=
  permutation_upper _ _ _ [40,48,192,6,66] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39232

theorem m43304_6 : Upper (D 6) (R 6) [40,48,192,65,6] 13 :=
  permutation_upper _ _ _ [40,48,192,5,66] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39224

def r43304 : Route 9 := (fun mask => (mask,id))

def c43304 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43304 : Upper (D 6) (R 6) [40,48,192,65] 13 := by
  apply FastRouting.sound _ _ [40,48,192,65] 13 (by decide) (choices 2) [3,5,6,257,258,260] r43304 c43304
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43304_3
  · exact m43304_5
  · exact m43304_6
  · exact u39238
  · exact u39239
  · exact u39240

theorem m43305_3 : Upper (D 6) (R 6) [40,48,192,66,3] 13 :=
  permutation_upper _ _ _ [40,48,192,3,65] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39215

theorem m43305_5 : Upper (D 6) (R 6) [40,48,192,66,5] 13 :=
  permutation_upper _ _ _ [40,48,192,6,65] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39231

theorem m43305_6 : Upper (D 6) (R 6) [40,48,192,66,6] 13 :=
  permutation_upper _ _ _ [40,48,192,5,65] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39223

def r43305 : Route 9 := (fun mask => (mask,id))

def c43305 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43305 : Upper (D 6) (R 6) [40,48,192,66] 13 := by
  apply FastRouting.sound _ _ [40,48,192,66] 13 (by decide) (choices 2) [3,5,6,257,258,260] r43305 c43305
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43305_3
  · exact m43305_5
  · exact m43305_6
  · exact u39241
  · exact u39242
  · exact u39243

def b43306 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 50 196 76 279 295 327 391 263), lower := (rows 41 50 196 76 16 32 64 128 256), losses := [] }

theorem u43306 : Upper (D 6) (R 6) [40,48,192,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43306 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43307_3 : Upper (D 6) (R 6) [40,48,192,257,3] 13 :=
  permutation_upper _ _ _ [40,48,192,3,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39218

theorem m43307_5 : Upper (D 6) (R 6) [40,48,192,257,5] 13 :=
  permutation_upper _ _ _ [40,48,192,6,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39235

theorem m43307_6 : Upper (D 6) (R 6) [40,48,192,257,6] 13 :=
  permutation_upper _ _ _ [40,48,192,5,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39227

theorem m43307_65 : Upper (D 6) (R 6) [40,48,192,257,65] 13 :=
  permutation_upper _ _ _ [40,48,192,66,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39242

theorem m43307_66 : Upper (D 6) (R 6) [40,48,192,257,66] 13 :=
  permutation_upper _ _ _ [40,48,192,65,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39239

theorem m43307_68 : Upper (D 6) (R 6) [40,48,192,257,68] 13 :=
  permutation_upper _ _ _ [40,48,192,68,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39245

def r43307 : Route 9 := (fun mask => (mask,id))

def c43307 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43307 : Upper (D 6) (R 6) [40,48,192,257] 13 := by
  apply FastRouting.sound _ _ [40,48,192,257] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43307 c43307
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43307_3
  · exact m43307_5
  · exact m43307_6
  · exact m43307_65
  · exact m43307_66
  · exact m43307_68

theorem m43308_3 : Upper (D 6) (R 6) [40,48,192,258,3] 13 :=
  permutation_upper _ _ _ [40,48,192,3,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39217

theorem m43308_5 : Upper (D 6) (R 6) [40,48,192,258,5] 13 :=
  permutation_upper _ _ _ [40,48,192,6,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39234

theorem m43308_6 : Upper (D 6) (R 6) [40,48,192,258,6] 13 :=
  permutation_upper _ _ _ [40,48,192,5,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39226

theorem m43308_65 : Upper (D 6) (R 6) [40,48,192,258,65] 13 :=
  permutation_upper _ _ _ [40,48,192,66,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39241

theorem m43308_66 : Upper (D 6) (R 6) [40,48,192,258,66] 13 :=
  permutation_upper _ _ _ [40,48,192,65,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39238

theorem m43308_68 : Upper (D 6) (R 6) [40,48,192,258,68] 13 :=
  permutation_upper _ _ _ [40,48,192,68,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39244

def r43308 : Route 9 := (fun mask => (mask,id))

def c43308 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43308 : Upper (D 6) (R 6) [40,48,192,258] 13 := by
  apply FastRouting.sound _ _ [40,48,192,258] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43308 c43308
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43308_3
  · exact m43308_5
  · exact m43308_6
  · exact m43308_65
  · exact m43308_66
  · exact m43308_68

theorem m43309_3 : Upper (D 6) (R 6) [40,48,192,260,3] 13 :=
  permutation_upper _ _ _ [40,48,192,3,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39219

theorem m43309_5 : Upper (D 6) (R 6) [40,48,192,260,5] 13 :=
  permutation_upper _ _ _ [40,48,192,6,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39236

theorem m43309_6 : Upper (D 6) (R 6) [40,48,192,260,6] 13 :=
  permutation_upper _ _ _ [40,48,192,5,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39228

theorem m43309_65 : Upper (D 6) (R 6) [40,48,192,260,65] 13 :=
  permutation_upper _ _ _ [40,48,192,66,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39243

theorem m43309_66 : Upper (D 6) (R 6) [40,48,192,260,66] 13 :=
  permutation_upper _ _ _ [40,48,192,65,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39240

theorem m43309_68 : Upper (D 6) (R 6) [40,48,192,260,68] 13 :=
  permutation_upper _ _ _ [40,48,192,68,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39246

def r43309 : Route 9 := (fun mask => (mask,id))

def c43309 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43309 : Upper (D 6) (R 6) [40,48,192,260] 13 := by
  apply FastRouting.sound _ _ [40,48,192,260] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43309 c43309
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43309_3
  · exact m43309_5
  · exact m43309_6
  · exact m43309_65
  · exact m43309_66
  · exact m43309_68

theorem m43310_3 : Upper (D 6) (R 6) [40,48,192,320,3] 13 :=
  permutation_upper _ _ _ [40,48,192,3,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39220

theorem m43310_5 : Upper (D 6) (R 6) [40,48,192,320,5] 13 :=
  permutation_upper _ _ _ [40,48,192,6,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39237

theorem m43310_6 : Upper (D 6) (R 6) [40,48,192,320,6] 13 :=
  permutation_upper _ _ _ [40,48,192,5,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39229

def r43310 : Route 9 := (fun mask => (mask,id))

def c43310 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43310 : Upper (D 6) (R 6) [40,48,192,320] 13 := by
  apply FastRouting.sound _ _ [40,48,192,320] 13 (by decide) (choices 2) [3,5,6] r43310 c43310
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m43310_3
  · exact m43310_5
  · exact m43310_6

def b43311 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 50 388 11 87 103 71 199 327), lower := (rows 41 50 388 11 16 32 64 128 256), losses := [] }

theorem u43311 : Upper (D 6) (R 6) [40,48,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43311 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43312_3 : Upper (D 6) (R 6) [40,48,384,5,3] 13 :=
  permutation_upper _ _ _ [40,48,384,3,6] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39248

def r43312 : Route 9 := (fun mask => (mask,id))

def c43312 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43312 : Upper (D 6) (R 6) [40,48,384,5] 13 := by
  apply FastRouting.sound _ _ [40,48,384,5] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43312 c43312
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43312_3
  · exact u39252
  · exact u39253
  · exact u39254
  · exact u39255
  · exact u39256

theorem m43313_3 : Upper (D 6) (R 6) [40,48,384,6,3] 13 :=
  permutation_upper _ _ _ [40,48,384,3,5] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39247

theorem m43313_6 : Upper (D 6) (R 6) [40,48,384,6,6] 13 :=
  permutation_upper _ _ _ [40,48,384,5,5] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39252

def r43313 : Route 9 := (fun mask => (mask,id))

def c43313 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43313 : Upper (D 6) (R 6) [40,48,384,6] 13 := by
  apply FastRouting.sound _ _ [40,48,384,6] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43313 c43313
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43313_3
  · exact u39257
  · exact m43313_6
  · exact u39258
  · exact u39259
  · exact u39260

theorem m43314_3 : Upper (D 6) (R 6) [40,48,384,65,3] 13 :=
  permutation_upper _ _ _ [40,48,384,3,66] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39250

theorem m43314_5 : Upper (D 6) (R 6) [40,48,384,65,5] 13 :=
  permutation_upper _ _ _ [40,48,384,6,66] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39259

theorem m43314_6 : Upper (D 6) (R 6) [40,48,384,65,6] 13 :=
  permutation_upper _ _ _ [40,48,384,5,66] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39255

def r43314 : Route 9 := (fun mask => (mask,id))

def c43314 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43314 : Upper (D 6) (R 6) [40,48,384,65] 13 := by
  apply FastRouting.sound _ _ [40,48,384,65] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43314 c43314
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43314_3
  · exact m43314_5
  · exact m43314_6
  · exact u39261
  · exact u39262
  · exact u39263

theorem m43315_3 : Upper (D 6) (R 6) [40,48,384,66,3] 13 :=
  permutation_upper _ _ _ [40,48,384,3,65] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39249

theorem m43315_5 : Upper (D 6) (R 6) [40,48,384,66,5] 13 :=
  permutation_upper _ _ _ [40,48,384,6,65] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39258

theorem m43315_6 : Upper (D 6) (R 6) [40,48,384,66,6] 13 :=
  permutation_upper _ _ _ [40,48,384,5,65] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39254

theorem m43315_66 : Upper (D 6) (R 6) [40,48,384,66,66] 13 :=
  permutation_upper _ _ _ [40,48,384,65,65] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39261

def r43315 : Route 9 := (fun mask => (mask,id))

def c43315 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43315 : Upper (D 6) (R 6) [40,48,384,66] 13 := by
  apply FastRouting.sound _ _ [40,48,384,66] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43315 c43315
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43315_3
  · exact m43315_5
  · exact m43315_6
  · exact u39264
  · exact m43315_66
  · exact u39265

theorem m43316_3 : Upper (D 6) (R 6) [40,48,384,68,3] 13 :=
  permutation_upper _ _ _ [40,48,384,3,68] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39251

theorem m43316_5 : Upper (D 6) (R 6) [40,48,384,68,5] 13 :=
  permutation_upper _ _ _ [40,48,384,6,68] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39260

theorem m43316_6 : Upper (D 6) (R 6) [40,48,384,68,6] 13 :=
  permutation_upper _ _ _ [40,48,384,5,68] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39256

theorem m43316_65 : Upper (D 6) (R 6) [40,48,384,68,65] 13 :=
  permutation_upper _ _ _ [40,48,384,66,68] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39265

theorem m43316_66 : Upper (D 6) (R 6) [40,48,384,68,66] 13 :=
  permutation_upper _ _ _ [40,48,384,65,68] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39263

def r43316 : Route 9 := (fun mask => (mask,id))

def c43316 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43316 : Upper (D 6) (R 6) [40,48,384,68] 13 := by
  apply FastRouting.sound _ _ [40,48,384,68] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43316 c43316
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43316_3
  · exact m43316_5
  · exact m43316_6
  · exact m43316_65
  · exact m43316_66
  · exact u39266

def r43317 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43317 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 3 | 36 => 5 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u43317 : Upper (D 6) (R 6) [40,80,96,3] 13 := by
  apply FastRouting.sound _ _ [40,80,96,3] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r43317 c43317
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39267
  · exact u39268
  · exact u39269
  · exact u39270
  · exact u39271
  · exact u39272
  · exact u39273

def b43318 : PairBound 9 := { available := 391, camps := [{ cop := 2, region := 9, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 82 100 13 407 423 455 391 391), lower := (rows 41 82 100 13 16 32 64 128 256), losses := [] }

theorem u43318 : Upper (D 6) (R 6) [40,80,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43319_3 : Upper (D 6) (R 6) [40,80,96,6,3] 13 :=
  permutation_upper _ _ _ [40,80,96,3,5] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39268

theorem m43319_6 : Upper (D 6) (R 6) [40,80,96,6,6] 13 :=
  permutation_upper _ _ _ [40,80,96,5,5] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39274

def r43319 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43319 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 3 | 36 => 5 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u43319 : Upper (D 6) (R 6) [40,80,96,6] 13 := by
  apply FastRouting.sound _ _ [40,80,96,6] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r43319 c43319
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43319_3
  · exact u39279
  · exact m43319_6
  · exact u39280
  · exact u39281
  · exact u39282
  · exact u39283

#print axioms u43319
end Delivery.IrregularNine14.P06
