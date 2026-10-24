import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0363
import IrregularNine14P06C0364
import IrregularNine14P06C0365

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r37020 : Route 9 := (fun mask => (mask,id))

def c37020 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37020 : Upper (D 6) (R 6) [34,129,40,272,66] 13 := by
  apply FastRouting.sound _ _ [34,129,40,272,66] 13 (by decide) (choices 1) [1,4,64] r37020 c37020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21799
  · exact u21800
  · exact u21801

def r37021 : Route 9 := (fun mask => (mask,id))

def c37021 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37021 : Upper (D 6) (R 6) [34,129,40,272,68] 13 := by
  apply FastRouting.sound _ _ [34,129,40,272,68] 13 (by decide) (choices 1) [1,2,4,64] r37021 c37021
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21802
  · exact u21803
  · exact u21804
  · exact u21805

def b37022 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 44 328 19 116 84 212 340), lower := (rows 35 131 44 328 19 32 64 128 256), losses := [] }

theorem u37022 : Upper (D 6) (R 6) [34,129,40,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37022 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37023 : Route 9 := (fun mask => (mask,id))

def c37023 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37023 : Upper (D 6) (R 6) [34,129,40,320,5] 13 := by
  apply FastRouting.sound _ _ [34,129,40,320,5] 13 (by decide) (choices 1) [2,4,16,64] r37023 c37023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21806
  · exact u21807
  · exact u21808
  · exact u21809

def r37024 : Route 9 := (fun mask => (mask,id))

def c37024 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37024 : Upper (D 6) (R 6) [34,129,40,320,6] 13 := by
  apply FastRouting.sound _ _ [34,129,40,320,6] 13 (by decide) (choices 1) [1,4,16,64] r37024 c37024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21810
  · exact u21811
  · exact u21812
  · exact u21813

def r37025 : Route 9 := (fun mask => (mask,id))

def c37025 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37025 : Upper (D 6) (R 6) [34,129,40,320,65] 13 := by
  apply FastRouting.sound _ _ [34,129,40,320,65] 13 (by decide) (choices 1) [2,4,16] r37025 c37025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21814
  · exact u21815
  · exact u21816

def r37026 : Route 9 := (fun mask => (mask,id))

def c37026 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37026 : Upper (D 6) (R 6) [34,129,40,320,66] 13 := by
  apply FastRouting.sound _ _ [34,129,40,320,66] 13 (by decide) (choices 1) [1,4,16] r37026 c37026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21817
  · exact u21818
  · exact u21819

def r37027 : Route 9 := (fun mask => (mask,id))

def c37027 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37027 : Upper (D 6) (R 6) [34,129,40,320,68] 13 := by
  apply FastRouting.sound _ _ [34,129,40,320,68] 13 (by decide) (choices 1) [1,2,4,16] r37027 c37027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21820
  · exact u21821
  · exact u21822
  · exact u21823

def b37028 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 16, targets := 3 },{ cop := 3, region := 16, targets := 32 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 70 13 28 368 368 496 368), lower := (rows 35 131 70 13 28 32 64 128 256), losses := [] }

theorem u37028 : Upper (D 6) (R 6) [34,129,66,5,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37028 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37029 : Route 9 := (fun mask => (mask,id))

def c37029 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u37029 : Upper (D 6) (R 6) [34,129,66,5,36] 13 := by
  apply FastRouting.sound _ _ [34,129,66,5,36] 13 (by decide) (choices 1) [8,16,64,256] r37029 c37029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21824
  · exact u21825
  · exact u21826
  · exact u21827

def r37030 : Route 9 := (fun mask => (mask,id))

def c37030 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | _ => 0)

theorem u37030 : Upper (D 6) (R 6) [34,129,66,5,40] 13 := by
  apply FastRouting.sound _ _ [34,129,66,5,40] 13 (by decide) (choices 1) [4,16,64,256] r37030 c37030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21828
  · exact u21829
  · exact u21830
  · exact u21831

def b37031 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 70 13 84 312 376 440 312), lower := (rows 35 131 70 13 84 32 64 128 256), losses := [] }

theorem u37031 : Upper (D 6) (R 6) [34,129,66,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37032 : Route 9 := (fun mask => (mask,id))

def c37032 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37032 : Upper (D 6) (R 6) [34,129,66,5,72] 13 := by
  apply FastRouting.sound _ _ [34,129,66,5,72] 13 (by decide) (choices 1) [4,16,256] r37032 c37032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21832
  · exact u21833
  · exact u21834

def r37033 : Route 9 := (fun mask => (mask,id))

def c37033 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37033 : Upper (D 6) (R 6) [34,129,66,5,96] 13 := by
  apply FastRouting.sound _ _ [34,129,66,5,96] 13 (by decide) (choices 1) [4,8,16,256] r37033 c37033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21835
  · exact u21836
  · exact u21837
  · exact u21838

def r37034 : Route 9 := (fun mask => (mask,id))

def c37034 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37034 : Upper (D 6) (R 6) [34,129,66,5,260] 13 := by
  apply FastRouting.sound _ _ [34,129,66,5,260] 13 (by decide) (choices 1) [8,16,64] r37034 c37034
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21839
  · exact u21840
  · exact u21841

def r37035 : Route 9 := (fun mask => (mask,id))

def c37035 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37035 : Upper (D 6) (R 6) [34,129,66,5,264] 13 := by
  apply FastRouting.sound _ _ [34,129,66,5,264] 13 (by decide) (choices 1) [4,16,64] r37035 c37035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21842
  · exact u21843
  · exact u21844

def r37036 : Route 9 := (fun mask => (mask,id))

def c37036 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37036 : Upper (D 6) (R 6) [34,129,66,5,288] 13 := by
  apply FastRouting.sound _ _ [34,129,66,5,288] 13 (by decide) (choices 1) [4,8,16,64] r37036 c37036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21845
  · exact u21846
  · exact u21847
  · exact u21848

def r37037 : Route 9 := (fun mask => (mask,id))

def c37037 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37037 : Upper (D 6) (R 6) [34,129,66,5,320] 13 := by
  apply FastRouting.sound _ _ [34,129,66,5,320] 13 (by decide) (choices 1) [4,8,16] r37037 c37037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21849
  · exact u21850
  · exact u21851

def r37038 : Route 9 := (fun mask => (mask,id))

def c37038 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37038 : Upper (D 6) (R 6) [34,129,66,17,12] 13 := by
  apply FastRouting.sound _ _ [34,129,66,17,12] 13 (by decide) (choices 1) [4,64,256] r37038 c37038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21852
  · exact u21853
  · exact u21854

def r37039 : Route 9 := (fun mask => (mask,id))

def c37039 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37039 : Upper (D 6) (R 6) [34,129,66,17,36] 13 := by
  apply FastRouting.sound _ _ [34,129,66,17,36] 13 (by decide) (choices 1) [4,8,64,256] r37039 c37039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21855
  · exact u21856
  · exact u21857
  · exact u21858

def b37040 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 131 70 25 56 356 324 452 324), lower := (rows 35 131 70 25 56 32 64 128 256), losses := [] }

theorem u37040 : Upper (D 6) (R 6) [34,129,66,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37040 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37041 : PairBound 9 := { available := 300, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 70 25 84 300 364 428 300), lower := (rows 35 131 70 25 84 32 64 128 256), losses := [] }

theorem u37041 : Upper (D 6) (R 6) [34,129,66,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37041 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37042 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 324, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 131 70 25 88 292 356 420 292), lower := (rows 35 131 70 25 88 32 64 128 256), losses := [] }

theorem u37042 : Upper (D 6) (R 6) [34,129,66,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37042 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37043 : Route 9 := (fun mask => (mask,id))

def c37043 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37043 : Upper (D 6) (R 6) [34,129,66,17,96] 13 := by
  apply FastRouting.sound _ _ [34,129,66,17,96] 13 (by decide) (choices 1) [4,8,256] r37043 c37043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21859
  · exact u21860
  · exact u21861

def r37044 : Route 9 := (fun mask => (mask,id))

def c37044 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37044 : Upper (D 6) (R 6) [34,129,66,17,260] 13 := by
  apply FastRouting.sound _ _ [34,129,66,17,260] 13 (by decide) (choices 1) [4,8,64] r37044 c37044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21862
  · exact u21863
  · exact u21864

def r37045 : Route 9 := (fun mask => (mask,id))

def c37045 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37045 : Upper (D 6) (R 6) [34,129,66,17,264] 13 := by
  apply FastRouting.sound _ _ [34,129,66,17,264] 13 (by decide) (choices 1) [4,64] r37045 c37045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21865
  · exact u21866

def r37046 : Route 9 := (fun mask => (mask,id))

def c37046 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37046 : Upper (D 6) (R 6) [34,129,66,17,288] 13 := by
  apply FastRouting.sound _ _ [34,129,66,17,288] 13 (by decide) (choices 1) [4,8,64] r37046 c37046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21867
  · exact u21868
  · exact u21869

def r37047 : Route 9 := (fun mask => (mask,id))

def c37047 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37047 : Upper (D 6) (R 6) [34,129,66,17,320] 13 := by
  apply FastRouting.sound _ _ [34,129,66,17,320] 13 (by decide) (choices 1) [4,8] r37047 c37047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21870
  · exact u21871

def b37048 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 70 28 28 353 353 481 353), lower := (rows 35 131 70 28 28 32 64 128 256), losses := [] }

theorem u37048 : Upper (D 6) (R 6) [34,129,66,20,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37048 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37049 : PairBound 9 := { available := 332, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 131 70 28 49 364 332 460 332), lower := (rows 35 131 70 28 49 32 64 128 256), losses := [] }

theorem u37049 : Upper (D 6) (R 6) [34,129,66,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37049 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37050 : PairBound 9 := { available := 329, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 70 28 52 361 329 457 329), lower := (rows 35 131 70 28 52 32 64 128 256), losses := [] }

theorem u37050 : Upper (D 6) (R 6) [34,129,66,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37050 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37051 : Route 9 := (fun mask => (mask,id))

def c37051 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37051 : Upper (D 6) (R 6) [34,129,66,20,40] 13 := by
  apply FastRouting.sound _ _ [34,129,66,20,40] 13 (by decide) (choices 1) [1,4,64,256] r37051 c37051
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21872
  · exact u21873
  · exact u21874
  · exact u21875

def r37052 : Route 9 := (fun mask => (mask,id))

def c37052 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37052 : Upper (D 6) (R 6) [34,129,66,20,65] 13 := by
  apply FastRouting.sound _ _ [34,129,66,20,65] 13 (by decide) (choices 1) [4,8,256] r37052 c37052
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21876
  · exact u21877
  · exact u21878

def b37053 : PairBound 9 := { available := 297, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 70 28 84 297 361 425 297), lower := (rows 35 131 70 28 84 32 64 128 256), losses := [] }

theorem u37053 : Upper (D 6) (R 6) [34,129,66,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37053 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37054 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 70 28 88 293 357 421 293), lower := (rows 35 131 70 28 88 32 64 128 256), losses := [] }

theorem u37054 : Upper (D 6) (R 6) [34,129,66,20,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37054 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37055 : Route 9 := (fun mask => (mask,id))

def c37055 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37055 : Upper (D 6) (R 6) [34,129,66,20,96] 13 := by
  apply FastRouting.sound _ _ [34,129,66,20,96] 13 (by decide) (choices 1) [1,4,8,256] r37055 c37055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21879
  · exact u21880
  · exact u21881
  · exact u21882

def r37056 : Route 9 := (fun mask => (mask,id))

def c37056 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37056 : Upper (D 6) (R 6) [34,129,66,20,257] 13 := by
  apply FastRouting.sound _ _ [34,129,66,20,257] 13 (by decide) (choices 1) [4,8,64] r37056 c37056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21883
  · exact u21884
  · exact u21885

def b37057 : PairBound 9 := { available := 105, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 70 28 276 105 105 233 361), lower := (rows 35 131 70 28 276 32 64 128 256), losses := [] }

theorem u37057 : Upper (D 6) (R 6) [34,129,66,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37057 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37058 : Route 9 := (fun mask => (mask,id))

def c37058 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37058 : Upper (D 6) (R 6) [34,129,66,20,264] 13 := by
  apply FastRouting.sound _ _ [34,129,66,20,264] 13 (by decide) (choices 1) [1,4,64] r37058 c37058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21886
  · exact u21887
  · exact u21888

def r37059 : Route 9 := (fun mask => (mask,id))

def c37059 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37059 : Upper (D 6) (R 6) [34,129,66,20,288] 13 := by
  apply FastRouting.sound _ _ [34,129,66,20,288] 13 (by decide) (choices 1) [1,4,8,64] r37059 c37059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21889
  · exact u21890
  · exact u21891
  · exact u21892

def r37060 : Route 9 := (fun mask => (mask,id))

def c37060 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37060 : Upper (D 6) (R 6) [34,129,66,20,320] 13 := by
  apply FastRouting.sound _ _ [34,129,66,20,320] 13 (by decide) (choices 1) [1,4,8] r37060 c37060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21893
  · exact u21894
  · exact u21895

def b37061 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 131 70 41 88 308 340 404 276), lower := (rows 35 131 70 41 88 32 64 128 256), losses := [] }

theorem u37061 : Upper (D 6) (R 6) [34,129,66,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37061 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37062 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 131 70 41 276 124 92 220 348), lower := (rows 35 131 70 41 276 32 64 128 256), losses := [] }

theorem u37062 : Upper (D 6) (R 6) [34,129,66,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37063 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 131 70 41 280 116 84 212 340), lower := (rows 35 131 70 41 280 32 64 128 256), losses := [] }

theorem u37063 : Upper (D 6) (R 6) [34,129,66,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37064 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 131 70 41 336 60 92 156 284), lower := (rows 35 131 70 41 336 32 64 128 256), losses := [] }

theorem u37064 : Upper (D 6) (R 6) [34,129,66,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37064 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37065 : Route 9 := (fun mask => (mask,id))

def c37065 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37065 : Upper (D 6) (R 6) [34,129,66,36,65] 13 := by
  apply FastRouting.sound _ _ [34,129,66,36,65] 13 (by decide) (choices 1) [4,8,16,256] r37065 c37065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21896
  · exact u21897
  · exact u21898
  · exact u21899

def b37066 : PairBound 9 := { available := 281, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 70 44 84 313 345 409 281), lower := (rows 35 131 70 44 84 32 64 128 256), losses := [] }

theorem u37066 : Upper (D 6) (R 6) [34,129,66,36,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37066 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37067 : Route 9 := (fun mask => (mask,id))

def c37067 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37067 : Upper (D 6) (R 6) [34,129,66,36,72] 13 := by
  apply FastRouting.sound _ _ [34,129,66,36,72] 13 (by decide) (choices 1) [1,4,16,256] r37067 c37067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21900
  · exact u21901
  · exact u21902
  · exact u21903

def r37068 : Route 9 := (fun mask => (mask,id))

def c37068 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37068 : Upper (D 6) (R 6) [34,129,66,36,257] 13 := by
  apply FastRouting.sound _ _ [34,129,66,36,257] 13 (by decide) (choices 1) [4,8,16,64] r37068 c37068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21904
  · exact u21905
  · exact u21906
  · exact u21907

def r37069 : Route 9 := (fun mask => (mask,id))

def c37069 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37069 : Upper (D 6) (R 6) [34,129,66,36,260] 13 := by
  apply FastRouting.sound _ _ [34,129,66,36,260] 13 (by decide) (choices 1) [1,8,16,64] r37069 c37069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21908
  · exact u21909
  · exact u21910
  · exact u21911

def r37070 : Route 9 := (fun mask => (mask,id))

def c37070 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37070 : Upper (D 6) (R 6) [34,129,66,36,264] 13 := by
  apply FastRouting.sound _ _ [34,129,66,36,264] 13 (by decide) (choices 1) [1,4,16,64] r37070 c37070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21912
  · exact u21913
  · exact u21914
  · exact u21915

def r37071 : Route 9 := (fun mask => (mask,id))

def c37071 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37071 : Upper (D 6) (R 6) [34,129,66,36,320] 13 := by
  apply FastRouting.sound _ _ [34,129,66,36,320] 13 (by decide) (choices 1) [1,4,8,16] r37071 c37071
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21916
  · exact u21917
  · exact u21918
  · exact u21919

def r37072 : Route 9 := (fun mask => (mask,id))

def c37072 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37072 : Upper (D 6) (R 6) [34,129,66,48,65] 13 := by
  apply FastRouting.sound _ _ [34,129,66,48,65] 13 (by decide) (choices 1) [4,8,256] r37072 c37072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21920
  · exact u21921
  · exact u21922

def b37073 : PairBound 9 := { available := 269, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 70 56 84 301 333 397 269), lower := (rows 35 131 70 56 84 32 64 128 256), losses := [] }

theorem u37073 : Upper (D 6) (R 6) [34,129,66,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37073 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37074 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 289, targets := 64 }], pairs := [(0,6),(1,5),(2,5)], upper := (rows 35 131 70 56 88 293 325 389 261), lower := (rows 35 131 70 56 88 32 64 128 256), losses := [] }

theorem u37074 : Upper (D 6) (R 6) [34,129,66,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37074 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37075 : Route 9 := (fun mask => (mask,id))

def c37075 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37075 : Upper (D 6) (R 6) [34,129,66,48,257] 13 := by
  apply FastRouting.sound _ _ [34,129,66,48,257] 13 (by decide) (choices 1) [4,8,64] r37075 c37075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21923
  · exact u21924
  · exact u21925

def r37076 : Route 9 := (fun mask => (mask,id))

def c37076 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37076 : Upper (D 6) (R 6) [34,129,66,48,260] 13 := by
  apply FastRouting.sound _ _ [34,129,66,48,260] 13 (by decide) (choices 1) [1,4,8,64] r37076 c37076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21926
  · exact u21927
  · exact u21928
  · exact u21929

def r37077 : Route 9 := (fun mask => (mask,id))

def c37077 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37077 : Upper (D 6) (R 6) [34,129,66,48,264] 13 := by
  apply FastRouting.sound _ _ [34,129,66,48,264] 13 (by decide) (choices 1) [1,4,64] r37077 c37077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21930
  · exact u21931
  · exact u21932

def r37078 : Route 9 := (fun mask => (mask,id))

def c37078 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37078 : Upper (D 6) (R 6) [34,129,66,48,320] 13 := by
  apply FastRouting.sound _ _ [34,129,66,48,320] 13 (by decide) (choices 1) [1,4,8] r37078 c37078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21933
  · exact u21934
  · exact u21935

def r37079 : Route 9 := (fun mask => (mask,id))

def c37079 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37079 : Upper (D 6) (R 6) [34,129,66,65,260] 13 := by
  apply FastRouting.sound _ _ [34,129,66,65,260] 13 (by decide) (choices 1) [4,8,16] r37079 c37079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21936
  · exact u21937
  · exact u21938

#print axioms u37079
end Delivery.IrregularNine14.P06
