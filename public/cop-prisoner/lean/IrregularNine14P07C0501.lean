import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0194
import IrregularNine14P07C0195
import IrregularNine14P07C0196

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r30060 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30060 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30060 : Upper (D 7) (R 7) [6,9,33,192,288] 13 := by
  apply FastRouting.sound _ _ [6,9,33,192,288] 13 (by decide) (choices 1) [2,16,64] r30060 c30060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11683
  · exact u11684
  · exact u11685

def r30061 : Route 9 := (fun mask => (mask,id))

def c30061 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30061 : Upper (D 7) (R 7) [6,9,33,192,320] 13 := by
  apply FastRouting.sound _ _ [6,9,33,192,320] 13 (by decide) (choices 1) [2,16,128] r30061 c30061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11686
  · exact u11687
  · exact u11688

def b30062 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 11 37 280 50 224 192 192 448), lower := (rows 7 11 37 280 50 32 64 128 256), losses := [] }

theorem u30062 : Upper (D 7) (R 7) [6,9,33,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30062 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30063 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 0, region := 228, targets := 2 },{ cop := 4, region := 424, targets := 2 }], pairs := [(2,1),(3,0),(3,1),(4,0)], upper := (rows 7 11 37 280 82 224 224 224 480), lower := (rows 7 11 37 280 82 32 64 128 256), losses := [] }

theorem u30063 : Upper (D 7) (R 7) [6,9,33,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30063 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30064 : Route 9 := (fun mask => (mask,id))

def c30064 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30064 : Upper (D 7) (R 7) [6,9,33,272,96] 13 := by
  apply FastRouting.sound _ _ [6,9,33,272,96] 13 (by decide) (choices 1) [2,64,128] r30064 c30064
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11689
  · exact u11690
  · exact u11691

def r30065 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30065 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30065 : Upper (D 7) (R 7) [6,9,33,272,192] 13 := by
  apply FastRouting.sound _ _ [6,9,33,272,192] 13 (by decide) (choices 1) [2,64] r30065 c30065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11692
  · exact u11693

def b30066 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 11 37 328 50 240 208 208 464), lower := (rows 7 11 37 328 50 32 64 128 256), losses := [] }

theorem u30066 : Upper (D 7) (R 7) [6,9,33,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30066 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30067 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(2,6),(3,0),(4,0)], upper := (rows 7 11 37 328 82 176 240 176 432), lower := (rows 7 11 37 328 82 32 64 128 256), losses := [] }

theorem u30067 : Upper (D 7) (R 7) [6,9,33,320,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30067 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30068 : Route 9 := (fun mask => (mask,id))

def c30068 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30068 : Upper (D 7) (R 7) [6,9,33,320,96] 13 := by
  apply FastRouting.sound _ _ [6,9,33,320,96] 13 (by decide) (choices 1) [2,16,128] r30068 c30068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11694
  · exact u11695
  · exact u11696

def r30069 : Route 9 := (fun mask => (mask,id))

def c30069 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30069 : Upper (D 7) (R 7) [6,9,33,320,130] 13 := by
  apply FastRouting.sound _ _ [6,9,33,320,130] 13 (by decide) (choices 1) [16,64,128] r30069 c30069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11697
  · exact u11698
  · exact u11699

def r30070 : Route 9 := (fun mask => (mask,id))

def c30070 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30070 : Upper (D 7) (R 7) [6,9,33,320,160] 13 := by
  apply FastRouting.sound _ _ [6,9,33,320,160] 13 (by decide) (choices 1) [2,16,64,128] r30070 c30070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11700
  · exact u11701
  · exact u11702
  · exact u11703

def r30071 : Route 9 := (fun mask => (mask,id))

def c30071 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30071 : Upper (D 7) (R 7) [6,9,33,320,192] 13 := by
  apply FastRouting.sound _ _ [6,9,33,320,192] 13 (by decide) (choices 1) [2,16,128] r30071 c30071
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11704
  · exact u11705
  · exact u11706

def b30072 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 23, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 11 52 104 19 480 448 448 448), lower := (rows 7 11 52 104 19 32 64 128 256), losses := [] }

theorem u30072 : Upper (D 7) (R 7) [6,9,48,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30072 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30073 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 23, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 11 52 104 81 418 450 386 386), lower := (rows 7 11 52 104 81 32 64 128 256), losses := [] }

theorem u30073 : Upper (D 7) (R 7) [6,9,48,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30073 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30074 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 23, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 11 52 104 82 417 449 385 385), lower := (rows 7 11 52 104 82 32 64 128 256), losses := [] }

theorem u30074 : Upper (D 7) (R 7) [6,9,48,96,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30074 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30075 : Route 9 := (fun mask => (mask,id))

def c30075 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u30075 : Upper (D 7) (R 7) [6,9,48,96,129] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,129] 13 (by decide) (choices 1) [2,64,128,256] r30075 c30075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11707
  · exact u11708
  · exact u11709
  · exact u11710

def r30076 : Route 9 := (fun mask => (mask,id))

def c30076 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u30076 : Upper (D 7) (R 7) [6,9,48,96,130] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,130] 13 (by decide) (choices 1) [1,64,128,256] r30076 c30076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11711
  · exact u11712
  · exact u11713
  · exact u11714

def r30077 : Route 9 := (fun mask => (mask,id))

def c30077 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30077 : Upper (D 7) (R 7) [6,9,48,96,192] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,192] 13 (by decide) (choices 1) [1,2,128,256] r30077 c30077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11715
  · exact u11716
  · exact u11717
  · exact u11718

def r30078 : Route 9 := (fun mask => (mask,id))

def c30078 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30078 : Upper (D 7) (R 7) [6,9,48,96,257] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,257] 13 (by decide) (choices 1) [2,64,128] r30078 c30078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11719
  · exact u11720
  · exact u11721

def r30079 : Route 9 := (fun mask => (mask,id))

def c30079 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30079 : Upper (D 7) (R 7) [6,9,48,96,258] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,258] 13 (by decide) (choices 1) [1,64,128] r30079 c30079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11722
  · exact u11723
  · exact u11724

def r30080 : Route 9 := (fun mask => (mask,id))

def c30080 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30080 : Upper (D 7) (R 7) [6,9,48,96,320] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,320] 13 (by decide) (choices 1) [1,2,128] r30080 c30080
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11725
  · exact u11726
  · exact u11727

def r30081 : Route 9 := (fun mask => (mask,id))

def c30081 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30081 : Upper (D 7) (R 7) [6,9,48,96,384] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,384] 13 (by decide) (choices 1) [1,2,64,128] r30081 c30081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11728
  · exact u11729
  · exact u11730
  · exact u11731

def b30082 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 11 52 200 19 480 480 480 480), lower := (rows 7 11 52 200 19 32 64 128 256), losses := [] }

theorem u30082 : Upper (D 7) (R 7) [6,9,48,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30082 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30083 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 4, targets := 195 }], pairs := [(2,0),(2,1),(2,6),(2,7)], upper := (rows 7 11 52 200 49 482 450 450 450), lower := (rows 7 11 52 200 49 32 64 128 256), losses := [] }

theorem u30083 : Upper (D 7) (R 7) [6,9,48,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30083 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30084 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 11 52 200 50 481 449 449 449), lower := (rows 7 11 52 200 50 32 64 128 256), losses := [] }

theorem u30084 : Upper (D 7) (R 7) [6,9,48,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30084 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30085 : Route 9 := (fun mask => (mask,id))

def c30085 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30085 : Upper (D 7) (R 7) [6,9,48,192,65] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,65] 13 (by decide) (choices 1) [2,128,256] r30085 c30085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11732
  · exact u11733
  · exact u11734

def b30086 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 421, targets := 64 },{ cop := 0, region := 488, targets := 2 }], pairs := [(0,6),(2,1),(2,6),(3,1)], upper := (rows 7 11 52 200 82 417 481 417 417), lower := (rows 7 11 52 200 82 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 27 16 35 67 131 259), good := (rows 493 489 60 200 508 32 64 128 256) }] }

theorem u30086 : Upper (D 7) (R 7) [6,9,48,192,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30086 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30087 : PairBound 9 := { available := 387, camps := [{ cop := 4, region := 4, targets := 195 }], pairs := [(2,0),(2,1),(2,6),(2,7)], upper := (rows 7 11 52 200 112 419 451 387 387), lower := (rows 7 11 52 200 112 32 64 128 256), losses := [] }

theorem u30087 : Upper (D 7) (R 7) [6,9,48,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30087 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30088 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 7 11 52 200 208 291 355 419 291), lower := (rows 7 11 52 200 208 32 64 128 256), losses := [] }

theorem u30088 : Upper (D 7) (R 7) [6,9,48,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30088 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30089 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30089 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30089 : Upper (D 7) (R 7) [6,9,48,192,257] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,257] 13 (by decide) (choices 1) [2,64] r30089 c30089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11735
  · exact u11736

def r30090 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30090 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30090 : Upper (D 7) (R 7) [6,9,48,192,258] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,258] 13 (by decide) (choices 1) [1,64] r30090 c30090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11737
  · exact u11738

def b30091 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 4, targets := 195 }], pairs := [(2,0),(2,1),(2,6),(2,7)], upper := (rows 7 11 52 200 304 227 195 195 451), lower := (rows 7 11 52 200 304 32 64 128 256), losses := [] }

theorem u30091 : Upper (D 7) (R 7) [6,9,48,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30092 : Route 9 := (fun mask => (mask,id))

def c30092 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30092 : Upper (D 7) (R 7) [6,9,48,192,320] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,320] 13 (by decide) (choices 1) [1,2,128] r30092 c30092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11739
  · exact u11740
  · exact u11741

def b30093 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 459, targets := 32 },{ cop := 0, region := 244, targets := 2 }], pairs := [(0,5),(1,5),(2,1),(3,5)], upper := (rows 7 11 52 266 49 224 192 192 448), lower := (rows 7 11 52 266 49 32 64 128 256), losses := [] }

theorem u30093 : Upper (D 7) (R 7) [6,9,48,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30093 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30094 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 488, targets := 1 },{ cop := 4, region := 164, targets := 1 }], pairs := [(2,0),(2,1),(3,0),(4,1)], upper := (rows 7 11 52 266 81 224 224 224 480), lower := (rows 7 11 52 266 81 32 64 128 256), losses := [] }

theorem u30094 : Upper (D 7) (R 7) [6,9,48,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30094 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30095 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 195 }], pairs := [(2,0),(2,1),(2,6),(2,7)], upper := (rows 7 11 52 266 112 225 193 193 449), lower := (rows 7 11 52 266 112 32 64 128 256), losses := [] }

theorem u30095 : Upper (D 7) (R 7) [6,9,48,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30095 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30096 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30096 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30096 : Upper (D 7) (R 7) [6,9,48,258,192] 13 := by
  apply FastRouting.sound _ _ [6,9,48,258,192] 13 (by decide) (choices 1) [1,64] r30096 c30096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11742
  · exact u11743

def b30097 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 23, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 11 52 296 19 224 192 192 448), lower := (rows 7 11 52 296 19 32 64 128 256), losses := [] }

theorem u30097 : Upper (D 7) (R 7) [6,9,48,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30098 : Route 9 := (fun mask => (mask,id))

def c30098 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30098 : Upper (D 7) (R 7) [6,9,48,288,65] 13 := by
  apply FastRouting.sound _ _ [6,9,48,288,65] 13 (by decide) (choices 1) [2,64,128] r30098 c30098
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11744
  · exact u11745
  · exact u11746

def r30099 : Route 9 := (fun mask => (mask,id))

def c30099 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30099 : Upper (D 7) (R 7) [6,9,48,288,66] 13 := by
  apply FastRouting.sound _ _ [6,9,48,288,66] 13 (by decide) (choices 1) [1,64,128] r30099 c30099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11747
  · exact u11748
  · exact u11749

def r30100 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30100 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30100 : Upper (D 7) (R 7) [6,9,48,288,192] 13 := by
  apply FastRouting.sound _ _ [6,9,48,288,192] 13 (by decide) (choices 1) [1,2,64] r30100 c30100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11750
  · exact u11751
  · exact u11752

def b30101 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 11 52 328 19 224 224 224 480), lower := (rows 7 11 52 328 19 32 64 128 256), losses := [] }

theorem u30101 : Upper (D 7) (R 7) [6,9,48,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30101 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30102 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 4, targets := 195 }], pairs := [(2,0),(2,1),(2,6),(2,7)], upper := (rows 7 11 52 328 49 226 194 194 450), lower := (rows 7 11 52 328 49 32 64 128 256), losses := [] }

theorem u30102 : Upper (D 7) (R 7) [6,9,48,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30102 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30103 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 11 52 328 50 225 193 193 449), lower := (rows 7 11 52 328 50 32 64 128 256), losses := [] }

theorem u30103 : Upper (D 7) (R 7) [6,9,48,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30103 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30104 : Route 9 := (fun mask => (mask,id))

def c30104 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30104 : Upper (D 7) (R 7) [6,9,48,320,65] 13 := by
  apply FastRouting.sound _ _ [6,9,48,320,65] 13 (by decide) (choices 1) [2,128] r30104 c30104
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11753
  · exact u11754

def b30105 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 165, targets := 64 },{ cop := 0, region := 488, targets := 2 }], pairs := [(0,6),(2,1),(2,6),(3,1)], upper := (rows 7 11 52 328 82 161 225 161 417), lower := (rows 7 11 52 328 82 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 27 16 35 67 131 259), good := (rows 493 489 60 328 508 32 64 128 256) }] }

theorem u30105 : Upper (D 7) (R 7) [6,9,48,320,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30105 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30106 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 195 }], pairs := [(2,0),(2,1),(2,6),(2,7)], upper := (rows 7 11 52 328 112 163 195 131 387), lower := (rows 7 11 52 328 112 32 64 128 256), losses := [] }

theorem u30106 : Upper (D 7) (R 7) [6,9,48,320,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30106 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30107 : Route 9 := (fun mask => (mask,id))

def c30107 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30107 : Upper (D 7) (R 7) [6,9,48,320,129] 13 := by
  apply FastRouting.sound _ _ [6,9,48,320,129] 13 (by decide) (choices 1) [2,64,128] r30107 c30107
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11755
  · exact u11756
  · exact u11757

def r30108 : Route 9 := (fun mask => (mask,id))

def c30108 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30108 : Upper (D 7) (R 7) [6,9,48,320,130] 13 := by
  apply FastRouting.sound _ _ [6,9,48,320,130] 13 (by decide) (choices 1) [1,64,128] r30108 c30108
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11758
  · exact u11759
  · exact u11760

def b30109 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 4, targets := 195 }], pairs := [(2,0),(2,1),(2,6),(2,7)], upper := (rows 7 11 52 328 176 227 195 195 451), lower := (rows 7 11 52 328 176 32 64 128 256), losses := [] }

theorem u30109 : Upper (D 7) (R 7) [6,9,48,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30109 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30110 : Route 9 := (fun mask => (mask,id))

def c30110 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30110 : Upper (D 7) (R 7) [6,9,48,320,192] 13 := by
  apply FastRouting.sound _ _ [6,9,48,320,192] 13 (by decide) (choices 1) [1,2,128] r30110 c30110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11761
  · exact u11762
  · exact u11763

def b30111 : PairBound 9 := { available := 464, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 11 100 168 19 496 464 464 464), lower := (rows 7 11 100 168 19 32 64 128 256), losses := [] }

theorem u30111 : Upper (D 7) (R 7) [6,9,96,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30111 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30112 : Route 9 := (fun mask => (mask,id))

def c30112 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u30112 : Upper (D 7) (R 7) [6,9,96,160,65] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,65] 13 (by decide) (choices 1) [2,16,128,256] r30112 c30112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11764
  · exact u11765
  · exact u11766
  · exact u11767

def r30113 : Route 9 := (fun mask => (mask,id))

def c30113 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u30113 : Upper (D 7) (R 7) [6,9,96,160,66] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,66] 13 (by decide) (choices 1) [1,16,128,256] r30113 c30113
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11768
  · exact u11769
  · exact u11770
  · exact u11771

theorem m30114_2 : Upper (D 7) (R 7) [6,9,96,160,192,2] 13 :=
  permutation_upper _ _ _ [6,9,96,160,192,1] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11772

def r30114 : Route 9 := (fun mask => (mask,id))

def c30114 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30114 : Upper (D 7) (R 7) [6,9,96,160,192] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,192] 13 (by decide) (choices 1) [1,2,16,256] r30114 c30114
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11772
  · exact m30114_2
  · exact u11773
  · exact u11774

def r30115 : Route 9 := (fun mask => (mask,id))

def c30115 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30115 : Upper (D 7) (R 7) [6,9,96,160,257] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,257] 13 (by decide) (choices 1) [2,16,64,128] r30115 c30115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11775
  · exact u11776
  · exact u11777
  · exact u11778

def r30116 : Route 9 := (fun mask => (mask,id))

def c30116 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30116 : Upper (D 7) (R 7) [6,9,96,160,320] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,320] 13 (by decide) (choices 1) [1,2,16,128] r30116 c30116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11779
  · exact u11780
  · exact u11781
  · exact u11782

def b30117 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(2,1),(3,5),(4,1)], upper := (rows 7 11 100 266 49 240 208 208 464), lower := (rows 7 11 100 266 49 32 64 128 256), losses := [] }

theorem u30117 : Upper (D 7) (R 7) [6,9,96,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30118 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 16, targets := 131 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,7)], upper := (rows 7 11 100 266 112 177 209 145 401), lower := (rows 7 11 100 266 112 32 64 128 256), losses := [] }

theorem u30118 : Upper (D 7) (R 7) [6,9,96,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30118 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30119 : Route 9 := (fun mask => (mask,id))

def c30119 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30119 : Upper (D 7) (R 7) [6,9,96,258,129] 13 := by
  apply FastRouting.sound _ _ [6,9,96,258,129] 13 (by decide) (choices 1) [16,64,128] r30119 c30119
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11783
  · exact u11784
  · exact u11785

#print axioms u30119
end Delivery.IrregularNine14.P07
