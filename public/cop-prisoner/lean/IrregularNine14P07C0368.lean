import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0110
import IrregularNine14P07C0111

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r22080 : Route 9 := (fun mask => (mask,id))

def c22080 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22080 : Upper (D 7) (R 7) [34,320,96,129,130,8] 13 := by
  apply FastRouting.sound _ _ [34,320,96,129,130,8] 13 (by decide) (choices 1) [1,4,16] r22080 c22080
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6641
  · exact u6642
  · exact u6643

def b22081 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 322 100 137 146 48 77 141 269), lower := (rows 35 322 100 137 146 48 64 128 256), losses := [] }

theorem u22081 : Upper (D 7) (R 7) [34,320,96,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22081 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22082 : Route 9 := (fun mask => (mask,id))

def c22082 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22082 : Upper (D 7) (R 7) [34,320,96,129,132,1] 13 := by
  apply FastRouting.sound _ _ [34,320,96,129,132,1] 13 (by decide) (choices 1) [2,8,16] r22082 c22082
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6644
  · exact u6645
  · exact u6646

def b22083 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 322 100 137 148 34 89 153 281), lower := (rows 35 322 100 137 148 34 64 128 256), losses := [] }

theorem u22083 : Upper (D 7) (R 7) [34,320,96,129,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22083 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22084 : Route 9 := (fun mask => (mask,id))

def c22084 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22084 : Upper (D 7) (R 7) [34,320,96,129,132,8] 13 := by
  apply FastRouting.sound _ _ [34,320,96,129,132,8] 13 (by decide) (choices 1) [1,2,16] r22084 c22084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6647
  · exact u6648
  · exact u6649

def b22085 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 0, region := 136, targets := 64 }], pairs := [(1,5),(3,5),(3,6)], upper := (rows 35 322 100 137 148 48 75 139 267), lower := (rows 35 322 100 137 148 48 64 128 256), losses := [] }

theorem u22085 : Upper (D 7) (R 7) [34,320,96,129,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22085 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22086 : Route 9 := (fun mask => (mask,id))

def c22086 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22086 : Upper (D 7) (R 7) [34,320,96,130,132,1] 13 := by
  apply FastRouting.sound _ _ [34,320,96,130,132,1] 13 (by decide) (choices 1) [1,8,16] r22086 c22086
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6650
  · exact u6651
  · exact u6652

def b22087 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 322 100 138 148 40 81 145 273), lower := (rows 35 322 100 138 148 40 64 128 256), losses := [] }

theorem u22087 : Upper (D 7) (R 7) [34,320,96,130,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22087 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22088 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 0, region := 136, targets := 64 }], pairs := [(1,5),(3,5),(3,6)], upper := (rows 35 322 100 138 148 48 73 137 265), lower := (rows 35 322 100 138 148 48 64 128 256), losses := [] }

theorem u22088 : Upper (D 7) (R 7) [34,320,96,130,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22088 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22089 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 37 42 21 73 400 34 194 194 450), lower := (rows 37 42 21 73 400 34 64 128 256), losses := [] }

theorem u22089 : Upper (D 7) (R 7) [36,40,17,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22089 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22090 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 37 42 21 73 400 96 194 130 386), lower := (rows 37 42 21 73 400 96 64 128 256), losses := [] }

theorem u22090 : Upper (D 7) (R 7) [36,40,17,65,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22090 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22091 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 42 21 73 400 160 66 194 322), lower := (rows 37 42 21 73 400 160 64 128 256), losses := [] }

theorem u22091 : Upper (D 7) (R 7) [36,40,17,65,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22092 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 21 74 146 33 448 448 448), lower := (rows 37 42 21 74 146 33 64 128 256), losses := [] }

theorem u22092 : Upper (D 7) (R 7) [36,40,17,66,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22092 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22093 : PairBound 9 := { available := 385, camps := [{ cop := 5, region := 10, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 42 21 74 146 96 449 385 385), lower := (rows 37 42 21 74 146 96 64 128 256), losses := [] }

theorem u22093 : Upper (D 7) (R 7) [36,40,17,66,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22093 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22094 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 4, region := 37, targets := 2 }], pairs := [(0,1),(1,7),(2,1),(3,7)], upper := (rows 37 42 21 74 146 160 321 449 321), lower := (rows 37 42 21 74 146 160 64 128 256), losses := [] }

theorem u22094 : Upper (D 7) (R 7) [36,40,17,66,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22094 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22095 : Route 9 := (fun mask => (mask,id))

def c22095 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22095 : Upper (D 7) (R 7) [36,40,17,66,130,256] 13 := by
  apply FastRouting.sound _ _ [36,40,17,66,130,256] 13 (by decide) (choices 1) [1,128] r22095 c22095
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6653
  · exact u6654

def b22096 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 21 74 208 33 450 386 386), lower := (rows 37 42 21 74 208 33 64 128 256), losses := [] }

theorem u22096 : Upper (D 7) (R 7) [36,40,17,66,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22096 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22097 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 42 21 74 208 34 449 385 385), lower := (rows 37 42 21 74 208 34 64 128 256), losses := [] }

theorem u22097 : Upper (D 7) (R 7) [36,40,17,66,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22098 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 42 21 74 208 160 323 387 259), lower := (rows 37 42 21 74 208 160 64 128 256), losses := [] }

theorem u22098 : Upper (D 7) (R 7) [36,40,17,66,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22099 : Route 9 := (fun mask => (mask,id))

def c22099 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22099 : Upper (D 7) (R 7) [36,40,17,66,192,256] 13 := by
  apply FastRouting.sound _ _ [36,40,17,66,192,256] 13 (by decide) (choices 1) [1,2,128] r22099 c22099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6655
  · exact u6656
  · exact u6657

def b22100 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 21 74 274 33 192 192 448), lower := (rows 37 42 21 74 274 33 64 128 256), losses := [] }

theorem u22100 : Upper (D 7) (R 7) [36,40,17,66,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22100 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22101 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 10, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 42 21 74 274 96 193 129 385), lower := (rows 37 42 21 74 274 96 64 128 256), losses := [] }

theorem u22101 : Upper (D 7) (R 7) [36,40,17,66,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22101 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22102 : Route 9 := (fun mask => (mask,id))

def c22102 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22102 : Upper (D 7) (R 7) [36,40,17,66,258,128] 13 := by
  apply FastRouting.sound _ _ [36,40,17,66,258,128] 13 (by decide) (choices 1) [1,128] r22102 c22102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6658
  · exact u6659

def b22103 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 21 74 336 33 194 130 386), lower := (rows 37 42 21 74 336 33 64 128 256), losses := [] }

theorem u22103 : Upper (D 7) (R 7) [36,40,17,66,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22103 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22104 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 42 21 74 336 34 193 129 385), lower := (rows 37 42 21 74 336 34 64 128 256), losses := [] }

theorem u22104 : Upper (D 7) (R 7) [36,40,17,66,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22104 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22105 : Route 9 := (fun mask => (mask,id))

def c22105 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22105 : Upper (D 7) (R 7) [36,40,17,66,320,128] 13 := by
  apply FastRouting.sound _ _ [36,40,17,66,320,128] 13 (by decide) (choices 1) [1,2,128] r22105 c22105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6660
  · exact u6661
  · exact u6662

def b22106 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 42 21 74 400 33 194 194 450), lower := (rows 37 42 21 74 400 33 64 128 256), losses := [] }

theorem u22106 : Upper (D 7) (R 7) [36,40,17,66,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22106 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22107 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 42 21 74 400 34 193 193 449), lower := (rows 37 42 21 74 400 34 64 128 256), losses := [] }

theorem u22107 : Upper (D 7) (R 7) [36,40,17,66,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22107 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22108 : PairBound 9 := { available := 131, camps := [{ cop := 5, region := 10, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 42 21 74 400 96 195 131 387), lower := (rows 37 42 21 74 400 96 64 128 256), losses := [] }

theorem u22108 : Upper (D 7) (R 7) [36,40,17,66,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22109 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 42 21 74 400 160 67 195 323), lower := (rows 37 42 21 74 400 160 64 128 256), losses := [] }

theorem u22109 : Upper (D 7) (R 7) [36,40,17,66,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22109 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22110 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 21 200 82 33 450 386 386), lower := (rows 37 42 21 200 82 33 64 128 256), losses := [] }

theorem u22110 : Upper (D 7) (R 7) [36,40,17,192,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22110 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22111 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 42 21 200 82 34 449 385 385), lower := (rows 37 42 21 200 82 34 64 128 256), losses := [] }

theorem u22111 : Upper (D 7) (R 7) [36,40,17,192,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22111 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22112 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 21 200 82 160 323 387 259), lower := (rows 37 42 21 200 82 160 64 128 256), losses := [] }

theorem u22112 : Upper (D 7) (R 7) [36,40,17,192,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22112 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22113 : Route 9 := (fun mask => (mask,id))

def c22113 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22113 : Upper (D 7) (R 7) [36,40,17,192,66,256] 13 := by
  apply FastRouting.sound _ _ [36,40,17,192,66,256] 13 (by decide) (choices 1) [1,2,128] r22113 c22113
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6663
  · exact u6664
  · exact u6665

def b22114 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 42 21 200 274 33 194 194 450), lower := (rows 37 42 21 200 274 33 64 128 256), losses := [] }

theorem u22114 : Upper (D 7) (R 7) [36,40,17,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22114 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22115 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 42 21 200 274 34 193 193 449), lower := (rows 37 42 21 200 274 34 64 128 256), losses := [] }

theorem u22115 : Upper (D 7) (R 7) [36,40,17,192,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22115 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22116 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 37 42 21 200 274 96 195 131 387), lower := (rows 37 42 21 200 274 96 64 128 256), losses := [] }

theorem u22116 : Upper (D 7) (R 7) [36,40,17,192,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22116 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22117 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 42 21 200 336 33 194 130 386), lower := (rows 37 42 21 200 336 33 64 128 256), losses := [] }

theorem u22117 : Upper (D 7) (R 7) [36,40,17,192,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22118 : Route 9 := (fun mask => (mask,id))

def c22118 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22118 : Upper (D 7) (R 7) [36,40,17,192,320,2] 13 := by
  apply FastRouting.sound _ _ [36,40,17,192,320,2] 13 (by decide) (choices 1) [1,2,128] r22118 c22118
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6666
  · exact u6667
  · exact u6668

def b22119 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 21 200 336 160 67 131 259), lower := (rows 37 42 21 200 336 160 64 128 256), losses := [] }

theorem u22119 : Upper (D 7) (R 7) [36,40,17,192,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22119 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22120 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 37 42 21 265 208 34 194 194 450), lower := (rows 37 42 21 265 208 34 64 128 256), losses := [] }

theorem u22120 : Upper (D 7) (R 7) [36,40,17,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22120 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22121 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 42 21 265 208 96 194 130 386), lower := (rows 37 42 21 265 208 96 64 128 256), losses := [] }

theorem u22121 : Upper (D 7) (R 7) [36,40,17,257,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22122 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 21 266 82 33 192 192 448), lower := (rows 37 42 21 266 82 33 64 128 256), losses := [] }

theorem u22122 : Upper (D 7) (R 7) [36,40,17,258,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22122 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22123 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 4, region := 37, targets := 2 }], pairs := [(0,1),(1,6),(2,1),(3,6)], upper := (rows 37 42 21 266 82 96 193 129 385), lower := (rows 37 42 21 266 82 96 64 128 256), losses := [] }

theorem u22123 : Upper (D 7) (R 7) [36,40,17,258,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22123 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22124 : Route 9 := (fun mask => (mask,id))

def c22124 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22124 : Upper (D 7) (R 7) [36,40,17,258,66,128] 13 := by
  apply FastRouting.sound _ _ [36,40,17,258,66,128] 13 (by decide) (choices 1) [1,128] r22124 c22124
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6669
  · exact u6670

def b22125 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 42 21 266 208 33 194 194 450), lower := (rows 37 42 21 266 208 33 64 128 256), losses := [] }

theorem u22125 : Upper (D 7) (R 7) [36,40,17,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22125 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22126 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 42, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 37 42 21 266 208 34 193 193 449), lower := (rows 37 42 21 266 208 34 64 128 256), losses := [] }

theorem u22126 : Upper (D 7) (R 7) [36,40,17,258,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22126 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22127 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 42 21 266 208 96 195 131 387), lower := (rows 37 42 21 266 208 96 64 128 256), losses := [] }

theorem u22127 : Upper (D 7) (R 7) [36,40,17,258,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22127 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22128 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 21 328 82 33 194 130 386), lower := (rows 37 42 21 328 82 33 64 128 256), losses := [] }

theorem u22128 : Upper (D 7) (R 7) [36,40,17,320,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22128 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22129 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 42 21 328 82 34 193 129 385), lower := (rows 37 42 21 328 82 34 64 128 256), losses := [] }

theorem u22129 : Upper (D 7) (R 7) [36,40,17,320,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22129 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22130 : Route 9 := (fun mask => (mask,id))

def c22130 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22130 : Upper (D 7) (R 7) [36,40,17,320,66,128] 13 := by
  apply FastRouting.sound _ _ [36,40,17,320,66,128] 13 (by decide) (choices 1) [1,2,128] r22130 c22130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6671
  · exact u6672
  · exact u6673

def b22131 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 42 21 328 146 33 194 194 450), lower := (rows 37 42 21 328 146 33 64 128 256), losses := [] }

theorem u22131 : Upper (D 7) (R 7) [36,40,17,320,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22131 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22132 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 42 21 328 146 34 193 193 449), lower := (rows 37 42 21 328 146 34 64 128 256), losses := [] }

theorem u22132 : Upper (D 7) (R 7) [36,40,17,320,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22132 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22133 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 149, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 37 42 21 328 146 96 195 131 387), lower := (rows 37 42 21 328 146 96 64 128 256), losses := [] }

theorem u22133 : Upper (D 7) (R 7) [36,40,17,320,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22133 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22134 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 42 21 328 146 160 67 195 323), lower := (rows 37 42 21 328 146 160 64 128 256), losses := [] }

theorem u22134 : Upper (D 7) (R 7) [36,40,17,320,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22134 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22135 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 42 21 328 208 33 194 130 386), lower := (rows 37 42 21 328 208 33 64 128 256), losses := [] }

theorem u22135 : Upper (D 7) (R 7) [36,40,17,320,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22136 : Route 9 := (fun mask => (mask,id))

def c22136 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22136 : Upper (D 7) (R 7) [36,40,17,320,192,2] 13 := by
  apply FastRouting.sound _ _ [36,40,17,320,192,2] 13 (by decide) (choices 1) [1,2,128] r22136 c22136
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6674
  · exact u6675
  · exact u6676

def b22137 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 42 21 328 208 160 67 131 259), lower := (rows 37 42 21 328 208 160 64 128 256), losses := [] }

theorem u22137 : Upper (D 7) (R 7) [36,40,17,320,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22137 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22138 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 22 73 145 34 448 448 448), lower := (rows 37 42 22 73 145 34 64 128 256), losses := [] }

theorem u22138 : Upper (D 7) (R 7) [36,40,18,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22138 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22139 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 37 42 22 73 145 96 450 386 386), lower := (rows 37 42 22 73 145 96 64 128 256), losses := [] }

theorem u22139 : Upper (D 7) (R 7) [36,40,18,65,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22139 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u22139
end Delivery.IrregularNine14.P07
