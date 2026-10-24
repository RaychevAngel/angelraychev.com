import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0109
import IrregularNine14P06C0110

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22080 : PairBound 9 := { available := 22, camps := [{ cop := 5, region := 12, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 44 273 96 86 150 278), lower := (rows 35 131 76 44 273 96 64 128 256), losses := [] }

theorem u22080 : Upper (D 6) (R 6) [34,129,72,36,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22080 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22081 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 44 274 33 84 212 340), lower := (rows 35 131 76 44 274 33 64 128 256), losses := [] }

theorem u22081 : Upper (D 6) (R 6) [34,129,72,36,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22081 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22082 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 131 76 44 274 36 81 209 337), lower := (rows 35 131 76 44 274 36 64 128 256), losses := [] }

theorem u22082 : Upper (D 6) (R 6) [34,129,72,36,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22082 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22083 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 76 44 274 48 69 197 325), lower := (rows 35 131 76 44 274 48 64 128 256), losses := [] }

theorem u22083 : Upper (D 6) (R 6) [34,129,72,36,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22083 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22084 : PairBound 9 := { available := 21, camps := [{ cop := 5, region := 12, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 44 274 96 85 149 277), lower := (rows 35 131 76 44 274 96 64 128 256), losses := [] }

theorem u22084 : Upper (D 6) (R 6) [34,129,72,36,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22084 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22085 : PairBound 9 := { available := 82, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 44 276 33 82 210 338), lower := (rows 35 131 76 44 276 33 64 128 256), losses := [] }

theorem u22085 : Upper (D 6) (R 6) [34,129,72,36,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22085 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22086 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 44 276 34 81 209 337), lower := (rows 35 131 76 44 276 34 64 128 256), losses := [] }

theorem u22086 : Upper (D 6) (R 6) [34,129,72,36,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22086 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22087 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 76 44 276 48 67 195 323), lower := (rows 35 131 76 44 276 48 64 128 256), losses := [] }

theorem u22087 : Upper (D 6) (R 6) [34,129,72,36,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22087 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22088 : PairBound 9 := { available := 19, camps := [{ cop := 5, region := 12, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 44 276 96 83 147 275), lower := (rows 35 131 76 44 276 96 64 128 256), losses := [] }

theorem u22088 : Upper (D 6) (R 6) [34,129,72,36,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22088 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22089 : PairBound 9 := { available := 22, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 44 336 33 86 150 278), lower := (rows 35 131 76 44 336 33 64 128 256), losses := [] }

theorem u22089 : Upper (D 6) (R 6) [34,129,72,36,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22089 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22090 : PairBound 9 := { available := 21, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 44 336 34 85 149 277), lower := (rows 35 131 76 44 336 34 64 128 256), losses := [] }

theorem u22090 : Upper (D 6) (R 6) [34,129,72,36,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22090 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22091 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 131 76 44 336 36 83 147 275), lower := (rows 35 131 76 44 336 36 64 128 256), losses := [] }

theorem u22091 : Upper (D 6) (R 6) [34,129,72,36,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22091 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22092 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 76 44 336 48 71 135 263), lower := (rows 35 131 76 44 336 48 64 128 256), losses := [] }

theorem u22092 : Upper (D 6) (R 6) [34,129,72,36,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22092 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22093 : PairBound 9 := { available := 324, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 56 21 34 324 452 324), lower := (rows 35 131 76 56 21 34 64 128 256), losses := [] }

theorem u22093 : Upper (D 6) (R 6) [34,129,72,48,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22093 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22094 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 131 76 56 21 36 322 450 322), lower := (rows 35 131 76 56 21 36 64 128 256), losses := [] }

theorem u22094 : Upper (D 6) (R 6) [34,129,72,48,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22094 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22095 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 386, targets := 32 },{ cop := 4, region := 386, targets := 64 }], pairs := [(1,5),(1,6),(3,0)], upper := (rows 35 131 76 56 21 96 326 390 262), lower := (rows 35 131 76 56 21 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 100 64 128 256), good := (rows 34 130 108 56 60 96 96 128 256) }] }

theorem u22095 : Upper (D 6) (R 6) [34,129,72,48,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22095 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22096 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 76 56 21 288 70 198 326), lower := (rows 35 131 76 56 21 288 64 128 256), losses := [{ target := 5, region := (rows 1 18 12 8 16 0 88 152 280), good := (rows 3 131 460 478 471 256 64 128 256) }] }

theorem u22096 : Upper (D 6) (R 6) [34,129,72,48,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22096 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22097 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 131 76 56 22 33 324 452 324), lower := (rows 35 131 76 56 22 33 64 128 256), losses := [] }

theorem u22097 : Upper (D 6) (R 6) [34,129,72,48,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22097 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22098 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 450, targets := 36 },{ cop := 4, region := 40, targets := 1 }], pairs := [(1,2),(1,5),(3,0)], upper := (rows 35 131 76 56 22 36 321 449 321), lower := (rows 35 131 76 56 22 36 64 128 256), losses := [] }

theorem u22098 : Upper (D 6) (R 6) [34,129,72,48,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22098 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22099 : PairBound 9 := { available := 261, camps := [], pairs := [(0,2),(3,0),(3,1)], upper := (rows 35 131 76 56 22 96 325 389 261), lower := (rows 35 131 76 56 22 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 100 64 128 256), good := (rows 34 130 108 56 62 96 96 128 256) },{ target := 1, region := (rows 1 0 4 24 16 100 64 128 256), good := (rows 33 129 108 56 60 96 96 128 256) },{ target := 2, region := (rows 17 2 0 24 16 100 64 128 256), good := (rows 35 131 104 57 59 96 96 128 256) }] }

theorem u22099 : Upper (D 6) (R 6) [34,129,72,48,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22099 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22100 : Route 9 := (fun mask => (mask,id))

def c22100 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22100 : Upper (D 6) (R 6) [34,129,72,48,6,256] 13 := by
  apply FastRouting.sound _ _ [34,129,72,48,6,256] 13 (by decide) (choices 1) [1,4] r22100 c22100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6574
  · exact u6575

def b22101 : PairBound 9 := { available := 260, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 56 81 34 324 388 260), lower := (rows 35 131 76 56 81 34 64 128 256), losses := [] }

theorem u22101 : Upper (D 6) (R 6) [34,129,72,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22101 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22102 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 56 81 36 326 390 262), lower := (rows 35 131 76 56 81 36 64 128 256), losses := [] }

theorem u22102 : Upper (D 6) (R 6) [34,129,72,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22102 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22103 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 76 56 81 288 70 134 262), lower := (rows 35 131 76 56 81 288 64 128 256), losses := [] }

theorem u22103 : Upper (D 6) (R 6) [34,129,72,48,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22103 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22104 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 131 76 56 82 33 324 388 260), lower := (rows 35 131 76 56 82 33 64 128 256), losses := [] }

theorem u22104 : Upper (D 6) (R 6) [34,129,72,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22104 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22105 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 56 82 36 325 389 261), lower := (rows 35 131 76 56 82 36 64 128 256), losses := [] }

theorem u22105 : Upper (D 6) (R 6) [34,129,72,48,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22105 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22106 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 76 56 82 288 69 133 261), lower := (rows 35 131 76 56 82 288 64 128 256), losses := [] }

theorem u22106 : Upper (D 6) (R 6) [34,129,72,48,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22106 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22107 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 56 273 34 68 196 324), lower := (rows 35 131 76 56 273 34 64 128 256), losses := [] }

theorem u22107 : Upper (D 6) (R 6) [34,129,72,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22107 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22108 : Route 9 := (fun mask => (mask,id))

def c22108 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22108 : Upper (D 6) (R 6) [34,129,72,48,257,4] 13 := by
  apply FastRouting.sound _ _ [34,129,72,48,257,4] 13 (by decide) (choices 1) [2,4] r22108 c22108
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6576
  · exact u6577

def r22109 : Route 9 := (fun mask => (mask,id))

def c22109 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22109 : Upper (D 6) (R 6) [34,129,72,48,257,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,48,257,64] 13 (by decide) (choices 1) [2,4] r22109 c22109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6578
  · exact u6579

def b22110 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 131 76 56 274 33 68 196 324), lower := (rows 35 131 76 56 274 33 64 128 256), losses := [] }

theorem u22110 : Upper (D 6) (R 6) [34,129,72,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22110 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22111 : Route 9 := (fun mask => (mask,id))

def c22111 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22111 : Upper (D 6) (R 6) [34,129,72,48,258,4] 13 := by
  apply FastRouting.sound _ _ [34,129,72,48,258,4] 13 (by decide) (choices 1) [1,4] r22111 c22111
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6580
  · exact u6581

def r22112 : Route 9 := (fun mask => (mask,id))

def c22112 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22112 : Upper (D 6) (R 6) [34,129,72,48,258,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,48,258,64] 13 (by decide) (choices 1) [1,4] r22112 c22112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6582
  · exact u6583

def b22113 : PairBound 9 := { available := 70, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 56 276 33 70 198 326), lower := (rows 35 131 76 56 276 33 64 128 256), losses := [] }

theorem u22113 : Upper (D 6) (R 6) [34,129,72,48,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22113 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22114 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 56 276 34 69 197 325), lower := (rows 35 131 76 56 276 34 64 128 256), losses := [] }

theorem u22114 : Upper (D 6) (R 6) [34,129,72,48,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22115 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 131 76 56 276 36 67 195 323), lower := (rows 35 131 76 56 276 36 64 128 256), losses := [] }

theorem u22115 : Upper (D 6) (R 6) [34,129,72,48,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22115 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22116 : PairBound 9 := { available := 7, camps := [], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 131 76 56 276 96 71 135 263), lower := (rows 35 131 76 56 276 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 100 64 128 256), good := (rows 34 130 108 56 316 96 96 128 256) },{ target := 1, region := (rows 1 0 4 24 16 100 64 128 256), good := (rows 33 129 108 56 316 96 96 128 256) },{ target := 2, region := (rows 1 2 0 24 16 100 64 128 256), good := (rows 35 131 104 56 312 96 96 128 256) }] }

theorem u22116 : Upper (D 6) (R 6) [34,129,72,48,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22116 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22117 : PairBound 9 := { available := 6, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 56 336 33 70 134 262), lower := (rows 35 131 76 56 336 33 64 128 256), losses := [] }

theorem u22117 : Upper (D 6) (R 6) [34,129,72,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22117 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22118 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 56 336 34 69 133 261), lower := (rows 35 131 76 56 336 34 64 128 256), losses := [] }

theorem u22118 : Upper (D 6) (R 6) [34,129,72,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22118 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22119 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 56 336 36 71 135 263), lower := (rows 35 131 76 56 336 36 64 128 256), losses := [] }

theorem u22119 : Upper (D 6) (R 6) [34,129,72,48,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22119 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22120 : Route 9 := (fun mask => (mask,id))

def c22120 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22120 : Upper (D 6) (R 6) [34,129,72,257,6,4] 13 := by
  apply FastRouting.sound _ _ [34,129,72,257,6,4] 13 (by decide) (choices 1) [16,32] r22120 c22120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6584
  · exact u6585

def b22121 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 76 265 22 48 100 228 356), lower := (rows 35 131 76 265 22 48 64 128 256), losses := [] }

theorem u22121 : Upper (D 6) (R 6) [34,129,72,257,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22121 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22122 : Route 9 := (fun mask => (mask,id))

def c22122 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22122 : Upper (D 6) (R 6) [34,129,72,257,6,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,257,6,64] 13 (by decide) (choices 1) [4,16,32] r22122 c22122
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6586
  · exact u6587
  · exact u6588

def b22123 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 265 52 34 84 212 340), lower := (rows 35 131 76 265 52 34 64 128 256), losses := [] }

theorem u22123 : Upper (D 6) (R 6) [34,129,72,257,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22123 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22124 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 131 76 265 52 36 82 210 338), lower := (rows 35 131 76 265 52 36 64 128 256), losses := [] }

theorem u22124 : Upper (D 6) (R 6) [34,129,72,257,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22125 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 76 265 52 48 70 198 326), lower := (rows 35 131 76 265 52 48 64 128 256), losses := [] }

theorem u22125 : Upper (D 6) (R 6) [34,129,72,257,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22125 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22126 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 76 265 52 96 86 150 278), lower := (rows 35 131 76 265 52 96 64 128 256), losses := [] }

theorem u22126 : Upper (D 6) (R 6) [34,129,72,257,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22126 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22127 : Route 9 := (fun mask => (mask,id))

def c22127 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22127 : Upper (D 6) (R 6) [34,129,72,257,66,4] 13 := by
  apply FastRouting.sound _ _ [34,129,72,257,66,4] 13 (by decide) (choices 1) [4,16,32] r22127 c22127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6589
  · exact u6590
  · exact u6591

def b22128 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 76 265 82 48 100 164 292), lower := (rows 35 131 76 265 82 48 64 128 256), losses := [] }

theorem u22128 : Upper (D 6) (R 6) [34,129,72,257,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22128 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22129 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 265 112 34 84 148 276), lower := (rows 35 131 76 265 112 34 64 128 256), losses := [] }

theorem u22129 : Upper (D 6) (R 6) [34,129,72,257,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22129 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22130 : Route 9 := (fun mask => (mask,id))

def c22130 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22130 : Upper (D 6) (R 6) [34,129,72,257,96,4] 13 := by
  apply FastRouting.sound _ _ [34,129,72,257,96,4] 13 (by decide) (choices 1) [2,4,16] r22130 c22130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6592
  · exact u6593
  · exact u6594

def b22131 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 76 265 112 48 70 134 262), lower := (rows 35 131 76 265 112 48 64 128 256), losses := [] }

theorem u22131 : Upper (D 6) (R 6) [34,129,72,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22131 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22132 : Route 9 := (fun mask => (mask,id))

def c22132 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22132 : Upper (D 6) (R 6) [34,129,72,258,5,4] 13 := by
  apply FastRouting.sound _ _ [34,129,72,258,5,4] 13 (by decide) (choices 1) [16,32] r22132 c22132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6595
  · exact u6596

def b22133 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 76 266 21 48 100 228 356), lower := (rows 35 131 76 266 21 48 64 128 256), losses := [] }

theorem u22133 : Upper (D 6) (R 6) [34,129,72,258,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22133 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22134 : Route 9 := (fun mask => (mask,id))

def c22134 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22134 : Upper (D 6) (R 6) [34,129,72,258,5,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,258,5,64] 13 (by decide) (choices 1) [4,16,32] r22134 c22134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6597
  · exact u6598
  · exact u6599

def b22135 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 266 52 33 84 212 340), lower := (rows 35 131 76 266 52 33 64 128 256), losses := [] }

theorem u22135 : Upper (D 6) (R 6) [34,129,72,258,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22135 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22136 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 131 76 266 52 36 81 209 337), lower := (rows 35 131 76 266 52 36 64 128 256), losses := [] }

theorem u22136 : Upper (D 6) (R 6) [34,129,72,258,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22136 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22137 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 76 266 52 48 69 197 325), lower := (rows 35 131 76 266 52 48 64 128 256), losses := [] }

theorem u22137 : Upper (D 6) (R 6) [34,129,72,258,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22137 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22138 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 76 266 52 96 85 149 277), lower := (rows 35 131 76 266 52 96 64 128 256), losses := [] }

theorem u22138 : Upper (D 6) (R 6) [34,129,72,258,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22138 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22139 : Route 9 := (fun mask => (mask,id))

def c22139 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22139 : Upper (D 6) (R 6) [34,129,72,258,65,4] 13 := by
  apply FastRouting.sound _ _ [34,129,72,258,65,4] 13 (by decide) (choices 1) [4,16,32] r22139 c22139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6600
  · exact u6601
  · exact u6602

#print axioms u22139
end Delivery.IrregularNine14.P06
