import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0007

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6000 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 70 44 152 276 33 65 194 322), lower := (rows 35 70 44 152 276 33 65 128 256), losses := [] }

theorem u6000 : Upper (D 6) (R 6) [34,68,40,144,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6000 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6001 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 66, targets := 33 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 70 44 152 276 33 66 193 321), lower := (rows 35 70 44 152 276 33 66 128 256), losses := [] }

theorem u6001 : Upper (D 6) (R 6) [34,68,40,144,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6001 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6002 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 70 44 152 336 33 65 134 262), lower := (rows 35 70 44 152 336 33 65 128 256), losses := [] }

theorem u6002 : Upper (D 6) (R 6) [34,68,40,144,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6002 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6003 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 66, targets := 33 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 70 44 152 336 33 66 133 261), lower := (rows 35 70 44 152 336 33 66 128 256), losses := [] }

theorem u6003 : Upper (D 6) (R 6) [34,68,40,144,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6003 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6004 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 441, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 70 44 152 336 33 68 131 259), lower := (rows 35 70 44 152 336 33 68 128 256), losses := [] }

theorem u6004 : Upper (D 6) (R 6) [34,68,40,144,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6004 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6005 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 132, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 35 70 133 25 336 40 66 164 292), lower := (rows 35 70 133 25 336 40 66 128 256), losses := [] }

theorem u6005 : Upper (D 6) (R 6) [34,68,129,17,320,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6005 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6006 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 313, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 133 25 336 40 68 162 290), lower := (rows 35 70 133 25 336 40 68 128 256), losses := [] }

theorem u6006 : Upper (D 6) (R 6) [34,68,129,17,320,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6006 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6007 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 132, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 35 70 133 25 336 40 96 134 262), lower := (rows 35 70 133 25 336 40 96 128 256), losses := [] }

theorem u6007 : Upper (D 6) (R 6) [34,68,129,17,320,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6007 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6008 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 312, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 70 133 26 52 288 65 200 328), lower := (rows 35 70 133 26 52 288 65 128 256), losses := [] }

theorem u6008 : Upper (D 6) (R 6) [34,68,129,18,36,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6008 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6009 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 74, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 133 26 52 288 72 193 321), lower := (rows 35 70 133 26 52 288 72 128 256), losses := [] }

theorem u6009 : Upper (D 6) (R 6) [34,68,129,18,36,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6009 [(5,8),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6010 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 428, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 35 70 133 28 81 288 66 168 296), lower := (rows 35 70 133 28 81 288 66 128 256), losses := [] }

theorem u6010 : Upper (D 6) (R 6) [34,68,129,20,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6010 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6011 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 90, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 133 28 81 288 72 162 290), lower := (rows 35 70 133 28 81 288 72 128 256), losses := [] }

theorem u6011 : Upper (D 6) (R 6) [34,68,129,20,65,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6011 [(5,8),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6012 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 142, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 133 28 81 288 96 138 266), lower := (rows 35 70 133 28 81 288 96 128 256), losses := [] }

theorem u6012 : Upper (D 6) (R 6) [34,68,129,20,65,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6012 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6013 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 133 28 112 288 65 138 266), lower := (rows 35 70 133 28 112 288 65 128 256), losses := [] }

theorem u6013 : Upper (D 6) (R 6) [34,68,129,20,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6013 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6014 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 66, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 133 28 112 288 66 137 265), lower := (rows 35 70 133 28 112 288 66 128 256), losses := [] }

theorem u6014 : Upper (D 6) (R 6) [34,68,129,20,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6014 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6015 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 289, targets := 4 }], pairs := [(0,2)], upper := (rows 35 70 133 28 112 288 72 131 259), lower := (rows 35 70 133 28 112 288 72 128 256), losses := [] }

theorem u6015 : Upper (D 6) (R 6) [34,68,129,20,96,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6015 [(5,8),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6016 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 428, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 35 70 133 44 81 288 66 152 280), lower := (rows 35 70 133 44 81 288 66 128 256), losses := [] }

theorem u6016 : Upper (D 6) (R 6) [34,68,129,36,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6016 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6017 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 305, targets := 4 }], pairs := [(0,2)], upper := (rows 35 70 133 44 81 288 72 146 274), lower := (rows 35 70 133 44 81 288 72 128 256), losses := [] }

theorem u6017 : Upper (D 6) (R 6) [34,68,129,36,65,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6017 [(5,8),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6018 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 80, targets := 2 }], pairs := [(4,1)], upper := (rows 35 70 133 44 81 288 80 138 266), lower := (rows 35 70 133 44 81 288 80 128 256), losses := [] }

theorem u6018 : Upper (D 6) (R 6) [34,68,129,36,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6018 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6019 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 312, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 70 133 44 88 288 65 146 274), lower := (rows 35 70 133 44 88 288 65 128 256), losses := [] }

theorem u6019 : Upper (D 6) (R 6) [34,68,129,36,72,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6019 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6020 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 66, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 133 44 88 288 66 145 273), lower := (rows 35 70 133 44 88 288 66 128 256), losses := [] }

theorem u6020 : Upper (D 6) (R 6) [34,68,129,36,72,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6020 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6021 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 82, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 133 44 88 288 80 131 259), lower := (rows 35 70 133 44 88 288 80 128 256), losses := [] }

theorem u6021 : Upper (D 6) (R 6) [34,68,129,36,72,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6021 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6022 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 428, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 35 70 133 56 81 288 66 140 268), lower := (rows 35 70 133 56 81 288 66 128 256), losses := [] }

theorem u6022 : Upper (D 6) (R 6) [34,68,129,48,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6022 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6023 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 313, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 133 56 81 288 68 138 266), lower := (rows 35 70 133 56 81 288 68 128 256), losses := [] }

theorem u6023 : Upper (D 6) (R 6) [34,68,129,48,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6023 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6024 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 88, targets := 2 }], pairs := [(3,1)], upper := (rows 35 70 133 56 81 288 72 134 262), lower := (rows 35 70 133 56 81 288 72 128 256), losses := [] }

theorem u6024 : Upper (D 6) (R 6) [34,68,129,48,65,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6024 [(5,8),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6025 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 35 70 133 73 276 48 66 168 296), lower := (rows 35 70 133 73 276 48 66 128 256), losses := [] }

theorem u6025 : Upper (D 6) (R 6) [34,68,129,65,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6025 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6026 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 73 276 48 72 162 290), lower := (rows 35 70 133 73 276 48 72 128 256), losses := [] }

theorem u6026 : Upper (D 6) (R 6) [34,68,129,65,260,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6026 [(5,4),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6027 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 134, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 133 73 276 48 96 138 266), lower := (rows 35 70 133 73 276 48 96 128 256), losses := [] }

theorem u6027 : Upper (D 6) (R 6) [34,68,129,65,260,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6027 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6028 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 66, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 133 104 273 48 66 140 268), lower := (rows 35 70 133 104 273 48 66 128 256), losses := [] }

theorem u6028 : Upper (D 6) (R 6) [34,68,129,96,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6028 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6029 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 313, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 133 104 273 48 68 138 266), lower := (rows 35 70 133 104 273 48 68 128 256), losses := [] }

theorem u6029 : Upper (D 6) (R 6) [34,68,129,96,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6029 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6030 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 104 273 48 72 134 262), lower := (rows 35 70 133 104 273 48 72 128 256), losses := [] }

theorem u6030 : Upper (D 6) (R 6) [34,68,129,96,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6030 [(5,4),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6031 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 312, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 70 133 104 276 48 65 138 266), lower := (rows 35 70 133 104 276 48 65 128 256), losses := [] }

theorem u6031 : Upper (D 6) (R 6) [34,68,129,96,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6031 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6032 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 66, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 133 104 276 48 66 137 265), lower := (rows 35 70 133 104 276 48 66 128 256), losses := [] }

theorem u6032 : Upper (D 6) (R 6) [34,68,129,96,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6032 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6033 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 104 276 48 72 131 259), lower := (rows 35 70 133 104 276 48 72 128 256), losses := [] }

theorem u6033 : Upper (D 6) (R 6) [34,68,129,96,260,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6033 [(5,4),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6034 : PairBound 9 := { available := 96, camps := [], pairs := [(3,1),(4,1)], upper := (rows 35 70 134 25 276 40 65 224 352), lower := (rows 35 70 134 25 276 40 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 22 105 73 235 363), good := (rows 505 500 404 505 276 488 489 128 256) }] }

theorem u6034 : Upper (D 6) (R 6) [34,68,130,17,260,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6034 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6035 : Route 9 := (fun mask => (mask,id))

def c6035 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6035 : Upper (D 6) (R 6) [34,68,130,17,260,8,32] 13 := by
  apply FastRouting.sound _ _ [34,68,130,17,260,8,32] 13 (by decide) (choices 1) [1,64] r6035 c6035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u449
  · exact u450

def b6036 : PairBound 9 := { available := 40, camps := [{ cop := 7, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 134 25 336 33 68 168 296), lower := (rows 35 70 134 25 336 33 68 128 256), losses := [] }

theorem u6036 : Upper (D 6) (R 6) [34,68,130,17,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6036 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6037 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 134 25 336 33 72 164 292), lower := (rows 35 70 134 25 336 33 72 128 256), losses := [] }

theorem u6037 : Upper (D 6) (R 6) [34,68,130,17,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6037 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6038 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 33, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 70 134 25 336 33 96 140 268), lower := (rows 35 70 134 25 336 33 96 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 24 32 97 136 264), good := (rows 98 70 134 478 336 96 96 128 256) }] }

theorem u6038 : Upper (D 6) (R 6) [34,68,130,17,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6038 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6039 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 132, targets := 1 },{ cop := 0, region := 132, targets := 64 }], pairs := [(2,0),(2,6)], upper := (rows 35 70 134 25 336 40 65 164 292), lower := (rows 35 70 134 25 336 40 65 128 256), losses := [] }

theorem u6039 : Upper (D 6) (R 6) [34,68,130,17,320,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6039 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6040 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 70, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 134 25 336 40 68 161 289), lower := (rows 35 70 134 25 336 40 68 128 256), losses := [] }

theorem u6040 : Upper (D 6) (R 6) [34,68,130,17,320,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6040 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6041 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 132, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 35 70 134 25 336 40 96 133 261), lower := (rows 35 70 134 25 336 40 96 128 256), losses := [] }

theorem u6041 : Upper (D 6) (R 6) [34,68,130,17,320,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6041 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6042 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 134 28 81 288 65 168 296), lower := (rows 35 70 134 28 81 288 65 128 256), losses := [] }

theorem u6042 : Upper (D 6) (R 6) [34,68,130,20,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6042 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6043 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 289, targets := 4 }], pairs := [(0,2)], upper := (rows 35 70 134 28 81 288 72 161 289), lower := (rows 35 70 134 28 81 288 72 128 256), losses := [] }

theorem u6043 : Upper (D 6) (R 6) [34,68,130,20,65,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6043 [(5,8),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6044 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 142, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 134 28 81 288 96 137 265), lower := (rows 35 70 134 28 81 288 96 128 256), losses := [] }

theorem u6044 : Upper (D 6) (R 6) [34,68,130,20,65,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6044 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6045 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 134 28 112 288 65 137 265), lower := (rows 35 70 134 28 112 288 65 128 256), losses := [] }

theorem u6045 : Upper (D 6) (R 6) [34,68,130,20,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6045 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6046 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 289, targets := 4 }], pairs := [(0,2)], upper := (rows 35 70 134 28 112 288 72 129 257), lower := (rows 35 70 134 28 112 288 72 128 256), losses := [] }

theorem u6046 : Upper (D 6) (R 6) [34,68,130,20,96,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6046 [(5,8),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6047 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 134 44 81 288 65 152 280), lower := (rows 35 70 134 44 81 288 65 128 256), losses := [] }

theorem u6047 : Upper (D 6) (R 6) [34,68,130,36,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6047 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6048 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 305, targets := 4 }], pairs := [(0,2)], upper := (rows 35 70 134 44 81 288 72 145 273), lower := (rows 35 70 134 44 81 288 72 128 256), losses := [] }

theorem u6048 : Upper (D 6) (R 6) [34,68,130,36,65,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6048 [(5,8),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6049 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 80, targets := 2 }], pairs := [(4,1)], upper := (rows 35 70 134 44 81 288 80 137 265), lower := (rows 35 70 134 44 81 288 80 128 256), losses := [] }

theorem u6049 : Upper (D 6) (R 6) [34,68,130,36,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6049 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6050 : PairBound 9 := { available := 17, camps := [], pairs := [(3,1),(4,1)], upper := (rows 35 70 134 44 88 288 65 145 273), lower := (rows 35 70 134 44 88 288 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 14 19 371 65 193 321), good := (rows 505 508 188 44 504 288 497 128 288) }] }

theorem u6050 : Upper (D 6) (R 6) [34,68,130,36,72,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6050 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6051 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 82, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 134 44 88 288 80 129 257), lower := (rows 35 70 134 44 88 288 80 128 256), losses := [] }

theorem u6051 : Upper (D 6) (R 6) [34,68,130,36,72,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6051 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6052 : PairBound 9 := { available := 72, camps := [], pairs := [(1,0),(2,0)], upper := (rows 35 70 134 44 273 48 65 200 328), lower := (rows 35 70 134 44 273 48 65 128 256), losses := [{ target := 0, region := (rows 0 66 70 9 16 48 64 192 320), good := (rows 46 454 134 44 312 48 462 128 256) }] }

theorem u6052 : Upper (D 6) (R 6) [34,68,130,36,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6052 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6053 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 305, targets := 4 }], pairs := [(0,2)], upper := (rows 35 70 134 44 273 48 72 193 321), lower := (rows 35 70 134 44 273 48 72 128 256), losses := [] }

theorem u6053 : Upper (D 6) (R 6) [34,68,130,36,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6053 [(5,4),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6054 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 70 134 56 81 288 65 140 268), lower := (rows 35 70 134 56 81 288 65 128 256), losses := [] }

theorem u6054 : Upper (D 6) (R 6) [34,68,130,48,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6054 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6055 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 70, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 134 56 81 288 68 137 265), lower := (rows 35 70 134 56 81 288 68 128 256), losses := [] }

theorem u6055 : Upper (D 6) (R 6) [34,68,130,48,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6055 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6056 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 88, targets := 2 }], pairs := [(3,1)], upper := (rows 35 70 134 56 81 288 72 133 261), lower := (rows 35 70 134 56 81 288 72 128 256), losses := [] }

theorem u6056 : Upper (D 6) (R 6) [34,68,130,48,65,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6056 [(5,8),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6057 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 33, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 70 134 56 336 33 65 140 268), lower := (rows 35 70 134 56 336 33 65 128 256), losses := [{ target := 0, region := (rows 0 82 95 9 82 32 64 233 361), good := (rows 446 470 150 446 470 428 478 128 256) }] }

theorem u6057 : Upper (D 6) (R 6) [34,68,130,48,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6057 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6058 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 134 56 336 33 68 137 265), lower := (rows 35 70 134 56 336 33 68 128 256), losses := [] }

theorem u6058 : Upper (D 6) (R 6) [34,68,130,48,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6059 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 134 56 336 33 72 133 261), lower := (rows 35 70 134 56 336 33 72 128 256), losses := [] }

theorem u6059 : Upper (D 6) (R 6) [34,68,130,48,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6059 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u6059
end Delivery.IrregularNine14.P06
