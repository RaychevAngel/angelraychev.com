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

def b6060 : PairBound 9 := { available := 40, camps := [{ cop := 7, region := 70, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 134 73 273 48 68 168 296), lower := (rows 35 70 134 73 273 48 68 128 256), losses := [] }

theorem u6060 : Upper (D 6) (R 6) [34,68,130,65,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6060 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6061 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 72, targets := 2 }], pairs := [(3,1)], upper := (rows 35 70 134 73 273 48 72 164 292), lower := (rows 35 70 134 73 273 48 72 128 256), losses := [] }

theorem u6061 : Upper (D 6) (R 6) [34,68,130,65,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6061 [(5,4),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6062 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 134, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 134 73 273 48 96 140 268), lower := (rows 35 70 134 73 273 48 96 128 256), losses := [] }

theorem u6062 : Upper (D 6) (R 6) [34,68,130,65,257,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6062 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6063 : PairBound 9 := { available := 40, camps := [{ cop := 7, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 134 88 273 33 68 168 296), lower := (rows 35 70 134 88 273 33 68 128 256), losses := [] }

theorem u6063 : Upper (D 6) (R 6) [34,68,130,80,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6064 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 134 88 273 33 72 164 292), lower := (rows 35 70 134 88 273 33 72 128 256), losses := [] }

theorem u6064 : Upper (D 6) (R 6) [34,68,130,80,257,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6064 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6065 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 134, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 134 88 273 33 96 140 268), lower := (rows 35 70 134 88 273 33 96 128 256), losses := [] }

theorem u6065 : Upper (D 6) (R 6) [34,68,130,80,257,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6065 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6066 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 134, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 134 88 304 33 65 140 268), lower := (rows 35 70 134 88 304 33 65 128 256), losses := [] }

theorem u6066 : Upper (D 6) (R 6) [34,68,130,80,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6066 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6067 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 134 88 304 33 68 137 265), lower := (rows 35 70 134 88 304 33 68 128 256), losses := [] }

theorem u6067 : Upper (D 6) (R 6) [34,68,130,80,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6067 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6068 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 134 88 304 33 72 133 261), lower := (rows 35 70 134 88 304 33 72 128 256), losses := [] }

theorem u6068 : Upper (D 6) (R 6) [34,68,130,80,288,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6068 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6069 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 134, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 134 104 273 48 65 140 268), lower := (rows 35 70 134 104 273 48 65 128 256), losses := [] }

theorem u6069 : Upper (D 6) (R 6) [34,68,130,96,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6069 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6070 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 70, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 134 104 273 48 68 137 265), lower := (rows 35 70 134 104 273 48 68 128 256), losses := [] }

theorem u6070 : Upper (D 6) (R 6) [34,68,130,96,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6070 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6071 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 134 104 273 48 72 133 261), lower := (rows 35 70 134 104 273 48 72 128 256), losses := [] }

theorem u6071 : Upper (D 6) (R 6) [34,68,130,96,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6071 [(5,4),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6072 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 66, targets := 33 },{ cop := 3, region := 164, targets := 2 }], pairs := [(1,0),(1,5),(2,1)], upper := (rows 35 70 140 25 336 33 66 164 292), lower := (rows 35 70 140 25 336 33 66 128 256), losses := [] }

theorem u6072 : Upper (D 6) (R 6) [34,68,136,17,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6072 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6073 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 313, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 70 140 25 336 33 68 162 290), lower := (rows 35 70 140 25 336 33 68 128 256), losses := [] }

theorem u6073 : Upper (D 6) (R 6) [34,68,136,17,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6073 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6074 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 272, targets := 33 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(4,0),(4,5)], upper := (rows 35 70 140 25 336 33 96 134 262), lower := (rows 35 70 140 25 336 33 96 128 256), losses := [] }

theorem u6074 : Upper (D 6) (R 6) [34,68,136,17,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6074 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6075 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 289, targets := 4 }], pairs := [(0,2),(4,1)], upper := (rows 35 70 140 26 52 288 65 193 321), lower := (rows 35 70 140 26 52 288 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 18 355 65 193 321), good := (rows 497 500 140 56 52 288 481 128 288) }] }

theorem u6075 : Upper (D 6) (R 6) [34,68,136,18,36,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6075 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6076 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 33, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 70 140 26 276 33 65 224 352), lower := (rows 35 70 140 26 276 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 26 97 97 227 355), good := (rows 497 500 156 412 276 481 481 128 256) }] }

theorem u6076 : Upper (D 6) (R 6) [34,68,136,18,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6076 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6077 : Route 9 := (fun mask => (mask,id))

def c6077 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6077 : Upper (D 6) (R 6) [34,68,136,18,260,1,32] 13 := by
  apply FastRouting.sound _ _ [34,68,136,18,260,1,32] 13 (by decide) (choices 1) [1,64] r6077 c6077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u451
  · exact u452

def b6078 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 33, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 70 140 26 304 33 65 196 324), lower := (rows 35 70 140 26 304 33 65 128 256), losses := [{ target := 0, region := (rows 0 66 79 73 17 32 64 194 322), good := (rows 446 462 140 414 304 60 478 128 256) }] }

theorem u6078 : Upper (D 6) (R 6) [34,68,136,18,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6078 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6079 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 313, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 70 140 26 304 33 68 193 321), lower := (rows 35 70 140 26 304 33 68 128 256), losses := [] }

theorem u6079 : Upper (D 6) (R 6) [34,68,136,18,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6079 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6080 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 272, targets := 33 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(4,0),(4,5)], upper := (rows 35 70 140 56 276 33 65 194 322), lower := (rows 35 70 140 56 276 33 65 128 256), losses := [] }

theorem u6080 : Upper (D 6) (R 6) [34,68,136,48,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6080 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6081 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 66, targets := 33 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 70 140 56 276 33 66 193 321), lower := (rows 35 70 140 56 276 33 66 128 256), losses := [] }

theorem u6081 : Upper (D 6) (R 6) [34,68,136,48,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6081 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6082 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 272, targets := 33 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(4,0),(4,5)], upper := (rows 35 70 140 56 336 33 65 134 262), lower := (rows 35 70 140 56 336 33 65 128 256), losses := [] }

theorem u6082 : Upper (D 6) (R 6) [34,68,136,48,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6082 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6083 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 66, targets := 33 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 70 140 56 336 33 66 133 261), lower := (rows 35 70 140 56 336 33 66 128 256), losses := [] }

theorem u6083 : Upper (D 6) (R 6) [34,68,136,48,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6083 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6084 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 313, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 70 140 56 336 33 68 131 259), lower := (rows 35 70 140 56 336 33 68 128 256), losses := [] }

theorem u6084 : Upper (D 6) (R 6) [34,68,136,48,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6084 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6085 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 66, targets := 33 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 70 164 25 276 33 66 200 328), lower := (rows 35 70 164 25 276 33 66 128 256), losses := [] }

theorem u6085 : Upper (D 6) (R 6) [34,68,160,17,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6085 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6086 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 272, targets := 33 }], pairs := [(4,0),(4,5)], upper := (rows 35 70 164 25 276 33 72 194 322), lower := (rows 35 70 164 25 276 33 72 128 256), losses := [] }

theorem u6086 : Upper (D 6) (R 6) [34,68,160,17,260,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6086 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6087 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 272, targets := 33 }], pairs := [(4,0),(4,5)], upper := (rows 35 70 164 25 276 40 65 194 322), lower := (rows 35 70 164 25 276 40 65 128 256), losses := [] }

theorem u6087 : Upper (D 6) (R 6) [34,68,160,17,260,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6087 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6088 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 66, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 164 25 276 40 66 193 321), lower := (rows 35 70 164 25 276 40 66 128 256), losses := [] }

theorem u6088 : Upper (D 6) (R 6) [34,68,160,17,260,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6088 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6089 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 66, targets := 33 },{ cop := 3, region := 164, targets := 2 }], pairs := [(1,0),(1,5),(2,1)], upper := (rows 35 70 164 25 336 33 66 140 268), lower := (rows 35 70 164 25 336 33 66 128 256), losses := [] }

theorem u6089 : Upper (D 6) (R 6) [34,68,160,17,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6089 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6090 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 313, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 70 164 25 336 33 68 138 266), lower := (rows 35 70 164 25 336 33 68 128 256), losses := [] }

theorem u6090 : Upper (D 6) (R 6) [34,68,160,17,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6090 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6091 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 272, targets := 33 }], pairs := [(4,0),(4,5)], upper := (rows 35 70 164 25 336 33 72 134 262), lower := (rows 35 70 164 25 336 33 72 128 256), losses := [] }

theorem u6091 : Upper (D 6) (R 6) [34,68,160,17,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6091 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6092 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 272, targets := 33 }], pairs := [(4,0),(4,5)], upper := (rows 35 70 164 25 336 40 65 134 262), lower := (rows 35 70 164 25 336 40 65 128 256), losses := [] }

theorem u6092 : Upper (D 6) (R 6) [34,68,160,17,320,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6092 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6093 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 132, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 35 70 164 25 336 40 66 133 261), lower := (rows 35 70 164 25 336 40 66 128 256), losses := [] }

theorem u6093 : Upper (D 6) (R 6) [34,68,160,17,320,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6093 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6094 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 313, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 164 25 336 40 68 131 259), lower := (rows 35 70 164 25 336 40 68 128 256), losses := [] }

theorem u6094 : Upper (D 6) (R 6) [34,68,160,17,320,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6094 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6095 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 280, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 70 164 26 276 33 65 200 328), lower := (rows 35 70 164 26 276 33 65 128 256), losses := [] }

theorem u6095 : Upper (D 6) (R 6) [34,68,160,18,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6095 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6096 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 74, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 164 26 276 33 72 193 321), lower := (rows 35 70 164 26 276 33 72 128 256), losses := [] }

theorem u6096 : Upper (D 6) (R 6) [34,68,160,18,260,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6096 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6097 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 164 28 81 288 65 138 266), lower := (rows 35 70 164 28 81 288 65 128 256), losses := [] }

theorem u6097 : Upper (D 6) (R 6) [34,68,160,20,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6097 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6098 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 428, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 35 70 164 28 81 288 66 137 265), lower := (rows 35 70 164 28 81 288 66 128 256), losses := [] }

theorem u6098 : Upper (D 6) (R 6) [34,68,160,20,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6098 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6099 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 289, targets := 4 }], pairs := [(0,2)], upper := (rows 35 70 164 28 81 288 72 131 259), lower := (rows 35 70 164 28 81 288 72 128 256), losses := [] }

theorem u6099 : Upper (D 6) (R 6) [34,68,160,20,65,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6099 [(5,8),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6100 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 280, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 70 164 28 274 33 65 200 328), lower := (rows 35 70 164 28 274 33 65 128 256), losses := [] }

theorem u6100 : Upper (D 6) (R 6) [34,68,160,20,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6100 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6101 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 305, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 70 164 28 274 33 72 193 321), lower := (rows 35 70 164 28 274 33 72 128 256), losses := [] }

theorem u6101 : Upper (D 6) (R 6) [34,68,160,20,258,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6101 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6102 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 280, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 70 164 28 280 33 65 194 322), lower := (rows 35 70 164 28 280 33 65 128 256), losses := [] }

theorem u6102 : Upper (D 6) (R 6) [34,68,160,20,264,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6102 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6103 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 66, targets := 33 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 70 164 28 280 33 66 193 321), lower := (rows 35 70 164 28 280 33 66 128 256), losses := [] }

theorem u6103 : Upper (D 6) (R 6) [34,68,160,20,264,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6103 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6104 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 280, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 70 164 28 336 33 65 138 266), lower := (rows 35 70 164 28 336 33 65 128 256), losses := [] }

theorem u6104 : Upper (D 6) (R 6) [34,68,160,20,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6104 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6105 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 66, targets := 33 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 70 164 28 336 33 66 137 265), lower := (rows 35 70 164 28 336 33 66 128 256), losses := [] }

theorem u6105 : Upper (D 6) (R 6) [34,68,160,20,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6105 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6106 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 305, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 70 164 28 336 33 72 131 259), lower := (rows 35 70 164 28 336 33 72 128 256), losses := [] }

theorem u6106 : Upper (D 6) (R 6) [34,68,160,20,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6106 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6107 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 35 70 164 73 273 48 66 140 268), lower := (rows 35 70 164 73 273 48 66 128 256), losses := [] }

theorem u6107 : Upper (D 6) (R 6) [34,68,160,65,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6107 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6108 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 313, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 164 73 273 48 68 138 266), lower := (rows 35 70 164 73 273 48 68 128 256), losses := [] }

theorem u6108 : Upper (D 6) (R 6) [34,68,160,65,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6108 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6109 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 72, targets := 2 }], pairs := [(3,1)], upper := (rows 35 70 164 73 273 48 72 134 262), lower := (rows 35 70 164 73 273 48 72 128 256), losses := [] }

theorem u6109 : Upper (D 6) (R 6) [34,68,160,65,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6109 [(5,4),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6110 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 66, targets := 33 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 70 164 88 273 33 66 140 268), lower := (rows 35 70 164 88 273 33 66 128 256), losses := [] }

theorem u6110 : Upper (D 6) (R 6) [34,68,160,80,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6110 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6111 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 313, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 70 164 88 273 33 68 138 266), lower := (rows 35 70 164 88 273 33 68 128 256), losses := [] }

theorem u6111 : Upper (D 6) (R 6) [34,68,160,80,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6111 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6112 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 164 88 273 33 72 134 262), lower := (rows 35 70 164 88 273 33 72 128 256), losses := [] }

theorem u6112 : Upper (D 6) (R 6) [34,68,160,80,257,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6112 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6113 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 280, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 70 164 88 276 33 65 138 266), lower := (rows 35 70 164 88 276 33 65 128 256), losses := [] }

theorem u6113 : Upper (D 6) (R 6) [34,68,160,80,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6113 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6114 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 74, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 70 164 88 276 33 66 137 265), lower := (rows 35 70 164 88 276 33 66 128 256), losses := [] }

theorem u6114 : Upper (D 6) (R 6) [34,68,160,80,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6115 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 74, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 164 88 276 33 72 131 259), lower := (rows 35 70 164 88 276 33 72 128 256), losses := [] }

theorem u6115 : Upper (D 6) (R 6) [34,68,160,80,260,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6115 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6116 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 66, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 35 74 52 137 81 288 66 132 260), lower := (rows 35 74 52 137 81 288 66 128 256), losses := [] }

theorem u6116 : Upper (D 6) (R 6) [34,72,48,129,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6116 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6117 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 84, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 74 52 137 81 288 68 134 262), lower := (rows 35 74 52 137 81 288 68 128 256), losses := [] }

theorem u6117 : Upper (D 6) (R 6) [34,72,48,129,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6117 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6118 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 84, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 74 52 137 84 288 65 134 262), lower := (rows 35 74 52 137 84 288 65 128 256), losses := [] }

theorem u6118 : Upper (D 6) (R 6) [34,72,48,129,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6118 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6119 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 35 74 52 137 84 288 66 133 261), lower := (rows 35 74 52 137 84 288 66 128 256), losses := [] }

theorem u6119 : Upper (D 6) (R 6) [34,72,48,129,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6119 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u6119
end Delivery.IrregularNine14.P06
