import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0010

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8100 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 41 98 134 25 336 36 65 134 262), lower := (rows 41 98 134 25 336 36 65 128 256), losses := [] }

theorem u8100 : Upper (D 6) (R 6) [40,96,130,17,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8100 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8101 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 66, targets := 5 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 41 98 134 25 336 36 66 133 261), lower := (rows 41 98 134 25 336 36 66 128 256), losses := [] }

theorem u8101 : Upper (D 6) (R 6) [40,96,130,17,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8101 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8102 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 134 25 336 36 68 131 259), lower := (rows 41 98 134 25 336 36 68 128 256), losses := [] }

theorem u8102 : Upper (D 6) (R 6) [40,96,130,17,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8102 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8103 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 166, targets := 1 },{ cop := 0, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 41 98 134 26 273 36 65 196 324), lower := (rows 41 98 134 26 273 36 65 128 256), losses := [] }

theorem u8103 : Upper (D 6) (R 6) [40,96,130,18,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8103 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8104 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 134 26 273 36 68 193 321), lower := (rows 41 98 134 26 273 36 68 128 256), losses := [] }

theorem u8104 : Upper (D 6) (R 6) [40,96,130,18,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8104 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8105 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 165, targets := 64 },{ cop := 0, region := 66, targets := 4 }], pairs := [(0,6),(1,2),(2,6)], upper := (rows 41 98 134 26 336 36 65 133 261), lower := (rows 41 98 134 26 336 36 65 128 256), losses := [] }

theorem u8105 : Upper (D 6) (R 6) [40,96,130,18,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8105 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8106 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 134 26 336 36 68 129 257), lower := (rows 41 98 134 26 336 36 68 128 256), losses := [] }

theorem u8106 : Upper (D 6) (R 6) [40,96,130,18,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8106 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8107 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 98 134 28 81 288 65 134 262), lower := (rows 41 98 134 28 81 288 65 128 256), losses := [] }

theorem u8107 : Upper (D 6) (R 6) [40,96,130,20,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8107 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8108 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 82, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 41 98 134 28 81 288 66 133 261), lower := (rows 41 98 134 28 81 288 66 128 256), losses := [] }

theorem u8108 : Upper (D 6) (R 6) [40,96,130,20,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8108 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8109 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 290, targets := 4 }], pairs := [(1,0),(1,2)], upper := (rows 41 98 134 28 81 288 68 131 259), lower := (rows 41 98 134 28 81 288 68 128 256), losses := [{ target := 0, region := (rows 0 3 4 8 16 288 76 128 256), good := (rows 106 98 198 92 82 288 68 128 288) }] }

theorem u8109 : Upper (D 6) (R 6) [40,96,130,20,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8109 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8110 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 72, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 41 98 134 76 21 288 65 146 274), lower := (rows 41 98 134 76 21 288 65 128 256), losses := [] }

theorem u8110 : Upper (D 6) (R 6) [40,96,130,68,5,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8110 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8111 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 305, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 98 134 76 21 288 66 145 273), lower := (rows 41 98 134 76 21 288 66 128 256), losses := [] }

theorem u8111 : Upper (D 6) (R 6) [40,96,130,68,5,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8111 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8112 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 72, targets := 1 }], pairs := [(3,0)], upper := (rows 41 98 134 76 21 288 80 131 259), lower := (rows 41 98 134 76 21 288 80 128 256), losses := [] }

theorem u8112 : Upper (D 6) (R 6) [40,96,130,68,5,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8112 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8113 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 132, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 41 98 134 76 273 48 65 134 262), lower := (rows 41 98 134 76 273 48 65 128 256), losses := [] }

theorem u8113 : Upper (D 6) (R 6) [40,96,130,68,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8113 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8114 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 305, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 98 134 76 273 48 66 133 261), lower := (rows 41 98 134 76 273 48 66 128 256), losses := [] }

theorem u8114 : Upper (D 6) (R 6) [40,96,130,68,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8114 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8115 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 41 98 134 76 273 48 68 131 259), lower := (rows 41 98 134 76 273 48 68 128 256), losses := [] }

theorem u8115 : Upper (D 6) (R 6) [40,96,130,68,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8115 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8116 : Route 9 := (fun mask => (mask,id))

def c8116 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8116 : Upper (D 6) (R 6) [40,96,130,68,258,16,1] 13 := by
  apply FastRouting.sound _ _ [40,96,130,68,258,16,1] 13 (by decide) (choices 1) [1,4] r8116 c8116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u631
  · exact u632

def b8117 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 41 98 134 76 274 48 68 129 257), lower := (rows 41 98 134 76 274 48 68 128 256), losses := [] }

theorem u8117 : Upper (D 6) (R 6) [40,96,130,68,258,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8117 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8118 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 105, targets := 2 }], pairs := [(0,1),(3,1)], upper := (rows 41 98 134 76 276 48 65 131 259), lower := (rows 41 98 134 76 276 48 65 128 256), losses := [] }

theorem u8118 : Upper (D 6) (R 6) [40,96,130,68,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8118 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8119 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 305, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 98 134 76 276 48 66 129 257), lower := (rows 41 98 134 76 276 48 66 128 256), losses := [] }

theorem u8119 : Upper (D 6) (R 6) [40,96,130,68,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8119 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8120 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 72, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 41 98 134 88 21 288 65 134 262), lower := (rows 41 98 134 88 21 288 65 128 256), losses := [] }

theorem u8120 : Upper (D 6) (R 6) [40,96,130,80,5,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8120 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8121 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 41 98 134 88 21 288 66 133 261), lower := (rows 41 98 134 88 21 288 66 128 256), losses := [] }

theorem u8121 : Upper (D 6) (R 6) [40,96,130,80,5,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8121 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8122 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 41 98 134 88 21 288 68 131 259), lower := (rows 41 98 134 88 21 288 68 128 256), losses := [] }

theorem u8122 : Upper (D 6) (R 6) [40,96,130,80,5,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8122 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8123 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 72, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 41 98 134 88 273 36 65 134 262), lower := (rows 41 98 134 88 273 36 65 128 256), losses := [] }

theorem u8123 : Upper (D 6) (R 6) [40,96,130,80,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8123 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8124 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 66, targets := 5 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 41 98 134 88 273 36 66 133 261), lower := (rows 41 98 134 88 273 36 66 128 256), losses := [] }

theorem u8124 : Upper (D 6) (R 6) [40,96,130,80,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8125 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 134 88 273 36 68 131 259), lower := (rows 41 98 134 88 273 36 68 128 256), losses := [] }

theorem u8125 : Upper (D 6) (R 6) [40,96,130,80,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8125 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8126 : Route 9 := (fun mask => (mask,id))

def c8126 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8126 : Upper (D 6) (R 6) [40,96,130,80,258,4,1] 13 := by
  apply FastRouting.sound _ _ [40,96,130,80,258,4,1] 13 (by decide) (choices 1) [1,4] r8126 c8126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u633
  · exact u634

def b8127 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 134 88 274 36 68 129 257), lower := (rows 41 98 134 88 274 36 68 128 256), losses := [] }

theorem u8127 : Upper (D 6) (R 6) [40,96,130,80,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8127 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8128 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 0, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 41 98 134 265 21 36 66 208 336), lower := (rows 41 98 134 265 21 36 66 128 256), losses := [] }

theorem u8128 : Upper (D 6) (R 6) [40,96,130,257,5,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8129 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 265, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 41 98 134 265 21 36 80 194 322), lower := (rows 41 98 134 265 21 36 80 128 256), losses := [] }

theorem u8129 : Upper (D 6) (R 6) [40,96,130,257,5,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8129 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8130 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 82, targets := 4 },{ cop := 4, region := 166, targets := 1 }], pairs := [(1,0),(1,2),(4,2)], upper := (rows 41 98 134 265 81 36 66 148 276), lower := (rows 41 98 134 265 81 36 66 128 256), losses := [] }

theorem u8130 : Upper (D 6) (R 6) [40,96,130,257,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8131 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 134 265 81 36 68 146 274), lower := (rows 41 98 134 265 81 36 68 128 256), losses := [] }

theorem u8131 : Upper (D 6) (R 6) [40,96,130,257,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8131 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8132 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 134 265 81 36 80 134 262), lower := (rows 41 98 134 265 81 36 80 128 256), losses := [] }

theorem u8132 : Upper (D 6) (R 6) [40,96,130,257,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8132 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8133 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 182, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 41 98 134 265 84 36 65 146 274), lower := (rows 41 98 134 265 84 36 65 128 256), losses := [] }

theorem u8133 : Upper (D 6) (R 6) [40,96,130,257,68,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8133 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8134 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 297, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 98 134 265 84 36 66 145 273), lower := (rows 41 98 134 265 84 36 66 128 256), losses := [] }

theorem u8134 : Upper (D 6) (R 6) [40,96,130,257,68,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8134 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8135 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 134 265 84 36 80 131 259), lower := (rows 41 98 134 265 84 36 80 128 256), losses := [] }

theorem u8135 : Upper (D 6) (R 6) [40,96,130,257,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8135 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8136 : Route 9 := (fun mask => (mask,id))

def c8136 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8136 : Upper (D 6) (R 6) [40,96,130,258,5,4,1] 13 := by
  apply FastRouting.sound _ _ [40,96,130,258,5,4,1] 13 (by decide) (choices 1) [16,64] r8136 c8136
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u635
  · exact u636

def b8137 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 265, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 41 98 134 266 21 36 80 193 321), lower := (rows 41 98 134 266 21 36 80 128 256), losses := [] }

theorem u8137 : Upper (D 6) (R 6) [40,96,130,258,5,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8137 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8138 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 132, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 41 98 134 266 21 48 65 196 324), lower := (rows 41 98 134 266 21 48 65 128 256), losses := [] }

theorem u8138 : Upper (D 6) (R 6) [40,96,130,258,5,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8138 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8139 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 265, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 41 98 134 266 21 48 68 193 321), lower := (rows 41 98 134 266 21 48 68 128 256), losses := [] }

theorem u8139 : Upper (D 6) (R 6) [40,96,130,258,5,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8139 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8140 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 41 98 134 266 81 36 65 148 276), lower := (rows 41 98 134 266 81 36 65 128 256), losses := [] }

theorem u8140 : Upper (D 6) (R 6) [40,96,130,258,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8140 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8141 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 134 266 81 36 68 145 273), lower := (rows 41 98 134 266 81 36 68 128 256), losses := [] }

theorem u8141 : Upper (D 6) (R 6) [40,96,130,258,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8142 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 134 266 81 36 80 133 261), lower := (rows 41 98 134 266 81 36 80 128 256), losses := [] }

theorem u8142 : Upper (D 6) (R 6) [40,96,130,258,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8142 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8143 : Route 9 := (fun mask => (mask,id))

def c8143 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8143 : Upper (D 6) (R 6) [40,96,130,258,68,4,1] 13 := by
  apply FastRouting.sound _ _ [40,96,130,258,68,4,1] 13 (by decide) (choices 1) [1,16] r8143 c8143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u637
  · exact u638

def b8144 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 134 266 84 36 80 129 257), lower := (rows 41 98 134 266 84 36 80 128 256), losses := [] }

theorem u8144 : Upper (D 6) (R 6) [40,96,130,258,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8144 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8145 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 82, targets := 4 },{ cop := 4, region := 196, targets := 32 }], pairs := [(1,2),(2,5),(4,2)], upper := (rows 41 98 134 280 19 36 65 196 324), lower := (rows 41 98 134 280 19 36 65 128 256), losses := [] }

theorem u8145 : Upper (D 6) (R 6) [40,96,130,272,3,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8145 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8146 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 134 280 19 36 68 193 321), lower := (rows 41 98 134 280 19 36 68 128 256), losses := [] }

theorem u8146 : Upper (D 6) (R 6) [40,96,130,272,3,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8146 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8147 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 41 98 134 280 81 36 65 134 262), lower := (rows 41 98 134 280 81 36 65 128 256), losses := [] }

theorem u8147 : Upper (D 6) (R 6) [40,96,130,272,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8147 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8148 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 82, targets := 4 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(1,2),(4,2)], upper := (rows 41 98 134 280 81 36 66 133 261), lower := (rows 41 98 134 280 81 36 66 128 256), losses := [] }

theorem u8148 : Upper (D 6) (R 6) [40,96,130,272,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8148 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8149 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 134 280 81 36 68 131 259), lower := (rows 41 98 134 280 81 36 68 128 256), losses := [] }

theorem u8149 : Upper (D 6) (R 6) [40,96,130,272,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8150 : Route 9 := (fun mask => (mask,id))

def c8150 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8150 : Upper (D 6) (R 6) [40,96,130,320,5,4,1] 13 := by
  apply FastRouting.sound _ _ [40,96,130,320,5,4,1] 13 (by decide) (choices 1) [2,16] r8150 c8150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u639
  · exact u640

def b8151 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 66, targets := 5 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 41 98 134 328 21 36 66 145 273), lower := (rows 41 98 134 328 21 36 66 128 256), losses := [] }

theorem u8151 : Upper (D 6) (R 6) [40,96,130,320,5,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8151 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8152 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 265, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 41 98 134 328 21 36 80 131 259), lower := (rows 41 98 134 328 21 36 80 128 256), losses := [] }

theorem u8152 : Upper (D 6) (R 6) [40,96,130,320,5,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8152 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8153 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 132, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 41 98 134 328 21 48 65 134 262), lower := (rows 41 98 134 328 21 48 65 128 256), losses := [] }

theorem u8153 : Upper (D 6) (R 6) [40,96,130,320,5,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8153 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8154 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 98, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 41 98 134 328 21 48 66 133 261), lower := (rows 41 98 134 328 21 48 66 128 256), losses := [] }

theorem u8154 : Upper (D 6) (R 6) [40,96,130,320,5,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8154 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8155 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 265, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 41 98 134 328 21 48 68 131 259), lower := (rows 41 98 134 328 21 48 68 128 256), losses := [] }

theorem u8155 : Upper (D 6) (R 6) [40,96,130,320,5,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8155 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8156 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 98 148 14 81 288 65 134 262), lower := (rows 41 98 148 14 81 288 65 128 256), losses := [] }

theorem u8156 : Upper (D 6) (R 6) [40,96,144,6,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8156 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8157 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 82, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 41 98 148 14 81 288 66 133 261), lower := (rows 41 98 148 14 81 288 66 128 256), losses := [] }

theorem u8157 : Upper (D 6) (R 6) [40,96,144,6,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8157 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8158 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 289, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 41 98 148 14 81 288 68 131 259), lower := (rows 41 98 148 14 81 288 68 128 256), losses := [] }

theorem u8158 : Upper (D 6) (R 6) [40,96,144,6,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8158 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8159 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 182, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 41 98 148 265 22 34 65 196 324), lower := (rows 41 98 148 265 22 34 65 128 256), losses := [] }

theorem u8159 : Upper (D 6) (R 6) [40,96,144,257,6,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8159 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u8159
end Delivery.IrregularNine14.P06
