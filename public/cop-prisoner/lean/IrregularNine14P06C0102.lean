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

def b6120 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 289, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 74 52 137 84 288 68 131 259), lower := (rows 35 74 52 137 84 288 68 128 256), losses := [] }

theorem u6120 : Upper (D 6) (R 6) [34,72,48,129,68,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6120 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6121 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 35 74 52 140 81 288 65 134 262), lower := (rows 35 74 52 140 81 288 65 128 256), losses := [] }

theorem u6121 : Upper (D 6) (R 6) [34,72,48,132,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6121 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6122 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 292, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 35 74 52 140 81 288 66 133 261), lower := (rows 35 74 52 140 81 288 66 128 256), losses := [] }

theorem u6122 : Upper (D 6) (R 6) [34,72,48,132,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6122 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6123 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 84, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 74 52 140 81 288 68 131 259), lower := (rows 35 74 52 140 81 288 68 128 256), losses := [] }

theorem u6123 : Upper (D 6) (R 6) [34,72,48,132,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6123 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6124 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 74 52 140 336 33 65 134 262), lower := (rows 35 74 52 140 336 33 65 128 256), losses := [] }

theorem u6124 : Upper (D 6) (R 6) [34,72,48,132,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6125 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 66, targets := 33 },{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 74 52 140 336 33 66 133 261), lower := (rows 35 74 52 140 336 33 66 128 256), losses := [] }

theorem u6125 : Upper (D 6) (R 6) [34,72,48,132,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6125 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6126 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 305, targets := 4 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,2),(1,0),(4,2)], upper := (rows 35 74 52 140 336 33 68 131 259), lower := (rows 35 74 52 140 336 33 68 128 256), losses := [] }

theorem u6126 : Upper (D 6) (R 6) [34,72,48,132,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6126 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6127 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 394, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 52 392 84 33 65 134 262), lower := (rows 35 74 52 392 84 33 65 128 256), losses := [] }

theorem u6127 : Upper (D 6) (R 6) [34,72,48,384,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6127 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6128 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 84, targets := 1 },{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 35 74 52 392 84 33 66 133 261), lower := (rows 35 74 52 392 84 33 66 128 256), losses := [] }

theorem u6128 : Upper (D 6) (R 6) [34,72,48,384,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6129 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 425, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 74 52 392 84 33 68 131 259), lower := (rows 35 74 52 392 84 33 68 128 256), losses := [] }

theorem u6129 : Upper (D 6) (R 6) [34,72,48,384,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6129 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6130 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 78, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 84 13 145 288 66 164 292), lower := (rows 35 74 84 13 145 288 66 128 256), losses := [] }

theorem u6130 : Upper (D 6) (R 6) [34,72,80,5,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6130 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6131 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 289, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 74 84 13 145 288 68 162 290), lower := (rows 35 74 84 13 145 288 68 128 256), losses := [] }

theorem u6131 : Upper (D 6) (R 6) [34,72,80,5,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6131 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6132 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 354, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 35 74 84 13 145 288 96 134 262), lower := (rows 35 74 84 13 145 288 96 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 298 363 136 264), good := (rows 98 490 84 494 212 352 96 128 352) }] }

theorem u6132 : Upper (D 6) (R 6) [34,72,80,5,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6132 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6133 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 436, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 74 84 13 176 288 65 134 262), lower := (rows 35 74 84 13 176 288 65 128 256), losses := [] }

theorem u6133 : Upper (D 6) (R 6) [34,72,80,5,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6133 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6134 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 35 74 84 13 176 288 66 133 261), lower := (rows 35 74 84 13 176 288 66 128 256), losses := [] }

theorem u6134 : Upper (D 6) (R 6) [34,72,80,5,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6134 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6135 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 289, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 74 84 13 176 288 68 131 259), lower := (rows 35 74 84 13 176 288 68 128 256), losses := [] }

theorem u6135 : Upper (D 6) (R 6) [34,72,80,5,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6135 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6136 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 86, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 84 137 21 288 66 164 292), lower := (rows 35 74 84 137 21 288 66 128 256), losses := [] }

theorem u6136 : Upper (D 6) (R 6) [34,72,80,129,5,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6136 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6137 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 84, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 35 74 84 137 21 288 68 162 290), lower := (rows 35 74 84 137 21 288 68 128 256), losses := [] }

theorem u6137 : Upper (D 6) (R 6) [34,72,80,129,5,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6137 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6138 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 84, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 74 84 137 21 288 96 134 262), lower := (rows 35 74 84 137 21 288 96 128 256), losses := [] }

theorem u6138 : Upper (D 6) (R 6) [34,72,80,129,5,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6138 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6139 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 84, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 74 84 137 52 288 65 134 262), lower := (rows 35 74 84 137 52 288 65 128 256), losses := [] }

theorem u6139 : Upper (D 6) (R 6) [34,72,80,129,36,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6139 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6140 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 35 74 84 137 52 288 66 133 261), lower := (rows 35 74 84 137 52 288 66 128 256), losses := [] }

theorem u6140 : Upper (D 6) (R 6) [34,72,80,129,36,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6140 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6141 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 289, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 74 84 137 52 288 68 131 259), lower := (rows 35 74 84 137 52 288 68 128 256), losses := [] }

theorem u6141 : Upper (D 6) (R 6) [34,72,80,129,36,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6141 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6142 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 66, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 74 84 137 273 36 66 164 292), lower := (rows 35 74 84 137 273 36 66 128 256), losses := [] }

theorem u6142 : Upper (D 6) (R 6) [34,72,80,129,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6143 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 408, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 74 84 137 273 36 68 162 290), lower := (rows 35 74 84 137 273 36 68 128 256), losses := [] }

theorem u6143 : Upper (D 6) (R 6) [34,72,80,129,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6143 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6144 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 100, targets := 3 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 35 74 84 137 273 36 96 134 262), lower := (rows 35 74 84 137 273 36 96 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 52 117 128 256), good := (rows 98 74 116 202 372 100 96 128 256) }] }

theorem u6144 : Upper (D 6) (R 6) [34,72,80,129,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6144 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6145 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 308, targets := 1 },{ cop := 3, region := 66, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 35 74 84 137 274 36 65 164 292), lower := (rows 35 74 84 137 274 36 65 128 256), losses := [] }

theorem u6145 : Upper (D 6) (R 6) [34,72,80,129,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6145 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6146 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 408, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 74 84 137 274 36 68 161 289), lower := (rows 35 74 84 137 274 36 68 128 256), losses := [] }

theorem u6146 : Upper (D 6) (R 6) [34,72,80,129,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6146 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6147 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 100, targets := 3 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 35 74 84 137 274 36 96 133 261), lower := (rows 35 74 84 137 274 36 96 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 52 117 128 256), good := (rows 98 74 116 202 374 100 96 128 256) }] }

theorem u6147 : Upper (D 6) (R 6) [34,72,80,129,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6147 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6148 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 308, targets := 1 },{ cop := 3, region := 66, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 35 74 84 137 304 36 65 134 262), lower := (rows 35 74 84 137 304 36 65 128 256), losses := [] }

theorem u6148 : Upper (D 6) (R 6) [34,72,80,129,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6148 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6149 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 66, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 74 84 137 304 36 66 133 261), lower := (rows 35 74 84 137 304 36 66 128 256), losses := [] }

theorem u6149 : Upper (D 6) (R 6) [34,72,80,129,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6150 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 408, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 74 84 137 304 36 68 131 259), lower := (rows 35 74 84 137 304 36 68 128 256), losses := [] }

theorem u6150 : Upper (D 6) (R 6) [34,72,80,129,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6151 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 2, region := 170, targets := 1 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 35 74 84 138 273 36 65 164 292), lower := (rows 35 74 84 138 273 36 65 128 256), losses := [] }

theorem u6151 : Upper (D 6) (R 6) [34,72,80,130,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6151 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6152 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 408, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 74 84 138 273 36 68 161 289), lower := (rows 35 74 84 138 273 36 68 128 256), losses := [] }

theorem u6152 : Upper (D 6) (R 6) [34,72,80,130,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6152 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6153 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 4, region := 100, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 74 84 138 273 36 96 133 261), lower := (rows 35 74 84 138 273 36 96 128 256), losses := [] }

theorem u6153 : Upper (D 6) (R 6) [34,72,80,130,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6153 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6154 : Route 9 := (fun mask => (mask,id))

def c6154 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6154 : Upper (D 6) (R 6) [34,72,80,130,288,4,1] 13 := by
  apply FastRouting.sound _ _ [34,72,80,130,288,4,1] 13 (by decide) (choices 1) [1,4] r6154 c6154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u453
  · exact u454

def b6155 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 408, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 74 84 138 304 36 68 129 257), lower := (rows 35 74 84 138 304 36 68 128 256), losses := [] }

theorem u6155 : Upper (D 6) (R 6) [34,72,80,130,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6155 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6156 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 66, targets := 33 },{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 74 84 140 273 33 66 164 292), lower := (rows 35 74 84 140 273 33 66 128 256), losses := [] }

theorem u6156 : Upper (D 6) (R 6) [34,72,80,132,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6157 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 305, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 74 84 140 273 33 68 162 290), lower := (rows 35 74 84 140 273 33 68 128 256), losses := [] }

theorem u6157 : Upper (D 6) (R 6) [34,72,80,132,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6157 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6158 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 138, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 84 140 273 33 96 134 262), lower := (rows 35 74 84 140 273 33 96 128 256), losses := [] }

theorem u6158 : Upper (D 6) (R 6) [34,72,80,132,257,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6158 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6159 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 138, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 84 140 304 33 65 134 262), lower := (rows 35 74 84 140 304 33 65 128 256), losses := [] }

theorem u6159 : Upper (D 6) (R 6) [34,72,80,132,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6159 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6160 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 66, targets := 33 },{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 74 84 140 304 33 66 133 261), lower := (rows 35 74 84 140 304 33 66 128 256), losses := [] }

theorem u6160 : Upper (D 6) (R 6) [34,72,80,132,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6161 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 305, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 74 84 140 304 33 68 131 259), lower := (rows 35 74 84 140 304 33 68 128 256), losses := [] }

theorem u6161 : Upper (D 6) (R 6) [34,72,80,132,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6161 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6162 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 170, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 35 74 84 168 273 36 65 134 262), lower := (rows 35 74 84 168 273 36 65 128 256), losses := [] }

theorem u6162 : Upper (D 6) (R 6) [34,72,80,160,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6162 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6163 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 35 74 84 168 273 36 66 133 261), lower := (rows 35 74 84 168 273 36 66 128 256), losses := [] }

theorem u6163 : Upper (D 6) (R 6) [34,72,80,160,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6163 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6164 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 408, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 74 84 168 273 36 68 131 259), lower := (rows 35 74 84 168 273 36 68 128 256), losses := [] }

theorem u6164 : Upper (D 6) (R 6) [34,72,80,160,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6164 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6165 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 3, region := 67, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 84 168 274 36 65 133 261), lower := (rows 35 74 84 168 274 36 65 128 256), losses := [] }

theorem u6165 : Upper (D 6) (R 6) [34,72,80,160,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6165 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6166 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 408, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 74 84 168 274 36 68 129 257), lower := (rows 35 74 84 168 274 36 68 128 256), losses := [] }

theorem u6166 : Upper (D 6) (R 6) [34,72,80,160,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6166 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6167 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 35 74 84 392 21 33 66 164 292), lower := (rows 35 74 84 392 21 33 66 128 256), losses := [] }

theorem u6167 : Upper (D 6) (R 6) [34,72,80,384,5,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6167 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6168 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 425, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 74 84 392 21 33 68 162 290), lower := (rows 35 74 84 392 21 33 68 128 256), losses := [] }

theorem u6168 : Upper (D 6) (R 6) [34,72,80,384,5,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6168 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6169 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 394, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 84 392 21 33 96 134 262), lower := (rows 35 74 84 392 21 33 96 128 256), losses := [] }

theorem u6169 : Upper (D 6) (R 6) [34,72,80,384,5,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6169 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6170 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 394, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 84 392 52 33 65 134 262), lower := (rows 35 74 84 392 52 33 65 128 256), losses := [] }

theorem u6170 : Upper (D 6) (R 6) [34,72,80,384,36,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6170 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6171 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 84, targets := 1 },{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 35 74 84 392 52 33 66 133 261), lower := (rows 35 74 84 392 52 33 66 128 256), losses := [] }

theorem u6171 : Upper (D 6) (R 6) [34,72,80,384,36,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6171 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6172 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 425, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 74 84 392 52 33 68 131 259), lower := (rows 35 74 84 392 52 33 68 128 256), losses := [] }

theorem u6172 : Upper (D 6) (R 6) [34,72,80,384,36,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6173 : PairBound 9 := { available := 260, camps := [{ cop := 1, region := 436, targets := 1 },{ cop := 3, region := 66, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 35 74 100 25 146 36 65 388 260), lower := (rows 35 74 100 25 146 36 65 128 256), losses := [] }

theorem u6173 : Upper (D 6) (R 6) [34,72,96,17,130,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6173 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6174 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 408, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 74 100 25 146 36 68 385 257), lower := (rows 35 74 100 25 146 36 68 128 256), losses := [] }

theorem u6174 : Upper (D 6) (R 6) [34,72,96,17,130,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6174 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6175 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 74 100 25 146 36 320 133 261), lower := (rows 35 74 100 25 146 36 320 128 256), losses := [] }

theorem u6175 : Upper (D 6) (R 6) [34,72,96,17,130,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6175 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6176 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 436, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 74 100 25 146 288 65 132 260), lower := (rows 35 74 100 25 146 288 65 128 256), losses := [] }

theorem u6176 : Upper (D 6) (R 6) [34,72,96,17,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6176 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6177 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 74 100 25 146 288 68 133 261), lower := (rows 35 74 100 25 146 288 68 128 256), losses := [] }

theorem u6177 : Upper (D 6) (R 6) [34,72,96,17,130,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6177 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6178 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 436, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 74 100 25 148 288 65 134 262), lower := (rows 35 74 100 25 148 288 65 128 256), losses := [] }

theorem u6178 : Upper (D 6) (R 6) [34,72,96,17,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6178 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6179 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 35 74 100 25 148 288 66 133 261), lower := (rows 35 74 100 25 148 288 66 128 256), losses := [] }

theorem u6179 : Upper (D 6) (R 6) [34,72,96,17,132,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6179 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u6179
end Delivery.IrregularNine14.P06
