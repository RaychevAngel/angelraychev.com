import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0135
import IrregularNine14P06C0136

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b26100 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 148 14 21 34 321 449 321), lower := (rows 41 98 148 14 21 34 64 128 256), losses := [] }

theorem u26100 : Upper (D 6) (R 6) [40,96,144,6,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26100 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26101 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 148 14 21 96 323 387 259), lower := (rows 41 98 148 14 21 96 64 128 256), losses := [] }

theorem u26101 : Upper (D 6) (R 6) [40,96,144,6,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26101 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26102 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 355, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 41 98 148 14 21 288 67 195 323), lower := (rows 41 98 148 14 21 288 64 128 256), losses := [] }

theorem u26102 : Upper (D 6) (R 6) [40,96,144,6,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26102 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26103 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 33, targets := 6 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 148 14 81 33 326 390 262), lower := (rows 41 98 148 14 81 33 64 128 256), losses := [] }

theorem u26103 : Upper (D 6) (R 6) [40,96,144,6,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26103 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26104 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 148 14 81 34 325 389 261), lower := (rows 41 98 148 14 81 34 64 128 256), losses := [] }

theorem u26104 : Upper (D 6) (R 6) [40,96,144,6,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26104 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26105 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 148 14 81 36 323 387 259), lower := (rows 41 98 148 14 81 36 64 128 256), losses := [] }

theorem u26105 : Upper (D 6) (R 6) [40,96,144,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26105 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26106 : Route 9 := (fun mask => (mask,id))

def c26106 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26106 : Upper (D 6) (R 6) [40,96,144,6,65,256] 13 := by
  apply FastRouting.sound _ _ [40,96,144,6,65,256] 13 (by decide) (choices 1) [1,2,4] r26106 c26106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8156
  · exact u8157
  · exact u8158

def b26107 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 148 14 273 33 70 198 326), lower := (rows 41 98 148 14 273 33 64 128 256), losses := [] }

theorem u26107 : Upper (D 6) (R 6) [40,96,144,6,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26107 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26108 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 148 14 273 34 69 197 325), lower := (rows 41 98 148 14 273 34 64 128 256), losses := [] }

theorem u26108 : Upper (D 6) (R 6) [40,96,144,6,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26108 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26109 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 148 14 273 36 67 195 323), lower := (rows 41 98 148 14 273 36 64 128 256), losses := [] }

theorem u26109 : Upper (D 6) (R 6) [40,96,144,6,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26109 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26110 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 148 14 273 96 71 135 263), lower := (rows 41 98 148 14 273 96 64 128 256), losses := [] }

theorem u26110 : Upper (D 6) (R 6) [40,96,144,6,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26110 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26111 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 33, targets := 68 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 148 14 274 33 69 197 325), lower := (rows 41 98 148 14 274 33 64 128 256), losses := [] }

theorem u26111 : Upper (D 6) (R 6) [40,96,144,6,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26111 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26112 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 148 14 274 36 65 193 321), lower := (rows 41 98 148 14 274 36 64 128 256), losses := [] }

theorem u26112 : Upper (D 6) (R 6) [40,96,144,6,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26112 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26113 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 148 14 274 96 69 133 261), lower := (rows 41 98 148 14 274 96 64 128 256), losses := [] }

theorem u26113 : Upper (D 6) (R 6) [40,96,144,6,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26113 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26114 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 148 14 276 33 67 195 323), lower := (rows 41 98 148 14 276 33 64 128 256), losses := [] }

theorem u26114 : Upper (D 6) (R 6) [40,96,144,6,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26115 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 148 14 276 34 65 193 321), lower := (rows 41 98 148 14 276 34 64 128 256), losses := [] }

theorem u26115 : Upper (D 6) (R 6) [40,96,144,6,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26115 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26116 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 148 14 276 96 67 131 259), lower := (rows 41 98 148 14 276 96 64 128 256), losses := [] }

theorem u26116 : Upper (D 6) (R 6) [40,96,144,6,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26116 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26117 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 33, targets := 6 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 148 14 336 33 71 135 263), lower := (rows 41 98 148 14 336 33 64 128 256), losses := [] }

theorem u26117 : Upper (D 6) (R 6) [40,96,144,6,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26117 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26118 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 148 14 336 34 69 133 261), lower := (rows 41 98 148 14 336 34 64 128 256), losses := [] }

theorem u26118 : Upper (D 6) (R 6) [40,96,144,6,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26118 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26119 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 148 14 336 36 67 131 259), lower := (rows 41 98 148 14 336 36 64 128 256), losses := [] }

theorem u26119 : Upper (D 6) (R 6) [40,96,144,6,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26119 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26120 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 41 98 148 76 21 33 322 386 258), lower := (rows 41 98 148 76 21 33 64 128 256), losses := [] }

theorem u26120 : Upper (D 6) (R 6) [40,96,144,68,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26120 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26121 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 35, targets := 4 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 148 76 21 34 323 387 259), lower := (rows 41 98 148 76 21 34 64 128 256), losses := [] }

theorem u26121 : Upper (D 6) (R 6) [40,96,144,68,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26121 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26122 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 291, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 41 98 148 76 21 288 67 131 259), lower := (rows 41 98 148 76 21 288 64 128 256), losses := [] }

theorem u26122 : Upper (D 6) (R 6) [40,96,144,68,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26122 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26123 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 148 76 22 33 323 387 259), lower := (rows 41 98 148 76 22 33 64 128 256), losses := [] }

theorem u26123 : Upper (D 6) (R 6) [40,96,144,68,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26123 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26124 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 50, targets := 1 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(1,0),(4,0)], upper := (rows 41 98 148 76 22 34 321 385 257), lower := (rows 41 98 148 76 22 34 64 128 256), losses := [] }

theorem u26124 : Upper (D 6) (R 6) [40,96,144,68,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26125 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 291, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 41 98 148 76 22 288 67 131 259), lower := (rows 41 98 148 76 22 288 64 128 256), losses := [] }

theorem u26125 : Upper (D 6) (R 6) [40,96,144,68,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26125 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26126 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 148 76 273 33 70 134 262), lower := (rows 41 98 148 76 273 33 64 128 256), losses := [] }

theorem u26126 : Upper (D 6) (R 6) [40,96,144,68,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26126 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26127 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 35, targets := 4 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 148 76 273 34 71 135 263), lower := (rows 41 98 148 76 273 34 64 128 256), losses := [] }

theorem u26127 : Upper (D 6) (R 6) [40,96,144,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26127 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26128 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 148 76 273 36 67 131 259), lower := (rows 41 98 148 76 273 36 64 128 256), losses := [] }

theorem u26128 : Upper (D 6) (R 6) [40,96,144,68,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26129 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 148 76 274 33 71 135 263), lower := (rows 41 98 148 76 274 33 64 128 256), losses := [] }

theorem u26129 : Upper (D 6) (R 6) [40,96,144,68,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26129 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26130 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 35, targets := 4 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 148 76 274 34 69 133 261), lower := (rows 41 98 148 76 274 34 64 128 256), losses := [] }

theorem u26130 : Upper (D 6) (R 6) [40,96,144,68,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26131 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 148 76 274 36 67 131 259), lower := (rows 41 98 148 76 274 36 64 128 256), losses := [] }

theorem u26131 : Upper (D 6) (R 6) [40,96,144,68,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26131 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26132 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 148 76 276 33 67 131 259), lower := (rows 41 98 148 76 276 33 64 128 256), losses := [] }

theorem u26132 : Upper (D 6) (R 6) [40,96,144,68,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26132 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26133 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 35, targets := 4 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 148 76 276 34 67 131 259), lower := (rows 41 98 148 76 276 34 64 128 256), losses := [] }

theorem u26133 : Upper (D 6) (R 6) [40,96,144,68,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26133 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26134 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 6, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 41 98 148 265 21 34 70 198 326), lower := (rows 41 98 148 265 21 34 64 128 256), losses := [] }

theorem u26134 : Upper (D 6) (R 6) [40,96,144,257,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26134 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26135 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 98 148 265 21 36 66 194 322), lower := (rows 41 98 148 265 21 36 64 128 256), losses := [] }

theorem u26135 : Upper (D 6) (R 6) [40,96,144,257,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26135 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26136 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 148 265 21 96 70 134 262), lower := (rows 41 98 148 265 21 96 64 128 256), losses := [] }

theorem u26136 : Upper (D 6) (R 6) [40,96,144,257,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26136 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26137 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 148 265 22 33 70 198 326), lower := (rows 41 98 148 265 22 33 64 128 256), losses := [] }

theorem u26137 : Upper (D 6) (R 6) [40,96,144,257,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26137 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26138 : Route 9 := (fun mask => (mask,id))

def c26138 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26138 : Upper (D 6) (R 6) [40,96,144,257,6,2] 13 := by
  apply FastRouting.sound _ _ [40,96,144,257,6,2] 13 (by decide) (choices 1) [1,4] r26138 c26138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8159
  · exact u8160

def b26139 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 98 148 265 22 36 67 195 323), lower := (rows 41 98 148 265 22 36 64 128 256), losses := [] }

theorem u26139 : Upper (D 6) (R 6) [40,96,144,257,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26139 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26140 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 148 265 22 96 71 135 263), lower := (rows 41 98 148 265 22 96 64 128 256), losses := [] }

theorem u26140 : Upper (D 6) (R 6) [40,96,144,257,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26140 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26141 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 166, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 41 98 148 265 81 34 70 134 262), lower := (rows 41 98 148 265 81 34 64 128 256), losses := [] }

theorem u26141 : Upper (D 6) (R 6) [40,96,144,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26142 : Route 9 := (fun mask => (mask,id))

def c26142 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26142 : Upper (D 6) (R 6) [40,96,144,257,65,4] 13 := by
  apply FastRouting.sound _ _ [40,96,144,257,65,4] 13 (by decide) (choices 1) [2,4] r26142 c26142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8161
  · exact u8162

def b26143 : PairBound 9 := { available := 6, camps := [{ cop := 8, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 148 265 84 33 70 134 262), lower := (rows 41 98 148 265 84 33 64 128 256), losses := [] }

theorem u26143 : Upper (D 6) (R 6) [40,96,144,257,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26143 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26144 : Route 9 := (fun mask => (mask,id))

def c26144 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26144 : Upper (D 6) (R 6) [40,96,144,257,68,2] 13 := by
  apply FastRouting.sound _ _ [40,96,144,257,68,2] 13 (by decide) (choices 1) [1,2,4] r26144 c26144
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8163
  · exact u8164
  · exact u8165

def b26145 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 98 148 265 84 36 67 131 259), lower := (rows 41 98 148 265 84 36 64 128 256), losses := [] }

theorem u26145 : Upper (D 6) (R 6) [40,96,144,257,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26145 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26146 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 148 266 21 33 70 198 326), lower := (rows 41 98 148 266 21 33 64 128 256), losses := [] }

theorem u26146 : Upper (D 6) (R 6) [40,96,144,258,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26146 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26147 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 148 266 21 34 69 197 325), lower := (rows 41 98 148 266 21 34 64 128 256), losses := [] }

theorem u26147 : Upper (D 6) (R 6) [40,96,144,258,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26147 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26148 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 98 148 266 21 36 67 195 323), lower := (rows 41 98 148 266 21 36 64 128 256), losses := [] }

theorem u26148 : Upper (D 6) (R 6) [40,96,144,258,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26148 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26149 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 148 266 21 96 71 135 263), lower := (rows 41 98 148 266 21 96 64 128 256), losses := [] }

theorem u26149 : Upper (D 6) (R 6) [40,96,144,258,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26150 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 148 266 22 33 69 197 325), lower := (rows 41 98 148 266 22 33 64 128 256), losses := [] }

theorem u26150 : Upper (D 6) (R 6) [40,96,144,258,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26151 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 98 148 266 22 36 65 193 321), lower := (rows 41 98 148 266 22 36 64 128 256), losses := [] }

theorem u26151 : Upper (D 6) (R 6) [40,96,144,258,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26151 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26152 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 148 266 22 96 69 133 261), lower := (rows 41 98 148 266 22 96 64 128 256), losses := [] }

theorem u26152 : Upper (D 6) (R 6) [40,96,144,258,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26152 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26153 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 148 266 81 33 70 134 262), lower := (rows 41 98 148 266 81 33 64 128 256), losses := [] }

theorem u26153 : Upper (D 6) (R 6) [40,96,144,258,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26153 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26154 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 148 266 81 34 69 133 261), lower := (rows 41 98 148 266 81 34 64 128 256), losses := [] }

theorem u26154 : Upper (D 6) (R 6) [40,96,144,258,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26154 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26155 : Route 9 := (fun mask => (mask,id))

def c26155 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26155 : Upper (D 6) (R 6) [40,96,144,258,65,4] 13 := by
  apply FastRouting.sound _ _ [40,96,144,258,65,4] 13 (by decide) (choices 1) [1,2,4] r26155 c26155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8166
  · exact u8167
  · exact u8168

def b26156 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 148 266 84 33 71 135 263), lower := (rows 41 98 148 266 84 33 64 128 256), losses := [] }

theorem u26156 : Upper (D 6) (R 6) [40,96,144,258,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26157 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 148 266 84 34 69 133 261), lower := (rows 41 98 148 266 84 34 64 128 256), losses := [] }

theorem u26157 : Upper (D 6) (R 6) [40,96,144,258,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26157 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26158 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 98 148 266 84 36 67 131 259), lower := (rows 41 98 148 266 84 36 64 128 256), losses := [] }

theorem u26158 : Upper (D 6) (R 6) [40,96,144,258,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26158 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26159 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 460, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 41 98 148 268 19 33 70 198 326), lower := (rows 41 98 148 268 19 33 64 128 256), losses := [] }

theorem u26159 : Upper (D 6) (R 6) [40,96,144,260,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26159 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u26159
end Delivery.IrregularNine14.P06
