import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0075

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17100 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 162 37 76 81 288 86 150 278), lower := (rows 11 162 37 76 81 288 64 128 256), losses := [] }

theorem u17100 : Upper (D 6) (R 6) [10,160,33,68,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17100 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17101 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 37 76 82 33 340 404 276), lower := (rows 11 162 37 76 82 33 64 128 256), losses := [] }

theorem u17101 : Upper (D 6) (R 6) [10,160,33,68,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17101 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17102 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 162 37 76 82 36 337 401 273), lower := (rows 11 162 37 76 82 36 64 128 256), losses := [] }

theorem u17102 : Upper (D 6) (R 6) [10,160,33,68,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17102 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17103 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 328, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 11 162 37 76 82 48 325 389 261), lower := (rows 11 162 37 76 82 48 64 128 256), losses := [] }

theorem u17103 : Upper (D 6) (R 6) [10,160,33,68,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17103 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17104 : Route 9 := (fun mask => (mask,id))

def c17104 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17104 : Upper (D 6) (R 6) [10,160,33,68,66,256] 13 := by
  apply FastRouting.sound _ _ [10,160,33,68,66,256] 13 (by decide) (choices 1) [1,4,16] r17104 c17104
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4514
  · exact u4515
  · exact u4516

def b17105 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 162 37 76 273 34 84 212 340), lower := (rows 11 162 37 76 273 34 64 128 256), losses := [] }

theorem u17105 : Upper (D 6) (R 6) [10,160,33,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17105 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17106 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 162 37 76 273 36 82 210 338), lower := (rows 11 162 37 76 273 36 64 128 256), losses := [] }

theorem u17106 : Upper (D 6) (R 6) [10,160,33,68,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17106 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17107 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 11 162 37 76 273 48 70 198 326), lower := (rows 11 162 37 76 273 48 64 128 256), losses := [] }

theorem u17107 : Upper (D 6) (R 6) [10,160,33,68,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17107 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17108 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 402, targets := 64 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 162 37 76 273 96 86 150 278), lower := (rows 11 162 37 76 273 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 104 64 128 256), good := (rows 45 160 37 108 277 96 96 128 256) }] }

theorem u17108 : Upper (D 6) (R 6) [10,160,33,68,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17108 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17109 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 37 76 274 33 84 212 340), lower := (rows 11 162 37 76 274 33 64 128 256), losses := [] }

theorem u17109 : Upper (D 6) (R 6) [10,160,33,68,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17109 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17110 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 162 37 76 274 36 81 209 337), lower := (rows 11 162 37 76 274 36 64 128 256), losses := [] }

theorem u17110 : Upper (D 6) (R 6) [10,160,33,68,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17110 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17111 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 72, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 11 162 37 76 274 48 69 197 325), lower := (rows 11 162 37 76 274 48 64 128 256), losses := [] }

theorem u17111 : Upper (D 6) (R 6) [10,160,33,68,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17111 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17112 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 402, targets := 64 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 162 37 76 274 96 85 149 277), lower := (rows 11 162 37 76 274 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 104 64 128 256), good := (rows 45 160 37 108 272 96 96 128 256) }] }

theorem u17112 : Upper (D 6) (R 6) [10,160,33,68,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17112 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17113 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 37 76 276 33 82 210 338), lower := (rows 11 162 37 76 276 33 64 128 256), losses := [] }

theorem u17113 : Upper (D 6) (R 6) [10,160,33,68,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17113 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17114 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 162 37 76 276 34 81 209 337), lower := (rows 11 162 37 76 276 34 64 128 256), losses := [] }

theorem u17114 : Upper (D 6) (R 6) [10,160,33,68,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17115 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 194, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 162 37 76 276 48 67 195 323), lower := (rows 11 162 37 76 276 48 64 128 256), losses := [{ target := 2, region := (rows 9 22 0 8 16 48 77 141 269), good := (rows 459 162 483 459 498 50 64 128 256) }] }

theorem u17115 : Upper (D 6) (R 6) [10,160,33,68,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17115 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17116 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 402, targets := 64 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 162 37 76 276 96 83 147 275), lower := (rows 11 162 37 76 276 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 104 64 128 256), good := (rows 45 160 37 108 276 96 96 128 256) }] }

theorem u17116 : Upper (D 6) (R 6) [10,160,33,68,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17116 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17117 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 37 76 336 33 86 150 278), lower := (rows 11 162 37 76 336 33 64 128 256), losses := [] }

theorem u17117 : Upper (D 6) (R 6) [10,160,33,68,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17117 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17118 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 162 37 76 336 34 85 149 277), lower := (rows 11 162 37 76 336 34 64 128 256), losses := [] }

theorem u17118 : Upper (D 6) (R 6) [10,160,33,68,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17118 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17119 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 162 37 76 336 36 83 147 275), lower := (rows 11 162 37 76 336 36 64 128 256), losses := [] }

theorem u17119 : Upper (D 6) (R 6) [10,160,33,68,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17119 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17120 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 130, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 37 76 336 48 71 135 263), lower := (rows 11 162 37 76 336 48 64 128 256), losses := [{ target := 6, region := (rows 9 6 4 8 16 48 0 140 268), good := (rows 395 162 423 399 304 48 0 128 256) }] }

theorem u17120 : Upper (D 6) (R 6) [10,160,33,68,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17120 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17121 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 162 37 88 273 34 68 196 324), lower := (rows 11 162 37 88 273 34 64 128 256), losses := [] }

theorem u17121 : Upper (D 6) (R 6) [10,160,33,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17121 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17122 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 162 37 88 273 36 70 198 326), lower := (rows 11 162 37 88 273 36 64 128 256), losses := [] }

theorem u17122 : Upper (D 6) (R 6) [10,160,33,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17122 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17123 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 402, targets := 64 },{ cop := 2, region := 130, targets := 1 }], pairs := [(1,0),(1,6),(4,6)], upper := (rows 11 162 37 88 273 96 70 134 262), lower := (rows 11 162 37 88 273 96 64 128 256), losses := [] }

theorem u17123 : Upper (D 6) (R 6) [10,160,33,80,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17123 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17124 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 37 88 274 33 68 196 324), lower := (rows 11 162 37 88 274 33 64 128 256), losses := [] }

theorem u17124 : Upper (D 6) (R 6) [10,160,33,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17125 : Route 9 := (fun mask => (mask,id))

def c17125 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17125 : Upper (D 6) (R 6) [10,160,33,80,258,4] 13 := by
  apply FastRouting.sound _ _ [10,160,33,80,258,4] 13 (by decide) (choices 1) [1,4] r17125 c17125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4517
  · exact u4518

def b17126 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 402, targets := 64 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 162 37 88 274 96 69 133 261), lower := (rows 11 162 37 88 274 96 64 128 256), losses := [] }

theorem u17126 : Upper (D 6) (R 6) [10,160,33,80,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17126 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17127 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 37 88 276 33 70 198 326), lower := (rows 11 162 37 88 276 33 64 128 256), losses := [] }

theorem u17127 : Upper (D 6) (R 6) [10,160,33,80,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17127 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17128 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 162 37 88 276 34 69 197 325), lower := (rows 11 162 37 88 276 34 64 128 256), losses := [] }

theorem u17128 : Upper (D 6) (R 6) [10,160,33,80,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17129 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 194, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 162 37 88 276 36 67 195 323), lower := (rows 11 162 37 88 276 36 64 128 256), losses := [] }

theorem u17129 : Upper (D 6) (R 6) [10,160,33,80,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17129 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17130 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 402, targets := 64 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 162 37 88 276 96 71 135 263), lower := (rows 11 162 37 88 276 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 104 64 128 256), good := (rows 45 160 37 120 276 96 96 128 256) }] }

theorem u17130 : Upper (D 6) (R 6) [10,160,33,80,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17131 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 162 37 265 82 36 84 212 340), lower := (rows 11 162 37 265 82 36 64 128 256), losses := [] }

theorem u17131 : Upper (D 6) (R 6) [10,160,33,257,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17131 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17132 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 162 37 265 82 48 68 196 324), lower := (rows 11 162 37 265 82 48 64 128 256), losses := [] }

theorem u17132 : Upper (D 6) (R 6) [10,160,33,257,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17132 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17133 : Route 9 := (fun mask => (mask,id))

def c17133 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17133 : Upper (D 6) (R 6) [10,160,33,257,66,64] 13 := by
  apply FastRouting.sound _ _ [10,160,33,257,66,64] 13 (by decide) (choices 1) [4,16] r17133 c17133
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4519
  · exact u4520

def b17134 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 162 37 265 84 34 84 212 340), lower := (rows 11 162 37 265 84 34 64 128 256), losses := [] }

theorem u17134 : Upper (D 6) (R 6) [10,160,33,257,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17134 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17135 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 162 37 265 84 36 82 210 338), lower := (rows 11 162 37 265 84 36 64 128 256), losses := [] }

theorem u17135 : Upper (D 6) (R 6) [10,160,33,257,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17135 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17136 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 162 37 265 84 48 70 198 326), lower := (rows 11 162 37 265 84 48 64 128 256), losses := [] }

theorem u17136 : Upper (D 6) (R 6) [10,160,33,257,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17136 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17137 : Route 9 := (fun mask => (mask,id))

def c17137 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17137 : Upper (D 6) (R 6) [10,160,33,257,68,64] 13 := by
  apply FastRouting.sound _ _ [10,160,33,257,68,64] 13 (by decide) (choices 1) [2,4,16] r17137 c17137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4521
  · exact u4522
  · exact u4523

def b17138 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 37 268 22 33 80 208 336), lower := (rows 11 162 37 268 22 33 64 128 256), losses := [] }

theorem u17138 : Upper (D 6) (R 6) [10,160,33,260,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17138 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17139 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 52, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 162 37 268 22 48 65 193 321), lower := (rows 11 162 37 268 22 48 64 128 256), losses := [] }

theorem u17139 : Upper (D 6) (R 6) [10,160,33,260,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17139 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17140 : Route 9 := (fun mask => (mask,id))

def c17140 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17140 : Upper (D 6) (R 6) [10,160,33,260,6,64] 13 := by
  apply FastRouting.sound _ _ [10,160,33,260,6,64] 13 (by decide) (choices 1) [1,16] r17140 c17140
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4524
  · exact u4525

def b17141 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 162 37 268 81 34 84 212 340), lower := (rows 11 162 37 268 81 34 64 128 256), losses := [] }

theorem u17141 : Upper (D 6) (R 6) [10,160,33,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17142 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 162 37 268 81 36 82 210 338), lower := (rows 11 162 37 268 81 36 64 128 256), losses := [] }

theorem u17142 : Upper (D 6) (R 6) [10,160,33,260,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17143 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 11 162 37 268 81 48 70 198 326), lower := (rows 11 162 37 268 81 48 64 128 256), losses := [] }

theorem u17143 : Upper (D 6) (R 6) [10,160,33,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17143 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17144 : Route 9 := (fun mask => (mask,id))

def c17144 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17144 : Upper (D 6) (R 6) [10,160,33,260,65,64] 13 := by
  apply FastRouting.sound _ _ [10,160,33,260,65,64] 13 (by decide) (choices 1) [2,4,16] r17144 c17144
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4526
  · exact u4527
  · exact u4528

def b17145 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 37 268 82 33 84 212 340), lower := (rows 11 162 37 268 82 33 64 128 256), losses := [] }

theorem u17145 : Upper (D 6) (R 6) [10,160,33,260,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17145 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17146 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 162 37 268 82 36 81 209 337), lower := (rows 11 162 37 268 82 36 64 128 256), losses := [] }

theorem u17146 : Upper (D 6) (R 6) [10,160,33,260,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17146 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17147 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 328, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 11 162 37 268 82 48 69 197 325), lower := (rows 11 162 37 268 82 48 64 128 256), losses := [] }

theorem u17147 : Upper (D 6) (R 6) [10,160,33,260,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17147 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17148 : Route 9 := (fun mask => (mask,id))

def c17148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17148 : Upper (D 6) (R 6) [10,160,33,260,66,64] 13 := by
  apply FastRouting.sound _ _ [10,160,33,260,66,64] 13 (by decide) (choices 1) [1,4,16] r17148 c17148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4529
  · exact u4530
  · exact u4531

def b17149 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 37 268 84 33 82 210 338), lower := (rows 11 162 37 268 84 33 64 128 256), losses := [] }

theorem u17149 : Upper (D 6) (R 6) [10,160,33,260,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17150 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 162 37 268 84 34 81 209 337), lower := (rows 11 162 37 268 84 34 64 128 256), losses := [] }

theorem u17150 : Upper (D 6) (R 6) [10,160,33,260,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17151 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 194, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 162 37 268 84 48 67 195 323), lower := (rows 11 162 37 268 84 48 64 128 256), losses := [{ target := 2, region := (rows 9 22 0 8 16 48 77 141 269), good := (rows 459 162 483 459 498 50 64 128 256) }] }

theorem u17151 : Upper (D 6) (R 6) [10,160,33,260,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17151 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17152 : Route 9 := (fun mask => (mask,id))

def c17152 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17152 : Upper (D 6) (R 6) [10,160,33,260,68,64] 13 := by
  apply FastRouting.sound _ _ [10,160,33,260,68,64] 13 (by decide) (choices 1) [1,2,16] r17152 c17152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4532
  · exact u4533
  · exact u4534

def b17153 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 162 37 280 81 34 68 196 324), lower := (rows 11 162 37 280 81 34 64 128 256), losses := [] }

theorem u17153 : Upper (D 6) (R 6) [10,160,33,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17153 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17154 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 162 37 280 81 36 70 198 326), lower := (rows 11 162 37 280 81 36 64 128 256), losses := [] }

theorem u17154 : Upper (D 6) (R 6) [10,160,33,272,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17154 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17155 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 130, targets := 1 },{ cop := 2, region := 130, targets := 64 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(1,6),(2,1)], upper := (rows 11 162 37 280 81 96 70 134 262), lower := (rows 11 162 37 280 81 96 64 128 256), losses := [] }

theorem u17155 : Upper (D 6) (R 6) [10,160,33,272,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17155 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17156 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 37 280 82 33 68 196 324), lower := (rows 11 162 37 280 82 33 64 128 256), losses := [] }

theorem u17156 : Upper (D 6) (R 6) [10,160,33,272,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17157 : Route 9 := (fun mask => (mask,id))

def c17157 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17157 : Upper (D 6) (R 6) [10,160,33,272,66,4] 13 := by
  apply FastRouting.sound _ _ [10,160,33,272,66,4] 13 (by decide) (choices 1) [1,4] r17157 c17157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4535
  · exact u4536

def r17158 : Route 9 := (fun mask => (mask,id))

def c17158 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17158 : Upper (D 6) (R 6) [10,160,33,272,66,64] 13 := by
  apply FastRouting.sound _ _ [10,160,33,272,66,64] 13 (by decide) (choices 1) [1,4] r17158 c17158
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4537
  · exact u4538

def b17159 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 37 280 84 33 70 198 326), lower := (rows 11 162 37 280 84 33 64 128 256), losses := [] }

theorem u17159 : Upper (D 6) (R 6) [10,160,33,272,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17159 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u17159
end Delivery.IrregularNine14.P06
