import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0050

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14040 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 292, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 50 37 200 84 288 71 135 263), lower := (rows 11 50 37 200 84 288 64 128 256), losses := [{ target := 6, region := (rows 1 18 5 8 16 293 0 129 257), good := (rows 431 50 421 136 54 288 0 128 288) }] }

theorem u14040 : Upper (D 6) (R 6) [10,48,33,192,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14040 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14041 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 50 37 200 273 34 68 196 324), lower := (rows 11 50 37 200 273 34 64 128 256), losses := [] }

theorem u14041 : Upper (D 6) (R 6) [10,48,33,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14041 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14042 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 4, region := 38, targets := 64 }], pairs := [(1,6),(2,1),(2,6)], upper := (rows 11 50 37 200 273 36 70 198 326), lower := (rows 11 50 37 200 273 36 64 128 256), losses := [] }

theorem u14042 : Upper (D 6) (R 6) [10,48,33,192,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14042 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14043 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 274, targets := 64 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 50 37 200 273 96 70 134 262), lower := (rows 11 50 37 200 273 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 104 64 128 256), good := (rows 45 48 37 232 277 96 96 128 256) }] }

theorem u14043 : Upper (D 6) (R 6) [10,48,33,192,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14043 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14044 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 50 37 200 276 33 70 198 326), lower := (rows 11 50 37 200 276 33 64 128 256), losses := [] }

theorem u14044 : Upper (D 6) (R 6) [10,48,33,192,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14044 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14045 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 50 37 200 276 34 69 197 325), lower := (rows 11 50 37 200 276 34 64 128 256), losses := [] }

theorem u14045 : Upper (D 6) (R 6) [10,48,33,192,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14045 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14046 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 201, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 37 200 276 36 67 195 323), lower := (rows 11 50 37 200 276 36 64 128 256), losses := [] }

theorem u14046 : Upper (D 6) (R 6) [10,48,33,192,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14046 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14047 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 274, targets := 64 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 50 37 200 276 96 71 135 263), lower := (rows 11 50 37 200 276 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 104 64 128 256), good := (rows 45 48 37 232 276 96 96 128 256) }] }

theorem u14047 : Upper (D 6) (R 6) [10,48,33,192,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14048 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 50 37 200 336 33 70 134 262), lower := (rows 11 50 37 200 336 33 64 128 256), losses := [] }

theorem u14048 : Upper (D 6) (R 6) [10,48,33,192,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14048 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14049 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 50 37 200 336 34 69 133 261), lower := (rows 11 50 37 200 336 34 64 128 256), losses := [] }

theorem u14049 : Upper (D 6) (R 6) [10,48,33,192,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14049 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14050 : Route 9 := (fun mask => (mask,id))

def c14050 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14050 : Upper (D 6) (R 6) [10,48,33,192,320,4] 13 := by
  apply FastRouting.sound _ _ [10,48,33,192,320,4] 13 (by decide) (choices 1) [1,2,4] r14050 c14050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3018
  · exact u3019
  · exact u3020

def b14051 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 50 37 392 81 34 68 196 324), lower := (rows 11 50 37 392 81 34 64 128 256), losses := [] }

theorem u14051 : Upper (D 6) (R 6) [10,48,33,384,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14051 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14052 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 4, region := 38, targets := 64 }], pairs := [(1,6),(2,1),(2,6)], upper := (rows 11 50 37 392 81 36 70 198 326), lower := (rows 11 50 37 392 81 36 64 128 256), losses := [] }

theorem u14052 : Upper (D 6) (R 6) [10,48,33,384,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14052 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14053 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 37 392 81 96 70 134 262), lower := (rows 11 50 37 392 81 96 64 128 256), losses := [] }

theorem u14053 : Upper (D 6) (R 6) [10,48,33,384,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14053 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14054 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 50 37 392 84 33 70 198 326), lower := (rows 11 50 37 392 84 33 64 128 256), losses := [] }

theorem u14054 : Upper (D 6) (R 6) [10,48,33,384,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14054 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14055 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 50 37 392 84 34 69 197 325), lower := (rows 11 50 37 392 84 34 64 128 256), losses := [] }

theorem u14055 : Upper (D 6) (R 6) [10,48,33,384,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14055 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14056 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 457, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 37 392 84 36 67 195 323), lower := (rows 11 50 37 392 84 36 64 128 256), losses := [] }

theorem u14056 : Upper (D 6) (R 6) [10,48,33,384,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14056 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14057 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 37 392 84 96 71 135 263), lower := (rows 11 50 37 392 84 96 64 128 256), losses := [] }

theorem u14057 : Upper (D 6) (R 6) [10,48,33,384,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14057 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14058 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 69 44 145 34 324 452 324), lower := (rows 11 50 69 44 145 34 64 128 256), losses := [] }

theorem u14058 : Upper (D 6) (R 6) [10,48,65,36,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14059 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 50 69 44 145 36 322 450 322), lower := (rows 11 50 69 44 145 36 64 128 256), losses := [] }

theorem u14059 : Upper (D 6) (R 6) [10,48,65,36,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14059 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14060 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 69 44 145 96 326 390 262), lower := (rows 11 50 69 44 145 96 64 128 256), losses := [] }

theorem u14060 : Upper (D 6) (R 6) [10,48,65,36,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14060 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14061 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 50 69 44 145 288 70 198 326), lower := (rows 11 50 69 44 145 288 64 128 256), losses := [] }

theorem u14061 : Upper (D 6) (R 6) [10,48,65,36,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14061 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14062 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 69 44 148 33 322 450 322), lower := (rows 11 50 69 44 148 33 64 128 256), losses := [] }

theorem u14062 : Upper (D 6) (R 6) [10,48,65,36,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14063 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 69 44 148 34 321 449 321), lower := (rows 11 50 69 44 148 34 64 128 256), losses := [] }

theorem u14063 : Upper (D 6) (R 6) [10,48,65,36,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14064 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 69 44 148 96 323 387 259), lower := (rows 11 50 69 44 148 96 64 128 256), losses := [] }

theorem u14064 : Upper (D 6) (R 6) [10,48,65,36,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14064 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14065 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 50 69 44 148 288 67 195 323), lower := (rows 11 50 69 44 148 288 64 128 256), losses := [] }

theorem u14065 : Upper (D 6) (R 6) [10,48,65,36,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14065 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14066 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 40, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 50 69 44 208 33 326 390 262), lower := (rows 11 50 69 44 208 33 64 128 256), losses := [] }

theorem u14066 : Upper (D 6) (R 6) [10,48,65,36,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14066 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14067 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 69 44 208 34 325 389 261), lower := (rows 11 50 69 44 208 34 64 128 256), losses := [] }

theorem u14067 : Upper (D 6) (R 6) [10,48,65,36,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14067 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14068 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 50 69 44 208 36 323 387 259), lower := (rows 11 50 69 44 208 36 64 128 256), losses := [] }

theorem u14068 : Upper (D 6) (R 6) [10,48,65,36,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14068 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14069 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 50 69 44 208 288 71 135 263), lower := (rows 11 50 69 44 208 288 64 128 256), losses := [] }

theorem u14069 : Upper (D 6) (R 6) [10,48,65,36,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14069 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14070 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 40, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 50 69 44 400 33 70 198 326), lower := (rows 11 50 69 44 400 33 64 128 256), losses := [] }

theorem u14070 : Upper (D 6) (R 6) [10,48,65,36,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14070 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14071 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 69 44 400 34 69 197 325), lower := (rows 11 50 69 44 400 34 64 128 256), losses := [] }

theorem u14071 : Upper (D 6) (R 6) [10,48,65,36,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14071 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14072 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 50 69 44 400 36 67 195 323), lower := (rows 11 50 69 44 400 36 64 128 256), losses := [] }

theorem u14072 : Upper (D 6) (R 6) [10,48,65,36,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14072 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14073 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 69 44 400 96 71 135 263), lower := (rows 11 50 69 44 400 96 64 128 256), losses := [] }

theorem u14073 : Upper (D 6) (R 6) [10,48,65,36,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14073 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14074 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 306, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 50 69 137 276 34 100 228 356), lower := (rows 11 50 69 137 276 34 64 128 256), losses := [] }

theorem u14074 : Upper (D 6) (R 6) [10,48,65,129,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14074 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14075 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 201, targets := 4 },{ cop := 2, region := 306, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 50 69 137 276 36 98 226 354), lower := (rows 11 50 69 137 276 36 64 128 256), losses := [] }

theorem u14075 : Upper (D 6) (R 6) [10,48,65,129,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14075 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14076 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 306, targets := 1 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 50 69 137 276 96 102 166 294), lower := (rows 11 50 69 137 276 96 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 8 16 100 64 128 256), good := (rows 11 50 97 137 306 96 96 128 256) }] }

theorem u14076 : Upper (D 6) (R 6) [10,48,65,129,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14076 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14077 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 69 137 336 34 100 164 292), lower := (rows 11 50 69 137 336 34 64 128 256), losses := [] }

theorem u14077 : Upper (D 6) (R 6) [10,48,65,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14077 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14078 : Route 9 := (fun mask => (mask,id))

def c14078 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14078 : Upper (D 6) (R 6) [10,48,65,129,320,4] 13 := by
  apply FastRouting.sound _ _ [10,48,65,129,320,4] 13 (by decide) (choices 1) [2,4,32] r14078 c14078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3021
  · exact u3022
  · exact u3023

def b14079 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 69 140 273 34 100 228 356), lower := (rows 11 50 69 140 273 34 64 128 256), losses := [] }

theorem u14079 : Upper (D 6) (R 6) [10,48,65,132,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14079 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14080 : Route 9 := (fun mask => (mask,id))

def c14080 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14080 : Upper (D 6) (R 6) [10,48,65,132,257,4] 13 := by
  apply FastRouting.sound _ _ [10,48,65,132,257,4] 13 (by decide) (choices 1) [2,32] r14080 c14080
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3024
  · exact u3025

def r14081 : Route 9 := (fun mask => (mask,id))

def c14081 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14081 : Upper (D 6) (R 6) [10,48,65,132,257,64] 13 := by
  apply FastRouting.sound _ _ [10,48,65,132,257,64] 13 (by decide) (choices 1) [2,4,32] r14081 c14081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3026
  · exact u3027
  · exact u3028

def r14082 : Route 9 := (fun mask => (mask,id))

def c14082 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14082 : Upper (D 6) (R 6) [10,48,65,132,258,1] 13 := by
  apply FastRouting.sound _ _ [10,48,65,132,258,1] 13 (by decide) (choices 1) [4,32] r14082 c14082
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3029
  · exact u3030

def r14083 : Route 9 := (fun mask => (mask,id))

def c14083 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14083 : Upper (D 6) (R 6) [10,48,65,132,258,4] 13 := by
  apply FastRouting.sound _ _ [10,48,65,132,258,4] 13 (by decide) (choices 1) [1,32] r14083 c14083
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3031
  · exact u3032

def r14084 : Route 9 := (fun mask => (mask,id))

def c14084 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14084 : Upper (D 6) (R 6) [10,48,65,132,258,64] 13 := by
  apply FastRouting.sound _ _ [10,48,65,132,258,64] 13 (by decide) (choices 1) [1,4,32] r14084 c14084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3033
  · exact u3034
  · exact u3035

def r14085 : Route 9 := (fun mask => (mask,id))

def c14085 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14085 : Upper (D 6) (R 6) [10,48,65,132,260,1] 13 := by
  apply FastRouting.sound _ _ [10,48,65,132,260,1] 13 (by decide) (choices 1) [2,32] r14085 c14085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3036
  · exact u3037

def b14086 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 69 140 276 34 97 225 353), lower := (rows 11 50 69 140 276 34 64 128 256), losses := [] }

theorem u14086 : Upper (D 6) (R 6) [10,48,65,132,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14086 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14087 : Route 9 := (fun mask => (mask,id))

def c14087 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14087 : Upper (D 6) (R 6) [10,48,65,132,260,64] 13 := by
  apply FastRouting.sound _ _ [10,48,65,132,260,64] 13 (by decide) (choices 1) [1,2,32] r14087 c14087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3038
  · exact u3039
  · exact u3040

def r14088 : Route 9 := (fun mask => (mask,id))

def c14088 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14088 : Upper (D 6) (R 6) [10,48,65,132,320,1] 13 := by
  apply FastRouting.sound _ _ [10,48,65,132,320,1] 13 (by decide) (choices 1) [2,4,32] r14088 c14088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3041
  · exact u3042
  · exact u3043

def b14089 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 69 140 336 34 101 165 293), lower := (rows 11 50 69 140 336 34 64 128 256), losses := [] }

theorem u14089 : Upper (D 6) (R 6) [10,48,65,132,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14089 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14090 : Route 9 := (fun mask => (mask,id))

def c14090 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14090 : Upper (D 6) (R 6) [10,48,65,132,320,4] 13 := by
  apply FastRouting.sound _ _ [10,48,65,132,320,4] 13 (by decide) (choices 1) [1,2,32] r14090 c14090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3044
  · exact u3045
  · exact u3046

def b14091 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 69 168 273 34 68 196 324), lower := (rows 11 50 69 168 273 34 64 128 256), losses := [] }

theorem u14091 : Upper (D 6) (R 6) [10,48,65,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14091 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14092 : Route 9 := (fun mask => (mask,id))

def c14092 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14092 : Upper (D 6) (R 6) [10,48,65,160,257,4] 13 := by
  apply FastRouting.sound _ _ [10,48,65,160,257,4] 13 (by decide) (choices 1) [2,4] r14092 c14092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3047
  · exact u3048

def r14093 : Route 9 := (fun mask => (mask,id))

def c14093 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14093 : Upper (D 6) (R 6) [10,48,65,160,257,64] 13 := by
  apply FastRouting.sound _ _ [10,48,65,160,257,64] 13 (by decide) (choices 1) [2,4] r14093 c14093
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3049
  · exact u3050

def b14094 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(1,2),(2,5),(4,5)], upper := (rows 11 50 69 168 276 33 70 198 326), lower := (rows 11 50 69 168 276 33 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 8 16 37 64 128 256), good := (rows 43 50 97 168 306 33 64 128 256) }] }

theorem u14094 : Upper (D 6) (R 6) [10,48,65,160,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14094 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14095 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 69 168 276 34 69 197 325), lower := (rows 11 50 69 168 276 34 64 128 256), losses := [] }

theorem u14095 : Upper (D 6) (R 6) [10,48,65,160,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14095 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14096 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 201, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 50 69 168 276 36 67 195 323), lower := (rows 11 50 69 168 276 36 64 128 256), losses := [] }

theorem u14096 : Upper (D 6) (R 6) [10,48,65,160,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14096 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14097 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 50 69 168 276 96 71 135 263), lower := (rows 11 50 69 168 276 96 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 100 64 128 256), good := (rows 10 50 100 168 310 96 96 128 256) }] }

theorem u14097 : Upper (D 6) (R 6) [10,48,65,160,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14097 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14098 : Route 9 := (fun mask => (mask,id))

def c14098 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14098 : Upper (D 6) (R 6) [10,48,65,160,320,1] 13 := by
  apply FastRouting.sound _ _ [10,48,65,160,320,1] 13 (by decide) (choices 1) [2,4] r14098 c14098
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3051
  · exact u3052

def b14099 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 69 168 336 34 69 133 261), lower := (rows 11 50 69 168 336 34 64 128 256), losses := [] }

theorem u14099 : Upper (D 6) (R 6) [10,48,65,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14099 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u14099
end Delivery.IrregularNine14.P06
