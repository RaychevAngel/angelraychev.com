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

def b8040 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 98 133 28 273 34 66 196 324), lower := (rows 41 98 133 28 273 34 66 128 256), losses := [] }

theorem u8040 : Upper (D 6) (R 6) [40,96,129,20,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8040 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8041 : Route 9 := (fun mask => (mask,id))

def c8041 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8041 : Upper (D 6) (R 6) [40,96,129,20,257,2,4] 13 := by
  apply FastRouting.sound _ _ [40,96,129,20,257,2,4] 13 (by decide) (choices 1) [2,64] r8041 c8041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u625
  · exact u626

def b8042 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 72, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 41 98 133 76 22 288 65 146 274), lower := (rows 41 98 133 76 22 288 65 128 256), losses := [] }

theorem u8042 : Upper (D 6) (R 6) [40,96,129,68,6,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8042 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8043 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 72, targets := 33 }], pairs := [(3,0),(3,5)], upper := (rows 41 98 133 76 22 288 66 145 273), lower := (rows 41 98 133 76 22 288 66 128 256), losses := [] }

theorem u8043 : Upper (D 6) (R 6) [40,96,129,68,6,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8043 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8044 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 72, targets := 1 }], pairs := [(3,0)], upper := (rows 41 98 133 76 22 288 80 131 259), lower := (rows 41 98 133 76 22 288 80 128 256), losses := [] }

theorem u8044 : Upper (D 6) (R 6) [40,96,129,68,6,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8044 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8045 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 98, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 41 98 133 76 273 48 66 134 262), lower := (rows 41 98 133 76 273 48 66 128 256), losses := [] }

theorem u8045 : Upper (D 6) (R 6) [40,96,129,68,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8045 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8046 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 41 98 133 76 273 48 68 130 258), lower := (rows 41 98 133 76 273 48 68 128 256), losses := [] }

theorem u8046 : Upper (D 6) (R 6) [40,96,129,68,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8046 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8047 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 72, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 41 98 133 76 274 48 65 134 262), lower := (rows 41 98 133 76 274 48 65 128 256), losses := [] }

theorem u8047 : Upper (D 6) (R 6) [40,96,129,68,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8047 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8048 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 114, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 41 98 133 76 274 48 66 133 261), lower := (rows 41 98 133 76 274 48 66 128 256), losses := [] }

theorem u8048 : Upper (D 6) (R 6) [40,96,129,68,258,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8048 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8049 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 41 98 133 76 274 48 68 131 259), lower := (rows 41 98 133 76 274 48 68 128 256), losses := [] }

theorem u8049 : Upper (D 6) (R 6) [40,96,129,68,258,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8049 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8050 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 72, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 41 98 133 76 276 48 65 130 258), lower := (rows 41 98 133 76 276 48 65 128 256), losses := [] }

theorem u8050 : Upper (D 6) (R 6) [40,96,129,68,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8050 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8051 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 41 98 133 76 276 48 66 131 259), lower := (rows 41 98 133 76 276 48 66 128 256), losses := [] }

theorem u8051 : Upper (D 6) (R 6) [40,96,129,68,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8051 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8052 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 66, targets := 4 }], pairs := [(1,0),(1,2)], upper := (rows 41 98 133 88 22 288 65 134 262), lower := (rows 41 98 133 88 22 288 65 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 312 64 144 272), good := (rows 42 98 132 506 438 288 64 128 288) }] }

theorem u8052 : Upper (D 6) (R 6) [40,96,129,80,6,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8052 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8053 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 421, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 98 133 88 22 288 66 133 261), lower := (rows 41 98 133 88 22 288 66 128 256), losses := [] }

theorem u8053 : Upper (D 6) (R 6) [40,96,129,80,6,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8053 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8054 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 41 98 133 88 22 288 68 131 259), lower := (rows 41 98 133 88 22 288 68 128 256), losses := [] }

theorem u8054 : Upper (D 6) (R 6) [40,96,129,80,6,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8054 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8055 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 66, targets := 1 },{ cop := 0, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 41 98 133 88 273 36 66 134 262), lower := (rows 41 98 133 88 273 36 66 128 256), losses := [{ target := 0, region := (rows 0 39 4 24 16 36 119 164 292), good := (rows 490 482 486 88 346 486 66 128 256) }] }

theorem u8055 : Upper (D 6) (R 6) [40,96,129,80,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8055 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8056 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 133 88 273 36 68 130 258), lower := (rows 41 98 133 88 273 36 68 128 256), losses := [] }

theorem u8056 : Upper (D 6) (R 6) [40,96,129,80,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8056 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8057 : Route 9 := (fun mask => (mask,id))

def c8057 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8057 : Upper (D 6) (R 6) [40,96,129,80,258,4,1] 13 := by
  apply FastRouting.sound _ _ [40,96,129,80,258,4,1] 13 (by decide) (choices 1) [2,4] r8057 c8057
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u627
  · exact u628

def b8058 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 165, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 41 98 133 88 274 36 66 133 261), lower := (rows 41 98 133 88 274 36 66 128 256), losses := [] }

theorem u8058 : Upper (D 6) (R 6) [40,96,129,80,258,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8059 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 133 88 274 36 68 131 259), lower := (rows 41 98 133 88 274 36 68 128 256), losses := [] }

theorem u8059 : Upper (D 6) (R 6) [40,96,129,80,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8059 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8060 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 0, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 41 98 133 265 22 36 66 208 336), lower := (rows 41 98 133 265 22 36 66 128 256), losses := [] }

theorem u8060 : Upper (D 6) (R 6) [40,96,129,257,6,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8060 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8061 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 265, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 41 98 133 265 22 36 80 194 322), lower := (rows 41 98 133 265 22 36 80 128 256), losses := [] }

theorem u8061 : Upper (D 6) (R 6) [40,96,129,257,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8061 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8062 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 0, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 41 98 133 265 84 36 66 146 274), lower := (rows 41 98 133 265 84 36 66 128 256), losses := [] }

theorem u8062 : Upper (D 6) (R 6) [40,96,129,257,68,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8063 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 133 265 84 36 80 130 258), lower := (rows 41 98 133 265 84 36 80 128 256), losses := [] }

theorem u8063 : Upper (D 6) (R 6) [40,96,129,257,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8063 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8064 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 66, targets := 4 }], pairs := [(1,2),(3,2),(3,5)], upper := (rows 41 98 133 266 22 36 65 208 336), lower := (rows 41 98 133 266 22 36 65 128 256), losses := [{ target := 2, region := (rows 1 35 0 24 16 32 69 144 272), good := (rows 107 98 195 266 474 98 67 128 256) },{ target := 5, region := (rows 1 2 4 24 16 0 69 144 272), good := (rows 73 66 197 266 478 68 65 128 256) }] }

theorem u8064 : Upper (D 6) (R 6) [40,96,129,258,6,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8064 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8065 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 265, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 41 98 133 266 22 36 80 193 321), lower := (rows 41 98 133 266 22 36 80 128 256), losses := [] }

theorem u8065 : Upper (D 6) (R 6) [40,96,129,258,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8065 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8066 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 82, targets := 4 },{ cop := 4, region := 132, targets := 2 }], pairs := [(1,2),(2,1),(4,2)], upper := (rows 41 98 133 266 81 36 66 148 276), lower := (rows 41 98 133 266 81 36 66 128 256), losses := [] }

theorem u8066 : Upper (D 6) (R 6) [40,96,129,258,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8066 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8067 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 133 266 81 36 68 146 274), lower := (rows 41 98 133 266 81 36 68 128 256), losses := [] }

theorem u8067 : Upper (D 6) (R 6) [40,96,129,258,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8067 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8068 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 133 266 81 36 80 134 262), lower := (rows 41 98 133 266 81 36 80 128 256), losses := [] }

theorem u8068 : Upper (D 6) (R 6) [40,96,129,258,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8068 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8069 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 298, targets := 1 },{ cop := 0, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 41 98 133 266 84 36 65 146 274), lower := (rows 41 98 133 266 84 36 65 128 256), losses := [] }

theorem u8069 : Upper (D 6) (R 6) [40,96,129,258,68,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8069 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8070 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 0, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 41 98 133 266 84 36 66 145 273), lower := (rows 41 98 133 266 84 36 66 128 256), losses := [] }

theorem u8070 : Upper (D 6) (R 6) [40,96,129,258,68,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8070 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8071 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 133 266 84 36 80 131 259), lower := (rows 41 98 133 266 84 36 80 128 256), losses := [] }

theorem u8071 : Upper (D 6) (R 6) [40,96,129,258,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8071 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8072 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 133 268 22 34 65 208 336), lower := (rows 41 98 133 268 22 34 65 128 256), losses := [] }

theorem u8072 : Upper (D 6) (R 6) [40,96,129,260,6,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8072 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8073 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 41 98 133 268 22 34 80 193 321), lower := (rows 41 98 133 268 22 34 80 128 256), losses := [] }

theorem u8073 : Upper (D 6) (R 6) [40,96,129,260,6,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8073 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8074 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 66, targets := 4 }], pairs := [(1,2),(3,0)], upper := (rows 41 98 133 268 22 48 65 194 322), lower := (rows 41 98 133 268 22 48 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 48 64 130 258), good := (rows 40 482 132 268 446 56 64 128 256) }] }

theorem u8074 : Upper (D 6) (R 6) [40,96,129,260,6,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8074 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8075 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 41 98 133 268 22 48 66 193 321), lower := (rows 41 98 133 268 22 48 66 128 256), losses := [] }

theorem u8075 : Upper (D 6) (R 6) [40,96,129,260,6,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8075 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8076 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 132, targets := 98 }], pairs := [(2,1),(2,5),(2,6)], upper := (rows 41 98 133 268 81 34 66 148 276), lower := (rows 41 98 133 268 81 34 66 128 256), losses := [] }

theorem u8076 : Upper (D 6) (R 6) [40,96,129,260,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8076 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8077 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 80, targets := 34 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 41 98 133 268 81 34 68 146 274), lower := (rows 41 98 133 268 81 34 68 128 256), losses := [] }

theorem u8077 : Upper (D 6) (R 6) [40,96,129,260,65,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8077 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8078 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 133 268 81 34 80 134 262), lower := (rows 41 98 133 268 81 34 80 128 256), losses := [] }

theorem u8078 : Upper (D 6) (R 6) [40,96,129,260,65,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8078 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8079 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 80, targets := 34 },{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(4,1),(4,5)], upper := (rows 41 98 133 268 84 34 65 146 274), lower := (rows 41 98 133 268 84 34 65 128 256), losses := [] }

theorem u8079 : Upper (D 6) (R 6) [40,96,129,260,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8079 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8080 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 98 133 268 84 34 66 145 273), lower := (rows 41 98 133 268 84 34 66 128 256), losses := [] }

theorem u8080 : Upper (D 6) (R 6) [40,96,129,260,68,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8080 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8081 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 133 268 84 34 80 131 259), lower := (rows 41 98 133 268 84 34 80 128 256), losses := [] }

theorem u8081 : Upper (D 6) (R 6) [40,96,129,260,68,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8081 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8082 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 82, targets := 4 },{ cop := 0, region := 66, targets := 1 }], pairs := [(1,0),(1,2),(4,2)], upper := (rows 41 98 133 280 81 36 66 134 262), lower := (rows 41 98 133 280 81 36 66 128 256), losses := [] }

theorem u8082 : Upper (D 6) (R 6) [40,96,129,272,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8082 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8083 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 133 280 81 36 68 130 258), lower := (rows 41 98 133 280 81 36 68 128 256), losses := [] }

theorem u8083 : Upper (D 6) (R 6) [40,96,129,272,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8083 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8084 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 66, targets := 4 }], pairs := [(1,2),(3,2),(3,5)], upper := (rows 41 98 133 328 22 36 65 146 274), lower := (rows 41 98 133 328 22 36 65 128 256), losses := [{ target := 2, region := (rows 1 35 0 24 16 32 69 144 272), good := (rows 107 98 195 328 474 98 67 128 256) },{ target := 5, region := (rows 1 2 4 24 16 0 69 144 272), good := (rows 73 66 197 328 478 68 65 128 256) }] }

theorem u8084 : Upper (D 6) (R 6) [40,96,129,320,6,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8084 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8085 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 0, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 41 98 133 328 22 36 66 145 273), lower := (rows 41 98 133 328 22 36 66 128 256), losses := [] }

theorem u8085 : Upper (D 6) (R 6) [40,96,129,320,6,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8085 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8086 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 265, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 41 98 133 328 22 36 80 131 259), lower := (rows 41 98 133 328 22 36 80 128 256), losses := [] }

theorem u8086 : Upper (D 6) (R 6) [40,96,129,320,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8086 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8087 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 66, targets := 4 }], pairs := [(1,2),(3,5)], upper := (rows 41 98 133 328 22 48 65 134 262), lower := (rows 41 98 133 328 22 48 65 128 256), losses := [{ target := 5, region := (rows 1 2 4 24 16 0 69 144 272), good := (rows 73 66 197 328 478 408 65 128 256) }] }

theorem u8087 : Upper (D 6) (R 6) [40,96,129,320,6,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8087 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8088 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 132, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 41 98 133 328 22 48 66 133 261), lower := (rows 41 98 133 328 22 48 66 128 256), losses := [] }

theorem u8088 : Upper (D 6) (R 6) [40,96,129,320,6,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8088 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8089 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 265, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 41 98 133 328 22 48 68 131 259), lower := (rows 41 98 133 328 22 48 68 128 256), losses := [] }

theorem u8089 : Upper (D 6) (R 6) [40,96,129,320,6,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8089 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8090 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 98 134 13 84 288 65 146 274), lower := (rows 41 98 134 13 84 288 65 128 256), losses := [] }

theorem u8090 : Upper (D 6) (R 6) [40,96,130,5,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8090 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8091 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 297, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 98 134 13 84 288 66 145 273), lower := (rows 41 98 134 13 84 288 66 128 256), losses := [] }

theorem u8091 : Upper (D 6) (R 6) [40,96,130,5,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8091 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8092 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6)], upper := (rows 41 98 134 13 84 288 80 131 259), lower := (rows 41 98 134 13 84 288 80 128 256), losses := [] }

theorem u8092 : Upper (D 6) (R 6) [40,96,130,5,68,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8092 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8093 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 98 134 13 274 48 65 196 324), lower := (rows 41 98 134 13 274 48 65 128 256), losses := [] }

theorem u8093 : Upper (D 6) (R 6) [40,96,130,5,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8093 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8094 : Route 9 := (fun mask => (mask,id))

def c8094 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8094 : Upper (D 6) (R 6) [40,96,130,5,258,16,4] 13 := by
  apply FastRouting.sound _ _ [40,96,130,5,258,16,4] 13 (by decide) (choices 1) [1,64] r8094 c8094
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u629
  · exact u630

def b8095 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 422, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 98 134 25 84 288 65 134 262), lower := (rows 41 98 134 25 84 288 65 128 256), losses := [] }

theorem u8095 : Upper (D 6) (R 6) [40,96,130,17,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8095 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8096 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 297, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 98 134 25 84 288 66 133 261), lower := (rows 41 98 134 25 84 288 66 128 256), losses := [] }

theorem u8096 : Upper (D 6) (R 6) [40,96,130,17,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8096 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8097 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 41 98 134 25 84 288 68 131 259), lower := (rows 41 98 134 25 84 288 68 128 256), losses := [] }

theorem u8097 : Upper (D 6) (R 6) [40,96,130,17,68,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8097 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8098 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 41 98 134 25 274 36 65 196 324), lower := (rows 41 98 134 25 274 36 65 128 256), losses := [] }

theorem u8098 : Upper (D 6) (R 6) [40,96,130,17,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8098 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8099 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 134 25 274 36 68 193 321), lower := (rows 41 98 134 25 274 36 68 128 256), losses := [] }

theorem u8099 : Upper (D 6) (R 6) [40,96,130,17,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8099 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u8099
end Delivery.IrregularNine14.P06
