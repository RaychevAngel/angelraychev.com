import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0012

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9060 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 259 69 56 208 34 72 130 386), lower := (rows 37 259 69 56 208 34 72 128 256), losses := [] }

theorem u9060 : Upper (D 7) (R 7) [36,257,65,48,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9060 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9061 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 259 69 56 208 34 192 138 266), lower := (rows 37 259 69 56 208 34 192 128 256), losses := [] }

theorem u9061 : Upper (D 7) (R 7) [36,257,65,48,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9061 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9062 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 37 259 69 74 146 160 72 176 304), lower := (rows 37 259 69 74 146 160 72 128 256), losses := [] }

theorem u9062 : Upper (D 7) (R 7) [36,257,65,66,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9062 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9063 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 3, region := 165, targets := 2 }], pairs := [(0,1),(3,0),(4,0)], upper := (rows 37 259 69 74 146 160 80 168 296), lower := (rows 37 259 69 74 146 160 80 128 256), losses := [] }

theorem u9063 : Upper (D 7) (R 7) [36,257,65,66,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9063 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9064 : PairBound 9 := { available := 24, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 259 69 74 146 160 96 152 280), lower := (rows 37 259 69 74 146 160 96 128 256), losses := [] }

theorem u9064 : Upper (D 7) (R 7) [36,257,65,66,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9064 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9065 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 37 259 69 74 152 160 66 176 304), lower := (rows 37 259 69 74 152 160 66 128 256), losses := [] }

theorem u9065 : Upper (D 7) (R 7) [36,257,65,66,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9065 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9066 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 37 259 69 74 152 160 80 162 290), lower := (rows 37 259 69 74 152 160 80 128 256), losses := [] }

theorem u9066 : Upper (D 7) (R 7) [36,257,65,66,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9066 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9067 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 259 69 74 152 160 96 146 274), lower := (rows 37 259 69 74 152 160 96 128 256), losses := [] }

theorem u9067 : Upper (D 7) (R 7) [36,257,65,66,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9067 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9068 : PairBound 9 := { available := 136, camps := [{ cop := 8, region := 103, targets := 128 },{ cop := 1, region := 248, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 37 259 69 88 176 34 66 136 392), lower := (rows 37 259 69 88 176 34 66 128 256), losses := [] }

theorem u9068 : Upper (D 7) (R 7) [36,257,65,80,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9068 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9069 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 77, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 259 69 88 176 34 72 130 386), lower := (rows 37 259 69 88 176 34 72 128 256), losses := [] }

theorem u9069 : Upper (D 7) (R 7) [36,257,65,80,160,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9069 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9070 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 69, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,7)], upper := (rows 37 259 69 88 176 34 192 138 266), lower := (rows 37 259 69 88 176 34 192 128 256), losses := [] }

theorem u9070 : Upper (D 7) (R 7) [36,257,65,80,160,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9070 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9071 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,7),(3,0),(4,0)], upper := (rows 37 259 69 138 176 34 72 208 336), lower := (rows 37 259 69 138 176 34 72 128 256), losses := [] }

theorem u9071 : Upper (D 7) (R 7) [36,257,65,130,160,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9071 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9072 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 259 69 138 176 34 80 200 328), lower := (rows 37 259 69 138 176 34 80 128 256), losses := [] }

theorem u9072 : Upper (D 7) (R 7) [36,257,65,130,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9072 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9073 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 259 69 138 208 34 72 176 304), lower := (rows 37 259 69 138 208 34 72 128 256), losses := [] }

theorem u9073 : Upper (D 7) (R 7) [36,257,65,130,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9073 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9074 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 259 69 138 208 34 80 168 296), lower := (rows 37 259 69 138 208 34 80 128 256), losses := [] }

theorem u9074 : Upper (D 7) (R 7) [36,257,65,130,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9074 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9075 : PairBound 9 := { available := 24, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 259 69 138 208 34 96 152 280), lower := (rows 37 259 69 138 208 34 96 128 256), losses := [] }

theorem u9075 : Upper (D 7) (R 7) [36,257,65,130,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9075 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9076 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 1, region := 68, targets := 32 }], pairs := [(2,5),(3,0),(4,0)], upper := (rows 37 259 69 138 208 40 66 176 304), lower := (rows 37 259 69 138 208 40 66 128 256), losses := [] }

theorem u9076 : Upper (D 7) (R 7) [36,257,65,130,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9076 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9077 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 37 259 69 138 208 40 80 162 290), lower := (rows 37 259 69 138 208 40 80 128 256), losses := [] }

theorem u9077 : Upper (D 7) (R 7) [36,257,65,130,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9077 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9078 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 259 69 138 208 40 96 146 274), lower := (rows 37 259 69 138 208 40 96 128 256), losses := [] }

theorem u9078 : Upper (D 7) (R 7) [36,257,65,130,192,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9078 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9079 : PairBound 9 := { available := 24, camps := [{ cop := 8, region := 103, targets := 128 },{ cop := 1, region := 248, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 37 259 69 168 208 34 66 152 280), lower := (rows 37 259 69 168 208 34 66 128 256), losses := [] }

theorem u9079 : Upper (D 7) (R 7) [36,257,65,160,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9079 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9080 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 85, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 259 69 168 208 34 72 146 274), lower := (rows 37 259 69 168 208 34 72 128 256), losses := [] }

theorem u9080 : Upper (D 7) (R 7) [36,257,65,160,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9080 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9081 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 259 69 168 208 34 80 138 266), lower := (rows 37 259 69 168 208 34 80 128 256), losses := [] }

theorem u9081 : Upper (D 7) (R 7) [36,257,65,160,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9081 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9082 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 259 70 25 50 160 72 192 448), lower := (rows 37 259 70 25 50 160 72 128 256), losses := [] }

theorem u9082 : Upper (D 7) (R 7) [36,257,66,17,34,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9082 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9083 : PairBound 9 := { available := 72, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,0),(2,5),(4,0)], upper := (rows 37 259 70 25 50 160 192 200 328), lower := (rows 37 259 70 25 50 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 20 232 232 136 264), good := (rows 116 258 118 508 118 224 224 224 256) }] }

theorem u9083 : Upper (D 7) (R 7) [36,257,66,17,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9083 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9084 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 92, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 37 259 70 25 88 160 66 160 416), lower := (rows 37 259 70 25 88 160 66 128 256), losses := [] }

theorem u9084 : Upper (D 7) (R 7) [36,257,66,17,72,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9084 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9085 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 37 259 70 25 88 160 96 130 386), lower := (rows 37 259 70 25 88 160 96 128 256), losses := [] }

theorem u9085 : Upper (D 7) (R 7) [36,257,66,17,72,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9085 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9086 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 258, targets := 128 },{ cop := 1, region := 228, targets := 1 }], pairs := [(0,6),(1,6),(1,7),(2,0)], upper := (rows 37 259 70 25 88 160 192 162 290), lower := (rows 37 259 70 25 88 160 192 128 256), losses := [] }

theorem u9086 : Upper (D 7) (R 7) [36,257,66,17,72,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9086 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9087 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 185, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 37 259 70 25 112 160 66 136 392), lower := (rows 37 259 70 25 112 160 66 128 256), losses := [] }

theorem u9087 : Upper (D 7) (R 7) [36,257,66,17,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9087 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9088 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 37 259 70 25 112 160 72 130 386), lower := (rows 37 259 70 25 112 160 72 128 256), losses := [] }

theorem u9088 : Upper (D 7) (R 7) [36,257,66,17,96,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9088 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9089 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 259 70 25 112 160 192 138 266), lower := (rows 37 259 70 25 112 160 192 128 256), losses := [] }

theorem u9089 : Upper (D 7) (R 7) [36,257,66,17,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9089 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9090 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 259 70 25 146 40 96 192 448), lower := (rows 37 259 70 25 146 40 96 128 256), losses := [] }

theorem u9090 : Upper (D 7) (R 7) [36,257,66,17,130,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9090 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9091 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 68, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 259 70 25 146 40 192 224 352), lower := (rows 37 259 70 25 146 40 192 128 256), losses := [{ target := 0, region := (rows 0 2 22 8 18 40 251 169 297), good := (rows 484 470 86 508 214 488 192 192 256) }] }

theorem u9091 : Upper (D 7) (R 7) [36,257,66,17,130,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9091 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r9092 : Route 9 := (fun mask => (mask,id))

def c9092 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9092 : Upper (D 7) (R 7) [36,257,66,17,130,128,8] 13 := by
  apply FastRouting.sound _ _ [36,257,66,17,130,128,8] 13 (by decide) (choices 1) [32,64] r9092 c9092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u725
  · exact u726

def b9093 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 100, targets := 1 }], pairs := [(1,5),(2,0),(3,5),(4,5)], upper := (rows 37 259 70 25 146 160 96 200 328), lower := (rows 37 259 70 25 146 160 96 128 256), losses := [{ target := 5, region := (rows 1 3 4 11 21 0 64 132 260), good := (rows 415 283 478 27 154 128 64 128 256) }] }

theorem u9093 : Upper (D 7) (R 7) [36,257,66,17,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9093 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9094 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 68, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 37 259 70 25 208 40 66 160 416), lower := (rows 37 259 70 25 208 40 66 128 256), losses := [] }

theorem u9094 : Upper (D 7) (R 7) [36,257,66,17,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9094 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9095 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 386, targets := 96 },{ cop := 2, region := 144, targets := 1 }], pairs := [(1,5),(1,6),(4,0)], upper := (rows 37 259 70 25 208 40 96 130 386), lower := (rows 37 259 70 25 208 40 96 128 256), losses := [] }

theorem u9095 : Upper (D 7) (R 7) [36,257,66,17,192,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9095 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9096 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 259 70 25 208 40 192 162 290), lower := (rows 37 259 70 25 208 40 192 128 256), losses := [] }

theorem u9096 : Upper (D 7) (R 7) [36,257,66,17,192,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9096 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9097 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 185, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 37 259 70 25 208 160 66 168 296), lower := (rows 37 259 70 25 208 160 66 128 256), losses := [] }

theorem u9097 : Upper (D 7) (R 7) [36,257,66,17,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9098 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 258, targets := 128 }], pairs := [(0,6),(1,6),(1,7)], upper := (rows 37 259 70 25 208 160 72 162 290), lower := (rows 37 259 70 25 208 160 72 128 256), losses := [] }

theorem u9098 : Upper (D 7) (R 7) [36,257,66,17,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9098 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9099 : PairBound 9 := { available := 10, camps := [{ cop := 5, region := 80, targets := 3 },{ cop := 3, region := 258, targets := 32 },{ cop := 3, region := 258, targets := 64 }], pairs := [(1,5),(1,6),(4,0),(4,1)], upper := (rows 37 259 70 25 208 160 96 138 266), lower := (rows 37 259 70 25 208 160 96 128 256), losses := [] }

theorem u9099 : Upper (D 7) (R 7) [36,257,66,17,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9099 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9100 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 92, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 37 259 70 26 81 160 72 160 416), lower := (rows 37 259 70 26 81 160 72 128 256), losses := [] }

theorem u9100 : Upper (D 7) (R 7) [36,257,66,18,65,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9100 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9101 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 37 259 70 26 81 160 96 136 392), lower := (rows 37 259 70 26 81 160 96 128 256), losses := [] }

theorem u9101 : Upper (D 7) (R 7) [36,257,66,18,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9101 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9102 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 3, region := 228, targets := 1 }], pairs := [(0,1),(1,6),(2,0),(3,6)], upper := (rows 37 259 70 26 81 160 192 168 296), lower := (rows 37 259 70 26 81 160 192 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 21 232 232 136 264), good := (rows 117 273 117 504 113 224 224 224 256) }] }

theorem u9102 : Upper (D 7) (R 7) [36,257,66,18,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9102 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9103 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 80, targets := 130 },{ cop := 1, region := 68, targets := 160 }], pairs := [(2,5),(2,7),(4,1),(4,7)], upper := (rows 37 259 70 26 112 160 65 136 392), lower := (rows 37 259 70 26 112 160 65 128 256), losses := [] }

theorem u9103 : Upper (D 7) (R 7) [36,257,66,18,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9103 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9104 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 68, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 37 259 70 26 112 160 72 129 385), lower := (rows 37 259 70 26 112 160 72 128 256), losses := [] }

theorem u9104 : Upper (D 7) (R 7) [36,257,66,18,96,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9104 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9105 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 259 70 26 112 160 192 137 265), lower := (rows 37 259 70 26 112 160 192 128 256), losses := [] }

theorem u9105 : Upper (D 7) (R 7) [36,257,66,18,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9105 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9106 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 101, targets := 128 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,7),(2,7),(4,1)], upper := (rows 37 259 70 26 145 40 96 192 448), lower := (rows 37 259 70 26 145 40 96 128 256), losses := [] }

theorem u9106 : Upper (D 7) (R 7) [36,257,66,18,129,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9106 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9107 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 208, targets := 2 },{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0),(2,5),(4,1)], upper := (rows 37 259 70 26 145 40 192 224 352), lower := (rows 37 259 70 26 145 40 192 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 16 0 208 128 256), good := (rows 5 259 70 94 209 12 192 192 256) }] }

theorem u9107 : Upper (D 7) (R 7) [36,257,66,18,129,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9107 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9108 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 3, region := 68, targets := 32 }], pairs := [(0,1),(2,5),(4,1)], upper := (rows 37 259 70 26 145 160 72 224 352), lower := (rows 37 259 70 26 145 160 72 128 256), losses := [] }

theorem u9108 : Upper (D 7) (R 7) [36,257,66,18,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9108 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9109 : PairBound 9 := { available := 72, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(1,5),(2,0),(3,5),(4,5)], upper := (rows 37 259 70 26 145 160 96 200 328), lower := (rows 37 259 70 26 145 160 96 128 256), losses := [{ target := 5, region := (rows 1 3 4 27 17 0 64 132 260), good := (rows 415 283 462 26 155 128 64 128 256) }] }

theorem u9109 : Upper (D 7) (R 7) [36,257,66,18,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9109 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9110 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 68, targets := 160 },{ cop := 2, region := 184, targets := 1 }], pairs := [(2,5),(2,7),(3,0)], upper := (rows 37 259 70 26 208 40 65 160 416), lower := (rows 37 259 70 26 208 40 65 128 256), losses := [] }

theorem u9110 : Upper (D 7) (R 7) [36,257,66,18,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9110 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9111 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 386, targets := 96 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,7),(1,5),(1,6)], upper := (rows 37 259 70 26 208 40 96 129 385), lower := (rows 37 259 70 26 208 40 96 128 256), losses := [] }

theorem u9111 : Upper (D 7) (R 7) [36,257,66,18,192,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9111 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9112 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 259 70 26 208 40 192 161 289), lower := (rows 37 259 70 26 208 40 192 128 256), losses := [] }

theorem u9112 : Upper (D 7) (R 7) [36,257,66,18,192,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9112 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9113 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 68, targets := 160 },{ cop := 2, region := 184, targets := 1 }], pairs := [(2,5),(2,7),(3,0),(4,0)], upper := (rows 37 259 70 26 208 160 65 168 296), lower := (rows 37 259 70 26 208 160 65 128 256), losses := [] }

theorem u9113 : Upper (D 7) (R 7) [36,257,66,18,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9113 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9114 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 68, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 37 259 70 26 208 160 72 161 289), lower := (rows 37 259 70 26 208 160 72 128 256), losses := [] }

theorem u9114 : Upper (D 7) (R 7) [36,257,66,18,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9114 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9115 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 80, targets := 3 }], pairs := [(1,5),(2,0),(4,0),(4,1)], upper := (rows 37 259 70 26 208 160 96 137 265), lower := (rows 37 259 70 26 208 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 14 8 176 176 249 128 256), good := (rows 116 326 70 126 240 240 112 240 256) },{ target := 5, region := (rows 1 3 4 13 20 0 64 131 259), good := (rows 415 395 478 410 208 128 64 128 256) }] }

theorem u9115 : Upper (D 7) (R 7) [36,257,66,18,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9115 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9116 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 85, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 259 70 42 81 160 72 144 400), lower := (rows 37 259 70 42 81 160 72 128 256), losses := [] }

theorem u9116 : Upper (D 7) (R 7) [36,257,66,34,65,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9116 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9117 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 84, targets := 160 }], pairs := [(2,5),(2,7),(4,5)], upper := (rows 37 259 70 42 81 160 80 136 392), lower := (rows 37 259 70 42 81 160 80 128 256), losses := [] }

theorem u9117 : Upper (D 7) (R 7) [36,257,66,34,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9117 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9118 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(3,6)], upper := (rows 37 259 70 42 81 160 192 152 280), lower := (rows 37 259 70 42 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 12 16 224 224 128 256), good := (rows 108 258 110 110 112 224 224 224 256) }] }

theorem u9118 : Upper (D 7) (R 7) [36,257,66,34,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9118 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9119 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 85, targets := 128 },{ cop := 2, region := 184, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 37 259 70 42 88 160 65 144 400), lower := (rows 37 259 70 42 88 160 65 128 256), losses := [] }

theorem u9119 : Upper (D 7) (R 7) [36,257,66,34,72,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9119 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u9119
end Delivery.IrregularNine14.P07
