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

def b9120 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 259 70 42 88 160 80 129 385), lower := (rows 37 259 70 42 88 160 80 128 256), losses := [] }

theorem u9120 : Upper (D 7) (R 7) [36,257,66,34,72,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9120 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9121 : PairBound 9 := { available := 17, camps := [], pairs := [(0,1),(2,0),(3,0),(4,0)], upper := (rows 37 259 70 42 88 160 192 145 273), lower := (rows 37 259 70 42 88 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 12 29 224 224 128 256), good := (rows 124 274 126 126 124 224 224 224 256) },{ target := 1, region := (rows 5 0 4 8 24 224 224 128 256), good := (rows 101 257 101 120 120 224 224 224 256) }] }

theorem u9121 : Upper (D 7) (R 7) [36,257,66,34,72,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9122 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 177, targets := 2 }], pairs := [(0,1),(4,1)], upper := (rows 37 259 70 42 145 48 72 192 448), lower := (rows 37 259 70 42 145 48 72 128 256), losses := [] }

theorem u9122 : Upper (D 7) (R 7) [36,257,66,34,129,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9122 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r9123 : Route 9 := (fun mask => (mask,id))

def c9123 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u9123 : Upper (D 7) (R 7) [36,257,66,34,129,16,128] 13 := by
  apply FastRouting.sound _ _ [36,257,66,34,129,16,128] 13 (by decide) (choices 1) [8,64] r9123 c9123
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u727
  · exact u728

def b9124 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,1),(2,0),(4,1)], upper := (rows 37 259 70 42 145 160 72 208 336), lower := (rows 37 259 70 42 145 160 72 128 256), losses := [] }

theorem u9124 : Upper (D 7) (R 7) [36,257,66,34,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9124 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r9125 : Route 9 := (fun mask => (mask,id))

def c9125 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u9125 : Upper (D 7) (R 7) [36,257,66,34,129,128,16] 13 := by
  apply FastRouting.sound _ _ [36,257,66,34,129,128,16] 13 (by decide) (choices 1) [8,64] r9125 c9125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u729
  · exact u730

def b9126 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 68, targets := 160 },{ cop := 2, region := 184, targets := 1 }], pairs := [(2,5),(2,7),(3,0),(4,0)], upper := (rows 37 259 70 42 152 160 65 208 336), lower := (rows 37 259 70 42 152 160 65 128 256), losses := [] }

theorem u9126 : Upper (D 7) (R 7) [36,257,66,34,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9126 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r9127 : Route 9 := (fun mask => (mask,id))

def c9127 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u9127 : Upper (D 7) (R 7) [36,257,66,34,136,128,16] 13 := by
  apply FastRouting.sound _ _ [36,257,66,34,136,128,16] 13 (by decide) (choices 1) [1,64] r9127 c9127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u731
  · exact u732

def b9128 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 1, region := 68, targets := 32 }], pairs := [(1,6),(2,5),(3,6)], upper := (rows 37 259 70 42 208 48 65 136 392), lower := (rows 37 259 70 42 208 48 65 128 256), losses := [] }

theorem u9128 : Upper (D 7) (R 7) [36,257,66,34,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9128 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9129 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 37 259 70 42 208 48 72 129 385), lower := (rows 37 259 70 42 208 48 72 128 256), losses := [] }

theorem u9129 : Upper (D 7) (R 7) [36,257,66,34,192,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9129 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9130 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 259 70 42 208 48 192 137 265), lower := (rows 37 259 70 42 208 48 192 128 256), losses := [] }

theorem u9130 : Upper (D 7) (R 7) [36,257,66,34,192,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9130 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9131 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 68, targets := 160 },{ cop := 2, region := 184, targets := 1 }], pairs := [(2,5),(2,7),(3,0),(4,0)], upper := (rows 37 259 70 42 208 160 65 152 280), lower := (rows 37 259 70 42 208 160 65 128 256), losses := [] }

theorem u9131 : Upper (D 7) (R 7) [36,257,66,34,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9131 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9132 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,1),(2,0),(4,1)], upper := (rows 37 259 70 42 208 160 72 145 273), lower := (rows 37 259 70 42 208 160 72 128 256), losses := [] }

theorem u9132 : Upper (D 7) (R 7) [36,257,66,34,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9132 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9133 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 259 70 42 208 160 80 137 265), lower := (rows 37 259 70 42 208 160 80 128 256), losses := [] }

theorem u9133 : Upper (D 7) (R 7) [36,257,66,34,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9133 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9134 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 84, targets := 160 }], pairs := [(2,5),(2,7),(4,5),(4,7)], upper := (rows 37 259 70 56 81 160 66 136 392), lower := (rows 37 259 70 56 81 160 66 128 256), losses := [] }

theorem u9134 : Upper (D 7) (R 7) [36,257,66,48,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9134 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9135 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 37 259 70 56 81 160 72 130 386), lower := (rows 37 259 70 56 81 160 72 128 256), losses := [] }

theorem u9135 : Upper (D 7) (R 7) [36,257,66,48,65,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9135 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9136 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 426, targets := 64 }], pairs := [(0,1),(1,6),(3,0),(3,6)], upper := (rows 37 259 70 56 81 160 192 138 266), lower := (rows 37 259 70 56 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 224 224 128 256), good := (rows 100 258 102 120 120 224 224 224 256) },{ target := 1, region := (rows 5 0 4 29 21 224 224 128 256), good := (rows 125 281 125 120 121 224 224 224 256) }] }

theorem u9136 : Upper (D 7) (R 7) [36,257,66,48,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9136 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9137 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 37 259 70 73 146 160 72 176 304), lower := (rows 37 259 70 73 146 160 72 128 256), losses := [] }

theorem u9137 : Upper (D 7) (R 7) [36,257,66,65,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9137 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9138 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 169, targets := 2 },{ cop := 3, region := 418, targets := 64 }], pairs := [(0,1),(1,6),(3,1)], upper := (rows 37 259 70 73 146 160 80 168 296), lower := (rows 37 259 70 73 146 160 80 128 256), losses := [] }

theorem u9138 : Upper (D 7) (R 7) [36,257,66,65,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9138 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9139 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 259 70 73 146 160 96 152 280), lower := (rows 37 259 70 73 146 160 96 128 256), losses := [] }

theorem u9139 : Upper (D 7) (R 7) [36,257,66,65,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9139 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9140 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 37 259 70 73 152 48 66 160 416), lower := (rows 37 259 70 73 152 48 66 128 256), losses := [] }

theorem u9140 : Upper (D 7) (R 7) [36,257,66,65,136,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9140 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9141 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 259 70 73 152 48 96 130 386), lower := (rows 37 259 70 73 152 48 96 128 256), losses := [] }

theorem u9141 : Upper (D 7) (R 7) [36,257,66,65,136,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9141 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9142 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 0, region := 258, targets := 128 }], pairs := [(1,6),(1,7),(4,6)], upper := (rows 37 259 70 73 152 48 192 162 290), lower := (rows 37 259 70 73 152 48 192 128 256), losses := [] }

theorem u9142 : Upper (D 7) (R 7) [36,257,66,65,136,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9142 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9143 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 37 259 70 73 152 160 66 176 304), lower := (rows 37 259 70 73 152 160 66 128 256), losses := [] }

theorem u9143 : Upper (D 7) (R 7) [36,257,66,65,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9143 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9144 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 258, targets := 128 }], pairs := [(0,6),(1,6),(1,7)], upper := (rows 37 259 70 73 152 160 80 162 290), lower := (rows 37 259 70 73 152 160 80 128 256), losses := [] }

theorem u9144 : Upper (D 7) (R 7) [36,257,66,65,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9144 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9145 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 259 70 73 152 160 96 146 274), lower := (rows 37 259 70 73 152 160 96 128 256), losses := [] }

theorem u9145 : Upper (D 7) (R 7) [36,257,66,65,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9146 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 68, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 37 259 70 88 145 40 66 160 416), lower := (rows 37 259 70 88 145 40 66 128 256), losses := [] }

theorem u9146 : Upper (D 7) (R 7) [36,257,66,80,129,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9146 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9147 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 402, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 37 259 70 88 145 40 96 130 386), lower := (rows 37 259 70 88 145 40 96 128 256), losses := [] }

theorem u9147 : Upper (D 7) (R 7) [36,257,66,80,129,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9147 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9148 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 259 70 88 145 40 192 162 290), lower := (rows 37 259 70 88 145 40 192 128 256), losses := [] }

theorem u9148 : Upper (D 7) (R 7) [36,257,66,80,129,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9148 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9149 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 185, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 37 259 70 88 145 160 66 168 296), lower := (rows 37 259 70 88 145 160 66 128 256), losses := [] }

theorem u9149 : Upper (D 7) (R 7) [36,257,66,80,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9149 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9150 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 37 259 70 88 145 160 72 162 290), lower := (rows 37 259 70 88 145 160 72 128 256), losses := [] }

theorem u9150 : Upper (D 7) (R 7) [36,257,66,80,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9150 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9151 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 104, targets := 3 }], pairs := [(1,5),(2,0),(3,0),(3,1)], upper := (rows 37 259 70 88 145 160 96 138 266), lower := (rows 37 259 70 88 145 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 6 24 16 176 249 128 256), good := (rows 100 326 70 120 248 224 96 224 256) },{ target := 5, region := (rows 1 19 12 12 19 0 64 141 269), good := (rows 415 403 478 478 403 128 64 128 256) }] }

theorem u9151 : Upper (D 7) (R 7) [36,257,66,80,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9151 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9152 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 259 70 88 146 40 65 160 416), lower := (rows 37 259 70 88 146 40 65 128 256), losses := [] }

theorem u9152 : Upper (D 7) (R 7) [36,257,66,80,130,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9152 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9153 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 402, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 37 259 70 88 146 40 96 129 385), lower := (rows 37 259 70 88 146 40 96 128 256), losses := [] }

theorem u9153 : Upper (D 7) (R 7) [36,257,66,80,130,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9153 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9154 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 259 70 88 146 40 192 161 289), lower := (rows 37 259 70 88 146 40 192 128 256), losses := [] }

theorem u9154 : Upper (D 7) (R 7) [36,257,66,80,130,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9154 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9155 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 68, targets := 160 },{ cop := 2, region := 184, targets := 1 }], pairs := [(2,5),(2,7),(3,0),(4,0)], upper := (rows 37 259 70 88 146 160 65 168 296), lower := (rows 37 259 70 88 146 160 65 128 256), losses := [] }

theorem u9155 : Upper (D 7) (R 7) [36,257,66,80,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9155 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9156 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 37 259 70 88 146 160 72 161 289), lower := (rows 37 259 70 88 146 160 72 128 256), losses := [] }

theorem u9156 : Upper (D 7) (R 7) [36,257,66,80,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9156 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9157 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 108, targets := 1 },{ cop := 4, region := 104, targets := 2 }], pairs := [(1,5),(2,0),(3,0),(3,1)], upper := (rows 37 259 70 88 146 160 96 137 265), lower := (rows 37 259 70 88 146 160 96 128 256), losses := [{ target := 5, region := (rows 1 3 4 12 19 0 64 129 257), good := (rows 415 403 94 88 146 128 64 128 256) }] }

theorem u9157 : Upper (D 7) (R 7) [36,257,66,80,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9157 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9158 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 68, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 37 259 70 104 145 48 66 136 392), lower := (rows 37 259 70 104 145 48 66 128 256), losses := [] }

theorem u9158 : Upper (D 7) (R 7) [36,257,66,96,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9158 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9159 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 37 259 70 104 145 48 72 130 386), lower := (rows 37 259 70 104 145 48 72 128 256), losses := [] }

theorem u9159 : Upper (D 7) (R 7) [36,257,66,96,129,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9159 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9160 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 259 70 104 145 48 192 138 266), lower := (rows 37 259 70 104 145 48 192 128 256), losses := [] }

theorem u9160 : Upper (D 7) (R 7) [36,257,66,96,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9160 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9161 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 185, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 37 259 70 104 145 160 66 152 280), lower := (rows 37 259 70 104 145 160 66 128 256), losses := [] }

theorem u9161 : Upper (D 7) (R 7) [36,257,66,96,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9162 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 37 259 70 104 145 160 72 146 274), lower := (rows 37 259 70 104 145 160 72 128 256), losses := [] }

theorem u9162 : Upper (D 7) (R 7) [36,257,66,96,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9162 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9163 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 259 70 104 145 160 80 138 266), lower := (rows 37 259 70 104 145 160 80 128 256), losses := [] }

theorem u9163 : Upper (D 7) (R 7) [36,257,66,96,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9163 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9164 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 259 70 104 146 48 65 136 392), lower := (rows 37 259 70 104 146 48 65 128 256), losses := [] }

theorem u9164 : Upper (D 7) (R 7) [36,257,66,96,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9164 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9165 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 37 259 70 104 146 48 72 129 385), lower := (rows 37 259 70 104 146 48 72 128 256), losses := [] }

theorem u9165 : Upper (D 7) (R 7) [36,257,66,96,130,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9165 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9166 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 259 70 104 146 48 192 137 265), lower := (rows 37 259 70 104 146 48 192 128 256), losses := [] }

theorem u9166 : Upper (D 7) (R 7) [36,257,66,96,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9166 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9167 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 72, targets := 130 },{ cop := 1, region := 68, targets := 160 }], pairs := [(2,5),(2,7),(3,1),(3,7)], upper := (rows 37 259 70 104 146 160 65 152 280), lower := (rows 37 259 70 104 146 160 65 128 256), losses := [] }

theorem u9167 : Upper (D 7) (R 7) [36,257,66,96,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9167 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9168 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 37 259 70 104 146 160 72 145 273), lower := (rows 37 259 70 104 146 160 72 128 256), losses := [] }

theorem u9168 : Upper (D 7) (R 7) [36,257,66,96,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9168 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9169 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 259 70 104 146 160 80 137 265), lower := (rows 37 259 70 104 146 160 80 128 256), losses := [] }

theorem u9169 : Upper (D 7) (R 7) [36,257,66,96,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9169 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9170 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 72, targets := 130 },{ cop := 1, region := 68, targets := 160 }], pairs := [(2,5),(2,7),(3,1),(3,7)], upper := (rows 37 259 70 104 152 160 65 146 274), lower := (rows 37 259 70 104 152 160 65 128 256), losses := [] }

theorem u9170 : Upper (D 7) (R 7) [36,257,66,96,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9170 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9171 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 185, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 37 259 70 104 152 160 66 145 273), lower := (rows 37 259 70 104 152 160 66 128 256), losses := [] }

theorem u9171 : Upper (D 7) (R 7) [36,257,66,96,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9172 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 37 259 70 104 152 160 80 131 259), lower := (rows 37 259 70 104 152 160 80 128 256), losses := [] }

theorem u9172 : Upper (D 7) (R 7) [36,257,66,96,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9172 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9173 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 68, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 37 259 70 137 146 40 80 224 352), lower := (rows 37 259 70 137 146 40 80 128 256), losses := [] }

theorem u9173 : Upper (D 7) (R 7) [36,257,66,129,130,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9173 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9174 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 144, targets := 33 }], pairs := [(2,0),(4,0),(4,5)], upper := (rows 37 259 70 137 146 40 96 208 336), lower := (rows 37 259 70 137 146 40 96 128 256), losses := [{ target := 0, region := (rows 0 2 6 8 22 40 105 135 263), good := (rows 500 470 470 488 406 104 96 128 256) }] }

theorem u9174 : Upper (D 7) (R 7) [36,257,66,129,130,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9174 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9175 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 200, targets := 2 },{ cop := 2, region := 176, targets := 1 }], pairs := [(3,1),(4,0)], upper := (rows 37 259 70 137 146 48 72 224 352), lower := (rows 37 259 70 137 146 48 72 128 256), losses := [] }

theorem u9175 : Upper (D 7) (R 7) [36,257,66,129,130,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9175 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9176 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 101, targets := 128 },{ cop := 0, region := 200, targets := 2 }], pairs := [(0,7),(2,7),(3,1)], upper := (rows 37 259 70 137 146 48 96 200 328), lower := (rows 37 259 70 137 146 48 96 128 256), losses := [] }

theorem u9176 : Upper (D 7) (R 7) [36,257,66,129,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9176 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9177 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 68, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 37 259 70 137 208 40 66 176 304), lower := (rows 37 259 70 137 208 40 66 128 256), losses := [] }

theorem u9177 : Upper (D 7) (R 7) [36,257,66,129,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9177 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9178 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 37 259 70 137 208 40 80 162 290), lower := (rows 37 259 70 137 208 40 80 128 256), losses := [] }

theorem u9178 : Upper (D 7) (R 7) [36,257,66,129,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9178 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9179 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 144, targets := 33 },{ cop := 3, region := 112, targets := 2 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 37 259 70 137 208 40 96 146 274), lower := (rows 37 259 70 137 208 40 96 128 256), losses := [] }

theorem u9179 : Upper (D 7) (R 7) [36,257,66,129,192,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9179 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u9179
end Delivery.IrregularNine14.P07
