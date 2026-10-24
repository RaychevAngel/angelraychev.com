import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0124

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b24120 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 194, targets := 1 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 138 261 28 112 33 70 198 326), lower := (rows 35 138 261 28 112 33 64 128 256), losses := [] }

theorem u24120 : Upper (D 6) (R 6) [34,136,257,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24120 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24121 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 261 28 112 34 69 197 325), lower := (rows 35 138 261 28 112 34 64 128 256), losses := [] }

theorem u24121 : Upper (D 6) (R 6) [34,136,257,20,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24121 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24122 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 80, targets := 4 },{ cop := 0, region := 324, targets := 32 }], pairs := [(0,6),(2,5),(4,2)], upper := (rows 35 138 261 28 112 36 67 195 323), lower := (rows 35 138 261 28 112 36 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 44 0 128 256), good := (rows 35 171 293 60 48 36 0 128 256) }] }

theorem u24122 : Upper (D 6) (R 6) [34,136,257,20,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24122 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24123 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 138 261 28 112 96 71 135 263), lower := (rows 35 138 261 28 112 96 64 128 256), losses := [] }

theorem u24123 : Upper (D 6) (R 6) [34,136,257,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24123 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24124 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 138 261 44 84 33 82 210 338), lower := (rows 35 138 261 44 84 33 64 128 256), losses := [] }

theorem u24124 : Upper (D 6) (R 6) [34,136,257,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24125 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 261 44 84 34 81 209 337), lower := (rows 35 138 261 44 84 34 64 128 256), losses := [] }

theorem u24125 : Upper (D 6) (R 6) [34,136,257,36,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24125 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24126 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 138 261 44 84 48 67 195 323), lower := (rows 35 138 261 44 84 48 64 128 256), losses := [] }

theorem u24126 : Upper (D 6) (R 6) [34,136,257,36,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24126 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24127 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 40, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 35 138 261 44 84 96 83 147 275), lower := (rows 35 138 261 44 84 96 64 128 256), losses := [] }

theorem u24127 : Upper (D 6) (R 6) [34,136,257,36,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24127 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24128 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 261 56 84 33 70 198 326), lower := (rows 35 138 261 56 84 33 64 128 256), losses := [] }

theorem u24128 : Upper (D 6) (R 6) [34,136,257,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24129 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 261 56 84 34 69 197 325), lower := (rows 35 138 261 56 84 34 64 128 256), losses := [] }

theorem u24129 : Upper (D 6) (R 6) [34,136,257,48,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24129 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24130 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 138 261 56 84 36 67 195 323), lower := (rows 35 138 261 56 84 36 64 128 256), losses := [] }

theorem u24130 : Upper (D 6) (R 6) [34,136,257,48,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24131 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 138 261 56 84 96 71 135 263), lower := (rows 35 138 261 56 84 96 64 128 256), losses := [] }

theorem u24131 : Upper (D 6) (R 6) [34,136,257,48,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24131 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24132 : Route 9 := (fun mask => (mask,id))

def c24132 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24132 : Upper (D 6) (R 6) [34,136,257,65,6,4] 13 := by
  apply FastRouting.sound _ _ [34,136,257,65,6,4] 13 (by decide) (choices 1) [16,32] r24132 c24132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7440
  · exact u7441

def b24133 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 138 261 73 22 48 100 228 356), lower := (rows 35 138 261 73 22 48 64 128 256), losses := [] }

theorem u24133 : Upper (D 6) (R 6) [34,136,257,65,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24133 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24134 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 276, targets := 64 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 35 138 261 73 22 96 116 180 308), lower := (rows 35 138 261 73 22 96 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 8 16 104 64 128 256), good := (rows 35 171 257 105 19 96 96 128 256) }] }

theorem u24134 : Upper (D 6) (R 6) [34,136,257,65,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24134 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24135 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 261 73 52 34 84 212 340), lower := (rows 35 138 261 73 52 34 64 128 256), losses := [] }

theorem u24135 : Upper (D 6) (R 6) [34,136,257,65,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24135 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24136 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 138 261 73 52 36 82 210 338), lower := (rows 35 138 261 73 52 36 64 128 256), losses := [] }

theorem u24136 : Upper (D 6) (R 6) [34,136,257,65,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24136 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24137 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 138 261 73 52 48 70 198 326), lower := (rows 35 138 261 73 52 48 64 128 256), losses := [] }

theorem u24137 : Upper (D 6) (R 6) [34,136,257,65,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24137 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24138 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 276, targets := 64 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 35 138 261 73 52 96 86 150 278), lower := (rows 35 138 261 73 52 96 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 8 16 104 64 128 256), good := (rows 35 171 257 105 48 96 96 128 256) }] }

theorem u24138 : Upper (D 6) (R 6) [34,136,257,65,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24138 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24139 : Route 9 := (fun mask => (mask,id))

def c24139 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24139 : Upper (D 6) (R 6) [34,136,257,65,66,4] 13 := by
  apply FastRouting.sound _ _ [34,136,257,65,66,4] 13 (by decide) (choices 1) [4,16,32] r24139 c24139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7442
  · exact u7443
  · exact u7444

def b24140 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 138 261 73 82 48 100 164 292), lower := (rows 35 138 261 73 82 48 64 128 256), losses := [] }

theorem u24140 : Upper (D 6) (R 6) [34,136,257,65,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24140 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24141 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 261 73 84 34 116 180 308), lower := (rows 35 138 261 73 84 34 64 128 256), losses := [] }

theorem u24141 : Upper (D 6) (R 6) [34,136,257,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24142 : Route 9 := (fun mask => (mask,id))

def c24142 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24142 : Upper (D 6) (R 6) [34,136,257,65,68,4] 13 := by
  apply FastRouting.sound _ _ [34,136,257,65,68,4] 13 (by decide) (choices 1) [2,16,32] r24142 c24142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7445
  · exact u7446
  · exact u7447

def b24143 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 260, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 35 138 261 73 84 48 102 166 294), lower := (rows 35 138 261 73 84 48 64 128 256), losses := [{ target := 6, region := (rows 1 10 13 8 16 48 0 129 257), good := (rows 423 142 389 399 52 48 0 128 256) }] }

theorem u24143 : Upper (D 6) (R 6) [34,136,257,65,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24143 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24144 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 261 73 112 34 84 148 276), lower := (rows 35 138 261 73 112 34 64 128 256), losses := [] }

theorem u24144 : Upper (D 6) (R 6) [34,136,257,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24144 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24145 : Route 9 := (fun mask => (mask,id))

def c24145 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24145 : Upper (D 6) (R 6) [34,136,257,65,96,4] 13 := by
  apply FastRouting.sound _ _ [34,136,257,65,96,4] 13 (by decide) (choices 1) [2,4,16] r24145 c24145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7448
  · exact u7449
  · exact u7450

def b24146 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 138 261 73 112 48 70 134 262), lower := (rows 35 138 261 73 112 48 64 128 256), losses := [] }

theorem u24146 : Upper (D 6) (R 6) [34,136,257,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24146 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24147 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 138 261 74 52 33 84 212 340), lower := (rows 35 138 261 74 52 33 64 128 256), losses := [] }

theorem u24147 : Upper (D 6) (R 6) [34,136,257,66,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24147 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24148 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 261 74 52 36 81 209 337), lower := (rows 35 138 261 74 52 36 64 128 256), losses := [] }

theorem u24148 : Upper (D 6) (R 6) [34,136,257,66,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24148 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24149 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 138 261 74 52 48 69 197 325), lower := (rows 35 138 261 74 52 48 64 128 256), losses := [] }

theorem u24149 : Upper (D 6) (R 6) [34,136,257,66,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24149 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24150 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 276, targets := 2 },{ cop := 0, region := 276, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 138 261 74 52 96 85 149 277), lower := (rows 35 138 261 74 52 96 64 128 256), losses := [] }

theorem u24150 : Upper (D 6) (R 6) [34,136,257,66,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24151 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 261 74 84 33 116 180 308), lower := (rows 35 138 261 74 84 33 64 128 256), losses := [] }

theorem u24151 : Upper (D 6) (R 6) [34,136,257,66,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24151 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24152 : Route 9 := (fun mask => (mask,id))

def c24152 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24152 : Upper (D 6) (R 6) [34,136,257,66,68,4] 13 := by
  apply FastRouting.sound _ _ [34,136,257,66,68,4] 13 (by decide) (choices 1) [1,16,32] r24152 c24152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7451
  · exact u7452
  · exact u7453

def b24153 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 138 261 74 84 48 101 165 293), lower := (rows 35 138 261 74 84 48 64 128 256), losses := [] }

theorem u24153 : Upper (D 6) (R 6) [34,136,257,66,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24153 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24154 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 261 74 112 33 84 148 276), lower := (rows 35 138 261 74 112 33 64 128 256), losses := [] }

theorem u24154 : Upper (D 6) (R 6) [34,136,257,66,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24154 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24155 : Route 9 := (fun mask => (mask,id))

def c24155 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24155 : Upper (D 6) (R 6) [34,136,257,66,96,4] 13 := by
  apply FastRouting.sound _ _ [34,136,257,66,96,4] 13 (by decide) (choices 1) [1,4,16] r24155 c24155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7454
  · exact u7455
  · exact u7456

def b24156 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 138 261 74 112 48 69 133 261), lower := (rows 35 138 261 74 112 48 64 128 256), losses := [] }

theorem u24156 : Upper (D 6) (R 6) [34,136,257,66,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24156 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24157 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(3,1)], upper := (rows 35 138 261 76 22 33 112 240 368), lower := (rows 35 138 261 76 22 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 37 80 144 272), good := (rows 33 136 293 108 508 33 64 128 256) }] }

theorem u24157 : Upper (D 6) (R 6) [34,136,257,68,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24157 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24158 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 138 261 76 22 48 97 225 353), lower := (rows 35 138 261 76 22 48 64 128 256), losses := [] }

theorem u24158 : Upper (D 6) (R 6) [34,136,257,68,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24158 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24159 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 276, targets := 64 },{ cop := 4, region := 97, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 35 138 261 76 22 96 113 177 305), lower := (rows 35 138 261 76 22 96 64 128 256), losses := [] }

theorem u24159 : Upper (D 6) (R 6) [34,136,257,68,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24159 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24160 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 138 261 76 52 33 82 210 338), lower := (rows 35 138 261 76 52 33 64 128 256), losses := [] }

theorem u24160 : Upper (D 6) (R 6) [34,136,257,68,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24161 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 261 76 52 34 81 209 337), lower := (rows 35 138 261 76 52 34 64 128 256), losses := [] }

theorem u24161 : Upper (D 6) (R 6) [34,136,257,68,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24161 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24162 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 138 261 76 52 48 67 195 323), lower := (rows 35 138 261 76 52 48 64 128 256), losses := [] }

theorem u24162 : Upper (D 6) (R 6) [34,136,257,68,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24162 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24163 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 276, targets := 64 },{ cop := 3, region := 48, targets := 1 }], pairs := [(2,6),(4,0),(4,6)], upper := (rows 35 138 261 76 52 96 83 147 275), lower := (rows 35 138 261 76 52 96 64 128 256), losses := [] }

theorem u24163 : Upper (D 6) (R 6) [34,136,257,68,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24163 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24164 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 261 76 81 34 116 180 308), lower := (rows 35 138 261 76 81 34 64 128 256), losses := [] }

theorem u24164 : Upper (D 6) (R 6) [34,136,257,68,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24164 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24165 : Route 9 := (fun mask => (mask,id))

def c24165 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24165 : Upper (D 6) (R 6) [34,136,257,68,65,4] 13 := by
  apply FastRouting.sound _ _ [34,136,257,68,65,4] 13 (by decide) (choices 1) [2,16,32] r24165 c24165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7457
  · exact u7458
  · exact u7459

def r24166 : Route 9 := (fun mask => (mask,id))

def c24166 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24166 : Upper (D 6) (R 6) [34,136,257,68,65,16] 13 := by
  apply FastRouting.sound _ _ [34,136,257,68,65,16] 13 (by decide) (choices 1) [2,4,32] r24166 c24166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7460
  · exact u7461
  · exact u7462

def b24167 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 293, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 138 261 76 82 33 116 180 308), lower := (rows 35 138 261 76 82 33 64 128 256), losses := [] }

theorem u24167 : Upper (D 6) (R 6) [34,136,257,68,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24167 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24168 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 293, targets := 64 },{ cop := 0, region := 80, targets := 4 }], pairs := [(0,6),(2,6),(4,2)], upper := (rows 35 138 261 76 82 36 113 177 305), lower := (rows 35 138 261 76 82 36 64 128 256), losses := [] }

theorem u24168 : Upper (D 6) (R 6) [34,136,257,68,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24168 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24169 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 138 261 76 82 48 101 165 293), lower := (rows 35 138 261 76 82 48 64 128 256), losses := [] }

theorem u24169 : Upper (D 6) (R 6) [34,136,257,68,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24169 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24170 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(4,1)], upper := (rows 35 138 261 76 112 33 86 150 278), lower := (rows 35 138 261 76 112 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 24 37 64 128 256), good := (rows 33 152 293 124 112 33 64 128 256) }] }

theorem u24170 : Upper (D 6) (R 6) [34,136,257,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24170 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24171 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 261 76 112 34 85 149 277), lower := (rows 35 138 261 76 112 34 64 128 256), losses := [] }

theorem u24171 : Upper (D 6) (R 6) [34,136,257,68,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24171 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24172 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 48, targets := 3 },{ cop := 0, region := 80, targets := 4 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 35 138 261 76 112 36 83 147 275), lower := (rows 35 138 261 76 112 36 64 128 256), losses := [] }

theorem u24172 : Upper (D 6) (R 6) [34,136,257,68,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24173 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 138 261 76 112 48 71 135 263), lower := (rows 35 138 261 76 112 48 64 128 256), losses := [] }

theorem u24173 : Upper (D 6) (R 6) [34,136,257,68,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24173 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24174 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 138 261 88 22 33 100 228 356), lower := (rows 35 138 261 88 22 33 64 128 256), losses := [] }

theorem u24174 : Upper (D 6) (R 6) [34,136,257,80,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24174 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24175 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 324, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 138 261 88 22 36 97 225 353), lower := (rows 35 138 261 88 22 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 24 16 53 69 133 261), good := (rows 485 136 485 120 508 484 64 128 256) }] }

theorem u24175 : Upper (D 6) (R 6) [34,136,257,80,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24175 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24176 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 276, targets := 64 },{ cop := 0, region := 260, targets := 2 }], pairs := [(2,1),(2,6),(4,6)], upper := (rows 35 138 261 88 22 96 101 165 293), lower := (rows 35 138 261 88 22 96 64 128 256), losses := [] }

theorem u24176 : Upper (D 6) (R 6) [34,136,257,80,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24177 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 138 261 88 52 33 70 198 326), lower := (rows 35 138 261 88 52 33 64 128 256), losses := [] }

theorem u24177 : Upper (D 6) (R 6) [34,136,257,80,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24177 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24178 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 261 88 52 34 69 197 325), lower := (rows 35 138 261 88 52 34 64 128 256), losses := [] }

theorem u24178 : Upper (D 6) (R 6) [34,136,257,80,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24178 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24179 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 138 261 88 52 36 67 195 323), lower := (rows 35 138 261 88 52 36 64 128 256), losses := [] }

theorem u24179 : Upper (D 6) (R 6) [34,136,257,80,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u24179
end Delivery.IrregularNine14.P06
