import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0123

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b24060 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 100 268 81 48 71 135 263), lower := (rows 35 138 100 268 81 48 64 128 256), losses := [] }

theorem u24060 : Upper (D 6) (R 6) [34,136,96,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24060 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24061 : Route 9 := (fun mask => (mask,id))

def c24061 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24061 : Upper (D 6) (R 6) [34,136,96,260,66,1] 13 := by
  apply FastRouting.sound _ _ [34,136,96,260,66,1] 13 (by decide) (choices 1) [1,4,16] r24061 c24061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7408
  · exact u7409
  · exact u7410

def b24062 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 35 138 100 268 82 36 81 145 273), lower := (rows 35 138 100 268 82 36 64 128 256), losses := [] }

theorem u24062 : Upper (D 6) (R 6) [34,136,96,260,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24063 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 100 268 82 48 69 133 261), lower := (rows 35 138 100 268 82 48 64 128 256), losses := [] }

theorem u24063 : Upper (D 6) (R 6) [34,136,96,260,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24063 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24064 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 138 100 280 21 33 70 198 326), lower := (rows 35 138 100 280 21 33 64 128 256), losses := [] }

theorem u24064 : Upper (D 6) (R 6) [34,136,96,272,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24064 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24065 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 100 280 21 34 69 197 325), lower := (rows 35 138 100 280 21 34 64 128 256), losses := [] }

theorem u24065 : Upper (D 6) (R 6) [34,136,96,272,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24065 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24066 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 138 100 280 21 36 67 195 323), lower := (rows 35 138 100 280 21 36 64 128 256), losses := [] }

theorem u24066 : Upper (D 6) (R 6) [34,136,96,272,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24066 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24067 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 100 280 21 96 71 135 263), lower := (rows 35 138 100 280 21 96 64 128 256), losses := [] }

theorem u24067 : Upper (D 6) (R 6) [34,136,96,272,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24067 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24068 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 68, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 138 100 280 22 33 69 197 325), lower := (rows 35 138 100 280 22 33 64 128 256), losses := [] }

theorem u24068 : Upper (D 6) (R 6) [34,136,96,272,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24068 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24069 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 36, targets := 3 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 138 100 280 22 36 65 193 321), lower := (rows 35 138 100 280 22 36 64 128 256), losses := [] }

theorem u24069 : Upper (D 6) (R 6) [34,136,96,272,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24069 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24070 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 100 280 22 96 69 133 261), lower := (rows 35 138 100 280 22 96 64 128 256), losses := [] }

theorem u24070 : Upper (D 6) (R 6) [34,136,96,272,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24070 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24071 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 68, targets := 1 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 35 138 100 280 81 33 70 134 262), lower := (rows 35 138 100 280 81 33 64 128 256), losses := [] }

theorem u24071 : Upper (D 6) (R 6) [34,136,96,272,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24071 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24072 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 100 280 81 34 69 133 261), lower := (rows 35 138 100 280 81 34 64 128 256), losses := [] }

theorem u24072 : Upper (D 6) (R 6) [34,136,96,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24072 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24073 : Route 9 := (fun mask => (mask,id))

def c24073 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24073 : Upper (D 6) (R 6) [34,136,96,272,65,4] 13 := by
  apply FastRouting.sound _ _ [34,136,96,272,65,4] 13 (by decide) (choices 1) [1,2,4] r24073 c24073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7411
  · exact u7412
  · exact u7413

def b24074 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 68, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 138 100 280 82 33 69 133 261), lower := (rows 35 138 100 280 82 33 64 128 256), losses := [] }

theorem u24074 : Upper (D 6) (R 6) [34,136,96,272,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24074 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24075 : Route 9 := (fun mask => (mask,id))

def c24075 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24075 : Upper (D 6) (R 6) [34,136,96,272,66,4] 13 := by
  apply FastRouting.sound _ _ [34,136,96,272,66,4] 13 (by decide) (choices 1) [1,4] r24075 c24075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7414
  · exact u7415

def b24076 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 138 100 328 21 33 86 150 278), lower := (rows 35 138 100 328 21 33 64 128 256), losses := [] }

theorem u24076 : Upper (D 6) (R 6) [34,136,96,320,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24076 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24077 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 100 328 21 34 85 149 277), lower := (rows 35 138 100 328 21 34 64 128 256), losses := [] }

theorem u24077 : Upper (D 6) (R 6) [34,136,96,320,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24077 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24078 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 138 100 328 21 36 83 147 275), lower := (rows 35 138 100 328 21 36 64 128 256), losses := [] }

theorem u24078 : Upper (D 6) (R 6) [34,136,96,320,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24078 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24079 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 138 100 328 21 48 71 135 263), lower := (rows 35 138 100 328 21 48 64 128 256), losses := [] }

theorem u24079 : Upper (D 6) (R 6) [34,136,96,320,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24079 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24080 : Route 9 := (fun mask => (mask,id))

def c24080 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24080 : Upper (D 6) (R 6) [34,136,96,320,6,1] 13 := by
  apply FastRouting.sound _ _ [34,136,96,320,6,1] 13 (by decide) (choices 1) [1,4,16] r24080 c24080
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7416
  · exact u7417
  · exact u7418

def b24081 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 138 100 328 22 36 81 145 273), lower := (rows 35 138 100 328 22 36 64 128 256), losses := [] }

theorem u24081 : Upper (D 6) (R 6) [34,136,96,320,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24081 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24082 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 138 100 328 22 48 69 133 261), lower := (rows 35 138 100 328 22 48 64 128 256), losses := [] }

theorem u24082 : Upper (D 6) (R 6) [34,136,96,320,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24082 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24083 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 138 261 14 52 33 80 208 336), lower := (rows 35 138 261 14 52 33 64 128 256), losses := [] }

theorem u24083 : Upper (D 6) (R 6) [34,136,257,6,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24083 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24084 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 138 261 14 52 48 65 193 321), lower := (rows 35 138 261 14 52 48 64 128 256), losses := [] }

theorem u24084 : Upper (D 6) (R 6) [34,136,257,6,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24084 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24085 : Route 9 := (fun mask => (mask,id))

def c24085 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24085 : Upper (D 6) (R 6) [34,136,257,6,36,64] 13 := by
  apply FastRouting.sound _ _ [34,136,257,6,36,64] 13 (by decide) (choices 1) [1,16] r24085 c24085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7419
  · exact u7420

def b24086 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(4,1),(4,2)], upper := (rows 35 138 261 14 81 36 112 240 368), lower := (rows 35 138 261 14 81 36 64 128 256), losses := [] }

theorem u24086 : Upper (D 6) (R 6) [34,136,257,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24086 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24087 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 138 261 14 81 48 100 228 356), lower := (rows 35 138 261 14 81 48 64 128 256), losses := [] }

theorem u24087 : Upper (D 6) (R 6) [34,136,257,6,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24087 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24088 : Route 9 := (fun mask => (mask,id))

def c24088 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24088 : Upper (D 6) (R 6) [34,136,257,6,65,64] 13 := by
  apply FastRouting.sound _ _ [34,136,257,6,65,64] 13 (by decide) (choices 1) [4,16,32] r24088 c24088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7421
  · exact u7422
  · exact u7423

def b24089 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 261 14 84 33 112 240 368), lower := (rows 35 138 261 14 84 33 64 128 256), losses := [] }

theorem u24089 : Upper (D 6) (R 6) [34,136,257,6,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24089 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24090 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 138 261 14 84 48 97 225 353), lower := (rows 35 138 261 14 84 48 64 128 256), losses := [] }

theorem u24090 : Upper (D 6) (R 6) [34,136,257,6,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24090 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24091 : Route 9 := (fun mask => (mask,id))

def c24091 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24091 : Upper (D 6) (R 6) [34,136,257,6,68,64] 13 := by
  apply FastRouting.sound _ _ [34,136,257,6,68,64] 13 (by decide) (choices 1) [1,16,32] r24091 c24091
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7424
  · exact u7425
  · exact u7426

def b24092 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 261 14 112 33 84 212 340), lower := (rows 35 138 261 14 112 33 64 128 256), losses := [] }

theorem u24092 : Upper (D 6) (R 6) [34,136,257,6,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24092 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24093 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(4,1),(4,2)], upper := (rows 35 138 261 14 112 36 81 209 337), lower := (rows 35 138 261 14 112 36 64 128 256), losses := [] }

theorem u24093 : Upper (D 6) (R 6) [34,136,257,6,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24093 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24094 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 138 261 14 112 48 69 197 325), lower := (rows 35 138 261 14 112 48 64 128 256), losses := [] }

theorem u24094 : Upper (D 6) (R 6) [34,136,257,6,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24094 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24095 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 138 261 14 112 96 85 149 277), lower := (rows 35 138 261 14 112 96 64 128 256), losses := [] }

theorem u24095 : Upper (D 6) (R 6) [34,136,257,6,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24095 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24096 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 41, targets := 64 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,6),(2,1),(3,6)], upper := (rows 35 138 261 25 22 36 96 224 352), lower := (rows 35 138 261 25 22 36 64 128 256), losses := [] }

theorem u24096 : Upper (D 6) (R 6) [34,136,257,17,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24096 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24097 : Route 9 := (fun mask => (mask,id))

def c24097 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24097 : Upper (D 6) (R 6) [34,136,257,17,6,64] 13 := by
  apply FastRouting.sound _ _ [34,136,257,17,6,64] 13 (by decide) (choices 1) [4,32] r24097 c24097
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7427
  · exact u7428

def b24098 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 261 25 52 34 68 196 324), lower := (rows 35 138 261 25 52 34 64 128 256), losses := [] }

theorem u24098 : Upper (D 6) (R 6) [34,136,257,17,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24098 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24099 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 56, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 35 138 261 25 52 36 66 194 322), lower := (rows 35 138 261 25 52 36 64 128 256), losses := [] }

theorem u24099 : Upper (D 6) (R 6) [34,136,257,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24099 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24100 : Route 9 := (fun mask => (mask,id))

def c24100 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24100 : Upper (D 6) (R 6) [34,136,257,17,36,64] 13 := by
  apply FastRouting.sound _ _ [34,136,257,17,36,64] 13 (by decide) (choices 1) [2,4] r24100 c24100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7429
  · exact u7430

def r24101 : Route 9 := (fun mask => (mask,id))

def c24101 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24101 : Upper (D 6) (R 6) [34,136,257,17,66,4] 13 := by
  apply FastRouting.sound _ _ [34,136,257,17,66,4] 13 (by decide) (choices 1) [4,32] r24101 c24101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7431
  · exact u7432

def b24102 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 41, targets := 4 },{ cop := 0, region := 260, targets := 2 }], pairs := [(0,2),(2,1),(3,2)], upper := (rows 35 138 261 25 82 96 100 164 292), lower := (rows 35 138 261 25 82 96 64 128 256), losses := [] }

theorem u24102 : Upper (D 6) (R 6) [34,136,257,17,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24102 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24103 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 261 25 84 34 100 228 356), lower := (rows 35 138 261 25 84 34 64 128 256), losses := [] }

theorem u24103 : Upper (D 6) (R 6) [34,136,257,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24103 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24104 : PairBound 9 := { available := 98, camps := [], pairs := [(1,0),(1,2),(4,0)], upper := (rows 35 138 261 25 84 36 98 226 354), lower := (rows 35 138 261 25 84 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 20 52 73 137 265), good := (rows 482 458 500 506 116 52 64 128 256) },{ target := 2, region := (rows 1 10 0 8 16 32 65 129 257), good := (rows 483 138 449 475 80 32 64 128 256) }] }

theorem u24104 : Upper (D 6) (R 6) [34,136,257,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24104 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24105 : Route 9 := (fun mask => (mask,id))

def c24105 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24105 : Upper (D 6) (R 6) [34,136,257,17,68,64] 13 := by
  apply FastRouting.sound _ _ [34,136,257,17,68,64] 13 (by decide) (choices 1) [2,4,32] r24105 c24105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7433
  · exact u7434
  · exact u7435

def b24106 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 261 25 112 34 68 196 324), lower := (rows 35 138 261 25 112 34 64 128 256), losses := [] }

theorem u24106 : Upper (D 6) (R 6) [34,136,257,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24106 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24107 : Route 9 := (fun mask => (mask,id))

def c24107 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24107 : Upper (D 6) (R 6) [34,136,257,17,96,4] 13 := by
  apply FastRouting.sound _ _ [34,136,257,17,96,4] 13 (by decide) (choices 1) [2,4] r24107 c24107
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7436
  · exact u7437

def b24108 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 138 261 25 112 96 70 134 262), lower := (rows 35 138 261 25 112 96 64 128 256), losses := [] }

theorem u24108 : Upper (D 6) (R 6) [34,136,257,17,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24108 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24109 : Route 9 := (fun mask => (mask,id))

def c24109 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24109 : Upper (D 6) (R 6) [34,136,257,18,65,4] 13 := by
  apply FastRouting.sound _ _ [34,136,257,18,65,4] 13 (by decide) (choices 1) [4,32] r24109 c24109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7438
  · exact u7439

def b24110 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 260, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 138 261 26 81 96 100 164 292), lower := (rows 35 138 261 26 81 96 64 128 256), losses := [] }

theorem u24110 : Upper (D 6) (R 6) [34,136,257,18,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24110 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24111 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 261 26 84 33 100 228 356), lower := (rows 35 138 261 26 84 33 64 128 256), losses := [] }

theorem u24111 : Upper (D 6) (R 6) [34,136,257,18,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24111 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24112 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 138 261 26 84 36 97 225 353), lower := (rows 35 138 261 26 84 36 64 128 256), losses := [{ target := 6, region := (rows 9 2 4 8 16 52 0 128 256), good := (rows 35 139 293 59 52 36 0 128 256) }] }

theorem u24112 : Upper (D 6) (R 6) [34,136,257,18,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24112 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24113 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 260, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 138 261 26 84 96 101 165 293), lower := (rows 35 138 261 26 84 96 64 128 256), losses := [] }

theorem u24113 : Upper (D 6) (R 6) [34,136,257,18,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24113 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24114 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 261 28 81 34 100 228 356), lower := (rows 35 138 261 28 81 34 64 128 256), losses := [] }

theorem u24114 : Upper (D 6) (R 6) [34,136,257,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24115 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 80, targets := 4 },{ cop := 3, region := 226, targets := 1 }], pairs := [(0,6),(1,0),(4,2)], upper := (rows 35 138 261 28 81 36 98 226 354), lower := (rows 35 138 261 28 81 36 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 44 0 128 256), good := (rows 35 171 293 60 17 36 0 128 256) }] }

theorem u24115 : Upper (D 6) (R 6) [34,136,257,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24115 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24116 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 260, targets := 64 },{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0),(1,6),(2,6)], upper := (rows 35 138 261 28 81 96 102 166 294), lower := (rows 35 138 261 28 81 96 64 128 256), losses := [{ target := 6, region := (rows 1 18 21 24 16 32 0 129 257), good := (rows 423 138 389 30 415 32 0 128 256) }] }

theorem u24116 : Upper (D 6) (R 6) [34,136,257,20,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24116 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24117 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 138 261 28 82 33 100 228 356), lower := (rows 35 138 261 28 82 33 64 128 256), losses := [] }

theorem u24117 : Upper (D 6) (R 6) [34,136,257,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24117 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24118 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 324, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(0,6),(2,1),(4,2)], upper := (rows 35 138 261 28 82 36 97 225 353), lower := (rows 35 138 261 28 82 36 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 44 0 128 256), good := (rows 35 171 293 60 19 36 0 128 256) }] }

theorem u24118 : Upper (D 6) (R 6) [34,136,257,20,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24118 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24119 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 260, targets := 2 },{ cop := 0, region := 260, targets := 64 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(2,6)], upper := (rows 35 138 261 28 82 96 101 165 293), lower := (rows 35 138 261 28 82 96 64 128 256), losses := [] }

theorem u24119 : Upper (D 6) (R 6) [34,136,257,20,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24119 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u24119
end Delivery.IrregularNine14.P06
