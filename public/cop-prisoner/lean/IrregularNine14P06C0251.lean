import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0057

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15060 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 98 164 13 81 288 86 150 278), lower := (rows 11 98 164 13 81 288 64 128 256), losses := [] }

theorem u15060 : Upper (D 6) (R 6) [10,96,160,5,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15060 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15061 : PairBound 9 := { available := 274, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 164 13 84 33 338 402 274), lower := (rows 11 98 164 13 84 33 64 128 256), losses := [] }

theorem u15061 : Upper (D 6) (R 6) [10,96,160,5,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15061 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15062 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 336, targets := 34 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 11 98 164 13 84 34 337 401 273), lower := (rows 11 98 164 13 84 34 64 128 256), losses := [] }

theorem u15062 : Upper (D 6) (R 6) [10,96,160,5,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15063 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 164 13 84 48 323 387 259), lower := (rows 11 98 164 13 84 48 64 128 256), losses := [] }

theorem u15063 : Upper (D 6) (R 6) [10,96,160,5,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15063 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15064 : Route 9 := (fun mask => (mask,id))

def c15064 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15064 : Upper (D 6) (R 6) [10,96,160,5,68,256] 13 := by
  apply FastRouting.sound _ _ [10,96,160,5,68,256] 13 (by decide) (choices 1) [1,2,16] r15064 c15064
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3449
  · exact u3450
  · exact u3451

def b15065 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 336, targets := 34 },{ cop := 4, region := 230, targets := 1 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 11 98 164 13 273 34 84 212 340), lower := (rows 11 98 164 13 273 34 64 128 256), losses := [] }

theorem u15065 : Upper (D 6) (R 6) [10,96,160,5,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15065 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15066 : PairBound 9 := { available := 82, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 164 13 273 36 82 210 338), lower := (rows 11 98 164 13 273 36 64 128 256), losses := [] }

theorem u15066 : Upper (D 6) (R 6) [10,96,160,5,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15066 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15067 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 230, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 98 164 13 273 48 70 198 326), lower := (rows 11 98 164 13 273 48 64 128 256), losses := [] }

theorem u15067 : Upper (D 6) (R 6) [10,96,160,5,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15067 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15068 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 164 13 273 96 86 150 278), lower := (rows 11 98 164 13 273 96 64 128 256), losses := [] }

theorem u15068 : Upper (D 6) (R 6) [10,96,160,5,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15068 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15069 : PairBound 9 := { available := 84, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 164 13 274 33 84 212 340), lower := (rows 11 98 164 13 274 33 64 128 256), losses := [] }

theorem u15069 : Upper (D 6) (R 6) [10,96,160,5,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15069 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15070 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 164 13 274 36 81 209 337), lower := (rows 11 98 164 13 274 36 64 128 256), losses := [] }

theorem u15070 : Upper (D 6) (R 6) [10,96,160,5,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15070 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15071 : Route 9 := (fun mask => (mask,id))

def c15071 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15071 : Upper (D 6) (R 6) [10,96,160,5,258,16] 13 := by
  apply FastRouting.sound _ _ [10,96,160,5,258,16] 13 (by decide) (choices 1) [1,4] r15071 c15071
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3452
  · exact u3453

def b15072 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 164 13 274 96 85 149 277), lower := (rows 11 98 164 13 274 96 64 128 256), losses := [] }

theorem u15072 : Upper (D 6) (R 6) [10,96,160,5,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15072 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15073 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 164 13 276 33 82 210 338), lower := (rows 11 98 164 13 276 33 64 128 256), losses := [] }

theorem u15073 : Upper (D 6) (R 6) [10,96,160,5,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15073 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15074 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 336, targets := 34 },{ cop := 6, region := 34, targets := 1 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 11 98 164 13 276 34 81 209 337), lower := (rows 11 98 164 13 276 34 64 128 256), losses := [] }

theorem u15074 : Upper (D 6) (R 6) [10,96,160,5,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15074 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15075 : Route 9 := (fun mask => (mask,id))

def c15075 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15075 : Upper (D 6) (R 6) [10,96,160,5,260,16] 13 := by
  apply FastRouting.sound _ _ [10,96,160,5,260,16] 13 (by decide) (choices 1) [1,2] r15075 c15075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3454
  · exact u3455

def b15076 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 164 13 276 96 83 147 275), lower := (rows 11 98 164 13 276 96 64 128 256), losses := [] }

theorem u15076 : Upper (D 6) (R 6) [10,96,160,5,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15076 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15077 : PairBound 9 := { available := 22, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 164 13 336 33 86 150 278), lower := (rows 11 98 164 13 336 33 64 128 256), losses := [] }

theorem u15077 : Upper (D 6) (R 6) [10,96,160,5,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15077 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15078 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 336, targets := 34 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 11 98 164 13 336 34 85 149 277), lower := (rows 11 98 164 13 336 34 64 128 256), losses := [] }

theorem u15078 : Upper (D 6) (R 6) [10,96,160,5,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15078 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15079 : PairBound 9 := { available := 19, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 164 13 336 36 83 147 275), lower := (rows 11 98 164 13 336 36 64 128 256), losses := [] }

theorem u15079 : Upper (D 6) (R 6) [10,96,160,5,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15079 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15080 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 164 13 336 48 71 135 263), lower := (rows 11 98 164 13 336 48 64 128 256), losses := [] }

theorem u15080 : Upper (D 6) (R 6) [10,96,160,5,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15080 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15081 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 98 164 25 84 33 326 390 262), lower := (rows 11 98 164 25 84 33 64 128 256), losses := [] }

theorem u15081 : Upper (D 6) (R 6) [10,96,160,17,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15081 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15082 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 98 164 25 84 34 325 389 261), lower := (rows 11 98 164 25 84 34 64 128 256), losses := [] }

theorem u15082 : Upper (D 6) (R 6) [10,96,160,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15082 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15083 : PairBound 9 := { available := 259, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 164 25 84 36 323 387 259), lower := (rows 11 98 164 25 84 36 64 128 256), losses := [] }

theorem u15083 : Upper (D 6) (R 6) [10,96,160,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15083 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15084 : Route 9 := (fun mask => (mask,id))

def c15084 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15084 : Upper (D 6) (R 6) [10,96,160,17,68,256] 13 := by
  apply FastRouting.sound _ _ [10,96,160,17,68,256] 13 (by decide) (choices 1) [1,2,4] r15084 c15084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3456
  · exact u3457
  · exact u3458

def b15085 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 164 25 276 33 70 198 326), lower := (rows 11 98 164 25 276 33 64 128 256), losses := [] }

theorem u15085 : Upper (D 6) (R 6) [10,96,160,17,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15085 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15086 : Route 9 := (fun mask => (mask,id))

def c15086 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15086 : Upper (D 6) (R 6) [10,96,160,17,260,2] 13 := by
  apply FastRouting.sound _ _ [10,96,160,17,260,2] 13 (by decide) (choices 1) [1,4] r15086 c15086
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3459
  · exact u3460

def b15087 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 164 25 276 36 67 195 323), lower := (rows 11 98 164 25 276 36 64 128 256), losses := [] }

theorem u15087 : Upper (D 6) (R 6) [10,96,160,17,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15087 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15088 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 164 25 276 96 71 135 263), lower := (rows 11 98 164 25 276 96 64 128 256), losses := [] }

theorem u15088 : Upper (D 6) (R 6) [10,96,160,17,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15088 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15089 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 98 164 25 336 33 70 134 262), lower := (rows 11 98 164 25 336 33 64 128 256), losses := [] }

theorem u15089 : Upper (D 6) (R 6) [10,96,160,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15089 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15090 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 98 164 25 336 34 69 133 261), lower := (rows 11 98 164 25 336 34 64 128 256), losses := [] }

theorem u15090 : Upper (D 6) (R 6) [10,96,160,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15090 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15091 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 164 25 336 36 71 135 263), lower := (rows 11 98 164 25 336 36 64 128 256), losses := [] }

theorem u15091 : Upper (D 6) (R 6) [10,96,160,17,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15091 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15092 : PairBound 9 := { available := 262, camps := [{ cop := 5, region := 454, targets := 1 },{ cop := 0, region := 420, targets := 64 }], pairs := [(1,0),(2,0),(2,6)], upper := (rows 11 98 164 28 81 33 326 390 262), lower := (rows 11 98 164 28 81 33 64 128 256), losses := [] }

theorem u15092 : Upper (D 6) (R 6) [10,96,160,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15092 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15093 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 34, targets := 5 },{ cop := 0, region := 420, targets := 64 }], pairs := [(1,0),(1,2),(2,6)], upper := (rows 11 98 164 28 81 34 325 389 261), lower := (rows 11 98 164 28 81 34 64 128 256), losses := [] }

theorem u15093 : Upper (D 6) (R 6) [10,96,160,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15093 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15094 : PairBound 9 := { available := 259, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 164 28 81 36 323 387 259), lower := (rows 11 98 164 28 81 36 64 128 256), losses := [] }

theorem u15094 : Upper (D 6) (R 6) [10,96,160,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15094 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15095 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 420, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 11 98 164 28 81 288 71 135 263), lower := (rows 11 98 164 28 81 288 64 128 256), losses := [{ target := 6, region := (rows 1 2 21 24 16 305 0 129 257), good := (rows 431 34 164 60 445 288 0 128 288) }] }

theorem u15095 : Upper (D 6) (R 6) [10,96,160,20,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15095 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15096 : Route 9 := (fun mask => (mask,id))

def c15096 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15096 : Upper (D 6) (R 6) [10,96,160,20,257,1] 13 := by
  apply FastRouting.sound _ _ [10,96,160,20,257,1] 13 (by decide) (choices 1) [2,4] r15096 c15096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3461
  · exact u3462

def r15097 : Route 9 := (fun mask => (mask,id))

def c15097 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15097 : Upper (D 6) (R 6) [10,96,160,20,257,2] 13 := by
  apply FastRouting.sound _ _ [10,96,160,20,257,2] 13 (by decide) (choices 1) [1,4] r15097 c15097
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3463
  · exact u3464

def b15098 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 164 28 273 36 67 195 323), lower := (rows 11 98 164 28 273 36 64 128 256), losses := [] }

theorem u15098 : Upper (D 6) (R 6) [10,96,160,20,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15098 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15099 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 164 28 273 96 71 135 263), lower := (rows 11 98 164 28 273 96 64 128 256), losses := [] }

theorem u15099 : Upper (D 6) (R 6) [10,96,160,20,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15099 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15100 : Route 9 := (fun mask => (mask,id))

def c15100 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15100 : Upper (D 6) (R 6) [10,96,160,20,258,1] 13 := by
  apply FastRouting.sound _ _ [10,96,160,20,258,1] 13 (by decide) (choices 1) [1,4] r15100 c15100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3465
  · exact u3466

def b15101 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 164 28 274 36 65 193 321), lower := (rows 11 98 164 28 274 36 64 128 256), losses := [] }

theorem u15101 : Upper (D 6) (R 6) [10,96,160,20,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15101 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15102 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 164 28 274 96 69 133 261), lower := (rows 11 98 164 28 274 96 64 128 256), losses := [] }

theorem u15102 : Upper (D 6) (R 6) [10,96,160,20,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15102 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15103 : Route 9 := (fun mask => (mask,id))

def c15103 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15103 : Upper (D 6) (R 6) [10,96,160,20,320,1] 13 := by
  apply FastRouting.sound _ _ [10,96,160,20,320,1] 13 (by decide) (choices 1) [1,2,4] r15103 c15103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3467
  · exact u3468
  · exact u3469

def b15104 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 34, targets := 5 },{ cop := 0, region := 164, targets := 64 }], pairs := [(1,0),(1,2),(2,6)], upper := (rows 11 98 164 28 336 34 69 133 261), lower := (rows 11 98 164 28 336 34 64 128 256), losses := [] }

theorem u15104 : Upper (D 6) (R 6) [10,96,160,20,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15104 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15105 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 164 28 336 36 67 131 259), lower := (rows 11 98 164 28 336 36 64 128 256), losses := [] }

theorem u15105 : Upper (D 6) (R 6) [10,96,160,20,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15105 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15106 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 98 164 76 273 33 86 150 278), lower := (rows 11 98 164 76 273 33 64 128 256), losses := [] }

theorem u15106 : Upper (D 6) (R 6) [10,96,160,68,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15106 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15107 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 98 164 76 273 34 85 149 277), lower := (rows 11 98 164 76 273 34 64 128 256), losses := [] }

theorem u15107 : Upper (D 6) (R 6) [10,96,160,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15107 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15108 : PairBound 9 := { available := 19, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 164 76 273 36 83 147 275), lower := (rows 11 98 164 76 273 36 64 128 256), losses := [] }

theorem u15108 : Upper (D 6) (R 6) [10,96,160,68,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15108 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15109 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 98 164 76 273 48 71 135 263), lower := (rows 11 98 164 76 273 48 64 128 256), losses := [] }

theorem u15109 : Upper (D 6) (R 6) [10,96,160,68,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15109 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15110 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 98 164 76 274 33 85 149 277), lower := (rows 11 98 164 76 274 33 64 128 256), losses := [] }

theorem u15110 : Upper (D 6) (R 6) [10,96,160,68,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15110 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15111 : PairBound 9 := { available := 17, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 164 76 274 36 81 145 273), lower := (rows 11 98 164 76 274 36 64 128 256), losses := [] }

theorem u15111 : Upper (D 6) (R 6) [10,96,160,68,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15111 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15112 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 98 164 76 274 48 69 133 261), lower := (rows 11 98 164 76 274 48 64 128 256), losses := [] }

theorem u15112 : Upper (D 6) (R 6) [10,96,160,68,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15112 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15113 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 98 164 76 276 33 83 147 275), lower := (rows 11 98 164 76 276 33 64 128 256), losses := [] }

theorem u15113 : Upper (D 6) (R 6) [10,96,160,68,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15113 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15114 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 98 164 76 276 34 81 145 273), lower := (rows 11 98 164 76 276 34 64 128 256), losses := [] }

theorem u15114 : Upper (D 6) (R 6) [10,96,160,68,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15115 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 98 164 76 276 48 67 131 259), lower := (rows 11 98 164 76 276 48 64 128 256), losses := [] }

theorem u15115 : Upper (D 6) (R 6) [10,96,160,68,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15115 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15116 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 98 164 88 21 33 326 390 262), lower := (rows 11 98 164 88 21 33 64 128 256), losses := [] }

theorem u15116 : Upper (D 6) (R 6) [10,96,160,80,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15116 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15117 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 98 164 88 21 34 325 389 261), lower := (rows 11 98 164 88 21 34 64 128 256), losses := [] }

theorem u15117 : Upper (D 6) (R 6) [10,96,160,80,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15117 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15118 : PairBound 9 := { available := 259, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 164 88 21 36 323 387 259), lower := (rows 11 98 164 88 21 36 64 128 256), losses := [] }

theorem u15118 : Upper (D 6) (R 6) [10,96,160,80,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15118 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15119 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 98 164 88 21 288 71 135 263), lower := (rows 11 98 164 88 21 288 64 128 256), losses := [] }

theorem u15119 : Upper (D 6) (R 6) [10,96,160,80,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15119 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u15119
end Delivery.IrregularNine14.P06
