import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0053
import IrregularNine14P06C0054

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14400 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 336, targets := 34 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 11 50 164 13 273 34 68 196 324), lower := (rows 11 50 164 13 273 34 64 128 256), losses := [] }

theorem u14400 : Upper (D 6) (R 6) [10,48,160,5,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14400 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14401 : PairBound 9 := { available := 66, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 50 164 13 273 36 66 194 322), lower := (rows 11 50 164 13 273 36 64 128 256), losses := [] }

theorem u14401 : Upper (D 6) (R 6) [10,48,160,5,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14401 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14402 : Route 9 := (fun mask => (mask,id))

def c14402 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14402 : Upper (D 6) (R 6) [10,48,160,5,257,64] 13 := by
  apply FastRouting.sound _ _ [10,48,160,5,257,64] 13 (by decide) (choices 1) [2,4] r14402 c14402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3223
  · exact u3224

def b14403 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 164 13 276 33 66 194 322), lower := (rows 11 50 164 13 276 33 64 128 256), losses := [] }

theorem u14403 : Upper (D 6) (R 6) [10,48,160,5,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14403 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14404 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 164 13 276 34 65 193 321), lower := (rows 11 50 164 13 276 34 64 128 256), losses := [] }

theorem u14404 : Upper (D 6) (R 6) [10,48,160,5,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14404 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14405 : Route 9 := (fun mask => (mask,id))

def c14405 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14405 : Upper (D 6) (R 6) [10,48,160,5,260,64] 13 := by
  apply FastRouting.sound _ _ [10,48,160,5,260,64] 13 (by decide) (choices 1) [1,2] r14405 c14405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3225
  · exact u3226

def b14406 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 164 13 336 33 70 198 326), lower := (rows 11 50 164 13 336 33 64 128 256), losses := [] }

theorem u14406 : Upper (D 6) (R 6) [10,48,160,5,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14406 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14407 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 164 13 336 34 69 197 325), lower := (rows 11 50 164 13 336 34 64 128 256), losses := [] }

theorem u14407 : Upper (D 6) (R 6) [10,48,160,5,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14407 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14408 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 50 164 13 336 36 67 195 323), lower := (rows 11 50 164 13 336 36 64 128 256), losses := [] }

theorem u14408 : Upper (D 6) (R 6) [10,48,160,5,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14409 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 164 13 336 96 71 135 263), lower := (rows 11 50 164 13 336 96 64 128 256), losses := [] }

theorem u14409 : Upper (D 6) (R 6) [10,48,160,5,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14410 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 328, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 50 164 73 21 34 324 452 324), lower := (rows 11 50 164 73 21 34 64 128 256), losses := [] }

theorem u14410 : Upper (D 6) (R 6) [10,48,160,65,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14410 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14411 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 164 73 21 36 322 450 322), lower := (rows 11 50 164 73 21 36 64 128 256), losses := [] }

theorem u14411 : Upper (D 6) (R 6) [10,48,160,65,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14412 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 1, region := 388, targets := 64 }], pairs := [(1,0),(2,0),(2,6)], upper := (rows 11 50 164 73 21 96 326 390 262), lower := (rows 11 50 164 73 21 96 64 128 256), losses := [] }

theorem u14412 : Upper (D 6) (R 6) [10,48,160,65,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14412 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14413 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 486, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 50 164 73 21 288 70 198 326), lower := (rows 11 50 164 73 21 288 64 128 256), losses := [] }

theorem u14413 : Upper (D 6) (R 6) [10,48,160,65,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14413 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14414 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 50 164 73 84 33 326 390 262), lower := (rows 11 50 164 73 84 33 64 128 256), losses := [] }

theorem u14414 : Upper (D 6) (R 6) [10,48,160,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14414 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14415 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 50 164 73 84 34 325 389 261), lower := (rows 11 50 164 73 84 34 64 128 256), losses := [] }

theorem u14415 : Upper (D 6) (R 6) [10,48,160,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14415 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14416 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 164 73 84 36 323 387 259), lower := (rows 11 50 164 73 84 36 64 128 256), losses := [] }

theorem u14416 : Upper (D 6) (R 6) [10,48,160,65,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14416 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14417 : Route 9 := (fun mask => (mask,id))

def c14417 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14417 : Upper (D 6) (R 6) [10,48,160,65,68,256] 13 := by
  apply FastRouting.sound _ _ [10,48,160,65,68,256] 13 (by decide) (choices 1) [1,2,4] r14417 c14417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3227
  · exact u3228
  · exact u3229

def b14418 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 50 164 73 273 34 68 196 324), lower := (rows 11 50 164 73 273 34 64 128 256), losses := [] }

theorem u14418 : Upper (D 6) (R 6) [10,48,160,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14418 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14419 : PairBound 9 := { available := 70, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 50 164 73 273 36 70 198 326), lower := (rows 11 50 164 73 273 36 64 128 256), losses := [] }

theorem u14419 : Upper (D 6) (R 6) [10,48,160,65,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14419 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14420 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 1, region := 132, targets := 64 }], pairs := [(1,0),(2,0),(2,6)], upper := (rows 11 50 164 73 273 96 70 134 262), lower := (rows 11 50 164 73 273 96 64 128 256), losses := [] }

theorem u14420 : Upper (D 6) (R 6) [10,48,160,65,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14420 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14421 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 164 73 274 33 68 196 324), lower := (rows 11 50 164 73 274 33 64 128 256), losses := [] }

theorem u14421 : Upper (D 6) (R 6) [10,48,160,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14421 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14422 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 50 164 73 274 36 69 197 325), lower := (rows 11 50 164 73 274 36 64 128 256), losses := [] }

theorem u14422 : Upper (D 6) (R 6) [10,48,160,65,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14423 : Route 9 := (fun mask => (mask,id))

def c14423 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14423 : Upper (D 6) (R 6) [10,48,160,65,258,64] 13 := by
  apply FastRouting.sound _ _ [10,48,160,65,258,64] 13 (by decide) (choices 1) [1,4] r14423 c14423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3230
  · exact u3231

def b14424 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 164 73 276 33 70 198 326), lower := (rows 11 50 164 73 276 33 64 128 256), losses := [] }

theorem u14424 : Upper (D 6) (R 6) [10,48,160,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14424 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14425 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 164 73 276 34 69 197 325), lower := (rows 11 50 164 73 276 34 64 128 256), losses := [] }

theorem u14425 : Upper (D 6) (R 6) [10,48,160,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14425 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14426 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 164 73 276 36 67 195 323), lower := (rows 11 50 164 73 276 36 64 128 256), losses := [] }

theorem u14426 : Upper (D 6) (R 6) [10,48,160,65,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14426 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14427 : Route 9 := (fun mask => (mask,id))

def c14427 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14427 : Upper (D 6) (R 6) [10,48,160,65,260,64] 13 := by
  apply FastRouting.sound _ _ [10,48,160,65,260,64] 13 (by decide) (choices 1) [1,2,4] r14427 c14427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3232
  · exact u3233
  · exact u3234

def b14428 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 50 164 73 336 33 70 134 262), lower := (rows 11 50 164 73 336 33 64 128 256), losses := [] }

theorem u14428 : Upper (D 6) (R 6) [10,48,160,65,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14428 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14429 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 50 164 73 336 34 69 133 261), lower := (rows 11 50 164 73 336 34 64 128 256), losses := [] }

theorem u14429 : Upper (D 6) (R 6) [10,48,160,65,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14429 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14430 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 50 164 73 336 36 71 135 263), lower := (rows 11 50 164 73 336 36 64 128 256), losses := [] }

theorem u14430 : Upper (D 6) (R 6) [10,48,160,65,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14430 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14431 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 164 76 81 33 326 390 262), lower := (rows 11 50 164 76 81 33 64 128 256), losses := [] }

theorem u14431 : Upper (D 6) (R 6) [10,48,160,68,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14431 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14432 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 164 76 81 34 325 389 261), lower := (rows 11 50 164 76 81 34 64 128 256), losses := [] }

theorem u14432 : Upper (D 6) (R 6) [10,48,160,68,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14432 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14433 : PairBound 9 := { available := 259, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 50 164 76 81 36 323 387 259), lower := (rows 11 50 164 76 81 36 64 128 256), losses := [] }

theorem u14433 : Upper (D 6) (R 6) [10,48,160,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14433 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14434 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 50 164 76 81 288 71 135 263), lower := (rows 11 50 164 76 81 288 64 128 256), losses := [] }

theorem u14434 : Upper (D 6) (R 6) [10,48,160,68,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14434 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14435 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 11 50 164 76 273 33 70 198 326), lower := (rows 11 50 164 76 273 33 64 128 256), losses := [] }

theorem u14435 : Upper (D 6) (R 6) [10,48,160,68,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14435 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14436 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 164 76 273 34 69 197 325), lower := (rows 11 50 164 76 273 34 64 128 256), losses := [] }

theorem u14436 : Upper (D 6) (R 6) [10,48,160,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14437 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 50 164 76 273 36 67 195 323), lower := (rows 11 50 164 76 273 36 64 128 256), losses := [] }

theorem u14437 : Upper (D 6) (R 6) [10,48,160,68,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14437 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14438 : Route 9 := (fun mask => (mask,id))

def c14438 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14438 : Upper (D 6) (R 6) [10,48,160,68,257,64] 13 := by
  apply FastRouting.sound _ _ [10,48,160,68,257,64] 13 (by decide) (choices 1) [1,2,4] r14438 c14438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3235
  · exact u3236
  · exact u3237

def r14439 : Route 9 := (fun mask => (mask,id))

def c14439 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14439 : Upper (D 6) (R 6) [10,48,160,68,258,1] 13 := by
  apply FastRouting.sound _ _ [10,48,160,68,258,1] 13 (by decide) (choices 1) [1,4] r14439 c14439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3238
  · exact u3239

def b14440 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 50 164 76 274 36 65 193 321), lower := (rows 11 50 164 76 274 36 64 128 256), losses := [] }

theorem u14440 : Upper (D 6) (R 6) [10,48,160,68,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14440 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14441 : Route 9 := (fun mask => (mask,id))

def c14441 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14441 : Upper (D 6) (R 6) [10,48,160,68,258,64] 13 := by
  apply FastRouting.sound _ _ [10,48,160,68,258,64] 13 (by decide) (choices 1) [1,4] r14441 c14441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3240
  · exact u3241

def r14442 : Route 9 := (fun mask => (mask,id))

def c14442 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14442 : Upper (D 6) (R 6) [10,48,160,68,260,1] 13 := by
  apply FastRouting.sound _ _ [10,48,160,68,260,1] 13 (by decide) (choices 1) [1,2] r14442 c14442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3242
  · exact u3243

def b14443 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 164 76 276 34 65 193 321), lower := (rows 11 50 164 76 276 34 64 128 256), losses := [] }

theorem u14443 : Upper (D 6) (R 6) [10,48,160,68,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14443 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14444 : Route 9 := (fun mask => (mask,id))

def c14444 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14444 : Upper (D 6) (R 6) [10,48,160,68,260,64] 13 := by
  apply FastRouting.sound _ _ [10,48,160,68,260,64] 13 (by decide) (choices 1) [1,2] r14444 c14444
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3244
  · exact u3245

def r14445 : Route 9 := (fun mask => (mask,id))

def c14445 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14445 : Upper (D 6) (R 6) [10,48,160,68,320,1] 13 := by
  apply FastRouting.sound _ _ [10,48,160,68,320,1] 13 (by decide) (choices 1) [1,2,4] r14445 c14445
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3246
  · exact u3247
  · exact u3248

def b14446 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 164 76 336 34 69 133 261), lower := (rows 11 50 164 76 336 34 64 128 256), losses := [] }

theorem u14446 : Upper (D 6) (R 6) [10,48,160,68,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14446 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14447 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 50 164 76 336 36 67 131 259), lower := (rows 11 50 164 76 336 36 64 128 256), losses := [] }

theorem u14447 : Upper (D 6) (R 6) [10,48,160,68,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14447 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14448 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 328, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 50 164 265 21 34 68 196 324), lower := (rows 11 50 164 265 21 34 64 128 256), losses := [] }

theorem u14448 : Upper (D 6) (R 6) [10,48,160,257,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14448 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14449 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 164 265 21 36 66 194 322), lower := (rows 11 50 164 265 21 36 64 128 256), losses := [] }

theorem u14449 : Upper (D 6) (R 6) [10,48,160,257,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14449 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14450 : Route 9 := (fun mask => (mask,id))

def c14450 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14450 : Upper (D 6) (R 6) [10,48,160,257,5,64] 13 := by
  apply FastRouting.sound _ _ [10,48,160,257,5,64] 13 (by decide) (choices 1) [2,4] r14450 c14450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3249
  · exact u3250

def b14451 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 166, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 50 164 265 81 34 68 196 324), lower := (rows 11 50 164 265 81 34 64 128 256), losses := [] }

theorem u14451 : Upper (D 6) (R 6) [10,48,160,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14451 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14452 : PairBound 9 := { available := 70, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 50 164 265 81 36 70 198 326), lower := (rows 11 50 164 265 81 36 64 128 256), losses := [] }

theorem u14452 : Upper (D 6) (R 6) [10,48,160,257,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14452 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14453 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 164 265 81 96 70 134 262), lower := (rows 11 50 164 265 81 96 64 128 256), losses := [] }

theorem u14453 : Upper (D 6) (R 6) [10,48,160,257,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14453 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14454 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 164 265 82 33 68 196 324), lower := (rows 11 50 164 265 82 33 64 128 256), losses := [] }

theorem u14454 : Upper (D 6) (R 6) [10,48,160,257,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14454 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14455 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 50 164 265 82 36 69 197 325), lower := (rows 11 50 164 265 82 36 64 128 256), losses := [] }

theorem u14455 : Upper (D 6) (R 6) [10,48,160,257,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14455 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14456 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 18, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 50 164 265 82 96 69 133 261), lower := (rows 11 50 164 265 82 96 64 128 256), losses := [] }

theorem u14456 : Upper (D 6) (R 6) [10,48,160,257,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14456 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14457 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 164 265 84 33 70 198 326), lower := (rows 11 50 164 265 84 33 64 128 256), losses := [] }

theorem u14457 : Upper (D 6) (R 6) [10,48,160,257,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14457 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14458 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 164 265 84 34 69 197 325), lower := (rows 11 50 164 265 84 34 64 128 256), losses := [] }

theorem u14458 : Upper (D 6) (R 6) [10,48,160,257,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14458 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14459 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 164 265 84 36 67 195 323), lower := (rows 11 50 164 265 84 36 64 128 256), losses := [] }

theorem u14459 : Upper (D 6) (R 6) [10,48,160,257,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u14459
end Delivery.IrregularNine14.P06
