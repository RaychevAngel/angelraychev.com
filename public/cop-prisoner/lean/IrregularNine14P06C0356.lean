import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0105

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21360 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 74 164 13 81 48 326 390 262), lower := (rows 35 74 164 13 81 48 64 128 256), losses := [] }

theorem u21360 : Upper (D 6) (R 6) [34,72,160,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21360 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21361 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 82, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 74 164 13 81 288 86 150 278), lower := (rows 35 74 164 13 81 288 64 128 256), losses := [] }

theorem u21361 : Upper (D 6) (R 6) [34,72,160,5,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21361 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21362 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 74 164 13 84 33 338 402 274), lower := (rows 35 74 164 13 84 33 64 128 256), losses := [] }

theorem u21362 : Upper (D 6) (R 6) [34,72,160,5,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21362 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21363 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 164 13 84 34 337 401 273), lower := (rows 35 74 164 13 84 34 64 128 256), losses := [] }

theorem u21363 : Upper (D 6) (R 6) [34,72,160,5,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21363 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21364 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 74 164 13 84 48 323 387 259), lower := (rows 35 74 164 13 84 48 64 128 256), losses := [] }

theorem u21364 : Upper (D 6) (R 6) [34,72,160,5,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21364 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21365 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 82, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 74 164 13 84 288 83 147 275), lower := (rows 35 74 164 13 84 288 64 128 256), losses := [] }

theorem u21365 : Upper (D 6) (R 6) [34,72,160,5,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21365 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21366 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 164 13 273 34 84 212 340), lower := (rows 35 74 164 13 273 34 64 128 256), losses := [] }

theorem u21366 : Upper (D 6) (R 6) [34,72,160,5,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21366 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21367 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 338, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 74 164 13 273 36 82 210 338), lower := (rows 35 74 164 13 273 36 64 128 256), losses := [] }

theorem u21367 : Upper (D 6) (R 6) [34,72,160,5,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21367 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21368 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 338, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 74 164 13 273 48 70 198 326), lower := (rows 35 74 164 13 273 48 64 128 256), losses := [] }

theorem u21368 : Upper (D 6) (R 6) [34,72,160,5,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21368 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21369 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 164 13 273 96 86 150 278), lower := (rows 35 74 164 13 273 96 64 128 256), losses := [] }

theorem u21369 : Upper (D 6) (R 6) [34,72,160,5,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21369 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21370 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 74 164 13 274 33 84 212 340), lower := (rows 35 74 164 13 274 33 64 128 256), losses := [] }

theorem u21370 : Upper (D 6) (R 6) [34,72,160,5,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21370 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21371 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 338, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 74 164 13 274 36 81 209 337), lower := (rows 35 74 164 13 274 36 64 128 256), losses := [] }

theorem u21371 : Upper (D 6) (R 6) [34,72,160,5,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21371 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21372 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 74 164 13 274 48 69 197 325), lower := (rows 35 74 164 13 274 48 64 128 256), losses := [] }

theorem u21372 : Upper (D 6) (R 6) [34,72,160,5,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21372 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21373 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 164 13 274 96 85 149 277), lower := (rows 35 74 164 13 274 96 64 128 256), losses := [] }

theorem u21373 : Upper (D 6) (R 6) [34,72,160,5,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21373 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21374 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 74 164 13 276 33 82 210 338), lower := (rows 35 74 164 13 276 33 64 128 256), losses := [] }

theorem u21374 : Upper (D 6) (R 6) [34,72,160,5,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21374 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21375 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 164 13 276 34 81 209 337), lower := (rows 35 74 164 13 276 34 64 128 256), losses := [] }

theorem u21375 : Upper (D 6) (R 6) [34,72,160,5,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21375 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21376 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 338, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 74 164 13 276 48 67 195 323), lower := (rows 35 74 164 13 276 48 64 128 256), losses := [] }

theorem u21376 : Upper (D 6) (R 6) [34,72,160,5,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21376 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21377 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 164 13 276 96 83 147 275), lower := (rows 35 74 164 13 276 96 64 128 256), losses := [] }

theorem u21377 : Upper (D 6) (R 6) [34,72,160,5,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21377 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21378 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 74 164 13 336 33 86 150 278), lower := (rows 35 74 164 13 336 33 64 128 256), losses := [] }

theorem u21378 : Upper (D 6) (R 6) [34,72,160,5,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21378 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21379 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 164 13 336 34 85 149 277), lower := (rows 35 74 164 13 336 34 64 128 256), losses := [] }

theorem u21379 : Upper (D 6) (R 6) [34,72,160,5,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21379 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21380 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 338, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 74 164 13 336 36 83 147 275), lower := (rows 35 74 164 13 336 36 64 128 256), losses := [] }

theorem u21380 : Upper (D 6) (R 6) [34,72,160,5,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21380 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21381 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 74 164 13 336 48 71 135 263), lower := (rows 35 74 164 13 336 48 64 128 256), losses := [] }

theorem u21381 : Upper (D 6) (R 6) [34,72,160,5,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21381 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21382 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 164 14 273 33 84 212 340), lower := (rows 35 74 164 14 273 33 64 128 256), losses := [] }

theorem u21382 : Upper (D 6) (R 6) [34,72,160,6,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21382 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21383 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 164 14 273 36 81 209 337), lower := (rows 35 74 164 14 273 36 64 128 256), losses := [] }

theorem u21383 : Upper (D 6) (R 6) [34,72,160,6,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21383 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21384 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 74 164 14 273 48 69 197 325), lower := (rows 35 74 164 14 273 48 64 128 256), losses := [] }

theorem u21384 : Upper (D 6) (R 6) [34,72,160,6,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21384 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21385 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 164 14 273 96 85 149 277), lower := (rows 35 74 164 14 273 96 64 128 256), losses := [] }

theorem u21385 : Upper (D 6) (R 6) [34,72,160,6,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21385 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21386 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 164 14 276 33 81 209 337), lower := (rows 35 74 164 14 276 33 64 128 256), losses := [] }

theorem u21386 : Upper (D 6) (R 6) [34,72,160,6,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21387 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 74 164 14 276 48 65 193 321), lower := (rows 35 74 164 14 276 48 64 128 256), losses := [] }

theorem u21387 : Upper (D 6) (R 6) [34,72,160,6,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21387 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21388 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 164 14 276 96 81 145 273), lower := (rows 35 74 164 14 276 96 64 128 256), losses := [] }

theorem u21388 : Upper (D 6) (R 6) [34,72,160,6,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21388 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21389 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 164 14 336 33 85 149 277), lower := (rows 35 74 164 14 336 33 64 128 256), losses := [] }

theorem u21389 : Upper (D 6) (R 6) [34,72,160,6,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21389 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21390 : PairBound 9 := { available := 17, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 164 14 336 36 81 145 273), lower := (rows 35 74 164 14 336 36 64 128 256), losses := [] }

theorem u21390 : Upper (D 6) (R 6) [34,72,160,6,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21390 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21391 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 74 164 14 336 48 69 133 261), lower := (rows 35 74 164 14 336 48 64 128 256), losses := [] }

theorem u21391 : Upper (D 6) (R 6) [34,72,160,6,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21391 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21392 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 74 164 25 22 33 324 452 324), lower := (rows 35 74 164 25 22 33 64 128 256), losses := [] }

theorem u21392 : Upper (D 6) (R 6) [34,72,160,17,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21393 : PairBound 9 := { available := 321, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 164 25 22 36 321 449 321), lower := (rows 35 74 164 25 22 36 64 128 256), losses := [] }

theorem u21393 : Upper (D 6) (R 6) [34,72,160,17,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21393 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21394 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 164 25 22 96 325 389 261), lower := (rows 35 74 164 25 22 96 64 128 256), losses := [] }

theorem u21394 : Upper (D 6) (R 6) [34,72,160,17,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21394 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21395 : Route 9 := (fun mask => (mask,id))

def c21395 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21395 : Upper (D 6) (R 6) [34,72,160,17,6,256] 13 := by
  apply FastRouting.sound _ _ [34,72,160,17,6,256] 13 (by decide) (choices 1) [1,4] r21395 c21395
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6304
  · exact u6305

def b21396 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 164 25 84 33 326 390 262), lower := (rows 35 74 164 25 84 33 64 128 256), losses := [] }

theorem u21396 : Upper (D 6) (R 6) [34,72,160,17,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21397 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 164 25 84 34 325 389 261), lower := (rows 35 74 164 25 84 34 64 128 256), losses := [] }

theorem u21397 : Upper (D 6) (R 6) [34,72,160,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21397 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21398 : PairBound 9 := { available := 259, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 164 25 84 36 323 387 259), lower := (rows 35 74 164 25 84 36 64 128 256), losses := [] }

theorem u21398 : Upper (D 6) (R 6) [34,72,160,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21398 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21399 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 74 164 25 84 288 71 135 263), lower := (rows 35 74 164 25 84 288 64 128 256), losses := [] }

theorem u21399 : Upper (D 6) (R 6) [34,72,160,17,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21399 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21400 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 74 164 25 274 33 68 196 324), lower := (rows 35 74 164 25 274 33 64 128 256), losses := [] }

theorem u21400 : Upper (D 6) (R 6) [34,72,160,17,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21400 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21401 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 164 25 274 36 69 197 325), lower := (rows 35 74 164 25 274 36 64 128 256), losses := [] }

theorem u21401 : Upper (D 6) (R 6) [34,72,160,17,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21401 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21402 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 164 25 274 96 69 133 261), lower := (rows 35 74 164 25 274 96 64 128 256), losses := [] }

theorem u21402 : Upper (D 6) (R 6) [34,72,160,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21402 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21403 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 164 25 276 33 70 198 326), lower := (rows 35 74 164 25 276 33 64 128 256), losses := [] }

theorem u21403 : Upper (D 6) (R 6) [34,72,160,17,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21403 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21404 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 164 25 276 34 69 197 325), lower := (rows 35 74 164 25 276 34 64 128 256), losses := [] }

theorem u21404 : Upper (D 6) (R 6) [34,72,160,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21404 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21405 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 164 25 276 36 67 195 323), lower := (rows 35 74 164 25 276 36 64 128 256), losses := [] }

theorem u21405 : Upper (D 6) (R 6) [34,72,160,17,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21405 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21406 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 164 25 276 96 71 135 263), lower := (rows 35 74 164 25 276 96 64 128 256), losses := [] }

theorem u21406 : Upper (D 6) (R 6) [34,72,160,17,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21406 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21407 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 164 25 336 33 70 134 262), lower := (rows 35 74 164 25 336 33 64 128 256), losses := [] }

theorem u21407 : Upper (D 6) (R 6) [34,72,160,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21407 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21408 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 164 25 336 34 69 133 261), lower := (rows 35 74 164 25 336 34 64 128 256), losses := [] }

theorem u21408 : Upper (D 6) (R 6) [34,72,160,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21409 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 164 25 336 36 71 135 263), lower := (rows 35 74 164 25 336 36 64 128 256), losses := [] }

theorem u21409 : Upper (D 6) (R 6) [34,72,160,17,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21410 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 164 26 273 33 68 196 324), lower := (rows 35 74 164 26 273 33 64 128 256), losses := [] }

theorem u21410 : Upper (D 6) (R 6) [34,72,160,18,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21410 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21411 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 164 26 273 36 69 197 325), lower := (rows 35 74 164 26 273 36 64 128 256), losses := [] }

theorem u21411 : Upper (D 6) (R 6) [34,72,160,18,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21412 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 164 26 273 96 69 133 261), lower := (rows 35 74 164 26 273 96 64 128 256), losses := [] }

theorem u21412 : Upper (D 6) (R 6) [34,72,160,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21412 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21413 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 164 26 276 33 69 197 325), lower := (rows 35 74 164 26 276 33 64 128 256), losses := [] }

theorem u21413 : Upper (D 6) (R 6) [34,72,160,18,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21413 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21414 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 164 26 276 36 65 193 321), lower := (rows 35 74 164 26 276 36 64 128 256), losses := [] }

theorem u21414 : Upper (D 6) (R 6) [34,72,160,18,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21414 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21415 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 164 26 276 96 69 133 261), lower := (rows 35 74 164 26 276 96 64 128 256), losses := [] }

theorem u21415 : Upper (D 6) (R 6) [34,72,160,18,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21415 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21416 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 74 164 28 273 33 70 198 326), lower := (rows 35 74 164 28 273 33 64 128 256), losses := [] }

theorem u21416 : Upper (D 6) (R 6) [34,72,160,20,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21416 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21417 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 164 28 273 34 69 197 325), lower := (rows 35 74 164 28 273 34 64 128 256), losses := [] }

theorem u21417 : Upper (D 6) (R 6) [34,72,160,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21417 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21418 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 164 28 273 36 67 195 323), lower := (rows 35 74 164 28 273 36 64 128 256), losses := [] }

theorem u21418 : Upper (D 6) (R 6) [34,72,160,20,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21418 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21419 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 164 28 273 96 71 135 263), lower := (rows 35 74 164 28 273 96 64 128 256), losses := [] }

theorem u21419 : Upper (D 6) (R 6) [34,72,160,20,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21419 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u21419
end Delivery.IrregularNine14.P06
