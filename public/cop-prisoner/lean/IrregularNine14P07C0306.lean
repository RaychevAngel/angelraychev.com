import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0082

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18360 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 140 336 34 209 145 401), lower := (rows 35 67 44 140 336 34 64 128 256), losses := [] }

theorem u18360 : Upper (D 7) (R 7) [34,65,40,132,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18360 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18361 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 140, targets := 64 }], pairs := [(1,5),(2,6),(4,5)], upper := (rows 35 67 44 140 336 48 195 131 387), lower := (rows 35 67 44 140 336 48 64 128 256), losses := [] }

theorem u18361 : Upper (D 7) (R 7) [34,65,40,132,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18361 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18362 : PairBound 9 := { available := 19, camps := [{ cop := 5, region := 12, targets := 67 }], pairs := [(2,0),(2,1),(2,6),(3,0)], upper := (rows 35 67 44 140 336 160 83 147 275), lower := (rows 35 67 44 140 336 160 64 128 256), losses := [] }

theorem u18362 : Upper (D 7) (R 7) [34,65,40,132,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18362 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18363 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 152 273 34 196 196 452), lower := (rows 35 67 44 152 273 34 64 128 256), losses := [] }

theorem u18363 : Upper (D 7) (R 7) [34,65,40,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18363 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18364 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 152 273 36 194 194 450), lower := (rows 35 67 44 152 273 36 64 128 256), losses := [] }

theorem u18364 : Upper (D 7) (R 7) [34,65,40,144,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18364 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18365 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 152 273 96 198 134 390), lower := (rows 35 67 44 152 273 96 64 128 256), losses := [] }

theorem u18365 : Upper (D 7) (R 7) [34,65,40,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18365 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18366 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 67 44 152 273 160 70 198 326), lower := (rows 35 67 44 152 273 160 64 128 256), losses := [] }

theorem u18366 : Upper (D 7) (R 7) [34,65,40,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18366 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18367 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 152 274 33 196 196 452), lower := (rows 35 67 44 152 274 33 64 128 256), losses := [] }

theorem u18367 : Upper (D 7) (R 7) [34,65,40,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18367 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18368 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 152 274 36 193 193 449), lower := (rows 35 67 44 152 274 36 64 128 256), losses := [] }

theorem u18368 : Upper (D 7) (R 7) [34,65,40,144,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18368 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18369 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 152 274 96 197 133 389), lower := (rows 35 67 44 152 274 96 64 128 256), losses := [] }

theorem u18369 : Upper (D 7) (R 7) [34,65,40,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18369 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18370 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 67 44 152 274 160 69 197 325), lower := (rows 35 67 44 152 274 160 64 128 256), losses := [] }

theorem u18370 : Upper (D 7) (R 7) [34,65,40,144,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18370 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18371 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 152 276 33 194 194 450), lower := (rows 35 67 44 152 276 33 64 128 256), losses := [] }

theorem u18371 : Upper (D 7) (R 7) [34,65,40,144,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18371 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18372 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 152 276 34 193 193 449), lower := (rows 35 67 44 152 276 34 64 128 256), losses := [] }

theorem u18372 : Upper (D 7) (R 7) [34,65,40,144,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18372 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18373 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 152 276 96 195 131 387), lower := (rows 35 67 44 152 276 96 64 128 256), losses := [] }

theorem u18373 : Upper (D 7) (R 7) [34,65,40,144,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18373 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18374 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 67 44 152 276 160 67 195 323), lower := (rows 35 67 44 152 276 160 64 128 256), losses := [] }

theorem u18374 : Upper (D 7) (R 7) [34,65,40,144,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18374 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18375 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 152 336 33 198 134 390), lower := (rows 35 67 44 152 336 33 64 128 256), losses := [] }

theorem u18375 : Upper (D 7) (R 7) [34,65,40,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18375 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18376 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 152 336 34 197 133 389), lower := (rows 35 67 44 152 336 34 64 128 256), losses := [] }

theorem u18376 : Upper (D 7) (R 7) [34,65,40,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18376 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18377 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 152 336 36 195 131 387), lower := (rows 35 67 44 152 336 36 64 128 256), losses := [] }

theorem u18377 : Upper (D 7) (R 7) [34,65,40,144,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18377 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18378 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 67 44 152 336 160 71 135 263), lower := (rows 35 67 44 152 336 160 64 128 256), losses := [] }

theorem u18378 : Upper (D 7) (R 7) [34,65,40,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18378 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18379 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 200 145 34 340 404 276), lower := (rows 35 67 44 200 145 34 64 128 256), losses := [] }

theorem u18379 : Upper (D 7) (R 7) [34,65,40,192,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18379 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18380 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 474, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 67 44 200 145 36 338 402 274), lower := (rows 35 67 44 200 145 36 64 128 256), losses := [] }

theorem u18380 : Upper (D 7) (R 7) [34,65,40,192,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18380 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18381 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 460, targets := 1 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(2,0),(3,0)], upper := (rows 35 67 44 200 145 48 326 390 262), lower := (rows 35 67 44 200 145 48 64 128 256), losses := [] }

theorem u18381 : Upper (D 7) (R 7) [34,65,40,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18381 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18382 : Route 9 := (fun mask => (mask,id))

def c18382 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18382 : Upper (D 7) (R 7) [34,65,40,192,129,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,129,256] 13 (by decide) (choices 1) [2,4,16] r18382 c18382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4937
  · exact u4938
  · exact u4939

def b18383 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 200 146 33 340 404 276), lower := (rows 35 67 44 200 146 33 64 128 256), losses := [] }

theorem u18383 : Upper (D 7) (R 7) [34,65,40,192,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18383 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18384 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 474, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 67 44 200 146 36 337 401 273), lower := (rows 35 67 44 200 146 36 64 128 256), losses := [] }

theorem u18384 : Upper (D 7) (R 7) [34,65,40,192,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18384 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18385 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(2,1),(3,1)], upper := (rows 35 67 44 200 146 48 325 389 261), lower := (rows 35 67 44 200 146 48 64 128 256), losses := [] }

theorem u18385 : Upper (D 7) (R 7) [34,65,40,192,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18385 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18386 : Route 9 := (fun mask => (mask,id))

def c18386 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18386 : Upper (D 7) (R 7) [34,65,40,192,130,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,130,256] 13 (by decide) (choices 1) [1,4,16] r18386 c18386
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4940
  · exact u4941
  · exact u4942

def b18387 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 200 148 33 338 402 274), lower := (rows 35 67 44 200 148 33 64 128 256), losses := [] }

theorem u18387 : Upper (D 7) (R 7) [34,65,40,192,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18387 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18388 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 200 148 34 337 401 273), lower := (rows 35 67 44 200 148 34 64 128 256), losses := [] }

theorem u18388 : Upper (D 7) (R 7) [34,65,40,192,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18388 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18389 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 200 148 48 323 387 259), lower := (rows 35 67 44 200 148 48 64 128 256), losses := [] }

theorem u18389 : Upper (D 7) (R 7) [34,65,40,192,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18389 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18390 : Route 9 := (fun mask => (mask,id))

def c18390 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18390 : Upper (D 7) (R 7) [34,65,40,192,132,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,132,256] 13 (by decide) (choices 1) [1,2,16] r18390 c18390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4943
  · exact u4944
  · exact u4945

def b18391 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 200 273 34 212 148 404), lower := (rows 35 67 44 200 273 34 64 128 256), losses := [] }

theorem u18391 : Upper (D 7) (R 7) [34,65,40,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18391 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18392 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 474, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 67 44 200 273 36 210 146 402), lower := (rows 35 67 44 200 273 36 64 128 256), losses := [] }

theorem u18392 : Upper (D 7) (R 7) [34,65,40,192,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18392 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18393 : Route 9 := (fun mask => (mask,id))

def c18393 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18393 : Upper (D 7) (R 7) [34,65,40,192,257,16] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,257,16] 13 (by decide) (choices 1) [2,4,128] r18393 c18393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4946
  · exact u4947
  · exact u4948

def b18394 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 67 44 200 273 160 86 150 278), lower := (rows 35 67 44 200 273 160 64 128 256), losses := [] }

theorem u18394 : Upper (D 7) (R 7) [34,65,40,192,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18394 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18395 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 200 274 33 212 148 404), lower := (rows 35 67 44 200 274 33 64 128 256), losses := [] }

theorem u18395 : Upper (D 7) (R 7) [34,65,40,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18395 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18396 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 474, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 67 44 200 274 36 209 145 401), lower := (rows 35 67 44 200 274 36 64 128 256), losses := [] }

theorem u18396 : Upper (D 7) (R 7) [34,65,40,192,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18396 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18397 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 67 44 200 274 48 197 133 389), lower := (rows 35 67 44 200 274 48 64 128 256), losses := [] }

theorem u18397 : Upper (D 7) (R 7) [34,65,40,192,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18397 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18398 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 67 44 200 274 160 85 149 277), lower := (rows 35 67 44 200 274 160 64 128 256), losses := [] }

theorem u18398 : Upper (D 7) (R 7) [34,65,40,192,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18398 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18399 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 200 276 33 210 146 402), lower := (rows 35 67 44 200 276 33 64 128 256), losses := [] }

theorem u18399 : Upper (D 7) (R 7) [34,65,40,192,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18399 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18400 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 200 276 34 209 145 401), lower := (rows 35 67 44 200 276 34 64 128 256), losses := [] }

theorem u18400 : Upper (D 7) (R 7) [34,65,40,192,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18400 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18401 : Route 9 := (fun mask => (mask,id))

def c18401 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18401 : Upper (D 7) (R 7) [34,65,40,192,260,16] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,260,16] 13 (by decide) (choices 1) [1,2,128] r18401 c18401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4949
  · exact u4950
  · exact u4951

def b18402 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 67 44 200 276 160 83 147 275), lower := (rows 35 67 44 200 276 160 64 128 256), losses := [] }

theorem u18402 : Upper (D 7) (R 7) [34,65,40,192,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18402 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18403 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 200 400 33 86 150 278), lower := (rows 35 67 44 200 400 33 64 128 256), losses := [] }

theorem u18403 : Upper (D 7) (R 7) [34,65,40,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18403 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18404 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 200 400 34 85 149 277), lower := (rows 35 67 44 200 400 34 64 128 256), losses := [] }

theorem u18404 : Upper (D 7) (R 7) [34,65,40,192,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18404 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18405 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 474, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 67 44 200 400 36 83 147 275), lower := (rows 35 67 44 200 400 36 64 128 256), losses := [] }

theorem u18405 : Upper (D 7) (R 7) [34,65,40,192,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18405 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18406 : Route 9 := (fun mask => (mask,id))

def c18406 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18406 : Upper (D 7) (R 7) [34,65,40,192,384,16] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,384,16] 13 (by decide) (choices 1) [1,2,4] r18406 c18406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4952
  · exact u4953
  · exact u4954

def b18407 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 265 146 36 208 208 464), lower := (rows 35 67 44 265 146 36 64 128 256), losses := [] }

theorem u18407 : Upper (D 7) (R 7) [34,65,40,257,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18407 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18408 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 67 44 265 146 48 196 196 452), lower := (rows 35 67 44 265 146 48 64 128 256), losses := [] }

theorem u18408 : Upper (D 7) (R 7) [34,65,40,257,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18408 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18409 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 265 146 96 212 148 404), lower := (rows 35 67 44 265 146 96 64 128 256), losses := [] }

theorem u18409 : Upper (D 7) (R 7) [34,65,40,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18409 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18410 : Route 9 := (fun mask => (mask,id))

def c18410 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18410 : Upper (D 7) (R 7) [34,65,40,257,130,128] 13 := by
  apply FastRouting.sound _ _ [34,65,40,257,130,128] 13 (by decide) (choices 1) [4,16] r18410 c18410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4955
  · exact u4956

def b18411 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 265 148 34 208 208 464), lower := (rows 35 67 44 265 148 34 64 128 256), losses := [] }

theorem u18411 : Upper (D 7) (R 7) [34,65,40,257,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18411 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18412 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5),(2,0),(3,5)], upper := (rows 35 67 44 265 148 48 194 194 450), lower := (rows 35 67 44 265 148 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 60 67 131 259), good := (rows 482 450 60 508 180 48 64 128 256) }] }

theorem u18412 : Upper (D 7) (R 7) [34,65,40,257,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18412 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18413 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 265 148 96 210 146 402), lower := (rows 35 67 44 265 148 96 64 128 256), losses := [] }

theorem u18413 : Upper (D 7) (R 7) [34,65,40,257,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18414 : Route 9 := (fun mask => (mask,id))

def c18414 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18414 : Upper (D 7) (R 7) [34,65,40,257,132,128] 13 := by
  apply FastRouting.sound _ _ [34,65,40,257,132,128] 13 (by decide) (choices 1) [2,16] r18414 c18414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4957
  · exact u4958

def b18415 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 265 208 34 212 148 404), lower := (rows 35 67 44 265 208 34 64 128 256), losses := [] }

theorem u18415 : Upper (D 7) (R 7) [34,65,40,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18415 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18416 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 265 208 36 210 146 402), lower := (rows 35 67 44 265 208 36 64 128 256), losses := [] }

theorem u18416 : Upper (D 7) (R 7) [34,65,40,257,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18416 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18417 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 67 44 265 208 48 198 134 390), lower := (rows 35 67 44 265 208 48 64 128 256), losses := [] }

theorem u18417 : Upper (D 7) (R 7) [34,65,40,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18417 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18418 : Route 9 := (fun mask => (mask,id))

def c18418 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18418 : Upper (D 7) (R 7) [34,65,40,257,192,128] 13 := by
  apply FastRouting.sound _ _ [34,65,40,257,192,128] 13 (by decide) (choices 1) [2,4,16] r18418 c18418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4959
  · exact u4960
  · exact u4961

def b18419 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 67 44 266 145 36 208 208 464), lower := (rows 35 67 44 266 145 36 64 128 256), losses := [] }

theorem u18419 : Upper (D 7) (R 7) [34,65,40,258,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18419 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u18419
end Delivery.IrregularNine14.P07
