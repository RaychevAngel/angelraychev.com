import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0045

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6360 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 38 133 88 274 33 456 392 392), lower := (rows 97 38 133 88 274 33 64 128 256), losses := [] }

theorem u6360 : Upper (D 9) (R 9) [96,36,129,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6360 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6361 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(4,6)], upper := (rows 97 38 133 88 274 40 449 385 385), lower := (rows 97 38 133 88 274 40 64 128 256), losses := [] }

theorem u6361 : Upper (D 9) (R 9) [96,36,129,80,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6361 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6362 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 345, targets := 128 },{ cop := 2, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(3,7),(4,7)], upper := (rows 97 38 133 88 274 160 329 393 265), lower := (rows 97 38 133 88 274 160 64 128 256), losses := [] }

theorem u6362 : Upper (D 9) (R 9) [96,36,129,80,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6362 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6363 : Route 9 := (fun mask => (mask,id))

def c6363 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6363 : Upper (D 9) (R 9) [96,36,129,80,258,256] 13 := by
  apply FastRouting.sound _ _ [96,36,129,80,258,256] 13 (by decide) (choices 1) [1,8,128] r6363 c6363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2718
  · exact u2719
  · exact u2720

def b6364 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 38 133 88 280 33 450 386 386), lower := (rows 97 38 133 88 280 33 64 128 256), losses := [] }

theorem u6364 : Upper (D 9) (R 9) [96,36,129,80,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6364 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6365 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,5),(3,5),(4,5)], upper := (rows 97 38 133 88 280 34 449 385 385), lower := (rows 97 38 133 88 280 34 64 128 256), losses := [] }

theorem u6365 : Upper (D 9) (R 9) [96,36,129,80,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6365 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6366 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 345, targets := 128 },{ cop := 0, region := 390, targets := 64 }], pairs := [(0,7),(1,6),(2,6),(3,7),(4,7)], upper := (rows 97 38 133 88 280 160 323 387 259), lower := (rows 97 38 133 88 280 160 64 128 256), losses := [] }

theorem u6366 : Upper (D 9) (R 9) [96,36,129,80,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6366 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6367 : PairBound 9 := { available := 131, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 0, region := 134, targets := 64 }], pairs := [(0,8),(1,6),(1,8),(2,6),(2,8)], upper := (rows 97 38 133 88 280 288 195 131 387), lower := (rows 97 38 133 88 280 288 64 128 256), losses := [] }

theorem u6367 : Upper (D 9) (R 9) [96,36,129,80,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6367 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6368 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 38 133 88 400 33 330 394 266), lower := (rows 97 38 133 88 400 33 64 128 256), losses := [] }

theorem u6368 : Upper (D 9) (R 9) [96,36,129,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6368 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6369 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 34, targets := 449 }], pairs := [(1,0),(1,6),(1,7),(1,8)], upper := (rows 97 38 133 88 400 34 329 393 265), lower := (rows 97 38 133 88 400 34 64 128 256), losses := [] }

theorem u6369 : Upper (D 9) (R 9) [96,36,129,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6369 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6370 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(4,6)], upper := (rows 97 38 133 88 400 40 323 387 259), lower := (rows 97 38 133 88 400 40 64 128 256), losses := [] }

theorem u6370 : Upper (D 9) (R 9) [96,36,129,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6370 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6371 : Route 9 := (fun mask => (mask,id))

def c6371 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6371 : Upper (D 9) (R 9) [96,36,129,80,384,256] 13 := by
  apply FastRouting.sound _ _ [96,36,129,80,384,256] 13 (by decide) (choices 1) [1,2,8] r6371 c6371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2721
  · exact u2722
  · exact u2723

def b6372 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 42, targets := 321 }], pairs := [(1,0),(1,6),(1,8),(3,0)], upper := (rows 97 38 133 138 273 40 336 464 336), lower := (rows 97 38 133 138 273 40 64 128 256), losses := [] }

theorem u6372 : Upper (D 9) (R 9) [96,36,129,130,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6372 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6373 : PairBound 9 := { available := 328, camps := [{ cop := 1, region := 456, targets := 33 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,7)], upper := (rows 97 38 133 138 273 48 328 456 328), lower := (rows 97 38 133 138 273 48 64 128 256), losses := [] }

theorem u6373 : Upper (D 9) (R 9) [96,36,129,130,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6373 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6374 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 38 133 138 273 96 344 408 280), lower := (rows 97 38 133 138 273 96 64 128 256), losses := [] }

theorem u6374 : Upper (D 9) (R 9) [96,36,129,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6374 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6375 : Route 9 := (fun mask => (mask,id))

def c6375 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6375 : Upper (D 9) (R 9) [96,36,129,130,257,256] 13 := by
  apply FastRouting.sound _ _ [96,36,129,130,257,256] 13 (by decide) (choices 1) [8,16] r6375 c6375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2724
  · exact u2725

def b6376 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 38 133 138 280 33 336 464 336), lower := (rows 97 38 133 138 280 33 64 128 256), losses := [] }

theorem u6376 : Upper (D 9) (R 9) [96,36,129,130,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6376 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6377 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 369, targets := 128 },{ cop := 0, region := 388, targets := 32 }], pairs := [(0,7),(2,5),(3,5),(4,7)], upper := (rows 97 38 133 138 280 48 321 449 321), lower := (rows 97 38 133 138 280 48 64 128 256), losses := [{ target := 5, region := (rows 1 2 5 10 18 0 69 133 261), good := (rows 453 478 453 154 280 16 64 128 256) }] }

theorem u6377 : Upper (D 9) (R 9) [96,36,129,130,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6377 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6378 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 38 133 138 280 96 337 401 273), lower := (rows 97 38 133 138 280 96 64 128 256), losses := [] }

theorem u6378 : Upper (D 9) (R 9) [96,36,129,130,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6378 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6379 : Route 9 := (fun mask => (mask,id))

def c6379 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6379 : Upper (D 9) (R 9) [96,36,129,130,264,256] 13 := by
  apply FastRouting.sound _ _ [96,36,129,130,264,256] 13 (by decide) (choices 1) [1,16] r6379 c6379
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2726
  · exact u2727

def b6380 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 38 133 138 336 33 344 408 280), lower := (rows 97 38 133 138 336 33 64 128 256), losses := [] }

theorem u6380 : Upper (D 9) (R 9) [96,36,129,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6380 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6381 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 42, targets := 321 }], pairs := [(1,0),(1,6),(1,8),(3,0)], upper := (rows 97 38 133 138 336 40 337 401 273), lower := (rows 97 38 133 138 336 40 64 128 256), losses := [] }

theorem u6381 : Upper (D 9) (R 9) [96,36,129,130,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6381 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6382 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 38 133 138 336 48 329 393 265), lower := (rows 97 38 133 138 336 48 64 128 256), losses := [] }

theorem u6382 : Upper (D 9) (R 9) [96,36,129,130,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6382 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6383 : Route 9 := (fun mask => (mask,id))

def c6383 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6383 : Upper (D 9) (R 9) [96,36,129,130,320,256] 13 := by
  apply FastRouting.sound _ _ [96,36,129,130,320,256] 13 (by decide) (choices 1) [1,8,16] r6383 c6383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2728
  · exact u2729
  · exact u2730

def b6384 : PairBound 9 := { available := 328, camps := [{ cop := 2, region := 34, targets := 449 }], pairs := [(1,0),(1,6),(1,7),(1,8)], upper := (rows 97 38 133 152 273 34 328 456 328), lower := (rows 97 38 133 152 273 34 64 128 256), losses := [] }

theorem u6384 : Upper (D 9) (R 9) [96,36,129,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6384 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6385 : Route 9 := (fun mask => (mask,id))

def c6385 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6385 : Upper (D 9) (R 9) [96,36,129,144,257,8] 13 := by
  apply FastRouting.sound _ _ [96,36,129,144,257,8] 13 (by decide) (choices 1) [2,256] r6385 c6385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2731
  · exact u2732

def b6386 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 38 133 152 273 96 330 394 266), lower := (rows 97 38 133 152 273 96 64 128 256), losses := [] }

theorem u6386 : Upper (D 9) (R 9) [96,36,129,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6386 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6387 : Route 9 := (fun mask => (mask,id))

def c6387 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6387 : Upper (D 9) (R 9) [96,36,129,144,257,256] 13 := by
  apply FastRouting.sound _ _ [96,36,129,144,257,256] 13 (by decide) (choices 1) [2,8] r6387 c6387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2733
  · exact u2734

def b6388 : PairBound 9 := { available := 328, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 38 133 152 274 33 328 456 328), lower := (rows 97 38 133 152 274 33 64 128 256), losses := [] }

theorem u6388 : Upper (D 9) (R 9) [96,36,129,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6388 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6389 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 337, targets := 128 },{ cop := 0, region := 388, targets := 32 }], pairs := [(0,7),(2,5),(3,5),(4,7)], upper := (rows 97 38 133 152 274 40 321 449 321), lower := (rows 97 38 133 152 274 40 64 128 256), losses := [{ target := 5, region := (rows 1 2 5 10 18 0 69 133 261), good := (rows 453 478 453 152 282 8 64 128 256) }] }

theorem u6389 : Upper (D 9) (R 9) [96,36,129,144,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6389 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6390 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 38 133 152 274 96 329 393 265), lower := (rows 97 38 133 152 274 96 64 128 256), losses := [] }

theorem u6390 : Upper (D 9) (R 9) [96,36,129,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6390 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6391 : Route 9 := (fun mask => (mask,id))

def c6391 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6391 : Upper (D 9) (R 9) [96,36,129,144,258,256] 13 := by
  apply FastRouting.sound _ _ [96,36,129,144,258,256] 13 (by decide) (choices 1) [1,8] r6391 c6391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2735
  · exact u2736

def b6392 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 38 133 152 280 33 322 450 322), lower := (rows 97 38 133 152 280 33 64 128 256), losses := [] }

theorem u6392 : Upper (D 9) (R 9) [96,36,129,144,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6392 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6393 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,5),(3,5),(4,5)], upper := (rows 97 38 133 152 280 34 321 449 321), lower := (rows 97 38 133 152 280 34 64 128 256), losses := [] }

theorem u6393 : Upper (D 9) (R 9) [96,36,129,144,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6393 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6394 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 38 133 152 280 96 323 387 259), lower := (rows 97 38 133 152 280 96 64 128 256), losses := [] }

theorem u6394 : Upper (D 9) (R 9) [96,36,129,144,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6394 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6395 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,8)], upper := (rows 97 38 133 152 280 288 67 195 323), lower := (rows 97 38 133 152 280 288 64 128 256), losses := [] }

theorem u6395 : Upper (D 9) (R 9) [96,36,129,144,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6395 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6396 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 38 133 152 336 33 330 394 266), lower := (rows 97 38 133 152 336 33 64 128 256), losses := [] }

theorem u6396 : Upper (D 9) (R 9) [96,36,129,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6396 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6397 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 34, targets := 449 }], pairs := [(1,0),(1,6),(1,7),(1,8)], upper := (rows 97 38 133 152 336 34 329 393 265), lower := (rows 97 38 133 152 336 34 64 128 256), losses := [] }

theorem u6397 : Upper (D 9) (R 9) [96,36,129,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6397 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6398 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(4,7)], upper := (rows 97 38 133 152 336 40 323 387 259), lower := (rows 97 38 133 152 336 40 64 128 256), losses := [] }

theorem u6398 : Upper (D 9) (R 9) [96,36,129,144,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6398 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6399 : Route 9 := (fun mask => (mask,id))

def c6399 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6399 : Upper (D 9) (R 9) [96,36,129,144,320,256] 13 := by
  apply FastRouting.sound _ _ [96,36,129,144,320,256] 13 (by decide) (choices 1) [1,2,8] r6399 c6399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2737
  · exact u2738
  · exact u2739

def b6400 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 34, targets := 449 }], pairs := [(1,0),(1,6),(1,7),(1,8)], upper := (rows 97 38 133 200 273 34 344 408 280), lower := (rows 97 38 133 200 273 34 64 128 256), losses := [] }

theorem u6400 : Upper (D 9) (R 9) [96,36,129,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6400 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6401 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 3, region := 33, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(4,6)], upper := (rows 97 38 133 200 273 40 338 402 274), lower := (rows 97 38 133 200 273 40 64 128 256), losses := [] }

theorem u6401 : Upper (D 9) (R 9) [96,36,129,192,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6401 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6402 : Route 9 := (fun mask => (mask,id))

def c6402 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6402 : Upper (D 9) (R 9) [96,36,129,192,257,16] 13 := by
  apply FastRouting.sound _ _ [96,36,129,192,257,16] 13 (by decide) (choices 1) [2,8,256] r6402 c6402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2740
  · exact u2741
  · exact u2742

def r6403 : Route 9 := (fun mask => (mask,id))

def c6403 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6403 : Upper (D 9) (R 9) [96,36,129,192,257,256] 13 := by
  apply FastRouting.sound _ _ [96,36,129,192,257,256] 13 (by decide) (choices 1) [2,8,16] r6403 c6403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2743
  · exact u2744
  · exact u2745

def b6404 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 38 133 200 274 33 344 408 280), lower := (rows 97 38 133 200 274 33 64 128 256), losses := [] }

theorem u6404 : Upper (D 9) (R 9) [96,36,129,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6404 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6405 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 3, region := 33, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(4,6)], upper := (rows 97 38 133 200 274 40 337 401 273), lower := (rows 97 38 133 200 274 40 64 128 256), losses := [] }

theorem u6405 : Upper (D 9) (R 9) [96,36,129,192,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6405 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6406 : Route 9 := (fun mask => (mask,id))

def c6406 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6406 : Upper (D 9) (R 9) [96,36,129,192,258,16] 13 := by
  apply FastRouting.sound _ _ [96,36,129,192,258,16] 13 (by decide) (choices 1) [1,8,256] r6406 c6406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2746
  · exact u2747
  · exact u2748

def r6407 : Route 9 := (fun mask => (mask,id))

def c6407 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6407 : Upper (D 9) (R 9) [96,36,129,192,258,256] 13 := by
  apply FastRouting.sound _ _ [96,36,129,192,258,256] 13 (by decide) (choices 1) [1,8,16] r6407 c6407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2749
  · exact u2750
  · exact u2751

def b6408 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 38 133 200 280 33 338 402 274), lower := (rows 97 38 133 200 280 33 64 128 256), losses := [] }

theorem u6408 : Upper (D 9) (R 9) [96,36,129,192,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6408 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6409 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 34, targets := 449 }], pairs := [(1,0),(1,6),(1,7),(1,8)], upper := (rows 97 38 133 200 280 34 337 401 273), lower := (rows 97 38 133 200 280 34 64 128 256), losses := [] }

theorem u6409 : Upper (D 9) (R 9) [96,36,129,192,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6409 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6410 : Route 9 := (fun mask => (mask,id))

def c6410 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6410 : Upper (D 9) (R 9) [96,36,129,192,264,16] 13 := by
  apply FastRouting.sound _ _ [96,36,129,192,264,16] 13 (by decide) (choices 1) [1,2,256] r6410 c6410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2752
  · exact u2753
  · exact u2754

def r6411 : Route 9 := (fun mask => (mask,id))

def c6411 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6411 : Upper (D 9) (R 9) [96,36,129,192,264,256] 13 := by
  apply FastRouting.sound _ _ [96,36,129,192,264,256] 13 (by decide) (choices 1) [1,2,16] r6411 c6411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2755
  · exact u2756
  · exact u2757

def r6412 : Route 9 := (fun mask => (mask,id))

def c6412 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6412 : Upper (D 9) (R 9) [96,36,129,257,258,8] 13 := by
  apply FastRouting.sound _ _ [96,36,129,257,258,8] 13 (by decide) (choices 1) [16,128] r6412 c6412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2758
  · exact u2759

def b6413 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 396, targets := 32 },{ cop := 3, region := 196, targets := 256 }], pairs := [(2,5),(2,8),(3,5),(4,5)], upper := (rows 97 38 133 265 274 48 200 200 456), lower := (rows 97 38 133 265 274 48 64 128 256), losses := [{ target := 5, region := (rows 1 2 13 13 18 0 79 143 271), good := (rows 461 478 461 461 466 16 64 128 256) }] }

theorem u6413 : Upper (D 9) (R 9) [96,36,129,257,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6413 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6414 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 38 133 265 274 96 216 152 408), lower := (rows 97 38 133 265 274 96 64 128 256), losses := [] }

theorem u6414 : Upper (D 9) (R 9) [96,36,129,257,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6414 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6415 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 345, targets := 128 },{ cop := 2, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(3,7),(4,7)], upper := (rows 97 38 133 265 274 160 88 216 344), lower := (rows 97 38 133 265 274 160 64 128 256), losses := [] }

theorem u6415 : Upper (D 9) (R 9) [96,36,129,257,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6415 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6416 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 34, targets := 449 }], pairs := [(1,0),(1,6),(1,7),(1,8)], upper := (rows 97 38 133 265 336 34 216 152 408), lower := (rows 97 38 133 265 336 34 64 128 256), losses := [] }

theorem u6416 : Upper (D 9) (R 9) [96,36,129,257,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6416 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6417 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 4, region := 41, targets := 128 }], pairs := [(0,7),(3,7),(4,0),(4,5)], upper := (rows 97 38 133 265 336 40 210 146 402), lower := (rows 97 38 133 265 336 40 64 128 256), losses := [] }

theorem u6417 : Upper (D 9) (R 9) [96,36,129,257,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6417 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6418 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 38 133 265 336 48 202 138 394), lower := (rows 97 38 133 265 336 48 64 128 256), losses := [] }

theorem u6418 : Upper (D 9) (R 9) [96,36,129,257,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6418 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6419 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 345, targets := 128 },{ cop := 2, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(3,7),(4,7)], upper := (rows 97 38 133 265 336 160 90 154 282), lower := (rows 97 38 133 265 336 160 64 128 256), losses := [] }

theorem u6419 : Upper (D 9) (R 9) [96,36,129,257,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6419 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u6419
end Delivery.IrregularNine14.P09
