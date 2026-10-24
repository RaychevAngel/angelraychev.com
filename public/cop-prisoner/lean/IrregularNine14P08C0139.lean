import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0029

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r8340 : Route 9 := (fun mask => (mask,id))

def c8340 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8340 : Upper (D 8) (R 8) [34,12,17,288,96] 13 := by
  apply FastRouting.sound _ _ [34,12,17,288,96] 13 (by decide) (choices 1) [1,64,128] r8340 c8340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1745
  · exact u1746
  · exact u1747

def r8341 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8341 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8341 : Upper (D 8) (R 8) [34,12,17,288,192] 13 := by
  apply FastRouting.sound _ _ [34,12,17,288,192] 13 (by decide) (choices 1) [1,64] r8341 c8341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1748
  · exact u1749

def b8342 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 35 14 21 328 49 224 224 224 480), lower := (rows 35 14 21 328 49 32 64 128 256), losses := [] }

theorem u8342 : Upper (D 8) (R 8) [34,12,17,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8342 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8343 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 490, targets := 1 }], pairs := [(1,0)], upper := (rows 35 14 21 328 81 160 224 160 416), lower := (rows 35 14 21 328 81 32 64 128 256), losses := [] }

theorem u8343 : Upper (D 8) (R 8) [34,12,17,320,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8343 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8344 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 21 328 112 161 225 161 417), lower := (rows 35 14 21 328 112 32 64 128 256), losses := [] }

theorem u8344 : Upper (D 8) (R 8) [34,12,17,320,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8344 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8345 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 14 21 328 145 224 224 224 480), lower := (rows 35 14 21 328 145 32 64 128 256), losses := [] }

theorem u8345 : Upper (D 8) (R 8) [34,12,17,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8345 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8346 : Route 9 := (fun mask => (mask,id))

def c8346 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8346 : Upper (D 8) (R 8) [34,12,17,320,160] 13 := by
  apply FastRouting.sound _ _ [34,12,17,320,160] 13 (by decide) (choices 1) [1,64,128] r8346 c8346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1750
  · exact u1751
  · exact u1752

def b8347 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 21 328 208 161 225 161 417), lower := (rows 35 14 21 328 208 32 64 128 256), losses := [] }

theorem u8347 : Upper (D 8) (R 8) [34,12,17,320,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8347 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8348 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 35 14 52 73 49 480 448 448 448), lower := (rows 35 14 52 73 49 32 64 128 256), losses := [] }

theorem u8348 : Upper (D 8) (R 8) [34,12,48,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8348 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8349 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 14 52 73 81 416 480 416 416), lower := (rows 35 14 52 73 81 32 64 128 256), losses := [] }

theorem u8349 : Upper (D 8) (R 8) [34,12,48,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8349 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8350 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 52 73 112 417 449 385 385), lower := (rows 35 14 52 73 112 32 64 128 256), losses := [] }

theorem u8350 : Upper (D 8) (R 8) [34,12,48,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8350 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8351 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 356, targets := 1 }], pairs := [(2,0)], upper := (rows 35 14 52 73 145 480 480 480 480), lower := (rows 35 14 52 73 145 32 64 128 256), losses := [] }

theorem u8351 : Upper (D 8) (R 8) [34,12,48,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8351 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8352 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 14 52 73 176 481 449 449 449), lower := (rows 35 14 52 73 176 32 64 128 256), losses := [] }

theorem u8352 : Upper (D 8) (R 8) [34,12,48,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8352 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8353 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 52 73 208 417 481 417 417), lower := (rows 35 14 52 73 208 32 64 128 256), losses := [] }

theorem u8353 : Upper (D 8) (R 8) [34,12,48,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8353 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8354 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 35 14 52 73 273 224 224 224 480), lower := (rows 35 14 52 73 273 32 64 128 256), losses := [] }

theorem u8354 : Upper (D 8) (R 8) [34,12,48,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8354 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8355 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 14 52 73 304 225 193 193 449), lower := (rows 35 14 52 73 304 32 64 128 256), losses := [] }

theorem u8355 : Upper (D 8) (R 8) [34,12,48,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8355 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8356 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 52 73 336 161 225 161 417), lower := (rows 35 14 52 73 336 32 64 128 256), losses := [] }

theorem u8356 : Upper (D 8) (R 8) [34,12,48,65,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8356 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8357 : Route 9 := (fun mask => (mask,id))

def c8357 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8357 : Upper (D 8) (R 8) [34,12,48,65,384] 13 := by
  apply FastRouting.sound _ _ [34,12,48,65,384] 13 (by decide) (choices 1) [1,64,128] r8357 c8357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1753
  · exact u1754
  · exact u1755

def b8358 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 35 14 52 200 49 481 449 449 449), lower := (rows 35 14 52 200 49 32 64 128 256), losses := [] }

theorem u8358 : Upper (D 8) (R 8) [34,12,48,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8358 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8359 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 52 200 81 417 481 417 417), lower := (rows 35 14 52 200 81 32 64 128 256), losses := [] }

theorem u8359 : Upper (D 8) (R 8) [34,12,48,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8359 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8360 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 14 52 200 112 417 449 385 385), lower := (rows 35 14 52 200 112 32 64 128 256), losses := [] }

theorem u8360 : Upper (D 8) (R 8) [34,12,48,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8360 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8361 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 14 52 200 208 289 353 417 289), lower := (rows 35 14 52 200 208 32 64 128 256), losses := [] }

theorem u8361 : Upper (D 8) (R 8) [34,12,48,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8361 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8362 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8362 : Upper (D 8) (R 8) [34,12,48,192,257] 13 := by
  apply FastRouting.sound _ _ [34,12,48,192,257] 13 (by decide) (choices 1) [1,64] r8362 c8362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1756
  · exact u1757

def b8363 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 14 52 200 304 225 193 193 449), lower := (rows 35 14 52 200 304 32 64 128 256), losses := [] }

theorem u8363 : Upper (D 8) (R 8) [34,12,48,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8363 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8364 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 52 200 336 161 225 161 417), lower := (rows 35 14 52 200 336 32 64 128 256), losses := [] }

theorem u8364 : Upper (D 8) (R 8) [34,12,48,192,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8364 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8365 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 35 14 52 265 49 224 192 192 448), lower := (rows 35 14 52 265 49 32 64 128 256), losses := [] }

theorem u8365 : Upper (D 8) (R 8) [34,12,48,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8365 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8366 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 164, targets := 1 }], pairs := [(2,0)], upper := (rows 35 14 52 265 81 224 224 224 480), lower := (rows 35 14 52 265 81 32 64 128 256), losses := [] }

theorem u8366 : Upper (D 8) (R 8) [34,12,48,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8366 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8367 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 14 52 265 112 225 193 193 449), lower := (rows 35 14 52 265 112 32 64 128 256), losses := [] }

theorem u8367 : Upper (D 8) (R 8) [34,12,48,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8367 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8368 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8368 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8368 : Upper (D 8) (R 8) [34,12,48,257,192] 13 := by
  apply FastRouting.sound _ _ [34,12,48,257,192] 13 (by decide) (choices 1) [1,64] r8368 c8368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1758
  · exact u1759

def b8369 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 35 14 52 328 49 225 193 193 449), lower := (rows 35 14 52 328 49 32 64 128 256), losses := [] }

theorem u8369 : Upper (D 8) (R 8) [34,12,48,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8369 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8370 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 52 328 81 161 225 161 417), lower := (rows 35 14 52 328 81 32 64 128 256), losses := [] }

theorem u8370 : Upper (D 8) (R 8) [34,12,48,320,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8370 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8371 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 14 52 328 112 161 193 129 385), lower := (rows 35 14 52 328 112 32 64 128 256), losses := [] }

theorem u8371 : Upper (D 8) (R 8) [34,12,48,320,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8371 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8372 : Route 9 := (fun mask => (mask,id))

def c8372 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8372 : Upper (D 8) (R 8) [34,12,48,320,129] 13 := by
  apply FastRouting.sound _ _ [34,12,48,320,129] 13 (by decide) (choices 1) [1,64,128] r8372 c8372
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1760
  · exact u1761
  · exact u1762

def b8373 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 14 52 328 176 225 193 193 449), lower := (rows 35 14 52 328 176 32 64 128 256), losses := [] }

theorem u8373 : Upper (D 8) (R 8) [34,12,48,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8373 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8374 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 52 328 208 161 225 161 417), lower := (rows 35 14 52 328 208 32 64 128 256), losses := [] }

theorem u8374 : Upper (D 8) (R 8) [34,12,48,320,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8374 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8375 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 14 69 152 49 480 480 480 480), lower := (rows 35 14 69 152 49 32 64 128 256), losses := [] }

theorem u8375 : Upper (D 8) (R 8) [34,12,65,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8375 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8376 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 14 69 152 81 416 480 416 416), lower := (rows 35 14 69 152 81 32 64 128 256), losses := [] }

theorem u8376 : Upper (D 8) (R 8) [34,12,65,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8376 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8377 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 69 152 112 417 481 417 417), lower := (rows 35 14 69 152 112 32 64 128 256), losses := [] }

theorem u8377 : Upper (D 8) (R 8) [34,12,65,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8377 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8378 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 69 152 145 352 352 480 352), lower := (rows 35 14 69 152 145 32 64 128 256), losses := [] }

theorem u8378 : Upper (D 8) (R 8) [34,12,65,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8378 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8379 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 69 152 176 353 353 481 353), lower := (rows 35 14 69 152 176 32 64 128 256), losses := [] }

theorem u8379 : Upper (D 8) (R 8) [34,12,65,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8379 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8380 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 69 152 208 289 353 417 289), lower := (rows 35 14 69 152 208 32 64 128 256), losses := [] }

theorem u8380 : Upper (D 8) (R 8) [34,12,65,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8380 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8381 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 35 14 69 152 273 224 224 224 480), lower := (rows 35 14 69 152 273 32 64 128 256), losses := [] }

theorem u8381 : Upper (D 8) (R 8) [34,12,65,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8381 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8382 : Route 9 := (fun mask => (mask,id))

def c8382 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8382 : Upper (D 8) (R 8) [34,12,65,144,288] 13 := by
  apply FastRouting.sound _ _ [34,12,65,144,288] 13 (by decide) (choices 1) [1,64,128] r8382 c8382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1763
  · exact u1764
  · exact u1765

def b8383 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 69 152 336 161 225 161 417), lower := (rows 35 14 69 152 336 32 64 128 256), losses := [] }

theorem u8383 : Upper (D 8) (R 8) [34,12,65,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8383 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8384 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 69 152 400 97 97 225 353), lower := (rows 35 14 69 152 400 32 64 128 256), losses := [] }

theorem u8384 : Upper (D 8) (R 8) [34,12,65,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8384 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8385 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 14 69 168 49 496 464 464 464), lower := (rows 35 14 69 168 49 32 64 128 256), losses := [] }

theorem u8385 : Upper (D 8) (R 8) [34,12,65,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8385 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8386 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 14 69 168 81 432 496 432 432), lower := (rows 35 14 69 168 81 32 64 128 256), losses := [] }

theorem u8386 : Upper (D 8) (R 8) [34,12,65,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8386 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8387 : Route 9 := (fun mask => (mask,id))

def c8387 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u8387 : Upper (D 8) (R 8) [34,12,65,160,96] 13 := by
  apply FastRouting.sound _ _ [34,12,65,160,96] 13 (by decide) (choices 1) [1,16,128,256] r8387 c8387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1766
  · exact u1767
  · exact u1768
  · exact u1769

def b8388 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 360, targets := 1 }], pairs := [(3,0)], upper := (rows 35 14 69 168 145 368 368 496 368), lower := (rows 35 14 69 168 145 32 64 128 256), losses := [] }

theorem u8388 : Upper (D 8) (R 8) [34,12,65,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8388 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8389 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 14 69 168 176 369 337 465 337), lower := (rows 35 14 69 168 176 32 64 128 256), losses := [] }

theorem u8389 : Upper (D 8) (R 8) [34,12,65,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8389 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8390 : Route 9 := (fun mask => (mask,id))

def c8390 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8390 : Upper (D 8) (R 8) [34,12,65,160,192] 13 := by
  apply FastRouting.sound _ _ [34,12,65,160,192] 13 (by decide) (choices 1) [1,16,256] r8390 c8390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1770
  · exact u1771
  · exact u1772

def b8391 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 35 14 69 168 273 240 240 240 496), lower := (rows 35 14 69 168 273 32 64 128 256), losses := [] }

theorem u8391 : Upper (D 8) (R 8) [34,12,65,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8391 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8392 : Route 9 := (fun mask => (mask,id))

def c8392 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8392 : Upper (D 8) (R 8) [34,12,65,160,288] 13 := by
  apply FastRouting.sound _ _ [34,12,65,160,288] 13 (by decide) (choices 1) [1,16,64,128] r8392 c8392
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1773
  · exact u1774
  · exact u1775
  · exact u1776

def r8393 : Route 9 := (fun mask => (mask,id))

def c8393 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8393 : Upper (D 8) (R 8) [34,12,65,160,320] 13 := by
  apply FastRouting.sound _ _ [34,12,65,160,320] 13 (by decide) (choices 1) [1,16,128] r8393 c8393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1777
  · exact u1778
  · exact u1779

def r8394 : Route 9 := (fun mask => (mask,id))

def c8394 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8394 : Upper (D 8) (R 8) [34,12,65,160,384] 13 := by
  apply FastRouting.sound _ _ [34,12,65,160,384] 13 (by decide) (choices 1) [1,16,64] r8394 c8394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1780
  · exact u1781
  · exact u1782

def b8395 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 14 69 280 49 224 224 224 480), lower := (rows 35 14 69 280 49 32 64 128 256), losses := [] }

theorem u8395 : Upper (D 8) (R 8) [34,12,65,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8395 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8396 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 14 69 280 81 160 224 160 416), lower := (rows 35 14 69 280 81 32 64 128 256), losses := [] }

theorem u8396 : Upper (D 8) (R 8) [34,12,65,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8396 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8397 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 69 280 112 161 225 161 417), lower := (rows 35 14 69 280 112 32 64 128 256), losses := [] }

theorem u8397 : Upper (D 8) (R 8) [34,12,65,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8397 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8398 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 360, targets := 1 }], pairs := [(3,0)], upper := (rows 35 14 69 280 145 224 224 224 480), lower := (rows 35 14 69 280 145 32 64 128 256), losses := [] }

theorem u8398 : Upper (D 8) (R 8) [34,12,65,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8398 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8399 : Route 9 := (fun mask => (mask,id))

def c8399 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8399 : Upper (D 8) (R 8) [34,12,65,272,160] 13 := by
  apply FastRouting.sound _ _ [34,12,65,272,160] 13 (by decide) (choices 1) [1,64,128] r8399 c8399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1783
  · exact u1784
  · exact u1785

#print axioms u8399
end Delivery.IrregularNine14.P08
