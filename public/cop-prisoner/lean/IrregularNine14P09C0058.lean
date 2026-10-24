import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0010

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3480 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 98 164 73 280 48 449 385 385), lower := (rows 7 98 164 73 280 48 64 128 256), losses := [] }

theorem u3480 : Upper (D 9) (R 9) [6,96,160,65,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3480 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3481 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 7 98 164 73 280 160 337 401 273), lower := (rows 7 98 164 73 280 160 64 128 256), losses := [] }

theorem u3481 : Upper (D 9) (R 9) [6,96,160,65,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3481 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3482 : Route 9 := (fun mask => (mask,id))

def c3482 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3482 : Upper (D 9) (R 9) [6,96,160,65,264,256] 13 := by
  apply FastRouting.sound _ _ [6,96,160,65,264,256] 13 (by decide) (choices 1) [1,16,128] r3482 c3482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u601
  · exact u602
  · exact u603

def b3483 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 436, targets := 64 },{ cop := 3, region := 34, targets := 128 }], pairs := [(1,7),(2,6),(3,5),(4,5),(4,6)], upper := (rows 7 98 164 73 400 33 344 408 280), lower := (rows 7 98 164 73 400 33 64 128 256), losses := [] }

theorem u3483 : Upper (D 9) (R 9) [6,96,160,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3483 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3484 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 7 98 164 73 400 40 337 401 273), lower := (rows 7 98 164 73 400 40 64 128 256), losses := [] }

theorem u3484 : Upper (D 9) (R 9) [6,96,160,65,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3484 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3485 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 98 164 73 400 48 329 393 265), lower := (rows 7 98 164 73 400 48 64 128 256), losses := [] }

theorem u3485 : Upper (D 9) (R 9) [6,96,160,65,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3485 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3486 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 436, targets := 64 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(2,6),(3,5),(4,5),(4,6)], upper := (rows 7 98 164 73 400 288 89 153 281), lower := (rows 7 98 164 73 400 288 64 128 256), losses := [] }

theorem u3486 : Upper (D 9) (R 9) [6,96,160,65,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3486 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3487 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 200, targets := 1 }], pairs := [(1,7),(2,6),(3,0),(3,5),(4,5)], upper := (rows 7 98 164 88 273 33 456 392 392), lower := (rows 7 98 164 88 273 33 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 16 49 0 136 264), good := (rows 39 34 164 444 305 33 0 128 256) },{ target := 7, region := (rows 1 10 4 8 16 49 64 0 256), good := (rows 39 98 36 122 305 33 64 0 256) }] }

theorem u3487 : Upper (D 9) (R 9) [6,96,160,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3487 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3488 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 7 98 164 88 273 40 449 385 385), lower := (rows 7 98 164 88 273 40 64 128 256), losses := [] }

theorem u3488 : Upper (D 9) (R 9) [6,96,160,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3488 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3489 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 7 98 164 88 273 160 329 393 265), lower := (rows 7 98 164 88 273 160 64 128 256), losses := [] }

theorem u3489 : Upper (D 9) (R 9) [6,96,160,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3489 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3490 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 200, targets := 256 }], pairs := [(1,0),(1,7),(3,5),(3,8),(4,5)], upper := (rows 7 98 164 88 273 288 201 137 393), lower := (rows 7 98 164 88 273 288 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 304 64 128 256), good := (rows 6 98 164 122 304 288 64 128 288) },{ target := 7, region := (rows 1 10 4 8 16 304 64 0 256), good := (rows 7 98 36 122 305 288 64 0 288) }] }

theorem u3490 : Upper (D 9) (R 9) [6,96,160,80,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3490 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3491 : Route 9 := (fun mask => (mask,id))

def c3491 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3491 : Upper (D 9) (R 9) [6,96,160,80,264,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,264,1] 13 (by decide) (choices 1) [1,128,256] r3491 c3491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u604
  · exact u605
  · exact u606

def b3492 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 7 98 164 88 280 160 321 385 257), lower := (rows 7 98 164 88 280 160 64 128 256), losses := [] }

theorem u3492 : Upper (D 9) (R 9) [6,96,160,80,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3492 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3493 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5),(4,5)], upper := (rows 7 98 164 88 280 288 193 129 385), lower := (rows 7 98 164 88 280 288 64 128 256), losses := [] }

theorem u3493 : Upper (D 9) (R 9) [6,96,160,80,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3493 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3494 : Route 9 := (fun mask => (mask,id))

def c3494 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3494 : Upper (D 9) (R 9) [6,96,160,80,384,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,384,1] 13 (by decide) (choices 1) [1,8,256] r3494 c3494
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u607
  · exact u608
  · exact u609

def b3495 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 7 98 164 88 400 40 321 385 257), lower := (rows 7 98 164 88 400 40 64 128 256), losses := [] }

theorem u3495 : Upper (D 9) (R 9) [6,96,160,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3495 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3496 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 36, targets := 65 }], pairs := [(1,0),(2,0),(2,6),(3,5),(4,5)], upper := (rows 7 98 164 88 400 288 73 137 265), lower := (rows 7 98 164 88 400 288 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 304 64 128 256), good := (rows 6 98 164 126 436 288 64 128 288) }] }

theorem u3496 : Upper (D 9) (R 9) [6,96,160,80,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3496 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3497 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 39, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5),(4,5)], upper := (rows 7 98 164 200 273 33 344 408 280), lower := (rows 7 98 164 200 273 33 64 128 256), losses := [] }

theorem u3497 : Upper (D 9) (R 9) [6,96,160,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3497 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3498 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 2, region := 339, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(4,6)], upper := (rows 7 98 164 200 273 40 337 401 273), lower := (rows 7 98 164 200 273 40 64 128 256), losses := [] }

theorem u3498 : Upper (D 9) (R 9) [6,96,160,192,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3498 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3499 : Route 9 := (fun mask => (mask,id))

def c3499 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3499 : Upper (D 9) (R 9) [6,96,160,192,257,16] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192,257,16] 13 (by decide) (choices 1) [1,8,256] r3499 c3499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u610
  · exact u611
  · exact u612

def r3500 : Route 9 := (fun mask => (mask,id))

def c3500 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3500 : Upper (D 9) (R 9) [6,96,160,192,257,256] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192,257,256] 13 (by decide) (choices 1) [1,8,16] r3500 c3500
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u613
  · exact u614
  · exact u615

def b3501 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 39, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5),(4,5)], upper := (rows 7 98 164 200 280 33 337 401 273), lower := (rows 7 98 164 200 280 33 64 128 256), losses := [] }

theorem u3501 : Upper (D 9) (R 9) [6,96,160,192,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3501 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3502 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 98 164 200 280 48 321 385 257), lower := (rows 7 98 164 200 280 48 64 128 256), losses := [] }

theorem u3502 : Upper (D 9) (R 9) [6,96,160,192,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3502 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3503 : Route 9 := (fun mask => (mask,id))

def c3503 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3503 : Upper (D 9) (R 9) [6,96,160,192,264,256] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192,264,256] 13 (by decide) (choices 1) [1,16] r3503 c3503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u616
  · exact u617

def r3504 : Route 9 := (fun mask => (mask,id))

def c3504 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3504 : Upper (D 9) (R 9) [6,96,160,257,320,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,257,320,1] 13 (by decide) (choices 1) [8,16,128] r3504 c3504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u618
  · exact u619
  · exact u620

def r3505 : Route 9 := (fun mask => (mask,id))

def c3505 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3505 : Upper (D 9) (R 9) [6,96,160,257,320,8] 13 := by
  apply FastRouting.sound _ _ [6,96,160,257,320,8] 13 (by decide) (choices 1) [1,16,128] r3505 c3505
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u621
  · exact u622
  · exact u623

def b3506 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 397, targets := 64 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6)], upper := (rows 7 98 164 265 336 48 201 137 393), lower := (rows 7 98 164 265 336 48 64 128 256), losses := [] }

theorem u3506 : Upper (D 9) (R 9) [6,96,160,257,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3506 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3507 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 7 98 164 265 336 160 89 153 281), lower := (rows 7 98 164 265 336 160 64 128 256), losses := [] }

theorem u3507 : Upper (D 9) (R 9) [6,96,160,257,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3507 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3508 : Route 9 := (fun mask => (mask,id))

def c3508 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3508 : Upper (D 9) (R 9) [6,96,160,320,384,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,320,384,1] 13 (by decide) (choices 1) [1,8,16] r3508 c3508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u624
  · exact u625
  · exact u626

def b3509 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 7 98 164 328 400 40 81 145 273), lower := (rows 7 98 164 328 400 40 64 128 256), losses := [] }

theorem u3509 : Upper (D 9) (R 9) [6,96,160,320,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3509 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3510 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 56, targets := 448 }], pairs := [(3,6),(3,7),(3,8),(4,6),(4,7)], upper := (rows 7 98 388 25 56 33 448 448 448), lower := (rows 7 98 388 25 56 33 64 128 256), losses := [] }

theorem u3510 : Upper (D 9) (R 9) [6,96,384,17,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3510 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3511 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 413, targets := 64 },{ cop := 5, region := 2, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6),(4,6)], upper := (rows 7 98 388 25 56 96 449 385 385), lower := (rows 7 98 388 25 56 96 64 128 256), losses := [] }

theorem u3511 : Upper (D 9) (R 9) [6,96,384,17,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3511 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3512 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 389, targets := 32 }], pairs := [(0,5),(1,7),(2,5),(3,6),(4,6)], upper := (rows 7 98 388 25 56 160 321 449 321), lower := (rows 7 98 388 25 56 160 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 17 164 0 128 256), good := (rows 63 34 420 25 56 160 0 160 256) },{ target := 7, region := (rows 1 18 4 8 16 32 73 0 265), good := (rows 327 98 260 347 378 32 64 0 256) }] }

theorem u3512 : Upper (D 9) (R 9) [6,96,384,17,40,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3512 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3513 : Route 9 := (fun mask => (mask,id))

def c3513 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3513 : Upper (D 9) (R 9) [6,96,384,17,160,1] 13 := by
  apply FastRouting.sound _ _ [6,96,384,17,160,1] 13 (by decide) (choices 1) [8,256] r3513 c3513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u627
  · exact u628

def r3514 : Route 9 := (fun mask => (mask,id))

def c3514 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3514 : Upper (D 9) (R 9) [6,96,384,17,160,8] 13 := by
  apply FastRouting.sound _ _ [6,96,384,17,160,8] 13 (by decide) (choices 1) [1,256] r3514 c3514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u629
  · exact u630

def b3515 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 413, targets := 64 },{ cop := 5, region := 2, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6),(4,6)], upper := (rows 7 98 388 25 176 96 329 393 265), lower := (rows 7 98 388 25 176 96 64 128 256), losses := [] }

theorem u3515 : Upper (D 9) (R 9) [6,96,384,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3515 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3516 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 48, targets := 65 },{ cop := 3, region := 452, targets := 32 },{ cop := 3, region := 354, targets := 128 }], pairs := [(1,7),(2,5),(3,6),(4,0),(4,6)], upper := (rows 7 98 388 25 176 288 73 201 329), lower := (rows 7 98 388 25 176 288 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 20 292 0 128 256), good := (rows 63 34 436 25 176 288 0 128 288) }] }

theorem u3516 : Upper (D 9) (R 9) [6,96,384,17,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3516 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3517 : PairBound 9 := { available := 400, camps := [{ cop := 4, region := 42, targets := 384 }], pairs := [(1,7),(1,8),(3,7),(3,8)], upper := (rows 7 98 388 41 81 40 464 400 400), lower := (rows 7 98 388 41 81 40 64 128 256), losses := [] }

theorem u3517 : Upper (D 9) (R 9) [6,96,384,33,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3517 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3518 : PairBound 9 := { available := 392, camps := [{ cop := 4, region := 42, targets := 384 }], pairs := [(1,7),(1,8),(3,7),(3,8)], upper := (rows 7 98 388 41 81 48 456 392 392), lower := (rows 7 98 388 41 81 48 64 128 256), losses := [] }

theorem u3518 : Upper (D 9) (R 9) [6,96,384,33,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3518 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3519 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 3, region := 338, targets := 128 },{ cop := 4, region := 428, targets := 64 }], pairs := [(1,7),(2,5),(2,6),(4,5),(4,7)], upper := (rows 7 98 388 41 81 160 344 408 280), lower := (rows 7 98 388 41 81 160 64 128 256), losses := [] }

theorem u3519 : Upper (D 9) (R 9) [6,96,384,33,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3519 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3520 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 40, targets := 448 },{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(3,6),(3,7),(3,8)], upper := (rows 7 98 388 41 88 33 464 400 400), lower := (rows 7 98 388 41 88 33 64 128 256), losses := [] }

theorem u3520 : Upper (D 9) (R 9) [6,96,384,33,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3520 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3521 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 397, targets := 64 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6)], upper := (rows 7 98 388 41 88 48 449 385 385), lower := (rows 7 98 388 41 88 48 64 128 256), losses := [] }

theorem u3521 : Upper (D 9) (R 9) [6,96,384,33,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3521 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3522 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 3, region := 338, targets := 128 }], pairs := [(1,7),(2,5),(3,6),(4,5),(4,7)], upper := (rows 7 98 388 41 88 160 337 401 273), lower := (rows 7 98 388 41 88 160 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 16 164 0 128 256), good := (rows 47 34 420 41 24 160 0 160 256) }] }

theorem u3522 : Upper (D 9) (R 9) [6,96,384,33,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3522 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3523 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 40, targets := 448 },{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(3,6),(3,7),(3,8)], upper := (rows 7 98 388 41 145 40 336 464 336), lower := (rows 7 98 388 41 145 40 64 128 256), losses := [] }

theorem u3523 : Upper (D 9) (R 9) [6,96,384,33,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3523 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3524 : PairBound 9 := { available := 328, camps := [{ cop := 3, region := 454, targets := 1 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,0),(2,0),(2,5),(4,5)], upper := (rows 7 98 388 41 145 48 328 456 328), lower := (rows 7 98 388 41 145 48 64 128 256), losses := [] }

theorem u3524 : Upper (D 9) (R 9) [6,96,384,33,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3524 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3525 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 413, targets := 64 },{ cop := 5, region := 2, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6),(4,6)], upper := (rows 7 98 388 41 145 96 344 408 280), lower := (rows 7 98 388 41 145 96 64 128 256), losses := [] }

theorem u3525 : Upper (D 9) (R 9) [6,96,384,33,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3525 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3526 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 3, region := 210, targets := 256 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(1,8),(2,5),(4,5),(4,8)], upper := (rows 7 98 388 41 145 288 88 216 344), lower := (rows 7 98 388 41 145 288 64 128 256), losses := [] }

theorem u3526 : Upper (D 9) (R 9) [6,96,384,33,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3526 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3527 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 40, targets := 448 },{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(3,6),(3,7),(3,8)], upper := (rows 7 98 388 41 152 33 336 464 336), lower := (rows 7 98 388 41 152 33 64 128 256), losses := [] }

theorem u3527 : Upper (D 9) (R 9) [6,96,384,33,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3527 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3528 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 389, targets := 32 },{ cop := 3, region := 464, targets := 32 },{ cop := 3, region := 322, targets := 128 }], pairs := [(0,5),(1,7),(2,5),(4,5)], upper := (rows 7 98 388 41 152 48 321 449 321), lower := (rows 7 98 388 41 152 48 64 128 256), losses := [] }

theorem u3528 : Upper (D 9) (R 9) [6,96,384,33,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3528 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3529 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 413, targets := 64 },{ cop := 5, region := 2, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6),(4,6)], upper := (rows 7 98 388 41 152 96 337 401 273), lower := (rows 7 98 388 41 152 96 64 128 256), losses := [] }

theorem u3529 : Upper (D 9) (R 9) [6,96,384,33,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3529 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3530 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 3, region := 210, targets := 256 }], pairs := [(1,8),(2,5),(3,6),(4,5),(4,8)], upper := (rows 7 98 388 41 152 288 81 209 337), lower := (rows 7 98 388 41 152 288 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 16 292 0 128 256), good := (rows 47 34 420 41 152 288 0 128 288) }] }

theorem u3530 : Upper (D 9) (R 9) [6,96,384,33,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3530 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3531 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 40, targets := 448 },{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(3,6),(3,7),(3,8)], upper := (rows 7 98 388 41 208 33 344 408 280), lower := (rows 7 98 388 41 208 33 64 128 256), losses := [] }

theorem u3531 : Upper (D 9) (R 9) [6,96,384,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3531 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3532 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 40, targets := 448 },{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(3,6),(3,7),(3,8)], upper := (rows 7 98 388 41 208 40 337 401 273), lower := (rows 7 98 388 41 208 40 64 128 256), losses := [] }

theorem u3532 : Upper (D 9) (R 9) [6,96,384,33,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3532 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3533 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 397, targets := 64 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6)], upper := (rows 7 98 388 41 208 48 329 393 265), lower := (rows 7 98 388 41 208 48 64 128 256), losses := [] }

theorem u3533 : Upper (D 9) (R 9) [6,96,384,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3533 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3534 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 3, region := 210, targets := 256 }], pairs := [(1,8),(2,5),(3,6),(4,5),(4,8)], upper := (rows 7 98 388 41 208 288 89 153 281), lower := (rows 7 98 388 41 208 288 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 16 292 0 128 256), good := (rows 47 34 420 41 144 288 0 128 288) }] }

theorem u3534 : Upper (D 9) (R 9) [6,96,384,33,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3534 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3535 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 389, targets := 32 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,5),(0,7),(1,7),(2,5),(4,5)], upper := (rows 7 98 388 56 152 33 321 449 321), lower := (rows 7 98 388 56 152 33 64 128 256), losses := [{ target := 5, region := (rows 3 2 47 8 24 0 99 163 291), good := (rows 455 455 388 476 156 453 64 128 256) }] }

theorem u3535 : Upper (D 9) (R 9) [6,96,384,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3535 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3536 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 413, targets := 64 },{ cop := 5, region := 2, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6),(4,6)], upper := (rows 7 98 388 56 152 96 321 385 257), lower := (rows 7 98 388 56 152 96 64 128 256), losses := [] }

theorem u3536 : Upper (D 9) (R 9) [6,96,384,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3536 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3537 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 56, targets := 65 },{ cop := 1, region := 389, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(4,0),(4,6)], upper := (rows 7 98 388 56 152 288 65 193 321), lower := (rows 7 98 388 56 152 288 64 128 256), losses := [] }

theorem u3537 : Upper (D 9) (R 9) [6,96,384,48,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3537 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3538 : Route 9 := (fun mask => (mask,id))

def c3538 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3538 : Upper (D 9) (R 9) [6,96,384,48,192,1] 13 := by
  apply FastRouting.sound _ _ [6,96,384,48,192,1] 13 (by decide) (choices 1) [1,8,256] r3538 c3538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u631
  · exact u632
  · exact u633

def b3539 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 42, targets := 385 }], pairs := [(1,0),(1,7),(1,8),(3,0)], upper := (rows 7 98 388 56 208 40 321 385 257), lower := (rows 7 98 388 56 208 40 64 128 256), losses := [] }

theorem u3539 : Upper (D 9) (R 9) [6,96,384,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3539 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u3539
end Delivery.IrregularNine14.P09
