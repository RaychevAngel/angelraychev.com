import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0260
import IrregularNine14P07C0261
import IrregularNine14P07C0262

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b32400 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 35 22 328 82 161 225 161 417), lower := (rows 13 35 22 328 82 32 64 128 256), losses := [] }

theorem u32400 : Upper (D 7) (R 7) [12,33,18,320,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32400 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32401 : Route 9 := (fun mask => (mask,id))

def c32401 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32401 : Upper (D 7) (R 7) [12,33,18,320,96] 13 := by
  apply FastRouting.sound _ _ [12,33,18,320,96] 13 (by decide) (choices 1) [1,2,128] r32401 c32401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15624
  · exact u15625
  · exact u15626

def r32402 : Route 9 := (fun mask => (mask,id))

def c32402 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32402 : Upper (D 7) (R 7) [12,33,18,320,129] 13 := by
  apply FastRouting.sound _ _ [12,33,18,320,129] 13 (by decide) (choices 1) [2,64,128] r32402 c32402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15627
  · exact u15628
  · exact u15629

def b32403 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 35 22 328 146 225 225 225 481), lower := (rows 13 35 22 328 146 32 64 128 256), losses := [] }

theorem u32403 : Upper (D 7) (R 7) [12,33,18,320,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32403 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32404 : Route 9 := (fun mask => (mask,id))

def c32404 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32404 : Upper (D 7) (R 7) [12,33,18,320,160] 13 := by
  apply FastRouting.sound _ _ [12,33,18,320,160] 13 (by decide) (choices 1) [1,2,64,128] r32404 c32404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15630
  · exact u15631
  · exact u15632
  · exact u15633

def r32405 : Route 9 := (fun mask => (mask,id))

def c32405 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32405 : Upper (D 7) (R 7) [12,33,18,320,192] 13 := by
  apply FastRouting.sound _ _ [12,33,18,320,192] 13 (by decide) (choices 1) [1,2,128] r32405 c32405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15634
  · exact u15635
  · exact u15636

def b32406 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 20, targets := 192 }], pairs := [(2,6),(2,7),(4,6),(4,7)], upper := (rows 13 35 52 74 19 480 448 448 448), lower := (rows 13 35 52 74 19 32 64 128 256), losses := [] }

theorem u32406 : Upper (D 7) (R 7) [12,33,48,66,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32406 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32407 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6),(3,5),(4,5)], upper := (rows 13 35 52 74 81 418 450 386 386), lower := (rows 13 35 52 74 81 32 64 128 256), losses := [] }

theorem u32407 : Upper (D 7) (R 7) [12,33,48,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32407 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32408 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 16, targets := 161 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,7)], upper := (rows 13 35 52 74 82 417 449 385 385), lower := (rows 13 35 52 74 82 32 64 128 256), losses := [] }

theorem u32408 : Upper (D 7) (R 7) [12,33,48,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32408 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32409 : Route 9 := (fun mask => (mask,id))

def c32409 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u32409 : Upper (D 7) (R 7) [12,33,48,66,129] 13 := by
  apply FastRouting.sound _ _ [12,33,48,66,129] 13 (by decide) (choices 1) [2,64,128,256] r32409 c32409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15637
  · exact u15638
  · exact u15639
  · exact u15640

def b32410 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(0,5),(2,1),(3,5),(4,5)], upper := (rows 13 35 52 74 146 481 449 449 449), lower := (rows 13 35 52 74 146 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 8 16 35 67 131 259), good := (rows 493 481 52 488 500 32 64 128 256) },{ target := 5, region := (rows 5 2 4 26 26 0 71 135 263), good := (rows 477 475 477 474 474 0 64 128 256) }] }

theorem u32410 : Upper (D 7) (R 7) [12,33,48,66,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32410 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32411 : Route 9 := (fun mask => (mask,id))

def c32411 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u32411 : Upper (D 7) (R 7) [12,33,48,66,192] 13 := by
  apply FastRouting.sound _ _ [12,33,48,66,192] 13 (by decide) (choices 1) [1,2,128,256] r32411 c32411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15641
  · exact u15642
  · exact u15643
  · exact u15644

def r32412 : Route 9 := (fun mask => (mask,id))

def c32412 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32412 : Upper (D 7) (R 7) [12,33,48,66,257] 13 := by
  apply FastRouting.sound _ _ [12,33,48,66,257] 13 (by decide) (choices 1) [2,64,128] r32412 c32412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15645
  · exact u15646
  · exact u15647

def b32413 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(0,5),(2,1),(3,5),(4,5)], upper := (rows 13 35 52 74 274 225 193 193 449), lower := (rows 13 35 52 74 274 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 8 16 35 67 131 259), good := (rows 493 481 52 488 500 32 64 128 256) },{ target := 5, region := (rows 5 2 4 26 26 0 71 135 263), good := (rows 477 475 477 474 474 0 64 128 256) }] }

theorem u32413 : Upper (D 7) (R 7) [12,33,48,66,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32414 : Route 9 := (fun mask => (mask,id))

def c32414 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32414 : Upper (D 7) (R 7) [12,33,48,66,320] 13 := by
  apply FastRouting.sound _ _ [12,33,48,66,320] 13 (by decide) (choices 1) [1,2,128] r32414 c32414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15648
  · exact u15649
  · exact u15650

def r32415 : Route 9 := (fun mask => (mask,id))

def c32415 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32415 : Upper (D 7) (R 7) [12,33,48,66,384] 13 := by
  apply FastRouting.sound _ _ [12,33,48,66,384] 13 (by decide) (choices 1) [1,2,64,128] r32415 c32415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15651
  · exact u15652
  · exact u15653
  · exact u15654

def b32416 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 20, targets := 192 }], pairs := [(2,6),(2,7),(4,6),(4,7)], upper := (rows 13 35 52 200 19 482 450 450 450), lower := (rows 13 35 52 200 19 32 64 128 256), losses := [] }

theorem u32416 : Upper (D 7) (R 7) [12,33,48,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32416 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32417 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6),(3,5),(4,5)], upper := (rows 13 35 52 200 81 418 450 386 386), lower := (rows 13 35 52 200 81 32 64 128 256), losses := [] }

theorem u32417 : Upper (D 7) (R 7) [12,33,48,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32417 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32418 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 0, region := 418, targets := 64 }], pairs := [(0,5),(1,6),(3,5),(4,5)], upper := (rows 13 35 52 200 82 419 451 387 387), lower := (rows 13 35 52 200 82 32 64 128 256), losses := [{ target := 5, region := (rows 5 2 4 26 18 0 66 130 258), good := (rows 13 475 29 200 474 0 64 128 256) }] }

theorem u32418 : Upper (D 7) (R 7) [12,33,48,192,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32418 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32419 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 13 35 52 200 208 291 323 387 259), lower := (rows 13 35 52 200 208 32 64 128 256), losses := [] }

theorem u32419 : Upper (D 7) (R 7) [12,33,48,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32419 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32420 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32420 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32420 : Upper (D 7) (R 7) [12,33,48,192,257] 13 := by
  apply FastRouting.sound _ _ [12,33,48,192,257] 13 (by decide) (choices 1) [2,64] r32420 c32420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15655
  · exact u15656

def r32421 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32421 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32421 : Upper (D 7) (R 7) [12,33,48,192,258] 13 := by
  apply FastRouting.sound _ _ [12,33,48,192,258] 13 (by decide) (choices 1) [1,2,64] r32421 c32421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15657
  · exact u15658
  · exact u15659

def r32422 : Route 9 := (fun mask => (mask,id))

def c32422 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32422 : Upper (D 7) (R 7) [12,33,48,192,320] 13 := by
  apply FastRouting.sound _ _ [12,33,48,192,320] 13 (by decide) (choices 1) [1,2,128] r32422 c32422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15660
  · exact u15661
  · exact u15662

def b32423 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 20, targets := 192 }], pairs := [(2,6),(2,7),(4,6),(4,7)], upper := (rows 13 35 52 266 19 224 192 192 448), lower := (rows 13 35 52 266 19 32 64 128 256), losses := [] }

theorem u32423 : Upper (D 7) (R 7) [12,33,48,258,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32423 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32424 : Route 9 := (fun mask => (mask,id))

def c32424 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32424 : Upper (D 7) (R 7) [12,33,48,258,65] 13 := by
  apply FastRouting.sound _ _ [12,33,48,258,65] 13 (by decide) (choices 1) [2,64,128] r32424 c32424
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15663
  · exact u15664
  · exact u15665

def b32425 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(0,5),(2,1),(3,5),(4,5)], upper := (rows 13 35 52 266 82 225 193 193 449), lower := (rows 13 35 52 266 82 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 8 16 35 67 131 259), good := (rows 493 481 52 488 500 32 64 128 256) },{ target := 5, region := (rows 5 2 4 26 26 0 71 135 263), good := (rows 477 475 477 474 474 0 64 128 256) }] }

theorem u32425 : Upper (D 7) (R 7) [12,33,48,258,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32425 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32426 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32426 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32426 : Upper (D 7) (R 7) [12,33,48,258,192] 13 := by
  apply FastRouting.sound _ _ [12,33,48,258,192] 13 (by decide) (choices 1) [1,2,64] r32426 c32426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15666
  · exact u15667
  · exact u15668

def b32427 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 20, targets := 192 }], pairs := [(2,6),(2,7),(4,6),(4,7)], upper := (rows 13 35 52 328 19 226 194 194 450), lower := (rows 13 35 52 328 19 32 64 128 256), losses := [] }

theorem u32427 : Upper (D 7) (R 7) [12,33,48,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32428 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 4, region := 166, targets := 64 }], pairs := [(1,6),(2,6),(3,5),(4,5)], upper := (rows 13 35 52 328 81 162 194 130 386), lower := (rows 13 35 52 328 81 32 64 128 256), losses := [] }

theorem u32428 : Upper (D 7) (R 7) [12,33,48,320,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32428 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32429 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 0, region := 162, targets := 64 }], pairs := [(0,5),(1,6),(3,5),(4,5)], upper := (rows 13 35 52 328 82 163 195 131 387), lower := (rows 13 35 52 328 82 32 64 128 256), losses := [{ target := 5, region := (rows 5 2 4 26 18 0 66 130 258), good := (rows 13 475 29 328 474 0 64 128 256) }] }

theorem u32429 : Upper (D 7) (R 7) [12,33,48,320,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32429 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32430 : Route 9 := (fun mask => (mask,id))

def c32430 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32430 : Upper (D 7) (R 7) [12,33,48,320,129] 13 := by
  apply FastRouting.sound _ _ [12,33,48,320,129] 13 (by decide) (choices 1) [2,64,128] r32430 c32430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15669
  · exact u15670
  · exact u15671

def r32431 : Route 9 := (fun mask => (mask,id))

def c32431 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32431 : Upper (D 7) (R 7) [12,33,48,320,130] 13 := by
  apply FastRouting.sound _ _ [12,33,48,320,130] 13 (by decide) (choices 1) [1,2,64,128] r32431 c32431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15672
  · exact u15673
  · exact u15674
  · exact u15675

def r32432 : Route 9 := (fun mask => (mask,id))

def c32432 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32432 : Upper (D 7) (R 7) [12,33,48,320,192] 13 := by
  apply FastRouting.sound _ _ [12,33,48,320,192] 13 (by decide) (choices 1) [1,2,128] r32432 c32432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15676
  · exact u15677
  · exact u15678

def b32433 : PairBound 9 := { available := 464, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 1, region := 472, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(3,5)], upper := (rows 13 35 69 138 50 496 464 464 464), lower := (rows 13 35 69 138 50 32 64 128 256), losses := [] }

theorem u32433 : Upper (D 7) (R 7) [12,33,65,130,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32433 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32434 : Route 9 := (fun mask => (mask,id))

def c32434 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u32434 : Upper (D 7) (R 7) [12,33,65,130,66] 13 := by
  apply FastRouting.sound _ _ [12,33,65,130,66] 13 (by decide) (choices 1) [16,128,256] r32434 c32434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15679
  · exact u15680
  · exact u15681

def r32435 : Route 9 := (fun mask => (mask,id))

def c32435 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u32435 : Upper (D 7) (R 7) [12,33,65,130,96] 13 := by
  apply FastRouting.sound _ _ [12,33,65,130,96] 13 (by decide) (choices 1) [2,16,128,256] r32435 c32435
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15682
  · exact u15683
  · exact u15684
  · exact u15685

def b32436 : PairBound 9 := { available := 368, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 3, region := 16, targets := 96 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 13 35 69 138 146 368 368 496 368), lower := (rows 13 35 69 138 146 32 64 128 256), losses := [] }

theorem u32436 : Upper (D 7) (R 7) [12,33,65,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32436 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32437 : Route 9 := (fun mask => (mask,id))

def c32437 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u32437 : Upper (D 7) (R 7) [12,33,65,130,160] 13 := by
  apply FastRouting.sound _ _ [12,33,65,130,160] 13 (by decide) (choices 1) [2,16,64,256] r32437 c32437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15686
  · exact u15687
  · exact u15688
  · exact u15689

def r32438 : Route 9 := (fun mask => (mask,id))

def c32438 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32438 : Upper (D 7) (R 7) [12,33,65,130,192] 13 := by
  apply FastRouting.sound _ _ [12,33,65,130,192] 13 (by decide) (choices 1) [2,16,256] r32438 c32438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15690
  · exact u15691
  · exact u15692

def r32439 : Route 9 := (fun mask => (mask,id))

def c32439 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32439 : Upper (D 7) (R 7) [12,33,65,130,258] 13 := by
  apply FastRouting.sound _ _ [12,33,65,130,258] 13 (by decide) (choices 1) [16,64,128] r32439 c32439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15693
  · exact u15694
  · exact u15695

def r32440 : Route 9 := (fun mask => (mask,id))

def c32440 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32440 : Upper (D 7) (R 7) [12,33,65,130,288] 13 := by
  apply FastRouting.sound _ _ [12,33,65,130,288] 13 (by decide) (choices 1) [2,16,64,128] r32440 c32440
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15696
  · exact u15697
  · exact u15698
  · exact u15699

def r32441 : Route 9 := (fun mask => (mask,id))

def c32441 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32441 : Upper (D 7) (R 7) [12,33,65,130,320] 13 := by
  apply FastRouting.sound _ _ [12,33,65,130,320] 13 (by decide) (choices 1) [2,16,128] r32441 c32441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15700
  · exact u15701
  · exact u15702

def r32442 : Route 9 := (fun mask => (mask,id))

def c32442 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32442 : Upper (D 7) (R 7) [12,33,65,130,384] 13 := by
  apply FastRouting.sound _ _ [12,33,65,130,384] 13 (by decide) (choices 1) [2,16,64] r32442 c32442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15703
  · exact u15704
  · exact u15705

def b32443 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 1, region := 472, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(3,5)], upper := (rows 13 35 69 152 50 482 450 450 450), lower := (rows 13 35 69 152 50 32 64 128 256), losses := [] }

theorem u32443 : Upper (D 7) (R 7) [12,33,65,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32443 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32444 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 0, region := 418, targets := 64 },{ cop := 4, region := 424, targets := 64 }], pairs := [(1,6),(3,0),(3,6),(4,0)], upper := (rows 13 35 69 152 82 418 482 418 418), lower := (rows 13 35 69 152 82 32 64 128 256), losses := [] }

theorem u32444 : Upper (D 7) (R 7) [12,33,65,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32444 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32445 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 0, region := 418, targets := 64 },{ cop := 1, region := 452, targets := 32 }], pairs := [(1,6),(2,5),(3,0),(4,0)], upper := (rows 13 35 69 152 112 418 450 386 386), lower := (rows 13 35 69 152 112 32 64 128 256), losses := [] }

theorem u32445 : Upper (D 7) (R 7) [12,33,65,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32445 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32446 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 359, targets := 128 },{ cop := 4, region := 8, targets := 2 }], pairs := [(0,7),(1,7),(2,7),(3,1)], upper := (rows 13 35 69 152 146 354 354 482 354), lower := (rows 13 35 69 152 146 32 64 128 256), losses := [] }

theorem u32446 : Upper (D 7) (R 7) [12,33,65,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32446 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32447 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 13 35 69 152 176 354 322 450 322), lower := (rows 13 35 69 152 176 32 64 128 256), losses := [] }

theorem u32447 : Upper (D 7) (R 7) [12,33,65,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32447 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32448 : PairBound 9 := { available := 290, camps := [{ cop := 4, region := 13, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 35 69 152 208 290 354 418 290), lower := (rows 13 35 69 152 208 32 64 128 256), losses := [] }

theorem u32448 : Upper (D 7) (R 7) [12,33,65,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32448 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32449 : Route 9 := (fun mask => (mask,id))

def c32449 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32449 : Upper (D 7) (R 7) [12,33,65,144,258] 13 := by
  apply FastRouting.sound _ _ [12,33,65,144,258] 13 (by decide) (choices 1) [2,64,128] r32449 c32449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15706
  · exact u15707
  · exact u15708

def r32450 : Route 9 := (fun mask => (mask,id))

def c32450 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32450 : Upper (D 7) (R 7) [12,33,65,144,288] 13 := by
  apply FastRouting.sound _ _ [12,33,65,144,288] 13 (by decide) (choices 1) [2,64,128] r32450 c32450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15709
  · exact u15710
  · exact u15711

def r32451 : Route 9 := (fun mask => (mask,id))

def c32451 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32451 : Upper (D 7) (R 7) [12,33,65,144,320] 13 := by
  apply FastRouting.sound _ _ [12,33,65,144,320] 13 (by decide) (choices 1) [2,128] r32451 c32451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15712
  · exact u15713

def b32452 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 13 35 69 152 400 98 98 226 354), lower := (rows 13 35 69 152 400 32 64 128 256), losses := [] }

theorem u32452 : Upper (D 7) (R 7) [12,33,65,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32452 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32453 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 1, region := 472, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(3,5)], upper := (rows 13 35 69 266 50 240 208 208 464), lower := (rows 13 35 69 266 50 32 64 128 256), losses := [] }

theorem u32453 : Upper (D 7) (R 7) [12,33,65,258,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32453 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32454 : Route 9 := (fun mask => (mask,id))

def c32454 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32454 : Upper (D 7) (R 7) [12,33,65,258,66] 13 := by
  apply FastRouting.sound _ _ [12,33,65,258,66] 13 (by decide) (choices 1) [16,128] r32454 c32454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15714
  · exact u15715

def r32455 : Route 9 := (fun mask => (mask,id))

def c32455 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32455 : Upper (D 7) (R 7) [12,33,65,258,96] 13 := by
  apply FastRouting.sound _ _ [12,33,65,258,96] 13 (by decide) (choices 1) [2,16,128] r32455 c32455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15716
  · exact u15717
  · exact u15718

def r32456 : Route 9 := (fun mask => (mask,id))

def c32456 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32456 : Upper (D 7) (R 7) [12,33,65,258,130] 13 := by
  apply FastRouting.sound _ _ [12,33,65,258,130] 13 (by decide) (choices 1) [16,64,128] r32456 c32456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15719
  · exact u15720
  · exact u15721

def r32457 : Route 9 := (fun mask => (mask,id))

def c32457 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32457 : Upper (D 7) (R 7) [12,33,65,258,160] 13 := by
  apply FastRouting.sound _ _ [12,33,65,258,160] 13 (by decide) (choices 1) [2,16,64,128] r32457 c32457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15722
  · exact u15723
  · exact u15724
  · exact u15725

def r32458 : Route 9 := (fun mask => (mask,id))

def c32458 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32458 : Upper (D 7) (R 7) [12,33,65,258,192] 13 := by
  apply FastRouting.sound _ _ [12,33,65,258,192] 13 (by decide) (choices 1) [2,16,128] r32458 c32458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15726
  · exact u15727
  · exact u15728

def b32459 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 1, region := 472, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(3,5)], upper := (rows 13 35 69 280 50 226 194 194 450), lower := (rows 13 35 69 280 50 32 64 128 256), losses := [] }

theorem u32459 : Upper (D 7) (R 7) [12,33,65,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32459 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u32459
end Delivery.IrregularNine14.P07
