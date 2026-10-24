import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0304
import IrregularNine14P06C0305
import IrregularNine14P06C0306

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r34680 : Route 9 := (fun mask => (mask,id))

def c34680 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34680 : Upper (D 6) (R 6) [24,33,66,96,130] 13 := by
  apply FastRouting.sound _ _ [24,33,66,96,130] 13 (by decide) (choices 1) [1,4,256] r34680 c34680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18288
  · exact u18289
  · exact u18290

def r34681 : Route 9 := (fun mask => (mask,id))

def c34681 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34681 : Upper (D 6) (R 6) [24,33,66,96,132] 13 := by
  apply FastRouting.sound _ _ [24,33,66,96,132] 13 (by decide) (choices 1) [1,2,4,256] r34681 c34681
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18291
  · exact u18292
  · exact u18293
  · exact u18294

def r34682 : Route 9 := (fun mask => (mask,id))

def c34682 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34682 : Upper (D 6) (R 6) [24,33,66,96,384] 13 := by
  apply FastRouting.sound _ _ [24,33,66,96,384] 13 (by decide) (choices 1) [1,2,4] r34682 c34682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18295
  · exact u18296
  · exact u18297

def r34683 : Route 9 := (fun mask => (mask,id))

def c34683 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34683 : Upper (D 6) (R 6) [24,33,66,129,258] 13 := by
  apply FastRouting.sound _ _ [24,33,66,129,258] 13 (by decide) (choices 1) [4,64] r34683 c34683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18298
  · exact u18299

def r34684 : Route 9 := (fun mask => (mask,id))

def c34684 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34684 : Upper (D 6) (R 6) [24,33,66,129,260] 13 := by
  apply FastRouting.sound _ _ [24,33,66,129,260] 13 (by decide) (choices 1) [2,4,64] r34684 c34684
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18300
  · exact u18301
  · exact u18302

def b34685 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 340, targets := 1 },{ cop := 1, region := 68, targets := 32 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 25 35 70 137 304 102 70 198 326), lower := (rows 25 35 70 137 304 32 64 128 256), losses := [] }

theorem u34685 : Upper (D 6) (R 6) [24,33,66,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34686 : Route 9 := (fun mask => (mask,id))

def c34686 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34686 : Upper (D 6) (R 6) [24,33,66,129,320] 13 := by
  apply FastRouting.sound _ _ [24,33,66,129,320] 13 (by decide) (choices 1) [2,4] r34686 c34686
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18303
  · exact u18304

def r34687 : Route 9 := (fun mask => (mask,id))

def c34687 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34687 : Upper (D 6) (R 6) [24,33,66,130,260] 13 := by
  apply FastRouting.sound _ _ [24,33,66,130,260] 13 (by decide) (choices 1) [1,4,64] r34687 c34687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18305
  · exact u18306
  · exact u18307

def r34688 : Route 9 := (fun mask => (mask,id))

def c34688 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34688 : Upper (D 6) (R 6) [24,33,66,130,288] 13 := by
  apply FastRouting.sound _ _ [24,33,66,130,288] 13 (by decide) (choices 1) [1,4,64] r34688 c34688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18308
  · exact u18309
  · exact u18310

def r34689 : Route 9 := (fun mask => (mask,id))

def c34689 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34689 : Upper (D 6) (R 6) [24,33,66,130,320] 13 := by
  apply FastRouting.sound _ _ [24,33,66,130,320] 13 (by decide) (choices 1) [1,4] r34689 c34689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18311
  · exact u18312

def r34690 : Route 9 := (fun mask => (mask,id))

def c34690 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34690 : Upper (D 6) (R 6) [24,33,66,132,260] 13 := by
  apply FastRouting.sound _ _ [24,33,66,132,260] 13 (by decide) (choices 1) [1,2,64] r34690 c34690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18313
  · exact u18314
  · exact u18315

def r34691 : Route 9 := (fun mask => (mask,id))

def c34691 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34691 : Upper (D 6) (R 6) [24,33,66,132,288] 13 := by
  apply FastRouting.sound _ _ [24,33,66,132,288] 13 (by decide) (choices 1) [1,2,4,64] r34691 c34691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18316
  · exact u18317
  · exact u18318
  · exact u18319

def r34692 : Route 9 := (fun mask => (mask,id))

def c34692 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34692 : Upper (D 6) (R 6) [24,33,66,132,320] 13 := by
  apply FastRouting.sound _ _ [24,33,66,132,320] 13 (by decide) (choices 1) [1,2,4] r34692 c34692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18320
  · exact u18321
  · exact u18322

def r34693 : Route 9 := (fun mask => (mask,id))

def c34693 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34693 : Upper (D 6) (R 6) [24,33,66,160,320] 13 := by
  apply FastRouting.sound _ _ [24,33,66,160,320] 13 (by decide) (choices 1) [1,2,4] r34693 c34693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18323
  · exact u18324
  · exact u18325

def b34694 : PairBound 9 := { available := 452, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 35 100 11 22 484 452 452 452), lower := (rows 25 35 100 11 22 32 64 128 256), losses := [] }

theorem u34694 : Upper (D 6) (R 6) [24,33,96,3,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34694 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34695 : PairBound 9 := { available := 388, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 35 100 11 82 420 452 388 388), lower := (rows 25 35 100 11 82 32 64 128 256), losses := [] }

theorem u34695 : Upper (D 6) (R 6) [24,33,96,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34695 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34696 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 35 100 11 146 356 324 452 324), lower := (rows 25 35 100 11 146 32 64 128 256), losses := [] }

theorem u34696 : Upper (D 6) (R 6) [24,33,96,3,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34696 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34697 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 25 35 100 11 148 358 326 454 326), lower := (rows 25 35 100 11 148 32 64 128 256), losses := [] }

theorem u34697 : Upper (D 6) (R 6) [24,33,96,3,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34697 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34698 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 25 35 100 11 208 294 326 390 262), lower := (rows 25 35 100 11 208 32 64 128 256), losses := [] }

theorem u34698 : Upper (D 6) (R 6) [24,33,96,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34698 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34699 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 25 35 100 11 400 102 70 198 326), lower := (rows 25 35 100 11 400 32 64 128 256), losses := [] }

theorem u34699 : Upper (D 6) (R 6) [24,33,96,3,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34699 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34700 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 35 100 13 22 482 450 450 450), lower := (rows 25 35 100 13 22 32 64 128 256), losses := [] }

theorem u34700 : Upper (D 6) (R 6) [24,33,96,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34700 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34701 : PairBound 9 := { available := 390, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 418, targets := 64 }], pairs := [(1,6),(2,0),(4,0)], upper := (rows 25 35 100 13 82 422 454 390 390), lower := (rows 25 35 100 13 82 32 64 128 256), losses := [] }

theorem u34701 : Upper (D 6) (R 6) [24,33,96,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34702 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 25, targets := 34 }], pairs := [(0,1),(0,5),(3,1)], upper := (rows 25 35 100 13 84 418 450 386 386), lower := (rows 25 35 100 13 84 32 64 128 256), losses := [] }

theorem u34702 : Upper (D 6) (R 6) [24,33,96,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34702 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34703 : Route 9 := (fun mask => (mask,id))

def c34703 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u34703 : Upper (D 6) (R 6) [24,33,96,5,130] 13 := by
  apply FastRouting.sound _ _ [24,33,96,5,130] 13 (by decide) (choices 1) [2,4,64,256] r34703 c34703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18326
  · exact u18327
  · exact u18328
  · exact u18329

def b34704 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 9, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 35 100 13 148 354 322 450 322), lower := (rows 25 35 100 13 148 32 64 128 256), losses := [] }

theorem u34704 : Upper (D 6) (R 6) [24,33,96,5,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34704 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34705 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 290, targets := 64 }], pairs := [(1,6),(2,0),(4,0)], upper := (rows 25 35 100 13 208 294 326 390 262), lower := (rows 25 35 100 13 208 32 64 128 256), losses := [] }

theorem u34705 : Upper (D 6) (R 6) [24,33,96,5,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34705 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34706 : Route 9 := (fun mask => (mask,id))

def c34706 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34706 : Upper (D 6) (R 6) [24,33,96,5,384] 13 := by
  apply FastRouting.sound _ _ [24,33,96,5,384] 13 (by decide) (choices 1) [2,4,64] r34706 c34706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18330
  · exact u18331
  · exact u18332

def b34707 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 35 100 14 22 481 449 449 449), lower := (rows 25 35 100 14 22 32 64 128 256), losses := [] }

theorem u34707 : Upper (D 6) (R 6) [24,33,96,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34707 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34708 : PairBound 9 := { available := 390, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 3, region := 465, targets := 32 }], pairs := [(0,5),(2,0),(3,0)], upper := (rows 25 35 100 14 81 422 454 390 390), lower := (rows 25 35 100 14 81 32 64 128 256), losses := [] }

theorem u34708 : Upper (D 6) (R 6) [24,33,96,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34708 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34709 : PairBound 9 := { available := 389, camps := [{ cop := 3, region := 465, targets := 32 },{ cop := 0, region := 484, targets := 2 }], pairs := [(0,5),(2,1),(4,5)], upper := (rows 25 35 100 14 82 421 453 389 389), lower := (rows 25 35 100 14 82 32 64 128 256), losses := [] }

theorem u34709 : Upper (D 6) (R 6) [24,33,96,6,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34709 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34710 : PairBound 9 := { available := 387, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 25 35 100 14 84 419 451 387 387), lower := (rows 25 35 100 14 84 32 64 128 256), losses := [] }

theorem u34710 : Upper (D 6) (R 6) [24,33,96,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34711 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 332, targets := 1 },{ cop := 3, region := 465, targets := 32 }], pairs := [(0,5),(2,0),(3,0)], upper := (rows 25 35 100 14 145 358 326 454 326), lower := (rows 25 35 100 14 145 32 64 128 256), losses := [] }

theorem u34711 : Upper (D 6) (R 6) [24,33,96,6,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34711 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34712 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 465, targets := 32 },{ cop := 0, region := 356, targets := 2 }], pairs := [(0,5),(2,1),(4,5)], upper := (rows 25 35 100 14 146 357 325 453 325), lower := (rows 25 35 100 14 146 32 64 128 256), losses := [] }

theorem u34712 : Upper (D 6) (R 6) [24,33,96,6,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34712 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34713 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 465, targets := 32 },{ cop := 0, region := 354, targets := 4 }], pairs := [(0,5),(1,2),(4,5)], upper := (rows 25 35 100 14 148 355 323 451 323), lower := (rows 25 35 100 14 148 32 64 128 256), losses := [] }

theorem u34713 : Upper (D 6) (R 6) [24,33,96,6,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34713 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34714 : Route 9 := (fun mask => (mask,id))

def c34714 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34714 : Upper (D 6) (R 6) [24,33,96,6,192] 13 := by
  apply FastRouting.sound _ _ [24,33,96,6,192] 13 (by decide) (choices 1) [1,2,4,256] r34714 c34714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18333
  · exact u18334
  · exact u18335
  · exact u18336

def r34715 : Route 9 := (fun mask => (mask,id))

def c34715 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34715 : Upper (D 6) (R 6) [24,33,96,6,384] 13 := by
  apply FastRouting.sound _ _ [24,33,96,6,384] 13 (by decide) (choices 1) [1,2,4,64] r34715 c34715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18337
  · exact u18338
  · exact u18339
  · exact u18340

def r34716 : Route 9 := (fun mask => (mask,id))

def c34716 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34716 : Upper (D 6) (R 6) [24,33,96,65,130] 13 := by
  apply FastRouting.sound _ _ [24,33,96,65,130] 13 (by decide) (choices 1) [2,4,256] r34716 c34716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18341
  · exact u18342
  · exact u18343

def r34717 : Route 9 := (fun mask => (mask,id))

def c34717 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34717 : Upper (D 6) (R 6) [24,33,96,65,132] 13 := by
  apply FastRouting.sound _ _ [24,33,96,65,132] 13 (by decide) (choices 1) [2,4,256] r34717 c34717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18344
  · exact u18345
  · exact u18346

def r34718 : Route 9 := (fun mask => (mask,id))

def c34718 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34718 : Upper (D 6) (R 6) [24,33,96,65,384] 13 := by
  apply FastRouting.sound _ _ [24,33,96,65,384] 13 (by decide) (choices 1) [2,4] r34718 c34718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18347
  · exact u18348

def r34719 : Route 9 := (fun mask => (mask,id))

def c34719 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34719 : Upper (D 6) (R 6) [24,33,96,66,129] 13 := by
  apply FastRouting.sound _ _ [24,33,96,66,129] 13 (by decide) (choices 1) [2,4,256] r34719 c34719
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18349
  · exact u18350
  · exact u18351

def r34720 : Route 9 := (fun mask => (mask,id))

def c34720 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34720 : Upper (D 6) (R 6) [24,33,96,66,130] 13 := by
  apply FastRouting.sound _ _ [24,33,96,66,130] 13 (by decide) (choices 1) [1,4,256] r34720 c34720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18352
  · exact u18353
  · exact u18354

def r34721 : Route 9 := (fun mask => (mask,id))

def c34721 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34721 : Upper (D 6) (R 6) [24,33,96,66,132] 13 := by
  apply FastRouting.sound _ _ [24,33,96,66,132] 13 (by decide) (choices 1) [1,2,4,256] r34721 c34721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18355
  · exact u18356
  · exact u18357
  · exact u18358

def r34722 : Route 9 := (fun mask => (mask,id))

def c34722 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34722 : Upper (D 6) (R 6) [24,33,96,66,384] 13 := by
  apply FastRouting.sound _ _ [24,33,96,66,384] 13 (by decide) (choices 1) [1,2,4] r34722 c34722
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18359
  · exact u18360
  · exact u18361

def b34723 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 25 35 100 76 145 294 326 390 262), lower := (rows 25 35 100 76 145 32 64 128 256), losses := [] }

theorem u34723 : Upper (D 6) (R 6) [24,33,96,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34723 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34724 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 25 35 100 76 146 295 327 391 263), lower := (rows 25 35 100 76 146 32 64 128 256), losses := [] }

theorem u34724 : Upper (D 6) (R 6) [24,33,96,68,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34724 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34725 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 25 35 100 76 148 291 323 387 259), lower := (rows 25 35 100 76 148 32 64 128 256), losses := [] }

theorem u34725 : Upper (D 6) (R 6) [24,33,96,68,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34725 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34726 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 25 35 100 76 400 39 71 135 263), lower := (rows 25 35 100 76 400 32 64 128 256), losses := [] }

theorem u34726 : Upper (D 6) (R 6) [24,33,96,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34726 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34727 : Route 9 := (fun mask => (mask,id))

def c34727 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34727 : Upper (D 6) (R 6) [24,33,96,129,258] 13 := by
  apply FastRouting.sound _ _ [24,33,96,129,258] 13 (by decide) (choices 1) [2,4,64] r34727 c34727
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18362
  · exact u18363
  · exact u18364

def r34728 : Route 9 := (fun mask => (mask,id))

def c34728 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34728 : Upper (D 6) (R 6) [24,33,96,129,260] 13 := by
  apply FastRouting.sound _ _ [24,33,96,129,260] 13 (by decide) (choices 1) [2,4,64] r34728 c34728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18365
  · exact u18366
  · exact u18367

def r34729 : Route 9 := (fun mask => (mask,id))

def c34729 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34729 : Upper (D 6) (R 6) [24,33,96,129,320] 13 := by
  apply FastRouting.sound _ _ [24,33,96,129,320] 13 (by decide) (choices 1) [2,4] r34729 c34729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18368
  · exact u18369

def r34730 : Route 9 := (fun mask => (mask,id))

def c34730 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34730 : Upper (D 6) (R 6) [24,33,96,130,258] 13 := by
  apply FastRouting.sound _ _ [24,33,96,130,258] 13 (by decide) (choices 1) [1,4,64] r34730 c34730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18370
  · exact u18371
  · exact u18372

def r34731 : Route 9 := (fun mask => (mask,id))

def c34731 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34731 : Upper (D 6) (R 6) [24,33,96,130,260] 13 := by
  apply FastRouting.sound _ _ [24,33,96,130,260] 13 (by decide) (choices 1) [1,2,4,64] r34731 c34731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18373
  · exact u18374
  · exact u18375
  · exact u18376

def r34732 : Route 9 := (fun mask => (mask,id))

def c34732 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34732 : Upper (D 6) (R 6) [24,33,96,130,320] 13 := by
  apply FastRouting.sound _ _ [24,33,96,130,320] 13 (by decide) (choices 1) [1,2,4] r34732 c34732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18377
  · exact u18378
  · exact u18379

def r34733 : Route 9 := (fun mask => (mask,id))

def c34733 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34733 : Upper (D 6) (R 6) [24,33,96,132,260] 13 := by
  apply FastRouting.sound _ _ [24,33,96,132,260] 13 (by decide) (choices 1) [1,2,64] r34733 c34733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18380
  · exact u18381
  · exact u18382

def r34734 : Route 9 := (fun mask => (mask,id))

def c34734 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34734 : Upper (D 6) (R 6) [24,33,96,132,320] 13 := by
  apply FastRouting.sound _ _ [24,33,96,132,320] 13 (by decide) (choices 1) [1,2,4] r34734 c34734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18383
  · exact u18384
  · exact u18385

def b34735 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 17, targets := 96 }], pairs := [(0,5),(0,6),(4,5)], upper := (rows 25 35 133 14 22 352 352 480 352), lower := (rows 25 35 133 14 22 32 64 128 256), losses := [] }

theorem u34735 : Upper (D 6) (R 6) [24,33,129,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34735 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34736 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 25 35 133 14 50 356 324 452 324), lower := (rows 25 35 133 14 50 32 64 128 256), losses := [] }

theorem u34736 : Upper (D 6) (R 6) [24,33,129,6,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34736 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34737 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 35 133 14 52 354 322 450 322), lower := (rows 25 35 133 14 52 32 64 128 256), losses := [] }

theorem u34737 : Upper (D 6) (R 6) [24,33,129,6,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34737 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34738 : Route 9 := (fun mask => (mask,id))

def c34738 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u34738 : Upper (D 6) (R 6) [24,33,129,6,66] 13 := by
  apply FastRouting.sound _ _ [24,33,129,6,66] 13 (by decide) (choices 1) [4,64,256] r34738 c34738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18386
  · exact u18387
  · exact u18388

def r34739 : Route 9 := (fun mask => (mask,id))

def c34739 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u34739 : Upper (D 6) (R 6) [24,33,129,6,68] 13 := by
  apply FastRouting.sound _ _ [24,33,129,6,68] 13 (by decide) (choices 1) [2,64,256] r34739 c34739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18389
  · exact u18390
  · exact u18391

#print axioms u34739
end Delivery.IrregularNine14.P06
