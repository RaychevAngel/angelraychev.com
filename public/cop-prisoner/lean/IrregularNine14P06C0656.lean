import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0428
import IrregularNine14P06C0429

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b39360 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 82 133 328 49 38 70 134 262), lower := (rows 41 82 133 328 49 32 64 128 256), losses := [] }

theorem u39360 : Upper (D 6) (R 6) [40,80,129,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39360 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39361 : Route 9 := (fun mask => (mask,id))

def c39361 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39361 : Upper (D 6) (R 6) [40,80,129,320,34] 13 := by
  apply FastRouting.sound _ _ [40,80,129,320,34] 13 (by decide) (choices 1) [1,2,4] r39361 c39361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25684
  · exact u25685
  · exact u25686

def r39362 : Route 9 := (fun mask => (mask,id))

def c39362 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39362 : Upper (D 6) (R 6) [40,80,129,320,36] 13 := by
  apply FastRouting.sound _ _ [40,80,129,320,36] 13 (by decide) (choices 1) [1,2,4] r39362 c39362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25687
  · exact u25688
  · exact u25689

def b39363 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 41 82 164 11 19 356 324 452 324), lower := (rows 41 82 164 11 19 32 64 128 256), losses := [] }

theorem u39363 : Upper (D 6) (R 6) [40,80,160,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39363 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39364 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 322, targets := 32 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 41 82 164 11 21 358 326 454 326), lower := (rows 41 82 164 11 21 32 64 128 256), losses := [] }

theorem u39364 : Upper (D 6) (R 6) [40,80,160,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39364 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39365 : Route 9 := (fun mask => (mask,id))

def c39365 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u39365 : Upper (D 6) (R 6) [40,80,160,3,6] 13 := by
  apply FastRouting.sound _ _ [40,80,160,3,6] 13 (by decide) (choices 1) [1,4,64,256] r39365 c39365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25690
  · exact u25691
  · exact u25692
  · exact u25693

def b39366 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 10, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 41 82 164 11 81 294 326 390 262), lower := (rows 41 82 164 11 81 32 64 128 256), losses := [] }

theorem u39366 : Upper (D 6) (R 6) [40,80,160,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39366 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39367 : PairBound 9 := { available := 261, camps := [{ cop := 6, region := 18, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 41 82 164 11 82 293 325 389 261), lower := (rows 41 82 164 11 82 32 64 128 256), losses := [] }

theorem u39367 : Upper (D 6) (R 6) [40,80,160,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39367 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39368 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 164 11 84 295 327 391 263), lower := (rows 41 82 164 11 84 32 64 128 256), losses := [] }

theorem u39368 : Upper (D 6) (R 6) [40,80,160,3,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39368 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39369 : Route 9 := (fun mask => (mask,id))

def c39369 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39369 : Upper (D 6) (R 6) [40,80,160,3,257] 13 := by
  apply FastRouting.sound _ _ [40,80,160,3,257] 13 (by decide) (choices 1) [2,4,64] r39369 c39369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25694
  · exact u25695
  · exact u25696

def r39370 : Route 9 := (fun mask => (mask,id))

def c39370 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39370 : Upper (D 6) (R 6) [40,80,160,3,258] 13 := by
  apply FastRouting.sound _ _ [40,80,160,3,258] 13 (by decide) (choices 1) [1,4,64] r39370 c39370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25697
  · exact u25698
  · exact u25699

def r39371 : Route 9 := (fun mask => (mask,id))

def c39371 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39371 : Upper (D 6) (R 6) [40,80,160,3,260] 13 := by
  apply FastRouting.sound _ _ [40,80,160,3,260] 13 (by decide) (choices 1) [1,2,4,64] r39371 c39371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25700
  · exact u25701
  · exact u25702
  · exact u25703

def b39372 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 173, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 164 11 336 39 71 135 263), lower := (rows 41 82 164 11 336 32 64 128 256), losses := [] }

theorem u39372 : Upper (D 6) (R 6) [40,80,160,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39373 : Route 9 := (fun mask => (mask,id))

def c39373 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u39373 : Upper (D 6) (R 6) [40,80,160,6,3] 13 := by
  apply FastRouting.sound _ _ [40,80,160,6,3] 13 (by decide) (choices 1) [1,4,64,256] r39373 c39373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25704
  · exact u25705
  · exact u25706
  · exact u25707

def b39374 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 330, targets := 32 },{ cop := 3, region := 353, targets := 4 }], pairs := [(0,2),(1,5),(3,5)], upper := (rows 41 82 164 14 21 355 323 451 323), lower := (rows 41 82 164 14 21 32 64 128 256), losses := [] }

theorem u39374 : Upper (D 6) (R 6) [40,80,160,6,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39374 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39375 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 82 164 14 22 353 321 449 321), lower := (rows 41 82 164 14 22 32 64 128 256), losses := [] }

theorem u39375 : Upper (D 6) (R 6) [40,80,160,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39375 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39376 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 164 14 81 295 327 391 263), lower := (rows 41 82 164 14 81 32 64 128 256), losses := [] }

theorem u39376 : Upper (D 6) (R 6) [40,80,160,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39376 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39377 : PairBound 9 := { available := 261, camps := [{ cop := 6, region := 18, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 41 82 164 14 82 293 325 389 261), lower := (rows 41 82 164 14 82 32 64 128 256), losses := [] }

theorem u39377 : Upper (D 6) (R 6) [40,80,160,6,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39377 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39378 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 10, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 41 82 164 14 84 291 323 387 259), lower := (rows 41 82 164 14 84 32 64 128 256), losses := [] }

theorem u39378 : Upper (D 6) (R 6) [40,80,160,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39378 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39379 : Route 9 := (fun mask => (mask,id))

def c39379 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39379 : Upper (D 6) (R 6) [40,80,160,6,257] 13 := by
  apply FastRouting.sound _ _ [40,80,160,6,257] 13 (by decide) (choices 1) [1,2,4,64] r39379 c39379
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25708
  · exact u25709
  · exact u25710
  · exact u25711

def r39380 : Route 9 := (fun mask => (mask,id))

def c39380 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39380 : Upper (D 6) (R 6) [40,80,160,6,258] 13 := by
  apply FastRouting.sound _ _ [40,80,160,6,258] 13 (by decide) (choices 1) [1,4,64] r39380 c39380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25712
  · exact u25713
  · exact u25714

def r39381 : Route 9 := (fun mask => (mask,id))

def c39381 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39381 : Upper (D 6) (R 6) [40,80,160,6,260] 13 := by
  apply FastRouting.sound _ _ [40,80,160,6,260] 13 (by decide) (choices 1) [1,2,64] r39381 c39381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25715
  · exact u25716
  · exact u25717

def b39382 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 173, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 164 14 336 39 71 135 263), lower := (rows 41 82 164 14 336 32 64 128 256), losses := [] }

theorem u39382 : Upper (D 6) (R 6) [40,80,160,6,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39382 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39383 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 18, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 41 82 164 73 19 294 326 390 262), lower := (rows 41 82 164 73 19 32 64 128 256), losses := [] }

theorem u39383 : Upper (D 6) (R 6) [40,80,160,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39383 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39384 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 322, targets := 32 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 41 82 164 73 21 294 326 390 262), lower := (rows 41 82 164 73 21 32 64 128 256), losses := [] }

theorem u39384 : Upper (D 6) (R 6) [40,80,160,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39384 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39385 : Route 9 := (fun mask => (mask,id))

def c39385 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39385 : Upper (D 6) (R 6) [40,80,160,65,6] 13 := by
  apply FastRouting.sound _ _ [40,80,160,65,6] 13 (by decide) (choices 1) [1,2,4,256] r39385 c39385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25718
  · exact u25719
  · exact u25720
  · exact u25721

def b39386 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 1, region := 164, targets := 64 }], pairs := [(1,0),(2,0),(2,6)], upper := (rows 41 82 164 73 273 38 70 134 262), lower := (rows 41 82 164 73 273 32 64 128 256), losses := [] }

theorem u39386 : Upper (D 6) (R 6) [40,80,160,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39387 : Route 9 := (fun mask => (mask,id))

def c39387 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39387 : Upper (D 6) (R 6) [40,80,160,65,258] 13 := by
  apply FastRouting.sound _ _ [40,80,160,65,258] 13 (by decide) (choices 1) [1,2,4] r39387 c39387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25722
  · exact u25723
  · exact u25724

def r39388 : Route 9 := (fun mask => (mask,id))

def c39388 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39388 : Upper (D 6) (R 6) [40,80,160,65,260] 13 := by
  apply FastRouting.sound _ _ [40,80,160,65,260] 13 (by decide) (choices 1) [1,2,4] r39388 c39388
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25725
  · exact u25726
  · exact u25727

def r39389 : Route 9 := (fun mask => (mask,id))

def c39389 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39389 : Upper (D 6) (R 6) [40,80,160,68,3] 13 := by
  apply FastRouting.sound _ _ [40,80,160,68,3] 13 (by decide) (choices 1) [1,2,4,256] r39389 c39389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25728
  · exact u25729
  · exact u25730
  · exact u25731

def b39390 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 330, targets := 32 },{ cop := 4, region := 322, targets := 4 }], pairs := [(1,2),(1,5),(3,5)], upper := (rows 41 82 164 76 21 291 323 387 259), lower := (rows 41 82 164 76 21 32 64 128 256), losses := [] }

theorem u39390 : Upper (D 6) (R 6) [40,80,160,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39390 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39391 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 18, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 41 82 164 76 22 291 323 387 259), lower := (rows 41 82 164 76 22 32 64 128 256), losses := [] }

theorem u39391 : Upper (D 6) (R 6) [40,80,160,68,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39391 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39392 : Route 9 := (fun mask => (mask,id))

def c39392 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39392 : Upper (D 6) (R 6) [40,80,160,68,257] 13 := by
  apply FastRouting.sound _ _ [40,80,160,68,257] 13 (by decide) (choices 1) [1,2,4] r39392 c39392
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25732
  · exact u25733
  · exact u25734

def r39393 : Route 9 := (fun mask => (mask,id))

def c39393 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39393 : Upper (D 6) (R 6) [40,80,160,68,258] 13 := by
  apply FastRouting.sound _ _ [40,80,160,68,258] 13 (by decide) (choices 1) [1,2,4] r39393 c39393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25735
  · exact u25736
  · exact u25737

def r39394 : Route 9 := (fun mask => (mask,id))

def c39394 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39394 : Upper (D 6) (R 6) [40,80,160,68,260] 13 := by
  apply FastRouting.sound _ _ [40,80,160,68,260] 13 (by decide) (choices 1) [1,2] r39394 c39394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25738
  · exact u25739

def r39395 : Route 9 := (fun mask => (mask,id))

def c39395 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39395 : Upper (D 6) (R 6) [40,80,160,257,3] 13 := by
  apply FastRouting.sound _ _ [40,80,160,257,3] 13 (by decide) (choices 1) [2,4,64] r39395 c39395
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25740
  · exact u25741
  · exact u25742

def b39396 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 41 82 164 265 21 102 70 198 326), lower := (rows 41 82 164 265 21 32 64 128 256), losses := [] }

theorem u39396 : Upper (D 6) (R 6) [40,80,160,257,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39397 : Route 9 := (fun mask => (mask,id))

def c39397 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39397 : Upper (D 6) (R 6) [40,80,160,257,6] 13 := by
  apply FastRouting.sound _ _ [40,80,160,257,6] 13 (by decide) (choices 1) [1,2,4,64] r39397 c39397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25743
  · exact u25744
  · exact u25745
  · exact u25746

def b39398 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 164 265 81 38 70 134 262), lower := (rows 41 82 164 265 81 32 64 128 256), losses := [] }

theorem u39398 : Upper (D 6) (R 6) [40,80,160,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39398 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39399 : PairBound 9 := { available := 7, camps := [{ cop := 6, region := 18, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 41 82 164 265 82 39 71 135 263), lower := (rows 41 82 164 265 82 32 64 128 256), losses := [] }

theorem u39399 : Upper (D 6) (R 6) [40,80,160,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39399 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39400 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 164 265 84 39 71 135 263), lower := (rows 41 82 164 265 84 32 64 128 256), losses := [] }

theorem u39400 : Upper (D 6) (R 6) [40,80,160,257,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39400 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39401 : Route 9 := (fun mask => (mask,id))

def c39401 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39401 : Upper (D 6) (R 6) [40,80,160,258,3] 13 := by
  apply FastRouting.sound _ _ [40,80,160,258,3] 13 (by decide) (choices 1) [1,4,64] r39401 c39401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25747
  · exact u25748
  · exact u25749

def r39402 : Route 9 := (fun mask => (mask,id))

def c39402 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39402 : Upper (D 6) (R 6) [40,80,160,258,5] 13 := by
  apply FastRouting.sound _ _ [40,80,160,258,5] 13 (by decide) (choices 1) [1,2,4,64] r39402 c39402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25750
  · exact u25751
  · exact u25752
  · exact u25753

def r39403 : Route 9 := (fun mask => (mask,id))

def c39403 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39403 : Upper (D 6) (R 6) [40,80,160,258,6] 13 := by
  apply FastRouting.sound _ _ [40,80,160,258,6] 13 (by decide) (choices 1) [1,4,64] r39403 c39403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25754
  · exact u25755
  · exact u25756

def b39404 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 164 266 81 39 71 135 263), lower := (rows 41 82 164 266 81 32 64 128 256), losses := [] }

theorem u39404 : Upper (D 6) (R 6) [40,80,160,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39404 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39405 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 18, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 41 82 164 266 82 37 69 133 261), lower := (rows 41 82 164 266 82 32 64 128 256), losses := [] }

theorem u39405 : Upper (D 6) (R 6) [40,80,160,258,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39405 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39406 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 164 266 84 39 71 135 263), lower := (rows 41 82 164 266 84 32 64 128 256), losses := [] }

theorem u39406 : Upper (D 6) (R 6) [40,80,160,258,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39406 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39407 : Route 9 := (fun mask => (mask,id))

def c39407 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39407 : Upper (D 6) (R 6) [40,80,160,260,3] 13 := by
  apply FastRouting.sound _ _ [40,80,160,260,3] 13 (by decide) (choices 1) [1,2,4,64] r39407 c39407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25757
  · exact u25758
  · exact u25759
  · exact u25760

def b39408 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 330, targets := 32 },{ cop := 4, region := 66, targets := 4 }], pairs := [(1,2),(1,5),(3,5)], upper := (rows 41 82 164 268 21 99 67 195 323), lower := (rows 41 82 164 268 21 32 64 128 256), losses := [] }

theorem u39408 : Upper (D 6) (R 6) [40,80,160,260,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39409 : Route 9 := (fun mask => (mask,id))

def c39409 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39409 : Upper (D 6) (R 6) [40,80,160,260,6] 13 := by
  apply FastRouting.sound _ _ [40,80,160,260,6] 13 (by decide) (choices 1) [1,2,64] r39409 c39409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25761
  · exact u25762
  · exact u25763

def b39410 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 164 268 81 39 71 135 263), lower := (rows 41 82 164 268 81 32 64 128 256), losses := [] }

theorem u39410 : Upper (D 6) (R 6) [40,80,160,260,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39410 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39411 : PairBound 9 := { available := 7, camps := [{ cop := 6, region := 18, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 41 82 164 268 82 39 71 135 263), lower := (rows 41 82 164 268 82 32 64 128 256), losses := [] }

theorem u39411 : Upper (D 6) (R 6) [40,80,160,260,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39412 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 164 268 84 35 67 131 259), lower := (rows 41 82 164 268 84 32 64 128 256), losses := [] }

theorem u39412 : Upper (D 6) (R 6) [40,80,160,260,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39412 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39413 : Route 9 := (fun mask => (mask,id))

def c39413 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39413 : Upper (D 6) (R 6) [40,80,160,320,3] 13 := by
  apply FastRouting.sound _ _ [40,80,160,320,3] 13 (by decide) (choices 1) [1,2,4] r39413 c39413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25764
  · exact u25765
  · exact u25766

def r39414 : Route 9 := (fun mask => (mask,id))

def c39414 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39414 : Upper (D 6) (R 6) [40,80,160,320,5] 13 := by
  apply FastRouting.sound _ _ [40,80,160,320,5] 13 (by decide) (choices 1) [1,2,4] r39414 c39414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25767
  · exact u25768
  · exact u25769

def r39415 : Route 9 := (fun mask => (mask,id))

def c39415 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39415 : Upper (D 6) (R 6) [40,80,160,320,6] 13 := by
  apply FastRouting.sound _ _ [40,80,160,320,6] 13 (by decide) (choices 1) [1,2,4] r39415 c39415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25770
  · exact u25771
  · exact u25772

def b39416 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 41 82 388 11 19 100 100 228 356), lower := (rows 41 82 388 11 19 32 64 128 256), losses := [] }

theorem u39416 : Upper (D 6) (R 6) [40,80,384,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39416 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39417 : Route 9 := (fun mask => (mask,id))

def c39417 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39417 : Upper (D 6) (R 6) [40,80,384,3,5] 13 := by
  apply FastRouting.sound _ _ [40,80,384,3,5] 13 (by decide) (choices 1) [2,4,64] r39417 c39417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25773
  · exact u25774
  · exact u25775

def r39418 : Route 9 := (fun mask => (mask,id))

def c39418 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39418 : Upper (D 6) (R 6) [40,80,384,3,6] 13 := by
  apply FastRouting.sound _ _ [40,80,384,3,6] 13 (by decide) (choices 1) [1,4,64] r39418 c39418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25776
  · exact u25777
  · exact u25778

def b39419 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 82 388 11 49 102 70 198 326), lower := (rows 41 82 388 11 49 32 64 128 256), losses := [] }

theorem u39419 : Upper (D 6) (R 6) [40,80,384,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39419 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u39419
end Delivery.IrregularNine14.P06
