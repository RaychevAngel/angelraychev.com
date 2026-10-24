import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0244
import IrregularNine14P06C0245
import IrregularNine14P06C0246

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r32280 : Route 9 := (fun mask => (mask,id))

def c32280 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32280 : Upper (D 6) (R 6) [10,96,33,80,132] 13 := by
  apply FastRouting.sound _ _ [10,96,33,80,132] 13 (by decide) (choices 1) [1,2,4,256] r32280 c32280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14656
  · exact u14657
  · exact u14658
  · exact u14659

def r32281 : Route 9 := (fun mask => (mask,id))

def c32281 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32281 : Upper (D 6) (R 6) [10,96,33,80,384] 13 := by
  apply FastRouting.sound _ _ [10,96,33,80,384] 13 (by decide) (choices 1) [1,2,4] r32281 c32281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14660
  · exact u14661
  · exact u14662

def b32282 : PairBound 9 := { available := 340, camps := [{ cop := 2, region := 338, targets := 1 },{ cop := 4, region := 457, targets := 32 }], pairs := [(0,5),(1,0),(4,0)], upper := (rows 11 98 37 137 22 372 340 468 340), lower := (rows 11 98 37 137 22 32 64 128 256), losses := [] }

theorem u32282 : Upper (D 6) (R 6) [10,96,33,129,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32282 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32283 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 11 98 37 137 82 308 340 404 276), lower := (rows 11 98 37 137 82 32 64 128 256), losses := [] }

theorem u32283 : Upper (D 6) (R 6) [10,96,33,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32284 : Route 9 := (fun mask => (mask,id))

def c32284 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32284 : Upper (D 6) (R 6) [10,96,33,129,68] 13 := by
  apply FastRouting.sound _ _ [10,96,33,129,68] 13 (by decide) (choices 1) [2,4,16,256] r32284 c32284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14663
  · exact u14664
  · exact u14665
  · exact u14666

def r32285 : Route 9 := (fun mask => (mask,id))

def c32285 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32285 : Upper (D 6) (R 6) [10,96,33,129,258] 13 := by
  apply FastRouting.sound _ _ [10,96,33,129,258] 13 (by decide) (choices 1) [4,16,64] r32285 c32285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14667
  · exact u14668
  · exact u14669

def r32286 : Route 9 := (fun mask => (mask,id))

def c32286 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32286 : Upper (D 6) (R 6) [10,96,33,129,260] 13 := by
  apply FastRouting.sound _ _ [10,96,33,129,260] 13 (by decide) (choices 1) [2,4,16,64] r32286 c32286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14670
  · exact u14671
  · exact u14672
  · exact u14673

def r32287 : Route 9 := (fun mask => (mask,id))

def c32287 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32287 : Upper (D 6) (R 6) [10,96,33,129,320] 13 := by
  apply FastRouting.sound _ _ [10,96,33,129,320] 13 (by decide) (choices 1) [2,4,16] r32287 c32287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14674
  · exact u14675
  · exact u14676

def b32288 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 98 37 140 19 372 340 468 340), lower := (rows 11 98 37 140 19 32 64 128 256), losses := [] }

theorem u32288 : Upper (D 6) (R 6) [10,96,33,132,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32288 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32289 : PairBound 9 := { available := 338, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 98 37 140 21 370 338 466 338), lower := (rows 11 98 37 140 21 32 64 128 256), losses := [] }

theorem u32289 : Upper (D 6) (R 6) [10,96,33,132,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32289 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32290 : Route 9 := (fun mask => (mask,id))

def c32290 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u32290 : Upper (D 6) (R 6) [10,96,33,132,6] 13 := by
  apply FastRouting.sound _ _ [10,96,33,132,6] 13 (by decide) (choices 1) [1,16,64,256] r32290 c32290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14677
  · exact u14678
  · exact u14679
  · exact u14680

def r32291 : Route 9 := (fun mask => (mask,id))

def c32291 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32291 : Upper (D 6) (R 6) [10,96,33,132,65] 13 := by
  apply FastRouting.sound _ _ [10,96,33,132,65] 13 (by decide) (choices 1) [2,4,16,256] r32291 c32291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14681
  · exact u14682
  · exact u14683
  · exact u14684

def b32292 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 11 98 37 140 82 309 341 405 277), lower := (rows 11 98 37 140 82 32 64 128 256), losses := [] }

theorem u32292 : Upper (D 6) (R 6) [10,96,33,132,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32293 : Route 9 := (fun mask => (mask,id))

def c32293 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32293 : Upper (D 6) (R 6) [10,96,33,132,68] 13 := by
  apply FastRouting.sound _ _ [10,96,33,132,68] 13 (by decide) (choices 1) [1,2,16,256] r32293 c32293
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14685
  · exact u14686
  · exact u14687
  · exact u14688

def r32294 : Route 9 := (fun mask => (mask,id))

def c32294 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32294 : Upper (D 6) (R 6) [10,96,33,132,257] 13 := by
  apply FastRouting.sound _ _ [10,96,33,132,257] 13 (by decide) (choices 1) [2,4,16,64] r32294 c32294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14689
  · exact u14690
  · exact u14691
  · exact u14692

def r32295 : Route 9 := (fun mask => (mask,id))

def c32295 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32295 : Upper (D 6) (R 6) [10,96,33,132,258] 13 := by
  apply FastRouting.sound _ _ [10,96,33,132,258] 13 (by decide) (choices 1) [1,4,16,64] r32295 c32295
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14693
  · exact u14694
  · exact u14695
  · exact u14696

def r32296 : Route 9 := (fun mask => (mask,id))

def c32296 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32296 : Upper (D 6) (R 6) [10,96,33,132,260] 13 := by
  apply FastRouting.sound _ _ [10,96,33,132,260] 13 (by decide) (choices 1) [1,2,16,64] r32296 c32296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14697
  · exact u14698
  · exact u14699
  · exact u14700

def r32297 : Route 9 := (fun mask => (mask,id))

def c32297 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32297 : Upper (D 6) (R 6) [10,96,33,132,320] 13 := by
  apply FastRouting.sound _ _ [10,96,33,132,320] 13 (by decide) (choices 1) [1,2,4,16] r32297 c32297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14701
  · exact u14702
  · exact u14703
  · exact u14704

def b32298 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 98 37 152 19 356 324 452 324), lower := (rows 11 98 37 152 19 32 64 128 256), losses := [] }

theorem u32298 : Upper (D 6) (R 6) [10,96,33,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32299 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 98 37 152 21 358 326 454 326), lower := (rows 11 98 37 152 21 32 64 128 256), losses := [] }

theorem u32299 : Upper (D 6) (R 6) [10,96,33,144,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32300 : PairBound 9 := { available := 325, camps := [{ cop := 4, region := 457, targets := 32 },{ cop := 0, region := 356, targets := 2 }], pairs := [(0,5),(2,1),(3,5)], upper := (rows 11 98 37 152 22 357 325 453 325), lower := (rows 11 98 37 152 22 32 64 128 256), losses := [] }

theorem u32300 : Upper (D 6) (R 6) [10,96,33,144,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32300 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32301 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 292, targets := 64 },{ cop := 2, region := 322, targets := 1 }], pairs := [(1,0),(2,6),(3,6)], upper := (rows 11 98 37 152 81 294 326 390 262), lower := (rows 11 98 37 152 81 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 21 24 16 33 0 129 257), good := (rows 431 34 421 156 445 32 0 128 256) }] }

theorem u32301 : Upper (D 6) (R 6) [10,96,33,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32301 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32302 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 11 98 37 152 82 293 325 389 261), lower := (rows 11 98 37 152 82 32 64 128 256), losses := [] }

theorem u32302 : Upper (D 6) (R 6) [10,96,33,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32303 : Route 9 := (fun mask => (mask,id))

def c32303 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32303 : Upper (D 6) (R 6) [10,96,33,144,68] 13 := by
  apply FastRouting.sound _ _ [10,96,33,144,68] 13 (by decide) (choices 1) [1,2,4,256] r32303 c32303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14705
  · exact u14706
  · exact u14707
  · exact u14708

def r32304 : Route 9 := (fun mask => (mask,id))

def c32304 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32304 : Upper (D 6) (R 6) [10,96,33,144,257] 13 := by
  apply FastRouting.sound _ _ [10,96,33,144,257] 13 (by decide) (choices 1) [2,4,64] r32304 c32304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14709
  · exact u14710
  · exact u14711

def r32305 : Route 9 := (fun mask => (mask,id))

def c32305 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32305 : Upper (D 6) (R 6) [10,96,33,144,258] 13 := by
  apply FastRouting.sound _ _ [10,96,33,144,258] 13 (by decide) (choices 1) [1,4,64] r32305 c32305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14712
  · exact u14713
  · exact u14714

def r32306 : Route 9 := (fun mask => (mask,id))

def c32306 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32306 : Upper (D 6) (R 6) [10,96,33,144,260] 13 := by
  apply FastRouting.sound _ _ [10,96,33,144,260] 13 (by decide) (choices 1) [1,2,4,64] r32306 c32306
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14715
  · exact u14716
  · exact u14717
  · exact u14718

def r32307 : Route 9 := (fun mask => (mask,id))

def c32307 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32307 : Upper (D 6) (R 6) [10,96,33,144,320] 13 := by
  apply FastRouting.sound _ _ [10,96,33,144,320] 13 (by decide) (choices 1) [1,2,4] r32307 c32307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14719
  · exact u14720
  · exact u14721

def b32308 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 16, targets := 36 },{ cop := 0, region := 308, targets := 64 }], pairs := [(2,6),(4,2),(4,5)], upper := (rows 11 98 37 200 19 308 340 404 276), lower := (rows 11 98 37 200 19 32 64 128 256), losses := [] }

theorem u32308 : Upper (D 6) (R 6) [10,96,33,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32308 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32309 : PairBound 9 := { available := 278, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 98 37 200 21 310 342 406 278), lower := (rows 11 98 37 200 21 32 64 128 256), losses := [] }

theorem u32309 : Upper (D 6) (R 6) [10,96,33,192,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32309 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32310 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 308, targets := 64 },{ cop := 4, region := 457, targets := 32 }], pairs := [(0,5),(2,6),(4,6)], upper := (rows 11 98 37 200 22 309 341 405 277), lower := (rows 11 98 37 200 22 32 64 128 256), losses := [] }

theorem u32310 : Upper (D 6) (R 6) [10,96,33,192,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32310 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32311 : Route 9 := (fun mask => (mask,id))

def c32311 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32311 : Upper (D 6) (R 6) [10,96,33,192,257] 13 := by
  apply FastRouting.sound _ _ [10,96,33,192,257] 13 (by decide) (choices 1) [2,4,16] r32311 c32311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14722
  · exact u14723
  · exact u14724

def r32312 : Route 9 := (fun mask => (mask,id))

def c32312 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32312 : Upper (D 6) (R 6) [10,96,33,192,258] 13 := by
  apply FastRouting.sound _ _ [10,96,33,192,258] 13 (by decide) (choices 1) [1,4,16] r32312 c32312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14725
  · exact u14726
  · exact u14727

def r32313 : Route 9 := (fun mask => (mask,id))

def c32313 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32313 : Upper (D 6) (R 6) [10,96,33,192,260] 13 := by
  apply FastRouting.sound _ _ [10,96,33,192,260] 13 (by decide) (choices 1) [1,2,4,16] r32313 c32313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14728
  · exact u14729
  · exact u14730
  · exact u14731

def b32314 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 98 37 392 19 116 84 212 340), lower := (rows 11 98 37 392 19 32 64 128 256), losses := [] }

theorem u32314 : Upper (D 6) (R 6) [10,96,33,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32314 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32315 : PairBound 9 := { available := 86, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 98 37 392 21 118 86 214 342), lower := (rows 11 98 37 392 21 32 64 128 256), losses := [] }

theorem u32315 : Upper (D 6) (R 6) [10,96,33,384,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32316 : Route 9 := (fun mask => (mask,id))

def c32316 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32316 : Upper (D 6) (R 6) [10,96,33,384,6] 13 := by
  apply FastRouting.sound _ _ [10,96,33,384,6] 13 (by decide) (choices 1) [1,4,16,64] r32316 c32316
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14732
  · exact u14733
  · exact u14734
  · exact u14735

def r32317 : Route 9 := (fun mask => (mask,id))

def c32317 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32317 : Upper (D 6) (R 6) [10,96,33,384,65] 13 := by
  apply FastRouting.sound _ _ [10,96,33,384,65] 13 (by decide) (choices 1) [2,4,16] r32317 c32317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14736
  · exact u14737
  · exact u14738

def b32318 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 11 98 37 392 82 53 85 149 277), lower := (rows 11 98 37 392 82 32 64 128 256), losses := [] }

theorem u32318 : Upper (D 6) (R 6) [10,96,33,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32319 : Route 9 := (fun mask => (mask,id))

def c32319 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32319 : Upper (D 6) (R 6) [10,96,33,384,68] 13 := by
  apply FastRouting.sound _ _ [10,96,33,384,68] 13 (by decide) (choices 1) [1,2,4,16] r32319 c32319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14739
  · exact u14740
  · exact u14741
  · exact u14742

def b32320 : PairBound 9 := { available := 452, camps := [{ cop := 1, region := 29, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 52 13 19 484 452 452 452), lower := (rows 11 98 52 13 19 32 64 128 256), losses := [] }

theorem u32320 : Upper (D 6) (R 6) [10,96,48,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32320 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32321 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 29, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 52 13 21 482 450 450 450), lower := (rows 11 98 52 13 21 32 64 128 256), losses := [] }

theorem u32321 : Upper (D 6) (R 6) [10,96,48,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32322 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 29, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 52 13 22 481 449 449 449), lower := (rows 11 98 52 13 22 32 64 128 256), losses := [] }

theorem u32322 : Upper (D 6) (R 6) [10,96,48,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32322 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32323 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c32323 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u32323 : Upper (D 6) (R 6) [10,96,48,5,65] 13 := by
  apply FastRouting.sound _ _ [10,96,48,5,65] 13 (by decide) (choices 1) [2,4,128] r32323 c32323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14743
  · exact u14744
  · exact u14745

def b32324 : PairBound 9 := { available := 389, camps := [{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 52 13 82 421 453 389 389), lower := (rows 11 98 52 13 82 32 64 128 256), losses := [] }

theorem u32324 : Upper (D 6) (R 6) [10,96,48,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32324 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32325 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 20, targets := 1 },{ cop := 1, region := 20, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 98 52 13 84 419 451 387 387), lower := (rows 11 98 52 13 84 32 64 128 256), losses := [] }

theorem u32325 : Upper (D 6) (R 6) [10,96,48,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32325 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32326 : Route 9 := (fun mask => (mask,id))

def c32326 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32326 : Upper (D 6) (R 6) [10,96,48,5,129] 13 := by
  apply FastRouting.sound _ _ [10,96,48,5,129] 13 (by decide) (choices 1) [2,4,64,256] r32326 c32326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14746
  · exact u14747
  · exact u14748
  · exact u14749

def r32327 : Route 9 := (fun mask => (mask,id))

def c32327 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32327 : Upper (D 6) (R 6) [10,96,48,5,130] 13 := by
  apply FastRouting.sound _ _ [10,96,48,5,130] 13 (by decide) (choices 1) [1,4,64,256] r32327 c32327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14750
  · exact u14751
  · exact u14752
  · exact u14753

def b32328 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 355, targets := 4 }], pairs := [(0,2),(1,2),(4,5)], upper := (rows 11 98 52 13 148 355 323 451 323), lower := (rows 11 98 52 13 148 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 24 0 65 129 257), good := (rows 475 66 20 477 148 0 64 128 256) }] }

theorem u32328 : Upper (D 6) (R 6) [10,96,48,5,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32328 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32329 : Route 9 := (fun mask => (mask,id))

def c32329 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32329 : Upper (D 6) (R 6) [10,96,48,5,192] 13 := by
  apply FastRouting.sound _ _ [10,96,48,5,192] 13 (by decide) (choices 1) [1,2,4,256] r32329 c32329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14754
  · exact u14755
  · exact u14756
  · exact u14757

def r32330 : Route 9 := (fun mask => (mask,id))

def c32330 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32330 : Upper (D 6) (R 6) [10,96,48,5,384] 13 := by
  apply FastRouting.sound _ _ [10,96,48,5,384] 13 (by decide) (choices 1) [1,2,4,64] r32330 c32330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14758
  · exact u14759
  · exact u14760
  · exact u14761

def b32331 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 16, targets := 36 },{ cop := 0, region := 436, targets := 64 }], pairs := [(2,6),(4,2),(4,5)], upper := (rows 11 98 52 76 19 421 453 389 389), lower := (rows 11 98 52 76 19 32 64 128 256), losses := [] }

theorem u32331 : Upper (D 6) (R 6) [10,96,48,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32331 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32332 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 3, region := 419, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 98 52 76 21 419 451 387 387), lower := (rows 11 98 52 76 21 32 64 128 256), losses := [] }

theorem u32332 : Upper (D 6) (R 6) [10,96,48,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32332 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32333 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 28, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 98 52 76 22 417 449 385 385), lower := (rows 11 98 52 76 22 32 64 128 256), losses := [] }

theorem u32333 : Upper (D 6) (R 6) [10,96,48,68,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32334 : Route 9 := (fun mask => (mask,id))

def c32334 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32334 : Upper (D 6) (R 6) [10,96,48,68,129] 13 := by
  apply FastRouting.sound _ _ [10,96,48,68,129] 13 (by decide) (choices 1) [1,2,4,256] r32334 c32334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14762
  · exact u14763
  · exact u14764
  · exact u14765

def r32335 : Route 9 := (fun mask => (mask,id))

def c32335 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32335 : Upper (D 6) (R 6) [10,96,48,68,130] 13 := by
  apply FastRouting.sound _ _ [10,96,48,68,130] 13 (by decide) (choices 1) [1,4,256] r32335 c32335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14766
  · exact u14767
  · exact u14768

def b32336 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 3, region := 291, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 98 52 76 148 291 323 387 259), lower := (rows 11 98 52 76 148 32 64 128 256), losses := [] }

theorem u32336 : Upper (D 6) (R 6) [10,96,48,68,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32336 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32337 : Route 9 := (fun mask => (mask,id))

def c32337 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32337 : Upper (D 6) (R 6) [10,96,48,68,384] 13 := by
  apply FastRouting.sound _ _ [10,96,48,68,384] 13 (by decide) (choices 1) [1,2,4] r32337 c32337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14769
  · exact u14770
  · exact u14771

def b32338 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 98 52 137 19 356 324 452 324), lower := (rows 11 98 52 137 19 32 64 128 256), losses := [] }

theorem u32338 : Upper (D 6) (R 6) [10,96,48,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32339 : Route 9 := (fun mask => (mask,id))

def c32339 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32339 : Upper (D 6) (R 6) [10,96,48,129,5] 13 := by
  apply FastRouting.sound _ _ [10,96,48,129,5] 13 (by decide) (choices 1) [2,4,64,256] r32339 c32339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14772
  · exact u14773
  · exact u14774
  · exact u14775

#print axioms u32339
end Delivery.IrregularNine14.P06
