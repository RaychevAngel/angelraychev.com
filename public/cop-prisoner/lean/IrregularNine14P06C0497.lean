import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0189
import IrregularNine14P06C0190

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r29820 : Route 9 := (fun mask => (mask,id))

def c29820 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u29820 : Upper (D 6) (R 6) [10,17,33,68,132] 13 := by
  apply FastRouting.sound _ _ [10,17,33,68,132] 13 (by decide) (choices 1) [2,64,256] r29820 c29820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11382
  · exact u11383
  · exact u11384

def r29821 : Route 9 := (fun mask => (mask,id))

def c29821 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u29821 : Upper (D 6) (R 6) [10,17,33,68,160] 13 := by
  apply FastRouting.sound _ _ [10,17,33,68,160] 13 (by decide) (choices 1) [2,4,64,256] r29821 c29821
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11385
  · exact u11386
  · exact u11387
  · exact u11388

def r29822 : Route 9 := (fun mask => (mask,id))

def c29822 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u29822 : Upper (D 6) (R 6) [10,17,33,68,192] 13 := by
  apply FastRouting.sound _ _ [10,17,33,68,192] 13 (by decide) (choices 1) [2,4,256] r29822 c29822
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11389
  · exact u11390
  · exact u11391

def r29823 : Route 9 := (fun mask => (mask,id))

def c29823 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29823 : Upper (D 6) (R 6) [10,17,33,68,384] 13 := by
  apply FastRouting.sound _ _ [10,17,33,68,384] 13 (by decide) (choices 1) [2,4,64] r29823 c29823
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11392
  · exact u11393
  · exact u11394

def b29824 : PairBound 9 := { available := 452, camps := [{ cop := 3, region := 23, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 19 37 104 22 484 452 452 452), lower := (rows 11 19 37 104 22 32 64 128 256), losses := [] }

theorem u29824 : Upper (D 6) (R 6) [10,17,33,96,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29824
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29825 : PairBound 9 := { available := 388, camps := [{ cop := 3, region := 19, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 19 37 104 82 420 452 388 388), lower := (rows 11 19 37 104 82 32 64 128 256), losses := [] }

theorem u29825 : Upper (D 6) (R 6) [10,17,33,96,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29825
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29826 : PairBound 9 := { available := 390, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 0, region := 420, targets := 64 }], pairs := [(1,5),(2,6),(4,5)], upper := (rows 11 19 37 104 84 422 454 390 390), lower := (rows 11 19 37 104 84 32 64 128 256), losses := [] }

theorem u29826 : Upper (D 6) (R 6) [10,17,33,96,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29826
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29827 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 11 19 37 104 146 356 324 452 324), lower := (rows 11 19 37 104 146 32 64 128 256), losses := [] }

theorem u29827 : Upper (D 6) (R 6) [10,17,33,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29827
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29828 : Route 9 := (fun mask => (mask,id))

def c29828 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u29828 : Upper (D 6) (R 6) [10,17,33,96,132] 13 := by
  apply FastRouting.sound _ _ [10,17,33,96,132] 13 (by decide) (choices 1) [2,4,64,256] r29828 c29828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11395
  · exact u11396
  · exact u11397
  · exact u11398

def b29829 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 0, region := 292, targets := 64 }], pairs := [(1,5),(2,6),(4,5)], upper := (rows 11 19 37 104 208 294 326 390 262), lower := (rows 11 19 37 104 208 32 64 128 256), losses := [] }

theorem u29829 : Upper (D 6) (R 6) [10,17,33,96,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29829
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29830 : Route 9 := (fun mask => (mask,id))

def c29830 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29830 : Upper (D 6) (R 6) [10,17,33,96,384] 13 := by
  apply FastRouting.sound _ _ [10,17,33,96,384] 13 (by decide) (choices 1) [2,4,64] r29830 c29830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11399
  · exact u11400
  · exact u11401

def b29831 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 19, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 19 37 140 22 352 352 480 352), lower := (rows 11 19 37 140 22 32 64 128 256), losses := [] }

theorem u29831 : Upper (D 6) (R 6) [10,17,33,132,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29831
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29832 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 18, targets := 4 }], pairs := [(1,2),(2,1),(3,1)], upper := (rows 11 19 37 140 50 356 324 452 324), lower := (rows 11 19 37 140 50 32 64 128 256), losses := [] }

theorem u29832 : Upper (D 6) (R 6) [10,17,33,132,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29832
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29833 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 19 37 140 52 354 322 450 322), lower := (rows 11 19 37 140 52 32 64 128 256), losses := [] }

theorem u29833 : Upper (D 6) (R 6) [10,17,33,132,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29833
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29834 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 456, targets := 1 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 19 37 140 82 356 356 484 356), lower := (rows 11 19 37 140 82 32 64 128 256), losses := [] }

theorem u29834 : Upper (D 6) (R 6) [10,17,33,132,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29834
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29835 : Route 9 := (fun mask => (mask,id))

def c29835 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u29835 : Upper (D 6) (R 6) [10,17,33,132,68] 13 := by
  apply FastRouting.sound _ _ [10,17,33,132,68] 13 (by decide) (choices 1) [2,64,256] r29835 c29835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11402
  · exact u11403
  · exact u11404

def r29836 : Route 9 := (fun mask => (mask,id))

def c29836 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u29836 : Upper (D 6) (R 6) [10,17,33,132,96] 13 := by
  apply FastRouting.sound _ _ [10,17,33,132,96] 13 (by decide) (choices 1) [2,4,64,256] r29836 c29836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11405
  · exact u11406
  · exact u11407
  · exact u11408

def b29837 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 2, region := 200, targets := 1 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 19 37 140 274 100 100 228 356), lower := (rows 11 19 37 140 274 32 64 128 256), losses := [] }

theorem u29837 : Upper (D 6) (R 6) [10,17,33,132,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29837
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29838 : Route 9 := (fun mask => (mask,id))

def c29838 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29838 : Upper (D 6) (R 6) [10,17,33,132,260] 13 := by
  apply FastRouting.sound _ _ [10,17,33,132,260] 13 (by decide) (choices 1) [2,64] r29838 c29838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11409
  · exact u11410

def r29839 : Route 9 := (fun mask => (mask,id))

def c29839 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29839 : Upper (D 6) (R 6) [10,17,33,132,288] 13 := by
  apply FastRouting.sound _ _ [10,17,33,132,288] 13 (by decide) (choices 1) [2,4,64] r29839 c29839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11411
  · exact u11412
  · exact u11413

def r29840 : Route 9 := (fun mask => (mask,id))

def c29840 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29840 : Upper (D 6) (R 6) [10,17,33,132,320] 13 := by
  apply FastRouting.sound _ _ [10,17,33,132,320] 13 (by decide) (choices 1) [2,4,64] r29840 c29840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11414
  · exact u11415
  · exact u11416

def b29841 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 23, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 19 37 168 22 356 324 452 324), lower := (rows 11 19 37 168 22 32 64 128 256), losses := [] }

theorem u29841 : Upper (D 6) (R 6) [10,17,33,160,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29841
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29842 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 338, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 11 19 37 168 82 356 324 452 324), lower := (rows 11 19 37 168 82 32 64 128 256), losses := [] }

theorem u29842 : Upper (D 6) (R 6) [10,17,33,160,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29842
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29843 : Route 9 := (fun mask => (mask,id))

def c29843 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u29843 : Upper (D 6) (R 6) [10,17,33,160,68] 13 := by
  apply FastRouting.sound _ _ [10,17,33,160,68] 13 (by decide) (choices 1) [2,4,64,256] r29843 c29843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11417
  · exact u11418
  · exact u11419
  · exact u11420

def b29844 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 2, region := 338, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 11 19 37 168 274 100 68 196 324), lower := (rows 11 19 37 168 274 32 64 128 256), losses := [] }

theorem u29844 : Upper (D 6) (R 6) [10,17,33,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29844
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29845 : Route 9 := (fun mask => (mask,id))

def c29845 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29845 : Upper (D 6) (R 6) [10,17,33,160,260] 13 := by
  apply FastRouting.sound _ _ [10,17,33,160,260] 13 (by decide) (choices 1) [2,4,64] r29845 c29845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11421
  · exact u11422
  · exact u11423

def r29846 : Route 9 := (fun mask => (mask,id))

def c29846 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29846 : Upper (D 6) (R 6) [10,17,33,160,320] 13 := by
  apply FastRouting.sound _ _ [10,17,33,160,320] 13 (by decide) (choices 1) [2,4,64] r29846 c29846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11424
  · exact u11425
  · exact u11426

def b29847 : PairBound 9 := { available := 356, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 11 19 37 200 22 356 356 484 356), lower := (rows 11 19 37 200 22 32 64 128 256), losses := [] }

theorem u29847 : Upper (D 6) (R 6) [10,17,33,192,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29847
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29848 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 18, targets := 4 }], pairs := [(1,2),(2,1),(3,1)], upper := (rows 11 19 37 200 50 356 324 452 324), lower := (rows 11 19 37 200 50 32 64 128 256), losses := [] }

theorem u29848 : Upper (D 6) (R 6) [10,17,33,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29848
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29849 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 19 37 200 52 358 326 454 326), lower := (rows 11 19 37 200 52 32 64 128 256), losses := [] }

theorem u29849 : Upper (D 6) (R 6) [10,17,33,192,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29849
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29850 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 19, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 19 37 200 82 292 356 420 292), lower := (rows 11 19 37 200 82 32 64 128 256), losses := [] }

theorem u29850 : Upper (D 6) (R 6) [10,17,33,192,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29850
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29851 : Route 9 := (fun mask => (mask,id))

def c29851 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u29851 : Upper (D 6) (R 6) [10,17,33,192,68] 13 := by
  apply FastRouting.sound _ _ [10,17,33,192,68] 13 (by decide) (choices 1) [2,4,256] r29851 c29851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11427
  · exact u11428
  · exact u11429

def r29852 : Route 9 := (fun mask => (mask,id))

def c29852 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u29852 : Upper (D 6) (R 6) [10,17,33,192,96] 13 := by
  apply FastRouting.sound _ _ [10,17,33,192,96] 13 (by decide) (choices 1) [2,4,256] r29852 c29852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11430
  · exact u11431
  · exact u11432

def b29853 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 2, region := 200, targets := 1 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 19 37 200 274 100 100 228 356), lower := (rows 11 19 37 200 274 32 64 128 256), losses := [] }

theorem u29853 : Upper (D 6) (R 6) [10,17,33,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29853
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29854 : Route 9 := (fun mask => (mask,id))

def c29854 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29854 : Upper (D 6) (R 6) [10,17,33,192,260] 13 := by
  apply FastRouting.sound _ _ [10,17,33,192,260] 13 (by decide) (choices 1) [2,4,64] r29854 c29854
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11433
  · exact u11434
  · exact u11435

def r29855 : Route 9 := (fun mask => (mask,id))

def c29855 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29855 : Upper (D 6) (R 6) [10,17,33,192,288] 13 := by
  apply FastRouting.sound _ _ [10,17,33,192,288] 13 (by decide) (choices 1) [2,4,64] r29855 c29855
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11436
  · exact u11437
  · exact u11438

def r29856 : Route 9 := (fun mask => (mask,id))

def c29856 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29856 : Upper (D 6) (R 6) [10,17,33,192,320] 13 := by
  apply FastRouting.sound _ _ [10,17,33,192,320] 13 (by decide) (choices 1) [2,4] r29856 c29856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11439
  · exact u11440

def b29857 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 11 19 37 392 22 100 100 228 356), lower := (rows 11 19 37 392 22 32 64 128 256), losses := [] }

theorem u29857 : Upper (D 6) (R 6) [10,17,33,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29857
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29858 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 18, targets := 4 }], pairs := [(1,2),(2,1),(3,1)], upper := (rows 11 19 37 392 50 100 68 196 324), lower := (rows 11 19 37 392 50 32 64 128 256), losses := [] }

theorem u29858 : Upper (D 6) (R 6) [10,17,33,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29858
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29859 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 19 37 392 52 102 70 198 326), lower := (rows 11 19 37 392 52 32 64 128 256), losses := [] }

theorem u29859 : Upper (D 6) (R 6) [10,17,33,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29859
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29860 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 456, targets := 1 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 19 37 392 82 100 100 228 356), lower := (rows 11 19 37 392 82 32 64 128 256), losses := [] }

theorem u29860 : Upper (D 6) (R 6) [10,17,33,384,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29860
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29861 : Route 9 := (fun mask => (mask,id))

def c29861 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29861 : Upper (D 6) (R 6) [10,17,33,384,68] 13 := by
  apply FastRouting.sound _ _ [10,17,33,384,68] 13 (by decide) (choices 1) [2,4,64] r29861 c29861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11441
  · exact u11442
  · exact u11443

def r29862 : Route 9 := (fun mask => (mask,id))

def c29862 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29862 : Upper (D 6) (R 6) [10,17,33,384,96] 13 := by
  apply FastRouting.sound _ _ [10,17,33,384,96] 13 (by decide) (choices 1) [2,4,64] r29862 c29862
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11444
  · exact u11445
  · exact u11446

def b29863 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 11, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 100 11 148 356 356 484 356), lower := (rows 11 19 100 11 148 32 64 128 256), losses := [] }

theorem u29863 : Upper (D 6) (R 6) [10,17,96,3,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29863
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29864 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 11, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 100 11 176 356 324 452 324), lower := (rows 11 19 100 11 176 32 64 128 256), losses := [] }

theorem u29864 : Upper (D 6) (R 6) [10,17,96,3,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29864
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29865 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 11, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 100 11 400 100 100 228 356), lower := (rows 11 19 100 11 400 32 64 128 256), losses := [] }

theorem u29865 : Upper (D 6) (R 6) [10,17,96,3,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29865
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29866 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 27, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 19 100 13 22 480 480 480 480), lower := (rows 11 19 100 13 22 32 64 128 256), losses := [] }

theorem u29866 : Upper (D 6) (R 6) [10,17,96,5,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29866
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29867 : PairBound 9 := { available := 452, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 19 100 13 50 484 452 452 452), lower := (rows 11 19 100 13 50 32 64 128 256), losses := [] }

theorem u29867 : Upper (D 6) (R 6) [10,17,96,5,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29867
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29868 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 19 100 13 52 482 450 450 450), lower := (rows 11 19 100 13 52 32 64 128 256), losses := [] }

theorem u29868 : Upper (D 6) (R 6) [10,17,96,5,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29868
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29869 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 2, region := 16, targets := 2 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 19 100 13 112 422 454 390 390), lower := (rows 11 19 100 13 112 32 64 128 256), losses := [] }

theorem u29869 : Upper (D 6) (R 6) [10,17,96,5,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29869
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29870 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 0, region := 356, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 100 13 146 356 356 484 356), lower := (rows 11 19 100 13 146 32 64 128 256), losses := [] }

theorem u29870 : Upper (D 6) (R 6) [10,17,96,5,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29870
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29871 : PairBound 9 := { available := 354, camps := [{ cop := 4, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 19 100 13 148 354 354 482 354), lower := (rows 11 19 100 13 148 32 64 128 256), losses := [] }

theorem u29871 : Upper (D 6) (R 6) [10,17,96,5,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29871
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29872 : Route 9 := (fun mask => (mask,id))

def c29872 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u29872 : Upper (D 6) (R 6) [10,17,96,5,160] 13 := by
  apply FastRouting.sound _ _ [10,17,96,5,160] 13 (by decide) (choices 1) [2,4,64,256] r29872 c29872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11447
  · exact u11448
  · exact u11449
  · exact u11450

def r29873 : Route 9 := (fun mask => (mask,id))

def c29873 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29873 : Upper (D 6) (R 6) [10,17,96,5,384] 13 := by
  apply FastRouting.sound _ _ [10,17,96,5,384] 13 (by decide) (choices 1) [2,4,64] r29873 c29873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11451
  · exact u11452
  · exact u11453

def b29874 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 19 100 14 148 353 353 481 353), lower := (rows 11 19 100 14 148 32 64 128 256), losses := [] }

theorem u29874 : Upper (D 6) (R 6) [10,17,96,6,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29874
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29875 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 11 19 100 14 176 357 325 453 325), lower := (rows 11 19 100 14 176 32 64 128 256), losses := [] }

theorem u29875 : Upper (D 6) (R 6) [10,17,96,6,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29875
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29876 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 100 14 400 101 101 229 357), lower := (rows 11 19 100 14 400 32 64 128 256), losses := [] }

theorem u29876 : Upper (D 6) (R 6) [10,17,96,6,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29876
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29877 : PairBound 9 := { available := 388, camps := [{ cop := 2, region := 27, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 19 100 41 82 420 452 388 388), lower := (rows 11 19 100 41 82 32 64 128 256), losses := [] }

theorem u29877 : Upper (D 6) (R 6) [10,17,96,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29877
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29878 : PairBound 9 := { available := 390, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 19 100 41 84 422 454 390 390), lower := (rows 11 19 100 41 84 32 64 128 256), losses := [] }

theorem u29878 : Upper (D 6) (R 6) [10,17,96,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29878
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29879 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 0, region := 356, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 100 41 146 356 324 452 324), lower := (rows 11 19 100 41 146 32 64 128 256), losses := [] }

theorem u29879 : Upper (D 6) (R 6) [10,17,96,33,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29879
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u29879
end Delivery.IrregularNine14.P06
