import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0512
import IrregularNine14P06C0513
import IrregularNine14P06C0514
import IrregularNine14P06C0515
import IrregularNine14P06C0516

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b41340 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 2, region := 368, targets := 2 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 35 134 25 372 356 356 484 356), lower := (rows 11 35 134 25 16 32 64 128 256), losses := [] }

theorem u41340 : Upper (D 6) (R 6) [10,33,130,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41340 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41341 : Route 9 := (fun mask => (mask,id))

def c41341 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41341 : Upper (D 6) (R 6) [10,33,130,20] 13 := by
  apply FastRouting.sound _ _ [10,33,130,20] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41341 c41341
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30746
  · exact u30747
  · exact u30748
  · exact u30749
  · exact u30750
  · exact u30751
  · exact u30752
  · exact u30753
  · exact u30754
  · exact u30755

def b41342 : PairBound 9 := { available := 340, camps := [{ cop := 5, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 134 41 340 372 340 468 340), lower := (rows 11 35 134 41 16 32 64 128 256), losses := [] }

theorem u41342 : Upper (D 6) (R 6) [10,33,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41343 : PairBound 9 := { available := 341, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 134 44 341 373 341 469 341), lower := (rows 11 35 134 44 16 32 64 128 256), losses := [] }

theorem u41343 : Upper (D 6) (R 6) [10,33,130,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41343 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41344 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 134 56 341 357 325 453 325), lower := (rows 11 35 134 56 16 32 64 128 256), losses := [] }

theorem u41344 : Upper (D 6) (R 6) [10,33,130,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41344 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41345 : PairBound 9 := { available := 372, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 2, region := 368, targets := 2 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 35 134 73 372 372 372 500 372), lower := (rows 11 35 134 73 16 32 64 128 256), losses := [] }

theorem u41345 : Upper (D 6) (R 6) [10,33,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41346 : Route 9 := (fun mask => (mask,id))

def c41346 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41346 : Upper (D 6) (R 6) [10,33,130,68] 13 := by
  apply FastRouting.sound _ _ [10,33,130,68] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41346 c41346
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30756
  · exact u30757
  · exact u30758
  · exact u30759
  · exact u30760
  · exact u30761
  · exact u30762
  · exact u30763
  · exact u30764
  · exact u30765

def r41347 : Route 9 := (fun mask => (mask,id))

def c41347 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41347 : Upper (D 6) (R 6) [10,33,130,80] 13 := by
  apply FastRouting.sound _ _ [10,33,130,80] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41347 c41347
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30766
  · exact u30767
  · exact u30768
  · exact u30769
  · exact u30770
  · exact u30771
  · exact u30772
  · exact u30773
  · exact u30774
  · exact u30775

def b41348 : PairBound 9 := { available := 341, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 134 104 341 373 341 469 341), lower := (rows 11 35 134 104 16 32 64 128 256), losses := [] }

theorem u41348 : Upper (D 6) (R 6) [10,33,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41348 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41349 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 244, targets := 1 },{ cop := 2, region := 112, targets := 2 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 35 134 265 116 116 116 244 372), lower := (rows 11 35 134 265 16 32 64 128 256), losses := [] }

theorem u41349 : Upper (D 6) (R 6) [10,33,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41349 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41350 : Route 9 := (fun mask => (mask,id))

def c41350 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41350 : Upper (D 6) (R 6) [10,33,130,260] 13 := by
  apply FastRouting.sound _ _ [10,33,130,260] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41350 c41350
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30776
  · exact u30777
  · exact u30778
  · exact u30779
  · exact u30780
  · exact u30781

def r41351 : Route 9 := (fun mask => (mask,id))

def c41351 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41351 : Upper (D 6) (R 6) [10,33,130,272] 13 := by
  apply FastRouting.sound _ _ [10,33,130,272] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41351 c41351
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30782
  · exact u30783
  · exact u30784
  · exact u30785
  · exact u30786
  · exact u30787

def b41352 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 134 296 85 117 85 213 341), lower := (rows 11 35 134 296 16 32 64 128 256), losses := [] }

theorem u41352 : Upper (D 6) (R 6) [10,33,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41352 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41353 : Route 9 := (fun mask => (mask,id))

def c41353 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41353 : Upper (D 6) (R 6) [10,33,130,320] 13 := by
  apply FastRouting.sound _ _ [10,33,130,320] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41353 c41353
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30788
  · exact u30789
  · exact u30790
  · exact u30791
  · exact u30792
  · exact u30793

def b41354 : PairBound 9 := { available := 356, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 148 11 372 356 356 484 356), lower := (rows 11 35 148 11 16 32 64 128 256), losses := [] }

theorem u41354 : Upper (D 6) (R 6) [10,33,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41354 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41355 : Route 9 := (fun mask => (mask,id))

def c41355 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41355 : Upper (D 6) (R 6) [10,33,144,5] 13 := by
  apply FastRouting.sound _ _ [10,33,144,5] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41355 c41355
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30794
  · exact u30795
  · exact u30796
  · exact u30797
  · exact u30798
  · exact u30799
  · exact u30800
  · exact u30801
  · exact u30802
  · exact u30803

def b41356 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 148 14 373 357 357 485 357), lower := (rows 11 35 148 14 16 32 64 128 256), losses := [] }

theorem u41356 : Upper (D 6) (R 6) [10,33,144,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41356 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41357 : PairBound 9 := { available := 326, camps := [{ cop := 5, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 41 342 358 326 454 326), lower := (rows 11 35 148 41 16 32 64 128 256), losses := [] }

theorem u41357 : Upper (D 6) (R 6) [10,33,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41357 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41358 : PairBound 9 := { available := 325, camps := [{ cop := 5, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 42 341 357 325 453 325), lower := (rows 11 35 148 42 16 32 64 128 256), losses := [] }

theorem u41358 : Upper (D 6) (R 6) [10,33,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41358 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41359 : PairBound 9 := { available := 327, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 44 343 359 327 455 327), lower := (rows 11 35 148 44 16 32 64 128 256), losses := [] }

theorem u41359 : Upper (D 6) (R 6) [10,33,144,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41359 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41360 : Route 9 := (fun mask => (mask,id))

def c41360 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41360 : Upper (D 6) (R 6) [10,33,144,65] 13 := by
  apply FastRouting.sound _ _ [10,33,144,65] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41360 c41360
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30804
  · exact u30805
  · exact u30806
  · exact u30807
  · exact u30808
  · exact u30809
  · exact u30810
  · exact u30811
  · exact u30812
  · exact u30813

def b41361 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 148 74 373 357 357 485 357), lower := (rows 11 35 148 74 16 32 64 128 256), losses := [] }

theorem u41361 : Upper (D 6) (R 6) [10,33,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41361 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41362 : Route 9 := (fun mask => (mask,id))

def c41362 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41362 : Upper (D 6) (R 6) [10,33,144,68] 13 := by
  apply FastRouting.sound _ _ [10,33,144,68] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r41362 c41362
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30814
  · exact u30815
  · exact u30816
  · exact u30817
  · exact u30818
  · exact u30819
  · exact u30820
  · exact u30821
  · exact u30822
  · exact u30823
  · exact u30824
  · exact u30825
  · exact u30826
  · exact u30827
  · exact u30828

def b41363 : PairBound 9 := { available := 327, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 104 343 359 327 455 327), lower := (rows 11 35 148 104 16 32 64 128 256), losses := [] }

theorem u41363 : Upper (D 6) (R 6) [10,33,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41363 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41364 : Route 9 := (fun mask => (mask,id))

def c41364 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41364 : Upper (D 6) (R 6) [10,33,144,257] 13 := by
  apply FastRouting.sound _ _ [10,33,144,257] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41364 c41364
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30829
  · exact u30830
  · exact u30831
  · exact u30832
  · exact u30833
  · exact u30834

def b41365 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 148 266 117 101 101 229 357), lower := (rows 11 35 148 266 16 32 64 128 256), losses := [] }

theorem u41365 : Upper (D 6) (R 6) [10,33,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41365 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41366 : Route 9 := (fun mask => (mask,id))

def c41366 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41366 : Upper (D 6) (R 6) [10,33,144,260] 13 := by
  apply FastRouting.sound _ _ [10,33,144,260] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41366 c41366
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30835
  · exact u30836
  · exact u30837
  · exact u30838
  · exact u30839
  · exact u30840
  · exact u30841
  · exact u30842
  · exact u30843
  · exact u30844

def b41367 : PairBound 9 := { available := 71, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 296 87 103 71 199 327), lower := (rows 11 35 148 296 16 32 64 128 256), losses := [] }

theorem u41367 : Upper (D 6) (R 6) [10,33,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41367 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41368 : Route 9 := (fun mask => (mask,id))

def c41368 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41368 : Upper (D 6) (R 6) [10,33,144,320] 13 := by
  apply FastRouting.sound _ _ [10,33,144,320] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41368 c41368
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30845
  · exact u30846
  · exact u30847
  · exact u30848
  · exact u30849
  · exact u30850
  · exact u30851
  · exact u30852
  · exact u30853
  · exact u30854

def b41369 : PairBound 9 := { available := 340, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 164 11 340 372 340 468 340), lower := (rows 11 35 164 11 16 32 64 128 256), losses := [] }

theorem u41369 : Upper (D 6) (R 6) [10,33,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41369 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41370 : PairBound 9 := { available := 342, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 164 13 342 374 342 470 342), lower := (rows 11 35 164 13 16 32 64 128 256), losses := [] }

theorem u41370 : Upper (D 6) (R 6) [10,33,160,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41370 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41371 : PairBound 9 := { available := 341, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 164 14 341 373 341 469 341), lower := (rows 11 35 164 14 16 32 64 128 256), losses := [] }

theorem u41371 : Upper (D 6) (R 6) [10,33,160,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41371 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41372 : Route 9 := (fun mask => (mask,id))

def c41372 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41372 : Upper (D 6) (R 6) [10,33,160,17] 13 := by
  apply FastRouting.sound _ _ [10,33,160,17] 13 (by decide) (choices 2) [6,66,68,258,260,320] r41372 c41372
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30855
  · exact u30856
  · exact u30857
  · exact u30858
  · exact u30859
  · exact u30860

def b41373 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 164 26 341 357 325 453 325), lower := (rows 11 35 164 26 16 32 64 128 256), losses := [] }

theorem u41373 : Upper (D 6) (R 6) [10,33,160,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41373 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41374 : Route 9 := (fun mask => (mask,id))

def c41374 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41374 : Upper (D 6) (R 6) [10,33,160,20] 13 := by
  apply FastRouting.sound _ _ [10,33,160,20] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41374 c41374
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30861
  · exact u30862
  · exact u30863
  · exact u30864
  · exact u30865
  · exact u30866
  · exact u30867
  · exact u30868
  · exact u30869
  · exact u30870

def r41375 : Route 9 := (fun mask => (mask,id))

def c41375 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41375 : Upper (D 6) (R 6) [10,33,160,65] 13 := by
  apply FastRouting.sound _ _ [10,33,160,65] 13 (by decide) (choices 2) [6,66,68,258,260,320] r41375 c41375
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30871
  · exact u30872
  · exact u30873
  · exact u30874
  · exact u30875
  · exact u30876

def b41376 : PairBound 9 := { available := 341, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 164 74 341 373 341 469 341), lower := (rows 11 35 164 74 16 32 64 128 256), losses := [] }

theorem u41376 : Upper (D 6) (R 6) [10,33,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41376 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41377 : Route 9 := (fun mask => (mask,id))

def c41377 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41377 : Upper (D 6) (R 6) [10,33,160,68] 13 := by
  apply FastRouting.sound _ _ [10,33,160,68] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41377 c41377
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30877
  · exact u30878
  · exact u30879
  · exact u30880
  · exact u30881
  · exact u30882
  · exact u30883
  · exact u30884
  · exact u30885
  · exact u30886

def r41378 : Route 9 := (fun mask => (mask,id))

def c41378 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41378 : Upper (D 6) (R 6) [10,33,160,80] 13 := by
  apply FastRouting.sound _ _ [10,33,160,80] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41378 c41378
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30887
  · exact u30888
  · exact u30889
  · exact u30890
  · exact u30891
  · exact u30892
  · exact u30893
  · exact u30894
  · exact u30895
  · exact u30896

def r41379 : Route 9 := (fun mask => (mask,id))

def c41379 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41379 : Upper (D 6) (R 6) [10,33,160,257] 13 := by
  apply FastRouting.sound _ _ [10,33,160,257] 13 (by decide) (choices 2) [6,66,68] r41379 c41379
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u30897
  · exact u30898
  · exact u30899

def b41380 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 164 266 85 117 85 213 341), lower := (rows 11 35 164 266 16 32 64 128 256), losses := [] }

theorem u41380 : Upper (D 6) (R 6) [10,33,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41380 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41381 : Route 9 := (fun mask => (mask,id))

def c41381 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41381 : Upper (D 6) (R 6) [10,33,160,260] 13 := by
  apply FastRouting.sound _ _ [10,33,160,260] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41381 c41381
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30900
  · exact u30901
  · exact u30902
  · exact u30903
  · exact u30904
  · exact u30905

def r41382 : Route 9 := (fun mask => (mask,id))

def c41382 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41382 : Upper (D 6) (R 6) [10,33,160,272] 13 := by
  apply FastRouting.sound _ _ [10,33,160,272] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41382 c41382
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30906
  · exact u30907
  · exact u30908
  · exact u30909
  · exact u30910
  · exact u30911

def r41383 : Route 9 := (fun mask => (mask,id))

def c41383 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41383 : Upper (D 6) (R 6) [10,33,160,320] 13 := by
  apply FastRouting.sound _ _ [10,33,160,320] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41383 c41383
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30912
  · exact u30913
  · exact u30914
  · exact u30915
  · exact u30916
  · exact u30917

def b41384 : PairBound 9 := { available := 372, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 196 11 372 372 372 500 372), lower := (rows 11 35 196 11 16 32 64 128 256), losses := [] }

theorem u41384 : Upper (D 6) (R 6) [10,33,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41384 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41385 : Route 9 := (fun mask => (mask,id))

def c41385 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41385 : Upper (D 6) (R 6) [10,33,192,5] 13 := by
  apply FastRouting.sound _ _ [10,33,192,5] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41385 c41385
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30918
  · exact u30919
  · exact u30920
  · exact u30921
  · exact u30922
  · exact u30923
  · exact u30924
  · exact u30925
  · exact u30926
  · exact u30927

def b41386 : PairBound 9 := { available := 373, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 196 14 373 373 373 501 373), lower := (rows 11 35 196 14 16 32 64 128 256), losses := [] }

theorem u41386 : Upper (D 6) (R 6) [10,33,192,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41387 : Route 9 := (fun mask => (mask,id))

def c41387 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41387 : Upper (D 6) (R 6) [10,33,192,17] 13 := by
  apply FastRouting.sound _ _ [10,33,192,17] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41387 c41387
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30928
  · exact u30929
  · exact u30930
  · exact u30931
  · exact u30932
  · exact u30933
  · exact u30934
  · exact u30935
  · exact u30936
  · exact u30937

def b41388 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 196 26 373 357 357 485 357), lower := (rows 11 35 196 26 16 32 64 128 256), losses := [] }

theorem u41388 : Upper (D 6) (R 6) [10,33,192,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41388 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41389 : Route 9 := (fun mask => (mask,id))

def c41389 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41389 : Upper (D 6) (R 6) [10,33,192,20] 13 := by
  apply FastRouting.sound _ _ [10,33,192,20] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r41389 c41389
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30938
  · exact u30939
  · exact u30940
  · exact u30941
  · exact u30942
  · exact u30943
  · exact u30944
  · exact u30945
  · exact u30946
  · exact u30947
  · exact u30948
  · exact u30949
  · exact u30950
  · exact u30951
  · exact u30952

def b41390 : PairBound 9 := { available := 342, camps := [{ cop := 5, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 41 342 374 342 470 342), lower := (rows 11 35 196 41 16 32 64 128 256), losses := [] }

theorem u41390 : Upper (D 6) (R 6) [10,33,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41390 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41391 : PairBound 9 := { available := 341, camps := [{ cop := 5, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 42 341 373 341 469 341), lower := (rows 11 35 196 42 16 32 64 128 256), losses := [] }

theorem u41391 : Upper (D 6) (R 6) [10,33,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41391 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41392 : PairBound 9 := { available := 343, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 44 343 375 343 471 343), lower := (rows 11 35 196 44 16 32 64 128 256), losses := [] }

theorem u41392 : Upper (D 6) (R 6) [10,33,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41393 : PairBound 9 := { available := 327, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 56 343 359 327 455 327), lower := (rows 11 35 196 56 16 32 64 128 256), losses := [] }

theorem u41393 : Upper (D 6) (R 6) [10,33,192,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41393 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41394 : Route 9 := (fun mask => (mask,id))

def c41394 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41394 : Upper (D 6) (R 6) [10,33,192,65] 13 := by
  apply FastRouting.sound _ _ [10,33,192,65] 13 (by decide) (choices 2) [6,34,36,258,260,288] r41394 c41394
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30953
  · exact u30954
  · exact u30955
  · exact u30956
  · exact u30957
  · exact u30958

def b41395 : PairBound 9 := { available := 309, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 196 74 309 309 373 437 309), lower := (rows 11 35 196 74 16 32 64 128 256), losses := [] }

theorem u41395 : Upper (D 6) (R 6) [10,33,192,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41395 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41396 : PairBound 9 := { available := 311, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 196 76 311 311 375 439 311), lower := (rows 11 35 196 76 16 32 64 128 256), losses := [] }

theorem u41396 : Upper (D 6) (R 6) [10,33,192,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41397 : Route 9 := (fun mask => (mask,id))

def c41397 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41397 : Upper (D 6) (R 6) [10,33,192,80] 13 := by
  apply FastRouting.sound _ _ [10,33,192,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r41397 c41397
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30959
  · exact u30960
  · exact u30961
  · exact u30962
  · exact u30963
  · exact u30964
  · exact u30965
  · exact u30966
  · exact u30967
  · exact u30968

def b41398 : PairBound 9 := { available := 279, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 104 279 311 343 407 279), lower := (rows 11 35 196 104 16 32 64 128 256), losses := [] }

theorem u41398 : Upper (D 6) (R 6) [10,33,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41398 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41399 : Route 9 := (fun mask => (mask,id))

def c41399 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41399 : Upper (D 6) (R 6) [10,33,192,257] 13 := by
  apply FastRouting.sound _ _ [10,33,192,257] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41399 c41399
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30969
  · exact u30970
  · exact u30971
  · exact u30972
  · exact u30973
  · exact u30974

#print axioms u41399
end Delivery.IrregularNine14.P06
