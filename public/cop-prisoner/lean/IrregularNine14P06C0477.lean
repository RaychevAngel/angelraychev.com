import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0164
import IrregularNine14P06C0165

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28620 : PairBound 9 := { available := 306, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 35 196 13 88 306 370 434 306), lower := (rows 7 35 196 13 88 32 64 128 256), losses := [] }

theorem u28620 : Upper (D 6) (R 6) [6,33,192,5,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28620
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28621 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 35 196 13 112 314 346 410 282), lower := (rows 7 35 196 13 112 32 64 128 256), losses := [] }

theorem u28621 : Upper (D 6) (R 6) [6,33,192,5,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28621
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28622 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 35 196 13 274 120 120 248 376), lower := (rows 7 35 196 13 274 32 64 128 256), losses := [] }

theorem u28622 : Upper (D 6) (R 6) [6,33,192,5,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28622
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28623 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 35 196 13 280 114 114 242 370), lower := (rows 7 35 196 13 280 32 64 128 256), losses := [] }

theorem u28623 : Upper (D 6) (R 6) [6,33,192,5,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28623
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28624 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 35 196 13 304 122 90 218 346), lower := (rows 7 35 196 13 304 32 64 128 256), losses := [] }

theorem u28624 : Upper (D 6) (R 6) [6,33,192,5,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28624
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28625 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 35 196 13 336 58 122 186 314), lower := (rows 7 35 196 13 336 32 64 128 256), losses := [] }

theorem u28625 : Upper (D 6) (R 6) [6,33,192,5,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28625
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28626 : PairBound 9 := { available := 368, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 35 196 14 25 368 368 496 368), lower := (rows 7 35 196 14 25 32 64 128 256), losses := [] }

theorem u28626 : Upper (D 6) (R 6) [6,33,192,6,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28626
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28627 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 35 196 14 56 369 337 465 337), lower := (rows 7 35 196 14 56 32 64 128 256), losses := [] }

theorem u28627 : Upper (D 6) (R 6) [6,33,192,6,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28627
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28628 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 35 196 14 81 312 376 440 312), lower := (rows 7 35 196 14 81 32 64 128 256), losses := [] }

theorem u28628 : Upper (D 6) (R 6) [6,33,192,6,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28628
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28629 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 35 196 14 88 305 369 433 305), lower := (rows 7 35 196 14 88 32 64 128 256), losses := [] }

theorem u28629 : Upper (D 6) (R 6) [6,33,192,6,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28629
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28630 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 35 196 14 112 313 345 409 281), lower := (rows 7 35 196 14 112 32 64 128 256), losses := [] }

theorem u28630 : Upper (D 6) (R 6) [6,33,192,6,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28630
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28631 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 35 196 14 273 120 120 248 376), lower := (rows 7 35 196 14 273 32 64 128 256), losses := [] }

theorem u28631 : Upper (D 6) (R 6) [6,33,192,6,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28631
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28632 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 35 196 14 280 113 113 241 369), lower := (rows 7 35 196 14 280 32 64 128 256), losses := [] }

theorem u28632 : Upper (D 6) (R 6) [6,33,192,6,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28632
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28633 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 35 196 14 304 121 89 217 345), lower := (rows 7 35 196 14 304 32 64 128 256), losses := [] }

theorem u28633 : Upper (D 6) (R 6) [6,33,192,6,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28633
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28634 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 35 196 14 336 57 121 185 313), lower := (rows 7 35 196 14 336 32 64 128 256), losses := [] }

theorem u28634 : Upper (D 6) (R 6) [6,33,192,6,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28634
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28635 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 35 196 25 26 356 356 484 356), lower := (rows 7 35 196 25 26 32 64 128 256), losses := [] }

theorem u28635 : Upper (D 6) (R 6) [6,33,192,17,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28635
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28636 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 35 196 25 28 354 354 482 354), lower := (rows 7 35 196 25 28 32 64 128 256), losses := [] }

theorem u28636 : Upper (D 6) (R 6) [6,33,192,17,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28636
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28637 : PairBound 9 := { available := 332, camps := [{ cop := 1, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 35 196 25 50 364 332 460 332), lower := (rows 7 35 196 25 50 32 64 128 256), losses := [] }

theorem u28637 : Upper (D 6) (R 6) [6,33,192,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28637
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28638 : PairBound 9 := { available := 330, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 35 196 25 52 362 330 458 330), lower := (rows 7 35 196 25 52 32 64 128 256), losses := [] }

theorem u28638 : Upper (D 6) (R 6) [6,33,192,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28638
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28639 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 35 196 25 56 358 326 454 326), lower := (rows 7 35 196 25 56 32 64 128 256), losses := [] }

theorem u28639 : Upper (D 6) (R 6) [6,33,192,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28639
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28640 : Route 9 := (fun mask => (mask,id))

def c28640 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28640 : Upper (D 6) (R 6) [6,33,192,17,66] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,66] 13 (by decide) (choices 1) [4,8,256] r28640 c28640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9864
  · exact u9865
  · exact u9866

def b28641 : PairBound 9 := { available := 298, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 35 196 25 84 298 362 426 298), lower := (rows 7 35 196 25 84 32 64 128 256), losses := [] }

theorem u28641 : Upper (D 6) (R 6) [6,33,192,17,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28641
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28642 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 291, targets := 64 },{ cop := 0, region := 484, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 7 35 196 25 88 294 358 422 294), lower := (rows 7 35 196 25 88 32 64 128 256), losses := [] }

theorem u28642 : Upper (D 6) (R 6) [6,33,192,17,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28642
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28643 : Route 9 := (fun mask => (mask,id))

def c28643 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28643 : Upper (D 6) (R 6) [6,33,192,17,96] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,96] 13 (by decide) (choices 1) [2,4,8,256] r28643 c28643
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9867
  · exact u9868
  · exact u9869
  · exact u9870

def r28644 : Route 9 := (fun mask => (mask,id))

def c28644 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28644 : Upper (D 6) (R 6) [6,33,192,17,258] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,258] 13 (by decide) (choices 1) [4,8,64] r28644 c28644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9871
  · exact u9872
  · exact u9873

def r28645 : Route 9 := (fun mask => (mask,id))

def c28645 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28645 : Upper (D 6) (R 6) [6,33,192,17,260] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,260] 13 (by decide) (choices 1) [2,8,64] r28645 c28645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9874
  · exact u9875
  · exact u9876

def r28646 : Route 9 := (fun mask => (mask,id))

def c28646 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28646 : Upper (D 6) (R 6) [6,33,192,17,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,264] 13 (by decide) (choices 1) [2,4,64] r28646 c28646
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9877
  · exact u9878
  · exact u9879

def r28647 : Route 9 := (fun mask => (mask,id))

def c28647 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28647 : Upper (D 6) (R 6) [6,33,192,17,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,288] 13 (by decide) (choices 1) [2,4,8,64] r28647 c28647
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9880
  · exact u9881
  · exact u9882
  · exact u9883

def r28648 : Route 9 := (fun mask => (mask,id))

def c28648 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28648 : Upper (D 6) (R 6) [6,33,192,17,320] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,320] 13 (by decide) (choices 1) [2,4,8] r28648 c28648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9884
  · exact u9885
  · exact u9886

def b28649 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 35 196 26 28 353 353 481 353), lower := (rows 7 35 196 26 28 32 64 128 256), losses := [] }

theorem u28649 : Upper (D 6) (R 6) [6,33,192,18,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28649
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28650 : PairBound 9 := { available := 332, camps := [{ cop := 1, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 35 196 26 49 364 332 460 332), lower := (rows 7 35 196 26 49 32 64 128 256), losses := [] }

theorem u28650 : Upper (D 6) (R 6) [6,33,192,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28650
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28651 : PairBound 9 := { available := 329, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 35 196 26 52 361 329 457 329), lower := (rows 7 35 196 26 52 32 64 128 256), losses := [] }

theorem u28651 : Upper (D 6) (R 6) [6,33,192,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28651
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28652 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 24, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 196 26 56 357 325 453 325), lower := (rows 7 35 196 26 56 32 64 128 256), losses := [] }

theorem u28652 : Upper (D 6) (R 6) [6,33,192,18,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28652
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28653 : Route 9 := (fun mask => (mask,id))

def c28653 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28653 : Upper (D 6) (R 6) [6,33,192,18,65] 13 := by
  apply FastRouting.sound _ _ [6,33,192,18,65] 13 (by decide) (choices 1) [4,8,256] r28653 c28653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9887
  · exact u9888
  · exact u9889

def b28654 : PairBound 9 := { available := 297, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 35 196 26 84 297 361 425 297), lower := (rows 7 35 196 26 84 32 64 128 256), losses := [] }

theorem u28654 : Upper (D 6) (R 6) [6,33,192,18,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28654
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28655 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 291, targets := 64 },{ cop := 0, region := 484, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 7 35 196 26 88 293 357 421 293), lower := (rows 7 35 196 26 88 32 64 128 256), losses := [] }

theorem u28655 : Upper (D 6) (R 6) [6,33,192,18,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28655
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28656 : Route 9 := (fun mask => (mask,id))

def c28656 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28656 : Upper (D 6) (R 6) [6,33,192,18,96] 13 := by
  apply FastRouting.sound _ _ [6,33,192,18,96] 13 (by decide) (choices 1) [1,4,8,256] r28656 c28656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9890
  · exact u9891
  · exact u9892
  · exact u9893

def r28657 : Route 9 := (fun mask => (mask,id))

def c28657 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28657 : Upper (D 6) (R 6) [6,33,192,18,257] 13 := by
  apply FastRouting.sound _ _ [6,33,192,18,257] 13 (by decide) (choices 1) [4,8,64] r28657 c28657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9894
  · exact u9895
  · exact u9896

def r28658 : Route 9 := (fun mask => (mask,id))

def c28658 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28658 : Upper (D 6) (R 6) [6,33,192,18,260] 13 := by
  apply FastRouting.sound _ _ [6,33,192,18,260] 13 (by decide) (choices 1) [1,8,64] r28658 c28658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9897
  · exact u9898
  · exact u9899

def r28659 : Route 9 := (fun mask => (mask,id))

def c28659 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28659 : Upper (D 6) (R 6) [6,33,192,18,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,18,264] 13 (by decide) (choices 1) [1,4,64] r28659 c28659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9900
  · exact u9901
  · exact u9902

def r28660 : Route 9 := (fun mask => (mask,id))

def c28660 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28660 : Upper (D 6) (R 6) [6,33,192,18,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,18,288] 13 (by decide) (choices 1) [1,4,8,64] r28660 c28660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9903
  · exact u9904
  · exact u9905
  · exact u9906

def r28661 : Route 9 := (fun mask => (mask,id))

def c28661 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28661 : Upper (D 6) (R 6) [6,33,192,18,320] 13 := by
  apply FastRouting.sound _ _ [6,33,192,18,320] 13 (by decide) (choices 1) [1,4,8] r28661 c28661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9907
  · exact u9908
  · exact u9909

def b28662 : PairBound 9 := { available := 330, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 7 35 196 28 49 362 330 458 330), lower := (rows 7 35 196 28 49 32 64 128 256), losses := [] }

theorem u28662 : Upper (D 6) (R 6) [6,33,192,20,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28662
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28663 : PairBound 9 := { available := 329, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 35 196 28 50 361 329 457 329), lower := (rows 7 35 196 28 50 32 64 128 256), losses := [] }

theorem u28663 : Upper (D 6) (R 6) [6,33,192,20,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28663
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28664 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 0, region := 354, targets := 4 }], pairs := [(0,5),(1,2),(2,5)], upper := (rows 7 35 196 28 56 355 323 451 323), lower := (rows 7 35 196 28 56 32 64 128 256), losses := [] }

theorem u28664 : Upper (D 6) (R 6) [6,33,192,20,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28664
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28665 : Route 9 := (fun mask => (mask,id))

def c28665 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28665 : Upper (D 6) (R 6) [6,33,192,20,65] 13 := by
  apply FastRouting.sound _ _ [6,33,192,20,65] 13 (by decide) (choices 1) [2,8,256] r28665 c28665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9910
  · exact u9911
  · exact u9912

def r28666 : Route 9 := (fun mask => (mask,id))

def c28666 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28666 : Upper (D 6) (R 6) [6,33,192,20,66] 13 := by
  apply FastRouting.sound _ _ [6,33,192,20,66] 13 (by decide) (choices 1) [1,8,256] r28666 c28666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9913
  · exact u9914
  · exact u9915

def b28667 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 7 35 196 28 88 291 355 419 291), lower := (rows 7 35 196 28 88 32 64 128 256), losses := [] }

theorem u28667 : Upper (D 6) (R 6) [6,33,192,20,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28667
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28668 : Route 9 := (fun mask => (mask,id))

def c28668 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28668 : Upper (D 6) (R 6) [6,33,192,20,96] 13 := by
  apply FastRouting.sound _ _ [6,33,192,20,96] 13 (by decide) (choices 1) [1,2,8,256] r28668 c28668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9916
  · exact u9917
  · exact u9918
  · exact u9919

def r28669 : Route 9 := (fun mask => (mask,id))

def c28669 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28669 : Upper (D 6) (R 6) [6,33,192,20,257] 13 := by
  apply FastRouting.sound _ _ [6,33,192,20,257] 13 (by decide) (choices 1) [2,8,64] r28669 c28669
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9920
  · exact u9921
  · exact u9922

def r28670 : Route 9 := (fun mask => (mask,id))

def c28670 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28670 : Upper (D 6) (R 6) [6,33,192,20,258] 13 := by
  apply FastRouting.sound _ _ [6,33,192,20,258] 13 (by decide) (choices 1) [1,8,64] r28670 c28670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9923
  · exact u9924
  · exact u9925

def r28671 : Route 9 := (fun mask => (mask,id))

def c28671 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28671 : Upper (D 6) (R 6) [6,33,192,20,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,20,264] 13 (by decide) (choices 1) [1,2,64] r28671 c28671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9926
  · exact u9927
  · exact u9928

def r28672 : Route 9 := (fun mask => (mask,id))

def c28672 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28672 : Upper (D 6) (R 6) [6,33,192,20,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,20,288] 13 (by decide) (choices 1) [1,2,8,64] r28672 c28672
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9929
  · exact u9930
  · exact u9931
  · exact u9932

def r28673 : Route 9 := (fun mask => (mask,id))

def c28673 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28673 : Upper (D 6) (R 6) [6,33,192,20,320] 13 := by
  apply FastRouting.sound _ _ [6,33,192,20,320] 13 (by decide) (choices 1) [1,2,8] r28673 c28673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9933
  · exact u9934
  · exact u9935

def b28674 : PairBound 9 := { available := 284, camps := [{ cop := 1, region := 8, targets := 68 },{ cop := 3, region := 2, targets := 4 }], pairs := [(1,2),(3,2),(3,6)], upper := (rows 7 35 196 41 82 316 348 412 284), lower := (rows 7 35 196 41 82 32 64 128 256), losses := [] }

theorem u28674 : Upper (D 6) (R 6) [6,33,192,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28674
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28675 : PairBound 9 := { available := 278, camps := [{ cop := 1, region := 8, targets := 68 },{ cop := 3, region := 2, targets := 4 }], pairs := [(1,2),(3,2),(3,6)], upper := (rows 7 35 196 41 88 310 342 406 278), lower := (rows 7 35 196 41 88 32 64 128 256), losses := [] }

theorem u28675 : Upper (D 6) (R 6) [6,33,192,33,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28675
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28676 : PairBound 9 := { available := 92, camps := [{ cop := 1, region := 8, targets := 68 },{ cop := 3, region := 2, targets := 4 }], pairs := [(1,2),(3,2),(3,6)], upper := (rows 7 35 196 41 274 124 92 220 348), lower := (rows 7 35 196 41 274 32 64 128 256), losses := [] }

theorem u28676 : Upper (D 6) (R 6) [6,33,192,33,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28676
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28677 : PairBound 9 := { available := 90, camps := [{ cop := 1, region := 8, targets := 68 },{ cop := 3, region := 2, targets := 4 }], pairs := [(1,2),(3,2),(3,6)], upper := (rows 7 35 196 41 276 122 90 218 346), lower := (rows 7 35 196 41 276 32 64 128 256), losses := [] }

theorem u28677 : Upper (D 6) (R 6) [6,33,192,33,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28677
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28678 : PairBound 9 := { available := 86, camps := [{ cop := 1, region := 8, targets := 68 },{ cop := 3, region := 2, targets := 4 }], pairs := [(1,2),(3,2),(3,6)], upper := (rows 7 35 196 41 280 118 86 214 342), lower := (rows 7 35 196 41 280 32 64 128 256), losses := [] }

theorem u28678 : Upper (D 6) (R 6) [6,33,192,33,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28678
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28679 : PairBound 9 := { available := 30, camps := [{ cop := 1, region := 8, targets := 68 },{ cop := 3, region := 2, targets := 4 }], pairs := [(1,2),(3,2),(3,6)], upper := (rows 7 35 196 41 336 62 94 158 286), lower := (rows 7 35 196 41 336 32 64 128 256), losses := [] }

theorem u28679 : Upper (D 6) (R 6) [6,33,192,33,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28679
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u28679
end Delivery.IrregularNine14.P06
