import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0089

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19620 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 140 328 176 48 67 131 259), lower := (rows 35 70 140 328 176 48 64 128 256), losses := [] }

theorem u19620 : Upper (D 7) (R 7) [34,68,136,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19620 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19621 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 164 25 208 33 330 394 266), lower := (rows 35 70 164 25 208 33 64 128 256), losses := [] }

theorem u19621 : Upper (D 7) (R 7) [34,68,160,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19622 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 164 25 208 34 329 393 265), lower := (rows 35 70 164 25 208 34 64 128 256), losses := [] }

theorem u19622 : Upper (D 7) (R 7) [34,68,160,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19622 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19623 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 35 70 164 25 208 40 323 387 259), lower := (rows 35 70 164 25 208 40 64 128 256), losses := [] }

theorem u19623 : Upper (D 7) (R 7) [34,68,160,17,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19623 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19624 : Route 9 := (fun mask => (mask,id))

def c19624 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19624 : Upper (D 7) (R 7) [34,68,160,17,192,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,192,256] 13 (by decide) (choices 1) [1,2,8] r19624 c19624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5340
  · exact u5341
  · exact u5342

def b19625 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 164 25 274 33 200 200 456), lower := (rows 35 70 164 25 274 33 64 128 256), losses := [] }

theorem u19625 : Upper (D 7) (R 7) [34,68,160,17,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19625 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19626 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 35 70 164 25 274 40 193 193 449), lower := (rows 35 70 164 25 274 40 64 128 256), losses := [] }

theorem u19626 : Upper (D 7) (R 7) [34,68,160,17,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19626 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19627 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 164 25 274 96 201 137 393), lower := (rows 35 70 164 25 274 96 64 128 256), losses := [] }

theorem u19627 : Upper (D 7) (R 7) [34,68,160,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19627 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19628 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 35 70 164 25 274 160 73 201 329), lower := (rows 35 70 164 25 274 160 64 128 256), losses := [] }

theorem u19628 : Upper (D 7) (R 7) [34,68,160,17,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19628 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19629 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 198, targets := 1 },{ cop := 0, region := 472, targets := 32 }], pairs := [(1,0),(2,0),(3,5),(4,5)], upper := (rows 35 70 164 25 280 33 194 194 450), lower := (rows 35 70 164 25 280 33 64 128 256), losses := [] }

theorem u19629 : Upper (D 7) (R 7) [34,68,160,17,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19629 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19630 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 164 25 280 34 193 193 449), lower := (rows 35 70 164 25 280 34 64 128 256), losses := [] }

theorem u19630 : Upper (D 7) (R 7) [34,68,160,17,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19630 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19631 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 164 25 280 96 195 131 387), lower := (rows 35 70 164 25 280 96 64 128 256), losses := [] }

theorem u19631 : Upper (D 7) (R 7) [34,68,160,17,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19631 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19632 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 35 70 164 25 280 160 67 195 323), lower := (rows 35 70 164 25 280 160 64 128 256), losses := [] }

theorem u19632 : Upper (D 7) (R 7) [34,68,160,17,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19632 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19633 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 164 25 336 33 202 138 394), lower := (rows 35 70 164 25 336 33 64 128 256), losses := [] }

theorem u19633 : Upper (D 7) (R 7) [34,68,160,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19633 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19634 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 164 25 336 34 201 137 393), lower := (rows 35 70 164 25 336 34 64 128 256), losses := [] }

theorem u19634 : Upper (D 7) (R 7) [34,68,160,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19634 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19635 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 132, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 164 25 336 40 195 131 387), lower := (rows 35 70 164 25 336 40 64 128 256), losses := [] }

theorem u19635 : Upper (D 7) (R 7) [34,68,160,17,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19635 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19636 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 35 70 164 25 336 160 75 139 267), lower := (rows 35 70 164 25 336 160 64 128 256), losses := [] }

theorem u19636 : Upper (D 7) (R 7) [34,68,160,17,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19636 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19637 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 164 25 400 33 74 202 330), lower := (rows 35 70 164 25 400 33 64 128 256), losses := [] }

theorem u19637 : Upper (D 7) (R 7) [34,68,160,17,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19638 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 164 25 400 34 73 201 329), lower := (rows 35 70 164 25 400 34 64 128 256), losses := [] }

theorem u19638 : Upper (D 7) (R 7) [34,68,160,17,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19638 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19639 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 35 70 164 25 400 40 67 195 323), lower := (rows 35 70 164 25 400 40 64 128 256), losses := [] }

theorem u19639 : Upper (D 7) (R 7) [34,68,160,17,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19639 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19640 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 164 25 400 96 75 139 267), lower := (rows 35 70 164 25 400 96 64 128 256), losses := [] }

theorem u19640 : Upper (D 7) (R 7) [34,68,160,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19640 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19641 : PairBound 9 := { available := 328, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 164 26 145 33 328 456 328), lower := (rows 35 70 164 26 145 33 64 128 256), losses := [] }

theorem u19641 : Upper (D 7) (R 7) [34,68,160,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19641 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19642 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 35 70 164 26 145 40 321 449 321), lower := (rows 35 70 164 26 145 40 64 128 256), losses := [] }

theorem u19642 : Upper (D 7) (R 7) [34,68,160,18,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19642 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19643 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 164 26 145 96 329 393 265), lower := (rows 35 70 164 26 145 96 64 128 256), losses := [] }

theorem u19643 : Upper (D 7) (R 7) [34,68,160,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19643 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19644 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 35 70 164 26 145 288 73 201 329), lower := (rows 35 70 164 26 145 288 64 128 256), losses := [] }

theorem u19644 : Upper (D 7) (R 7) [34,68,160,18,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19644 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19645 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 164 26 273 33 200 200 456), lower := (rows 35 70 164 26 273 33 64 128 256), losses := [] }

theorem u19645 : Upper (D 7) (R 7) [34,68,160,18,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19645 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19646 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 35 70 164 26 273 40 193 193 449), lower := (rows 35 70 164 26 273 40 64 128 256), losses := [] }

theorem u19646 : Upper (D 7) (R 7) [34,68,160,18,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19646 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19647 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 164 26 273 96 201 137 393), lower := (rows 35 70 164 26 273 96 64 128 256), losses := [] }

theorem u19647 : Upper (D 7) (R 7) [34,68,160,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19647 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19648 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 35 70 164 26 273 160 73 201 329), lower := (rows 35 70 164 26 273 160 64 128 256), losses := [] }

theorem u19648 : Upper (D 7) (R 7) [34,68,160,18,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19648 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19649 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 164 26 280 33 193 193 449), lower := (rows 35 70 164 26 280 33 64 128 256), losses := [] }

theorem u19649 : Upper (D 7) (R 7) [34,68,160,18,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19649 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19650 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 164 26 280 96 193 129 385), lower := (rows 35 70 164 26 280 96 64 128 256), losses := [] }

theorem u19650 : Upper (D 7) (R 7) [34,68,160,18,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19650 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19651 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 35 70 164 26 280 160 65 193 321), lower := (rows 35 70 164 26 280 160 64 128 256), losses := [] }

theorem u19651 : Upper (D 7) (R 7) [34,68,160,18,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19651 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19652 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 164 26 400 33 73 201 329), lower := (rows 35 70 164 26 400 33 64 128 256), losses := [] }

theorem u19652 : Upper (D 7) (R 7) [34,68,160,18,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19652 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19653 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 35 70 164 26 400 40 65 193 321), lower := (rows 35 70 164 26 400 40 64 128 256), losses := [] }

theorem u19653 : Upper (D 7) (R 7) [34,68,160,18,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19653 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19654 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 164 26 400 96 73 137 265), lower := (rows 35 70 164 26 400 96 64 128 256), losses := [] }

theorem u19654 : Upper (D 7) (R 7) [34,68,160,18,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19654 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19655 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 164 73 145 34 344 408 280), lower := (rows 35 70 164 73 145 34 64 128 256), losses := [] }

theorem u19655 : Upper (D 7) (R 7) [34,68,160,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19655 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19656 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 164 73 145 40 338 402 274), lower := (rows 35 70 164 73 145 40 64 128 256), losses := [] }

theorem u19656 : Upper (D 7) (R 7) [34,68,160,65,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19656 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19657 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 35 70 164 73 145 48 330 394 266), lower := (rows 35 70 164 73 145 48 64 128 256), losses := [] }

theorem u19657 : Upper (D 7) (R 7) [34,68,160,65,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19657 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19658 : Route 9 := (fun mask => (mask,id))

def c19658 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19658 : Upper (D 7) (R 7) [34,68,160,65,129,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,65,129,256] 13 (by decide) (choices 1) [2,8,16] r19658 c19658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5343
  · exact u5344
  · exact u5345

def b19659 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,5),(3,7),(4,5)], upper := (rows 35 70 164 73 152 33 338 402 274), lower := (rows 35 70 164 73 152 33 64 128 256), losses := [] }

theorem u19659 : Upper (D 7) (R 7) [34,68,160,65,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19659 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19660 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 164 73 152 34 337 401 273), lower := (rows 35 70 164 73 152 34 64 128 256), losses := [] }

theorem u19660 : Upper (D 7) (R 7) [34,68,160,65,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19661 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 35 70 164 73 152 48 323 387 259), lower := (rows 35 70 164 73 152 48 64 128 256), losses := [] }

theorem u19661 : Upper (D 7) (R 7) [34,68,160,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19661 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19662 : Route 9 := (fun mask => (mask,id))

def c19662 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19662 : Upper (D 7) (R 7) [34,68,160,65,136,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,65,136,256] 13 (by decide) (choices 1) [1,2,16] r19662 c19662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5346
  · exact u5347
  · exact u5348

def b19663 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 164 73 273 34 216 152 408), lower := (rows 35 70 164 73 273 34 64 128 256), losses := [] }

theorem u19663 : Upper (D 7) (R 7) [34,68,160,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19663 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19664 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 164 73 273 40 210 146 402), lower := (rows 35 70 164 73 273 40 64 128 256), losses := [] }

theorem u19664 : Upper (D 7) (R 7) [34,68,160,65,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19664 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19665 : Route 9 := (fun mask => (mask,id))

def c19665 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u19665 : Upper (D 7) (R 7) [34,68,160,65,257,16] 13 := by
  apply FastRouting.sound _ _ [34,68,160,65,257,16] 13 (by decide) (choices 1) [2,8,128] r19665 c19665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5349
  · exact u5350
  · exact u5351

def b19666 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 35 70 164 73 273 160 90 154 282), lower := (rows 35 70 164 73 273 160 64 128 256), losses := [] }

theorem u19666 : Upper (D 7) (R 7) [34,68,160,65,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19666 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19667 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,5),(3,7),(4,5)], upper := (rows 35 70 164 73 274 33 216 152 408), lower := (rows 35 70 164 73 274 33 64 128 256), losses := [] }

theorem u19667 : Upper (D 7) (R 7) [34,68,160,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19667 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19668 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 164 73 274 40 209 145 401), lower := (rows 35 70 164 73 274 40 64 128 256), losses := [] }

theorem u19668 : Upper (D 7) (R 7) [34,68,160,65,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19668 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19669 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,1),(3,1),(3,5)], upper := (rows 35 70 164 73 274 48 201 137 393), lower := (rows 35 70 164 73 274 48 64 128 256), losses := [] }

theorem u19669 : Upper (D 7) (R 7) [34,68,160,65,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19669 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19670 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 35 70 164 73 274 160 89 153 281), lower := (rows 35 70 164 73 274 160 64 128 256), losses := [] }

theorem u19670 : Upper (D 7) (R 7) [34,68,160,65,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19670 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19671 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,5),(3,7),(4,5)], upper := (rows 35 70 164 73 280 33 210 146 402), lower := (rows 35 70 164 73 280 33 64 128 256), losses := [] }

theorem u19671 : Upper (D 7) (R 7) [34,68,160,65,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19671 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19672 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 164 73 280 34 209 145 401), lower := (rows 35 70 164 73 280 34 64 128 256), losses := [] }

theorem u19672 : Upper (D 7) (R 7) [34,68,160,65,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19672 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19673 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 132, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 164 73 280 48 195 131 387), lower := (rows 35 70 164 73 280 48 64 128 256), losses := [] }

theorem u19673 : Upper (D 7) (R 7) [34,68,160,65,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19673 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19674 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 35 70 164 73 280 160 83 147 275), lower := (rows 35 70 164 73 280 160 64 128 256), losses := [] }

theorem u19674 : Upper (D 7) (R 7) [34,68,160,65,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19674 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19675 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,5),(3,7),(4,5)], upper := (rows 35 70 164 73 400 33 90 154 282), lower := (rows 35 70 164 73 400 33 64 128 256), losses := [] }

theorem u19675 : Upper (D 7) (R 7) [34,68,160,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19675 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19676 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 164 73 400 34 89 153 281), lower := (rows 35 70 164 73 400 34 64 128 256), losses := [] }

theorem u19676 : Upper (D 7) (R 7) [34,68,160,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19676 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19677 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 164 73 400 40 83 147 275), lower := (rows 35 70 164 73 400 40 64 128 256), losses := [] }

theorem u19677 : Upper (D 7) (R 7) [34,68,160,65,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19677 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19678 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 75, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 35 70 164 73 400 48 75 139 267), lower := (rows 35 70 164 73 400 48 64 128 256), losses := [] }

theorem u19678 : Upper (D 7) (R 7) [34,68,160,65,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19678 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19679 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 164 88 145 33 330 394 266), lower := (rows 35 70 164 88 145 33 64 128 256), losses := [] }

theorem u19679 : Upper (D 7) (R 7) [34,68,160,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19679 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u19679
end Delivery.IrregularNine14.P07
