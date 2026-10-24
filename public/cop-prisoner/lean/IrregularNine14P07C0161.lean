import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0012

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9660 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 72, targets := 130 },{ cop := 4, region := 68, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,7)], upper := (rows 37 266 196 104 145 34 65 146 274), lower := (rows 37 266 196 104 145 34 65 128 256), losses := [] }

theorem u9660 : Upper (D 7) (R 7) [36,264,192,96,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9661 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 266 196 104 145 34 66 145 273), lower := (rows 37 266 196 104 145 34 66 128 256), losses := [] }

theorem u9661 : Upper (D 7) (R 7) [36,264,192,96,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9661 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9662 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 266 196 104 145 34 80 131 259), lower := (rows 37 266 196 104 145 34 80 128 256), losses := [] }

theorem u9662 : Upper (D 7) (R 7) [36,264,192,96,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9662 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r9663 : Route 9 := (fun mask => (mask,id))

def c9663 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9663 : Upper (D 7) (R 7) [36,264,192,96,130,2,1] 13 := by
  apply FastRouting.sound _ _ [36,264,192,96,130,2,1] 13 (by decide) (choices 1) [1,16] r9663 c9663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u759
  · exact u760

def b9664 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 266 196 104 146 34 80 129 257), lower := (rows 37 266 196 104 146 34 80 128 256), losses := [] }

theorem u9664 : Upper (D 7) (R 7) [36,264,192,96,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9664 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9665 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 109, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 266 196 104 146 48 65 131 259), lower := (rows 37 266 196 104 146 48 65 128 256), losses := [] }

theorem u9665 : Upper (D 7) (R 7) [36,264,192,96,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9665 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9666 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 3, region := 133, targets := 2 }], pairs := [(0,1),(1,7),(3,7)], upper := (rows 37 266 196 104 146 48 66 129 257), lower := (rows 37 266 196 104 146 48 66 128 256), losses := [] }

theorem u9666 : Upper (D 7) (R 7) [36,264,192,96,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9666 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9667 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 290 13 26 81 160 66 192 448), lower := (rows 37 290 13 26 81 160 66 128 256), losses := [] }

theorem u9667 : Upper (D 7) (R 7) [36,288,9,18,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9667 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9668 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,5)], upper := (rows 37 290 13 26 81 160 192 194 322), lower := (rows 37 290 13 26 81 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 224 224 128 256), good := (rows 117 352 29 24 113 224 224 224 256) },{ target := 5, region := (rows 1 2 4 8 21 0 238 138 266), good := (rows 85 450 477 474 81 192 192 192 256) }] }

theorem u9668 : Upper (D 7) (R 7) [36,288,9,18,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9668 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9669 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 290 13 74 81 160 66 144 400), lower := (rows 37 290 13 74 81 160 66 128 256), losses := [] }

theorem u9669 : Upper (D 7) (R 7) [36,288,9,66,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9670 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 290 13 74 81 160 80 130 386), lower := (rows 37 290 13 74 81 160 80 128 256), losses := [] }

theorem u9670 : Upper (D 7) (R 7) [36,288,9,66,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9670 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9671 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 4, region := 418, targets := 64 }], pairs := [(0,1),(1,0),(1,6),(3,0)], upper := (rows 37 290 13 74 81 160 192 146 274), lower := (rows 37 290 13 74 81 160 192 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 25 224 224 128 256), good := (rows 117 352 29 125 113 224 224 224 256) }] }

theorem u9671 : Upper (D 7) (R 7) [36,288,9,66,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9671 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9672 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 3, region := 181, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 37 290 13 74 145 160 66 208 336), lower := (rows 37 290 13 74 145 160 66 128 256), losses := [] }

theorem u9672 : Upper (D 7) (R 7) [36,288,9,66,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9672 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9673 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(3,0),(4,5)], upper := (rows 37 290 13 74 145 160 80 194 322), lower := (rows 37 290 13 74 145 160 80 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 20 0 85 136 264), good := (rows 85 258 477 458 209 128 80 128 256) }] }

theorem u9673 : Upper (D 7) (R 7) [36,288,9,66,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9673 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9674 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 290 13 74 146 48 65 192 448), lower := (rows 37 290 13 74 146 48 65 128 256), losses := [] }

theorem u9674 : Upper (D 7) (R 7) [36,288,9,66,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9674 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r9675 : Route 9 := (fun mask => (mask,id))

def c9675 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u9675 : Upper (D 7) (R 7) [36,288,9,66,130,16,128] 13 := by
  apply FastRouting.sound _ _ [36,288,9,66,130,16,128] 13 (by decide) (choices 1) [1,64] r9675 c9675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u761
  · exact u762

def b9676 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 6, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 290 13 74 146 160 65 208 336), lower := (rows 37 290 13 74 146 160 65 128 256), losses := [] }

theorem u9676 : Upper (D 7) (R 7) [36,288,9,66,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9676 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9677 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 165, targets := 2 },{ cop := 4, region := 72, targets := 32 }], pairs := [(0,1),(2,1),(3,5)], upper := (rows 37 290 13 74 146 160 80 193 321), lower := (rows 37 290 13 74 146 160 80 128 256), losses := [] }

theorem u9677 : Upper (D 7) (R 7) [36,288,9,66,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9677 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9678 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 290 13 74 208 48 65 130 386), lower := (rows 37 290 13 74 208 48 65 128 256), losses := [] }

theorem u9678 : Upper (D 7) (R 7) [36,288,9,66,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9678 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9679 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 290 13 74 208 48 66 129 385), lower := (rows 37 290 13 74 208 48 66 128 256), losses := [] }

theorem u9679 : Upper (D 7) (R 7) [36,288,9,66,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9679 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9680 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 290 13 74 208 48 192 131 259), lower := (rows 37 290 13 74 208 48 192 128 256), losses := [] }

theorem u9680 : Upper (D 7) (R 7) [36,288,9,66,192,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9680 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9681 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 6, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 290 13 74 208 160 65 146 274), lower := (rows 37 290 13 74 208 160 65 128 256), losses := [] }

theorem u9681 : Upper (D 7) (R 7) [36,288,9,66,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9681 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9682 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 3, region := 181, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 37 290 13 74 208 160 66 145 273), lower := (rows 37 290 13 74 208 160 66 128 256), losses := [] }

theorem u9682 : Upper (D 7) (R 7) [36,288,9,66,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9682 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9683 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 37 290 13 74 208 160 80 131 259), lower := (rows 37 290 13 74 208 160 80 128 256), losses := [] }

theorem u9683 : Upper (D 7) (R 7) [36,288,9,66,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9683 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9684 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 4, region := 136, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 37 290 13 200 82 34 65 144 400), lower := (rows 37 290 13 200 82 34 65 128 256), losses := [] }

theorem u9684 : Upper (D 7) (R 7) [36,288,9,192,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9685 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 290 13 200 82 34 80 129 385), lower := (rows 37 290 13 200 82 34 80 128 256), losses := [] }

theorem u9685 : Upper (D 7) (R 7) [36,288,9,192,66,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9685 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9686 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 290 13 200 82 34 192 145 273), lower := (rows 37 290 13 200 82 34 192 128 256), losses := [] }

theorem u9686 : Upper (D 7) (R 7) [36,288,9,192,66,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9686 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9687 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 290 13 200 82 48 65 130 386), lower := (rows 37 290 13 200 82 48 65 128 256), losses := [] }

theorem u9687 : Upper (D 7) (R 7) [36,288,9,192,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9687 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9688 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 290 13 200 82 48 66 129 385), lower := (rows 37 290 13 200 82 48 66 128 256), losses := [] }

theorem u9688 : Upper (D 7) (R 7) [36,288,9,192,66,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9688 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9689 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 290 13 200 82 48 192 131 259), lower := (rows 37 290 13 200 82 48 192 128 256), losses := [] }

theorem u9689 : Upper (D 7) (R 7) [36,288,9,192,66,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9689 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9690 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 290 14 25 82 160 65 192 448), lower := (rows 37 290 14 25 82 160 65 128 256), losses := [] }

theorem u9690 : Upper (D 7) (R 7) [36,288,10,17,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9691 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(3,5),(4,0),(4,5)], upper := (rows 37 290 14 25 82 160 192 193 321), lower := (rows 37 290 14 25 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 224 224 128 256), good := (rows 100 370 30 24 114 224 224 224 256) },{ target := 5, region := (rows 1 2 4 9 22 0 237 137 265), good := (rows 477 338 478 473 82 192 192 192 256) }] }

theorem u9691 : Upper (D 7) (R 7) [36,288,10,17,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9691 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9692 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 97, targets := 130 },{ cop := 5, region := 402, targets := 1 }], pairs := [(0,1),(0,7),(1,0),(4,0)], upper := (rows 37 290 14 25 208 96 65 130 386), lower := (rows 37 290 14 25 208 96 65 128 256), losses := [] }

theorem u9692 : Upper (D 7) (R 7) [36,288,10,17,192,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9693 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 98, targets := 129 },{ cop := 0, region := 386, targets := 64 },{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(1,7)], upper := (rows 37 290 14 25 208 96 66 129 385), lower := (rows 37 290 14 25 208 96 66 128 256), losses := [] }

theorem u9693 : Upper (D 7) (R 7) [36,288,10,17,192,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9693 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9694 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 290 14 25 208 96 192 131 259), lower := (rows 37 290 14 25 208 96 192 128 256), losses := [] }

theorem u9694 : Upper (D 7) (R 7) [36,288,10,17,192,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9694 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9695 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 290 14 73 82 160 65 144 400), lower := (rows 37 290 14 73 82 160 65 128 256), losses := [] }

theorem u9695 : Upper (D 7) (R 7) [36,288,10,65,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9695 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9696 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 290 14 73 82 160 80 129 385), lower := (rows 37 290 14 73 82 160 80 128 256), losses := [] }

theorem u9696 : Upper (D 7) (R 7) [36,288,10,65,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9696 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9697 : PairBound 9 := { available := 17, camps := [], pairs := [(3,1),(3,5),(4,0),(4,5)], upper := (rows 37 290 14 73 82 160 192 145 273), lower := (rows 37 290 14 73 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 224 224 128 256), good := (rows 100 370 30 104 114 224 224 224 256) },{ target := 1, region := (rows 1 0 4 9 16 224 224 128 256), good := (rows 109 352 12 105 112 224 224 224 256) },{ target := 5, region := (rows 1 2 4 9 22 0 233 129 257), good := (rows 477 338 94 457 82 192 192 192 256) }] }

theorem u9697 : Upper (D 7) (R 7) [36,288,10,65,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9697 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9698 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 3, region := 144, targets := 2 }], pairs := [(0,7),(2,7),(3,7),(4,1)], upper := (rows 37 290 14 73 145 160 66 208 336), lower := (rows 37 290 14 73 145 160 66 128 256), losses := [] }

theorem u9698 : Upper (D 7) (R 7) [36,288,10,65,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9698 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9699 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 422, targets := 1 },{ cop := 4, region := 72, targets := 32 }], pairs := [(1,0),(2,0),(3,5)], upper := (rows 37 290 14 73 145 160 80 194 322), lower := (rows 37 290 14 73 145 160 80 128 256), losses := [] }

theorem u9699 : Upper (D 7) (R 7) [36,288,10,65,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9699 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9700 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 72, targets := 162 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 37 290 14 73 146 160 65 208 336), lower := (rows 37 290 14 73 146 160 65 128 256), losses := [] }

theorem u9700 : Upper (D 7) (R 7) [36,288,10,65,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9700 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9701 : PairBound 9 := { available := 65, camps := [], pairs := [(0,1),(3,5),(4,5)], upper := (rows 37 290 14 73 146 160 80 193 321), lower := (rows 37 290 14 73 146 160 80 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 188 80 136 264), good := (rows 37 288 429 489 240 160 112 160 256) },{ target := 5, region := (rows 1 2 4 9 20 0 85 137 265), good := (rows 477 258 478 457 210 128 80 128 256) }] }

theorem u9701 : Upper (D 7) (R 7) [36,288,10,65,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9701 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9702 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 72, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 37 290 14 73 208 48 65 130 386), lower := (rows 37 290 14 73 208 48 65 128 256), losses := [] }

theorem u9702 : Upper (D 7) (R 7) [36,288,10,65,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9702 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9703 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 290 14 73 208 48 66 129 385), lower := (rows 37 290 14 73 208 48 66 128 256), losses := [] }

theorem u9703 : Upper (D 7) (R 7) [36,288,10,65,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9703 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9704 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 290 14 73 208 48 192 131 259), lower := (rows 37 290 14 73 208 48 192 128 256), losses := [] }

theorem u9704 : Upper (D 7) (R 7) [36,288,10,65,192,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9704 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9705 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 72, targets := 162 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 37 290 14 73 208 160 65 146 274), lower := (rows 37 290 14 73 208 160 65 128 256), losses := [] }

theorem u9705 : Upper (D 7) (R 7) [36,288,10,65,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9705 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9706 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 3, region := 144, targets := 2 }], pairs := [(0,7),(2,7),(3,7),(4,1)], upper := (rows 37 290 14 73 208 160 66 145 273), lower := (rows 37 290 14 73 208 160 66 128 256), losses := [] }

theorem u9706 : Upper (D 7) (R 7) [36,288,10,65,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9706 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9707 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 37 290 14 73 208 160 80 131 259), lower := (rows 37 290 14 73 208 160 80 128 256), losses := [] }

theorem u9707 : Upper (D 7) (R 7) [36,288,10,65,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9707 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9708 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 422, targets := 1 },{ cop := 4, region := 72, targets := 160 }], pairs := [(1,0),(2,0),(3,5),(3,7)], upper := (rows 37 290 14 88 145 160 65 194 322), lower := (rows 37 290 14 88 145 160 65 128 256), losses := [] }

theorem u9708 : Upper (D 7) (R 7) [36,288,10,80,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9708 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9709 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(1,7),(2,7),(3,5),(4,5)], upper := (rows 37 290 14 88 145 160 66 193 321), lower := (rows 37 290 14 88 145 160 66 128 256), losses := [{ target := 5, region := (rows 1 2 4 9 17 0 70 129 257), good := (rows 477 322 78 88 409 128 66 128 256) },{ target := 7, region := (rows 1 3 20 24 16 32 87 0 273), good := (rows 359 354 78 348 351 32 66 0 256) }] }

theorem u9709 : Upper (D 7) (R 7) [36,288,10,80,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9709 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r9710 : Route 9 := (fun mask => (mask,id))

def c9710 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u9710 : Upper (D 7) (R 7) [36,288,10,80,130,128,1] 13 := by
  apply FastRouting.sound _ _ [36,288,10,80,130,128,1] 13 (by decide) (choices 1) [1,64] r9710 c9710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u763
  · exact u764

def b9711 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 113, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 290 14 200 81 48 65 130 386), lower := (rows 37 290 14 200 81 48 65 128 256), losses := [] }

theorem u9711 : Upper (D 7) (R 7) [36,288,10,192,65,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9711 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9712 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 113, targets := 128 },{ cop := 0, region := 386, targets := 64 }], pairs := [(0,7),(1,6),(4,7)], upper := (rows 37 290 14 200 81 48 66 129 385), lower := (rows 37 290 14 200 81 48 66 128 256), losses := [] }

theorem u9712 : Upper (D 7) (R 7) [36,288,10,192,65,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9712 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9713 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 290 14 200 81 48 192 131 259), lower := (rows 37 290 14 200 81 48 192 128 256), losses := [] }

theorem u9713 : Upper (D 7) (R 7) [36,288,10,192,65,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9713 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9714 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 140, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 290 14 200 82 33 65 144 400), lower := (rows 37 290 14 200 82 33 65 128 256), losses := [] }

theorem u9714 : Upper (D 7) (R 7) [36,288,10,192,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9714 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9715 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 80, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 37 290 14 200 82 33 80 129 385), lower := (rows 37 290 14 200 82 33 80 128 256), losses := [] }

theorem u9715 : Upper (D 7) (R 7) [36,288,10,192,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9715 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9716 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 290 14 200 82 33 192 145 273), lower := (rows 37 290 14 200 82 33 192 128 256), losses := [] }

theorem u9716 : Upper (D 7) (R 7) [36,288,10,192,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9716 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9717 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 290 28 11 81 160 66 192 448), lower := (rows 37 290 28 11 81 160 66 128 256), losses := [] }

theorem u9717 : Upper (D 7) (R 7) [36,288,24,3,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9717 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9718 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 212, targets := 32 },{ cop := 0, region := 450, targets := 1 }], pairs := [(1,0),(2,1),(2,5),(4,5)], upper := (rows 37 290 28 11 81 160 192 194 322), lower := (rows 37 290 28 11 81 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 224 224 128 256), good := (rows 117 352 28 29 113 224 224 224 256) }] }

theorem u9718 : Upper (D 7) (R 7) [36,288,24,3,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9718 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9719 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 290 28 11 82 160 65 192 448), lower := (rows 37 290 28 11 82 160 65 128 256), losses := [] }

theorem u9719 : Upper (D 7) (R 7) [36,288,24,3,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9719 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u9719
end Delivery.IrregularNine14.P07
