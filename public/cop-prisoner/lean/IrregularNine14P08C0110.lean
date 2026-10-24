import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0013
import IrregularNine14P08C0014

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6600 : PairBound 9 := { available := 52, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 67 76 168 146 33 116 180 308), lower := (rows 289 67 76 168 146 33 64 128 256), losses := [] }

theorem u6600 : Upper (D 8) (R 8) [288,65,72,160,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6600 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6601 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 289 67 76 168 146 36 113 177 305), lower := (rows 289 67 76 168 146 36 64 128 256), losses := [] }

theorem u6601 : Upper (D 8) (R 8) [288,65,72,160,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6601 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6602 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 289 67 76 168 146 48 101 165 293), lower := (rows 289 67 76 168 146 48 64 128 256), losses := [] }

theorem u6602 : Upper (D 8) (R 8) [288,65,72,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6602 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6603 : PairBound 9 := { available := 28, camps := [], pairs := [], upper := (rows 289 67 100 137 176 34 92 156 284), lower := (rows 289 67 100 137 176 34 64 128 256), losses := [] }

theorem u6603 : Upper (D 8) (R 8) [288,65,96,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6603 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6604 : PairBound 9 := { available := 26, camps := [], pairs := [], upper := (rows 289 67 100 137 176 36 90 154 282), lower := (rows 289 67 100 137 176 36 64 128 256), losses := [] }

theorem u6604 : Upper (D 8) (R 8) [288,65,96,129,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6604 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6605 : PairBound 9 := { available := 56, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 67 100 138 148 33 120 184 312), lower := (rows 289 67 100 138 148 33 64 128 256), losses := [] }

theorem u6605 : Upper (D 8) (R 8) [288,65,96,130,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6605 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6606 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 289 67 100 138 148 40 113 177 305), lower := (rows 289 67 100 138 148 40 64 128 256), losses := [] }

theorem u6606 : Upper (D 8) (R 8) [288,65,96,130,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6606 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6607 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 289 67 100 138 148 48 105 169 297), lower := (rows 289 67 100 138 148 48 64 128 256), losses := [] }

theorem u6607 : Upper (D 8) (R 8) [288,65,96,130,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6607 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6608 : PairBound 9 := { available := 28, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 67 100 138 176 33 92 156 284), lower := (rows 289 67 100 138 176 33 64 128 256), losses := [] }

theorem u6608 : Upper (D 8) (R 8) [288,65,96,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6608 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6609 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 289 67 100 138 176 36 89 153 281), lower := (rows 289 67 100 138 176 36 64 128 256), losses := [] }

theorem u6609 : Upper (D 8) (R 8) [288,65,96,130,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6609 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6610 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 289 67 100 138 176 40 85 149 277), lower := (rows 289 67 100 138 176 40 64 128 256), losses := [] }

theorem u6610 : Upper (D 8) (R 8) [288,65,96,130,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6610 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6611 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 289 67 100 138 176 48 77 141 269), lower := (rows 289 67 100 138 176 48 64 128 256), losses := [] }

theorem u6611 : Upper (D 8) (R 8) [288,65,96,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6611 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6612 : PairBound 9 := { available := 26, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 67 100 140 176 33 90 154 282), lower := (rows 289 67 100 140 176 33 64 128 256), losses := [] }

theorem u6612 : Upper (D 8) (R 8) [288,65,96,132,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6612 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6613 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 289 67 100 140 176 34 89 153 281), lower := (rows 289 67 100 140 176 34 64 128 256), losses := [] }

theorem u6613 : Upper (D 8) (R 8) [288,65,96,132,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6613 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6614 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 289 67 100 140 176 40 83 147 275), lower := (rows 289 67 100 140 176 40 64 128 256), losses := [] }

theorem u6614 : Upper (D 8) (R 8) [288,65,96,132,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6614 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6615 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 289 67 100 140 176 48 75 139 267), lower := (rows 289 67 100 140 176 48 64 128 256), losses := [] }

theorem u6615 : Upper (D 8) (R 8) [288,65,96,132,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6615 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6616 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 70 164 104 152 33 83 147 275), lower := (rows 289 70 164 104 152 33 64 128 256), losses := [] }

theorem u6616 : Upper (D 8) (R 8) [288,68,160,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6616 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6617 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 289 70 164 104 152 34 81 145 273), lower := (rows 289 70 164 104 152 34 64 128 256), losses := [] }

theorem u6617 : Upper (D 8) (R 8) [288,68,160,96,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6617 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6618 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 14 56 208 33 224 160 416), lower := (rows 321 7 14 56 208 33 64 128 256), losses := [] }

theorem u6618 : Upper (D 8) (R 8) [320,5,10,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6618 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6619 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 14 56 208 160 97 161 289), lower := (rows 321 7 14 56 208 160 64 128 256), losses := [] }

theorem u6619 : Upper (D 8) (R 8) [320,5,10,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6619 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6620 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 14 152 112 33 224 160 416), lower := (rows 321 7 14 152 112 33 64 128 256), losses := [] }

theorem u6620 : Upper (D 8) (R 8) [320,5,10,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6620 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6621 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 14 152 112 160 97 161 289), lower := (rows 321 7 14 152 112 160 64 128 256), losses := [] }

theorem u6621 : Upper (D 8) (R 8) [320,5,10,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6621 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6622 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 14 168 112 33 240 176 432), lower := (rows 321 7 14 168 112 33 64 128 256), losses := [] }

theorem u6622 : Upper (D 8) (R 8) [320,5,10,160,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6622 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6623 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 7 14 168 112 48 225 161 417), lower := (rows 321 7 14 168 112 48 64 128 256), losses := [] }

theorem u6623 : Upper (D 8) (R 8) [320,5,10,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6623 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6624 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 14 168 112 160 113 177 305), lower := (rows 321 7 14 168 112 160 64 128 256), losses := [] }

theorem u6624 : Upper (D 8) (R 8) [320,5,10,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6624 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6625 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 28 42 176 33 224 224 480), lower := (rows 321 7 28 42 176 33 64 128 256), losses := [] }

theorem u6625 : Upper (D 8) (R 8) [320,5,24,34,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6625 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6626 : PairBound 9 := { available := 161, camps := [], pairs := [(3,0)], upper := (rows 321 7 28 42 176 96 225 161 417), lower := (rows 321 7 28 42 176 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 97 64 128 256), good := (rows 352 46 28 42 176 96 96 128 256) }] }

theorem u6626 : Upper (D 8) (R 8) [320,5,24,34,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6626 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6627 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 28 42 176 160 97 225 353), lower := (rows 321 7 28 42 176 160 64 128 256), losses := [] }

theorem u6627 : Upper (D 8) (R 8) [320,5,24,34,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6627 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6628 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 38, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 38 56 152 33 224 224 480), lower := (rows 321 7 38 56 152 33 64 128 256), losses := [] }

theorem u6628 : Upper (D 8) (R 8) [320,5,34,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6628 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6629 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 38, targets := 128 }], pairs := [(1,7)], upper := (rows 321 7 38 56 152 96 225 161 417), lower := (rows 321 7 38 56 152 96 64 128 256), losses := [] }

theorem u6629 : Upper (D 8) (R 8) [320,5,34,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6629 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6630 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 38 56 152 160 97 225 353), lower := (rows 321 7 38 56 152 160 64 128 256), losses := [] }

theorem u6630 : Upper (D 8) (R 8) [320,5,34,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6630 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6631 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 38, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 38 56 208 33 232 168 424), lower := (rows 321 7 38 56 208 33 64 128 256), losses := [] }

theorem u6631 : Upper (D 8) (R 8) [320,5,34,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6631 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6632 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 7 38 56 208 40 225 161 417), lower := (rows 321 7 38 56 208 40 64 128 256), losses := [] }

theorem u6632 : Upper (D 8) (R 8) [320,5,34,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6632 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6633 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 38 56 208 160 105 169 297), lower := (rows 321 7 38 56 208 160 64 128 256), losses := [] }

theorem u6633 : Upper (D 8) (R 8) [320,5,34,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6633 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6634 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 38, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 38 88 176 33 232 168 424), lower := (rows 321 7 38 88 176 33 64 128 256), losses := [] }

theorem u6634 : Upper (D 8) (R 8) [320,5,34,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6634 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6635 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 7 38 88 176 40 225 161 417), lower := (rows 321 7 38 88 176 40 64 128 256), losses := [] }

theorem u6635 : Upper (D 8) (R 8) [320,5,34,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6635 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6636 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 329, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 38 88 176 160 105 169 297), lower := (rows 321 7 38 88 176 160 64 128 256), losses := [] }

theorem u6636 : Upper (D 8) (R 8) [320,5,34,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6636 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6637 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 38 104 152 33 240 176 432), lower := (rows 321 7 38 104 152 33 64 128 256), losses := [] }

theorem u6637 : Upper (D 8) (R 8) [320,5,34,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6637 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6638 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 7 38 104 152 48 225 161 417), lower := (rows 321 7 38 104 152 48 64 128 256), losses := [] }

theorem u6638 : Upper (D 8) (R 8) [320,5,34,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6638 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6639 : Route 9 := (fun mask => (mask,id))

def c6639 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6639 : Upper (D 8) (R 8) [320,5,34,96,136,128] 13 := by
  apply FastRouting.sound _ _ [320,5,34,96,136,128] 13 (by decide) (choices 1) [1,16,32] r6639 c6639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u839
  · exact u840
  · exact u841

def b6640 : PairBound 9 := { available := 152, camps := [{ cop := 5, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 38 104 176 33 216 152 408), lower := (rows 321 7 38 104 176 33 64 128 256), losses := [] }

theorem u6640 : Upper (D 8) (R 8) [320,5,34,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6640 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6641 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 321 7 38 104 176 40 209 145 401), lower := (rows 321 7 38 104 176 40 64 128 256), losses := [] }

theorem u6641 : Upper (D 8) (R 8) [320,5,34,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6641 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6642 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 321 7 38 104 176 48 201 137 393), lower := (rows 321 7 38 104 176 48 64 128 256), losses := [] }

theorem u6642 : Upper (D 8) (R 8) [320,5,34,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6642 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6643 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 329, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 38 104 176 160 89 153 281), lower := (rows 321 7 38 104 176 160 64 128 256), losses := [] }

theorem u6643 : Upper (D 8) (R 8) [320,5,34,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6643 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6644 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 38, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 38 168 208 33 120 184 312), lower := (rows 321 7 38 168 208 33 64 128 256), losses := [] }

theorem u6644 : Upper (D 8) (R 8) [320,5,34,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6644 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6645 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 321 7 38 168 208 40 113 177 305), lower := (rows 321 7 38 168 208 40 64 128 256), losses := [] }

theorem u6645 : Upper (D 8) (R 8) [320,5,34,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6645 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6646 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 321 7 38 168 208 48 105 169 297), lower := (rows 321 7 38 168 208 48 64 128 256), losses := [] }

theorem u6646 : Upper (D 8) (R 8) [320,5,34,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6646 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6647 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 44 26 176 33 224 224 480), lower := (rows 321 7 44 26 176 33 64 128 256), losses := [] }

theorem u6647 : Upper (D 8) (R 8) [320,5,40,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6647 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6648 : Route 9 := (fun mask => (mask,id))

def c6648 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u6648 : Upper (D 8) (R 8) [320,5,40,18,160,64] 13 := by
  apply FastRouting.sound _ _ [320,5,40,18,160,64] 13 (by decide) (choices 1) [1,32,128] r6648 c6648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u842
  · exact u843
  · exact u844

def b6649 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 44 26 176 160 97 225 353), lower := (rows 321 7 44 26 176 160 64 128 256), losses := [] }

theorem u6649 : Upper (D 8) (R 8) [320,5,40,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6649 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6650 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 321 7 44 138 49 48 224 224 480), lower := (rows 321 7 44 138 49 48 64 128 256), losses := [] }

theorem u6650 : Upper (D 8) (R 8) [320,5,40,130,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6650 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6651 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 142, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 44 138 49 96 240 176 432), lower := (rows 321 7 44 138 49 96 64 128 256), losses := [] }

theorem u6651 : Upper (D 8) (R 8) [320,5,40,130,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6651 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6652 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 44 138 49 160 112 240 368), lower := (rows 321 7 44 138 49 160 64 128 256), losses := [] }

theorem u6652 : Upper (D 8) (R 8) [320,5,40,130,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6652 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6653 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 321 7 44 138 112 33 240 176 432), lower := (rows 321 7 44 138 112 33 64 128 256), losses := [] }

theorem u6653 : Upper (D 8) (R 8) [320,5,40,130,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6653 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6654 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 7 44 138 112 48 225 161 417), lower := (rows 321 7 44 138 112 48 64 128 256), losses := [] }

theorem u6654 : Upper (D 8) (R 8) [320,5,40,130,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6654 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6655 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 44 138 112 160 113 177 305), lower := (rows 321 7 44 138 112 160 64 128 256), losses := [] }

theorem u6655 : Upper (D 8) (R 8) [320,5,40,130,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6655 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6656 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 321 7 44 152 49 34 224 224 480), lower := (rows 321 7 44 152 49 34 64 128 256), losses := [] }

theorem u6656 : Upper (D 8) (R 8) [320,5,40,144,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6656 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6657 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 142, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 44 152 49 96 226 162 418), lower := (rows 321 7 44 152 49 96 64 128 256), losses := [] }

theorem u6657 : Upper (D 8) (R 8) [320,5,40,144,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6657 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6658 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 44 152 49 160 98 226 354), lower := (rows 321 7 44 152 49 160 64 128 256), losses := [] }

theorem u6658 : Upper (D 8) (R 8) [320,5,40,144,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6658 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6659 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 44 152 50 33 224 224 480), lower := (rows 321 7 44 152 50 33 64 128 256), losses := [] }

theorem u6659 : Upper (D 8) (R 8) [320,5,40,144,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6659 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u6659
end Delivery.IrregularNine14.P08
