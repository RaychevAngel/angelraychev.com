import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0076
import IrregularNine14P08C0077

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13620 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 292 137 152 114 114 242 370), lower := (rows 97 7 292 137 152 32 64 128 256), losses := [] }

theorem u13620 : Upper (D 8) (R 8) [96,5,288,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13620 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13621 : Route 9 := (fun mask => (mask,id))

def c13621 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13621 : Upper (D 8) (R 8) [96,5,288,129,160] 13 := by
  apply FastRouting.sound _ _ [96,5,288,129,160] 13 (by decide) (choices 1) [2,8,16,64] r13621 c13621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4590
  · exact u4591
  · exact u4592
  · exact u4593

def r13622 : Route 9 := (fun mask => (mask,id))

def c13622 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13622 : Upper (D 8) (R 8) [96,5,288,129,192] 13 := by
  apply FastRouting.sound _ _ [96,5,288,129,192] 13 (by decide) (choices 1) [2,8,16] r13622 c13622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4594
  · exact u4595
  · exact u4596

def b13623 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 292 138 152 113 113 241 369), lower := (rows 97 7 292 138 152 32 64 128 256), losses := [] }

theorem u13623 : Upper (D 8) (R 8) [96,5,288,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13623 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13624 : Route 9 := (fun mask => (mask,id))

def c13624 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13624 : Upper (D 8) (R 8) [96,5,288,130,160] 13 := by
  apply FastRouting.sound _ _ [96,5,288,130,160] 13 (by decide) (choices 1) [1,8,16,64] r13624 c13624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4597
  · exact u4598
  · exact u4599
  · exact u4600

def r13625 : Route 9 := (fun mask => (mask,id))

def c13625 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13625 : Upper (D 8) (R 8) [96,5,288,130,192] 13 := by
  apply FastRouting.sound _ _ [96,5,288,130,192] 13 (by decide) (choices 1) [1,8,16] r13625 c13625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4601
  · exact u4602
  · exact u4603

def b13626 : PairBound 9 := { available := 99, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 292 152 152 99 99 227 355), lower := (rows 97 7 292 152 152 32 64 128 256), losses := [] }

theorem u13626 : Upper (D 8) (R 8) [96,5,288,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13626 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13627 : PairBound 9 := { available := 75, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 152 176 107 75 203 331), lower := (rows 97 7 292 152 176 32 64 128 256), losses := [] }

theorem u13627 : Upper (D 8) (R 8) [96,5,288,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13627 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13628 : PairBound 9 := { available := 43, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 152 208 43 107 171 299), lower := (rows 97 7 292 152 208 32 64 128 256), losses := [] }

theorem u13628 : Upper (D 8) (R 8) [96,5,288,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13628 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13629 : Route 9 := (fun mask => (mask,id))

def c13629 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13629 : Upper (D 8) (R 8) [96,5,288,160,192] 13 := by
  apply FastRouting.sound _ _ [96,5,288,160,192] 13 (by decide) (choices 1) [1,2,8,16] r13629 c13629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4604
  · exact u4605
  · exact u4606
  · exact u4607

def b13630 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 324 26 56 161 225 161 417), lower := (rows 97 7 324 26 56 32 64 128 256), losses := [] }

theorem u13630 : Upper (D 8) (R 8) [96,5,320,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13630 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13631 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 324 26 145 168 232 168 424), lower := (rows 97 7 324 26 145 32 64 128 256), losses := [] }

theorem u13631 : Upper (D 8) (R 8) [96,5,320,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13631 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13632 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 324 26 152 161 225 161 417), lower := (rows 97 7 324 26 152 32 64 128 256), losses := [] }

theorem u13632 : Upper (D 8) (R 8) [96,5,320,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13632 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13633 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 324 26 176 169 233 169 425), lower := (rows 97 7 324 26 176 32 64 128 256), losses := [] }

theorem u13633 : Upper (D 8) (R 8) [96,5,320,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13633 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13634 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 324 42 145 184 248 184 440), lower := (rows 97 7 324 42 145 32 64 128 256), losses := [] }

theorem u13634 : Upper (D 8) (R 8) [96,5,320,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13634 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13635 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 324 42 152 177 241 177 433), lower := (rows 97 7 324 42 152 32 64 128 256), losses := [] }

theorem u13635 : Upper (D 8) (R 8) [96,5,320,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13635 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13636 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 324 42 176 185 217 153 409), lower := (rows 97 7 324 42 176 32 64 128 256), losses := [] }

theorem u13636 : Upper (D 8) (R 8) [96,5,320,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13636 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13637 : PairBound 9 := { available := 170, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 324 56 145 170 234 170 426), lower := (rows 97 7 324 56 145 32 64 128 256), losses := [] }

theorem u13637 : Upper (D 8) (R 8) [96,5,320,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13637 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13638 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 324 56 146 169 233 169 425), lower := (rows 97 7 324 56 146 32 64 128 256), losses := [] }

theorem u13638 : Upper (D 8) (R 8) [96,5,320,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13638 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13639 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 324 56 152 163 227 163 419), lower := (rows 97 7 324 56 152 32 64 128 256), losses := [] }

theorem u13639 : Upper (D 8) (R 8) [96,5,320,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13639 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13640 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 324 137 146 56 120 184 312), lower := (rows 97 7 324 137 146 32 64 128 256), losses := [] }

theorem u13640 : Upper (D 8) (R 8) [96,5,320,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13640 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13641 : PairBound 9 := { available := 58, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 324 137 176 58 122 186 314), lower := (rows 97 7 324 137 176 32 64 128 256), losses := [] }

theorem u13641 : Upper (D 8) (R 8) [96,5,320,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13641 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13642 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 324 138 176 57 121 185 313), lower := (rows 97 7 324 138 176 32 64 128 256), losses := [] }

theorem u13642 : Upper (D 8) (R 8) [96,5,320,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13642 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13643 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 388 26 49 232 232 232 488), lower := (rows 97 7 388 26 49 32 64 128 256), losses := [] }

theorem u13643 : Upper (D 8) (R 8) [96,5,384,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13643 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13644 : Route 9 := (fun mask => (mask,id))

def c13644 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13644 : Upper (D 8) (R 8) [96,5,384,18,40] 13 := by
  apply FastRouting.sound _ _ [96,5,384,18,40] 13 (by decide) (choices 1) [1,64,128] r13644 c13644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4608
  · exact u4609
  · exact u4610

def b13645 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 388 26 81 168 232 168 424), lower := (rows 97 7 388 26 81 32 64 128 256), losses := [] }

theorem u13645 : Upper (D 8) (R 8) [96,5,384,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13645 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13646 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 388 26 88 161 225 161 417), lower := (rows 97 7 388 26 88 32 64 128 256), losses := [] }

theorem u13646 : Upper (D 8) (R 8) [96,5,384,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13646 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13647 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 388 26 112 169 233 169 425), lower := (rows 97 7 388 26 112 32 64 128 256), losses := [] }

theorem u13647 : Upper (D 8) (R 8) [96,5,384,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13647 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13648 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 388 26 145 104 104 232 360), lower := (rows 97 7 388 26 145 32 64 128 256), losses := [] }

theorem u13648 : Upper (D 8) (R 8) [96,5,384,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13648 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13649 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 388 26 152 97 97 225 353), lower := (rows 97 7 388 26 152 32 64 128 256), losses := [] }

theorem u13649 : Upper (D 8) (R 8) [96,5,384,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13649 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13650 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 388 26 176 105 105 233 361), lower := (rows 97 7 388 26 176 32 64 128 256), losses := [] }

theorem u13650 : Upper (D 8) (R 8) [96,5,384,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13650 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13651 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 388 26 208 41 105 169 297), lower := (rows 97 7 388 26 208 32 64 128 256), losses := [] }

theorem u13651 : Upper (D 8) (R 8) [96,5,384,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13651 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13652 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 388 41 50 248 216 216 472), lower := (rows 97 7 388 41 50 32 64 128 256), losses := [] }

theorem u13652 : Upper (D 8) (R 8) [96,5,384,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13652 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13653 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 388 41 56 242 210 210 466), lower := (rows 97 7 388 41 56 32 64 128 256), losses := [] }

theorem u13653 : Upper (D 8) (R 8) [96,5,384,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13653 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13654 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 388 41 82 184 248 184 440), lower := (rows 97 7 388 41 82 32 64 128 256), losses := [] }

theorem u13654 : Upper (D 8) (R 8) [96,5,384,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13654 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13655 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 8, targets := 128 }], pairs := [(3,7)], upper := (rows 97 7 388 41 88 178 242 178 434), lower := (rows 97 7 388 41 88 32 64 128 256), losses := [] }

theorem u13655 : Upper (D 8) (R 8) [96,5,384,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13655 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13656 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 388 41 152 114 114 242 370), lower := (rows 97 7 388 41 152 32 64 128 256), losses := [] }

theorem u13656 : Upper (D 8) (R 8) [96,5,384,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13656 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13657 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 388 41 176 122 90 218 346), lower := (rows 97 7 388 41 176 32 64 128 256), losses := [] }

theorem u13657 : Upper (D 8) (R 8) [96,5,384,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13657 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13658 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 388 41 208 58 122 186 314), lower := (rows 97 7 388 41 208 32 64 128 256), losses := [] }

theorem u13658 : Upper (D 8) (R 8) [96,5,384,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13658 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13659 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 388 42 56 241 209 209 465), lower := (rows 97 7 388 42 56 32 64 128 256), losses := [] }

theorem u13659 : Upper (D 8) (R 8) [96,5,384,34,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13659 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13660 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 388 42 81 184 248 184 440), lower := (rows 97 7 388 42 81 32 64 128 256), losses := [] }

theorem u13660 : Upper (D 8) (R 8) [96,5,384,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13660 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13661 : Route 9 := (fun mask => (mask,id))

def c13661 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13661 : Upper (D 8) (R 8) [96,5,384,34,72] 13 := by
  apply FastRouting.sound _ _ [96,5,384,34,72] 13 (by decide) (choices 1) [1,16,128] r13661 c13661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4611
  · exact u4612
  · exact u4613

def b13662 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 388 42 112 185 217 153 409), lower := (rows 97 7 388 42 112 32 64 128 256), losses := [] }

theorem u13662 : Upper (D 8) (R 8) [96,5,384,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13662 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13663 : Route 9 := (fun mask => (mask,id))

def c13663 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13663 : Upper (D 8) (R 8) [96,5,384,34,129] 13 := by
  apply FastRouting.sound _ _ [96,5,384,34,129] 13 (by decide) (choices 1) [8,16,64] r13663 c13663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4614
  · exact u4615
  · exact u4616

def b13664 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 388 42 152 113 113 241 369), lower := (rows 97 7 388 42 152 32 64 128 256), losses := [] }

theorem u13664 : Upper (D 8) (R 8) [96,5,384,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13664 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13665 : Route 9 := (fun mask => (mask,id))

def c13665 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13665 : Upper (D 8) (R 8) [96,5,384,34,160] 13 := by
  apply FastRouting.sound _ _ [96,5,384,34,160] 13 (by decide) (choices 1) [1,8,16,64] r13665 c13665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4617
  · exact u4618
  · exact u4619
  · exact u4620

def r13666 : Route 9 := (fun mask => (mask,id))

def c13666 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13666 : Upper (D 8) (R 8) [96,5,384,34,192] 13 := by
  apply FastRouting.sound _ _ [96,5,384,34,192] 13 (by decide) (choices 1) [1,8,16] r13666 c13666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4621
  · exact u4622
  · exact u4623

def b13667 : PairBound 9 := { available := 195, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 388 56 56 227 195 195 451), lower := (rows 97 7 388 56 56 32 64 128 256), losses := [] }

theorem u13667 : Upper (D 8) (R 8) [96,5,384,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13667 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13668 : PairBound 9 := { available := 170, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 388 56 81 170 234 170 426), lower := (rows 97 7 388 56 81 32 64 128 256), losses := [] }

theorem u13668 : Upper (D 8) (R 8) [96,5,384,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13668 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13669 : Route 9 := (fun mask => (mask,id))

def c13669 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13669 : Upper (D 8) (R 8) [96,5,384,48,66] 13 := by
  apply FastRouting.sound _ _ [96,5,384,48,66] 13 (by decide) (choices 1) [1,8,128] r13669 c13669
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4624
  · exact u4625
  · exact u4626

def b13670 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 388 56 88 163 227 163 419), lower := (rows 97 7 388 56 88 32 64 128 256), losses := [] }

theorem u13670 : Upper (D 8) (R 8) [96,5,384,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13670 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13671 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 388 56 112 171 203 139 395), lower := (rows 97 7 388 56 112 32 64 128 256), losses := [] }

theorem u13671 : Upper (D 8) (R 8) [96,5,384,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13671 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13672 : Route 9 := (fun mask => (mask,id))

def c13672 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13672 : Upper (D 8) (R 8) [96,5,384,48,129] 13 := by
  apply FastRouting.sound _ _ [96,5,384,48,129] 13 (by decide) (choices 1) [2,8,64] r13672 c13672
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4627
  · exact u4628
  · exact u4629

def b13673 : PairBound 9 := { available := 105, camps := [{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 388 56 146 105 105 233 361), lower := (rows 97 7 388 56 146 32 64 128 256), losses := [] }

theorem u13673 : Upper (D 8) (R 8) [96,5,384,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13673 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13674 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 388 56 152 99 99 227 355), lower := (rows 97 7 388 56 152 32 64 128 256), losses := [] }

theorem u13674 : Upper (D 8) (R 8) [96,5,384,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13674 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13675 : PairBound 9 := { available := 75, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 388 56 176 107 75 203 331), lower := (rows 97 7 388 56 176 32 64 128 256), losses := [] }

theorem u13675 : Upper (D 8) (R 8) [96,5,384,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13675 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13676 : Route 9 := (fun mask => (mask,id))

def c13676 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13676 : Upper (D 8) (R 8) [96,5,384,48,192] 13 := by
  apply FastRouting.sound _ _ [96,5,384,48,192] 13 (by decide) (choices 1) [1,2,8] r13676 c13676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4630
  · exact u4631
  · exact u4632

def b13677 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 388 73 152 50 114 178 306), lower := (rows 97 7 388 73 152 32 64 128 256), losses := [] }

theorem u13677 : Upper (D 8) (R 8) [96,5,384,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13677 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13678 : PairBound 9 := { available := 58, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 388 73 176 58 122 186 314), lower := (rows 97 7 388 73 176 32 64 128 256), losses := [] }

theorem u13678 : Upper (D 8) (R 8) [96,5,384,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13678 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13679 : Route 9 := (fun mask => (mask,id))

def c13679 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13679 : Upper (D 8) (R 8) [96,5,384,66,129] 13 := by
  apply FastRouting.sound _ _ [96,5,384,66,129] 13 (by decide) (choices 1) [8,16] r13679 c13679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4633
  · exact u4634

#print axioms u13679
end Delivery.IrregularNine14.P08
