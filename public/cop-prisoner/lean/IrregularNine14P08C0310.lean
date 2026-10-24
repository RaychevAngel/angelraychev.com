import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0115

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18600 : PairBound 9 := { available := 45, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 70 152 176 45 109 173 301), lower := (rows 321 35 70 152 176 32 64 128 256), losses := [] }

theorem u18600 : Upper (D 8) (R 8) [320,33,66,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18600 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18601 : PairBound 9 := { available := 29, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 321 35 70 168 176 61 93 157 285), lower := (rows 321 35 70 168 176 32 64 128 256), losses := [] }

theorem u18601 : Upper (D 8) (R 8) [320,33,66,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18601 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18602 : Route 9 := (fun mask => (mask,id))

def c18602 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18602 : Upper (D 8) (R 8) [320,33,72,129,130] 13 := by
  apply FastRouting.sound _ _ [320,33,72,129,130] 13 (by decide) (choices 1) [4,16] r18602 c18602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6919
  · exact u6920

def b18603 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 76 137 148 50 114 178 306), lower := (rows 321 35 76 137 148 32 64 128 256), losses := [] }

theorem u18603 : Upper (D 8) (R 8) [320,33,72,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18603 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18604 : Route 9 := (fun mask => (mask,id))

def c18604 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18604 : Upper (D 8) (R 8) [320,33,72,129,160] 13 := by
  apply FastRouting.sound _ _ [320,33,72,129,160] 13 (by decide) (choices 1) [2,4,16] r18604 c18604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6921
  · exact u6922
  · exact u6923

def r18605 : Route 9 := (fun mask => (mask,id))

def c18605 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18605 : Upper (D 8) (R 8) [320,33,72,130,129] 13 := by
  apply FastRouting.sound _ _ [320,33,72,130,129] 13 (by decide) (choices 1) [4,16] r18605 c18605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6924
  · exact u6925

def b18606 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 76 138 148 49 113 177 305), lower := (rows 321 35 76 138 148 32 64 128 256), losses := [] }

theorem u18606 : Upper (D 8) (R 8) [320,33,72,130,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18606 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18607 : Route 9 := (fun mask => (mask,id))

def c18607 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18607 : Upper (D 8) (R 8) [320,33,72,130,160] 13 := by
  apply FastRouting.sound _ _ [320,33,72,130,160] 13 (by decide) (choices 1) [1,4,16] r18607 c18607
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6926
  · exact u6927
  · exact u6928

def b18608 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 321 35 76 140 145 50 114 178 306), lower := (rows 321 35 76 140 145 32 64 128 256), losses := [] }

theorem u18608 : Upper (D 8) (R 8) [320,33,72,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18608 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18609 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 321 35 76 140 146 49 113 177 305), lower := (rows 321 35 76 140 146 32 64 128 256), losses := [] }

theorem u18609 : Upper (D 8) (R 8) [320,33,72,132,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18609 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18610 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 321 35 76 140 176 51 115 179 307), lower := (rows 321 35 76 140 176 32 64 128 256), losses := [] }

theorem u18610 : Upper (D 8) (R 8) [320,33,72,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18610 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18611 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 76 152 145 38 102 166 294), lower := (rows 321 35 76 152 145 32 64 128 256), losses := [] }

theorem u18611 : Upper (D 8) (R 8) [320,33,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18611 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18612 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 357, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 76 152 146 37 101 165 293), lower := (rows 321 35 76 152 146 32 64 128 256), losses := [] }

theorem u18612 : Upper (D 8) (R 8) [320,33,72,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18612 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18613 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 76 152 148 35 99 163 291), lower := (rows 321 35 76 152 148 32 64 128 256), losses := [] }

theorem u18613 : Upper (D 8) (R 8) [320,33,72,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18613 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18614 : PairBound 9 := { available := 39, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 76 152 176 39 103 167 295), lower := (rows 321 35 76 152 176 32 64 128 256), losses := [] }

theorem u18614 : Upper (D 8) (R 8) [320,33,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18614 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18615 : Route 9 := (fun mask => (mask,id))

def c18615 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18615 : Upper (D 8) (R 8) [320,33,72,160,129] 13 := by
  apply FastRouting.sound _ _ [320,33,72,160,129] 13 (by decide) (choices 1) [2,4,16] r18615 c18615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6929
  · exact u6930
  · exact u6931

def r18616 : Route 9 := (fun mask => (mask,id))

def c18616 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18616 : Upper (D 8) (R 8) [320,33,72,160,130] 13 := by
  apply FastRouting.sound _ _ [320,33,72,160,130] 13 (by decide) (choices 1) [1,4,16] r18616 c18616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6932
  · exact u6933
  · exact u6934

def b18617 : PairBound 9 := { available := 51, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 76 168 148 51 115 179 307), lower := (rows 321 35 76 168 148 32 64 128 256), losses := [] }

theorem u18617 : Upper (D 8) (R 8) [320,33,72,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18617 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18618 : PairBound 9 := { available := 23, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 321 35 76 168 176 55 87 151 279), lower := (rows 321 35 76 168 176 32 64 128 256), losses := [] }

theorem u18618 : Upper (D 8) (R 8) [320,33,72,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18618 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18619 : Route 9 := (fun mask => (mask,id))

def c18619 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18619 : Upper (D 8) (R 8) [320,33,96,129,130] 13 := by
  apply FastRouting.sound _ _ [320,33,96,129,130] 13 (by decide) (choices 1) [4,8,16] r18619 c18619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6935
  · exact u6936
  · exact u6937

def r18620 : Route 9 := (fun mask => (mask,id))

def c18620 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18620 : Upper (D 8) (R 8) [320,33,96,129,132] 13 := by
  apply FastRouting.sound _ _ [320,33,96,129,132] 13 (by decide) (choices 1) [2,8,16] r18620 c18620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6938
  · exact u6939
  · exact u6940

def b18621 : PairBound 9 := { available := 54, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 321 35 100 137 152 54 118 182 310), lower := (rows 321 35 100 137 152 32 64 128 256), losses := [] }

theorem u18621 : Upper (D 8) (R 8) [320,33,96,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18621 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18622 : Route 9 := (fun mask => (mask,id))

def c18622 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18622 : Upper (D 8) (R 8) [320,33,96,129,160] 13 := by
  apply FastRouting.sound _ _ [320,33,96,129,160] 13 (by decide) (choices 1) [2,4,8,16] r18622 c18622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6941
  · exact u6942
  · exact u6943
  · exact u6944

def r18623 : Route 9 := (fun mask => (mask,id))

def c18623 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18623 : Upper (D 8) (R 8) [320,33,96,130,132] 13 := by
  apply FastRouting.sound _ _ [320,33,96,130,132] 13 (by decide) (choices 1) [1,8,16] r18623 c18623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6945
  · exact u6946
  · exact u6947

def b18624 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 321 35 100 138 152 53 117 181 309), lower := (rows 321 35 100 138 152 32 64 128 256), losses := [] }

theorem u18624 : Upper (D 8) (R 8) [320,33,96,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18624 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18625 : Route 9 := (fun mask => (mask,id))

def c18625 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18625 : Upper (D 8) (R 8) [320,33,96,130,160] 13 := by
  apply FastRouting.sound _ _ [320,33,96,130,160] 13 (by decide) (choices 1) [1,4,8,16] r18625 c18625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6948
  · exact u6949
  · exact u6950
  · exact u6951

def b18626 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 321 35 100 140 152 51 115 179 307), lower := (rows 321 35 100 140 152 32 64 128 256), losses := [] }

theorem u18626 : Upper (D 8) (R 8) [320,33,96,132,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18626 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18627 : Route 9 := (fun mask => (mask,id))

def c18627 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18627 : Upper (D 8) (R 8) [320,33,96,132,160] 13 := by
  apply FastRouting.sound _ _ [320,33,96,132,160] 13 (by decide) (choices 1) [1,2,8,16] r18627 c18627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6952
  · exact u6953
  · exact u6954
  · exact u6955

def b18628 : PairBound 9 := { available := 39, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 321 35 100 152 152 39 103 167 295), lower := (rows 321 35 100 152 152 32 64 128 256), losses := [] }

theorem u18628 : Upper (D 8) (R 8) [320,33,96,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18628 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18629 : PairBound 9 := { available := 15, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 100 152 176 47 79 143 271), lower := (rows 321 35 100 152 176 32 64 128 256), losses := [] }

theorem u18629 : Upper (D 8) (R 8) [320,33,96,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18629 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18630 : PairBound 9 := { available := 201, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 38 56 145 233 201 201 457), lower := (rows 321 38 38 56 145 32 64 128 256), losses := [] }

theorem u18630 : Upper (D 8) (R 8) [320,36,34,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18630 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18631 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 38 56 152 225 193 193 449), lower := (rows 321 38 38 56 152 32 64 128 256), losses := [] }

theorem u18631 : Upper (D 8) (R 8) [320,36,34,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18631 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18632 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 38 56 208 169 201 137 393), lower := (rows 321 38 38 56 208 32 64 128 256), losses := [] }

theorem u18632 : Upper (D 8) (R 8) [320,36,34,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18632 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18633 : PairBound 9 := { available := 169, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 38 88 145 169 233 169 425), lower := (rows 321 38 38 88 145 32 64 128 256), losses := [] }

theorem u18633 : Upper (D 8) (R 8) [320,36,34,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18633 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18634 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 38 88 176 169 201 137 393), lower := (rows 321 38 38 88 176 32 64 128 256), losses := [] }

theorem u18634 : Upper (D 8) (R 8) [320,36,34,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18634 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18635 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 38 104 145 185 217 153 409), lower := (rows 321 38 38 104 145 32 64 128 256), losses := [] }

theorem u18635 : Upper (D 8) (R 8) [320,36,34,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18635 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18636 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 38 104 152 177 209 145 401), lower := (rows 321 38 38 104 152 32 64 128 256), losses := [] }

theorem u18636 : Upper (D 8) (R 8) [320,36,34,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18636 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18637 : PairBound 9 := { available := 89, camps := [{ cop := 4, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 38 137 176 121 89 217 345), lower := (rows 321 38 38 137 176 32 64 128 256), losses := [] }

theorem u18637 : Upper (D 8) (R 8) [320,36,34,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18637 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18638 : PairBound 9 := { available := 57, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 38 137 208 57 121 185 313), lower := (rows 321 38 38 137 208 32 64 128 256), losses := [] }

theorem u18638 : Upper (D 8) (R 8) [320,36,34,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18638 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18639 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 38 168 208 57 89 153 281), lower := (rows 321 38 38 168 208 32 64 128 256), losses := [] }

theorem u18639 : Upper (D 8) (R 8) [320,36,34,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18639 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18640 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 56 82 161 193 129 385), lower := (rows 321 38 44 56 82 32 64 128 256), losses := [] }

theorem u18640 : Upper (D 8) (R 8) [320,36,40,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18640 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18641 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 56 145 227 195 195 451), lower := (rows 321 38 44 56 145 32 64 128 256), losses := [] }

theorem u18641 : Upper (D 8) (R 8) [320,36,40,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18641 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18642 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 56 146 225 193 193 449), lower := (rows 321 38 44 56 146 32 64 128 256), losses := [] }

theorem u18642 : Upper (D 8) (R 8) [320,36,40,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18642 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18643 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 56 208 163 195 131 387), lower := (rows 321 38 44 56 208 32 64 128 256), losses := [] }

theorem u18643 : Upper (D 8) (R 8) [320,36,40,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18643 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18644 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 74 145 177 241 177 433), lower := (rows 321 38 44 74 145 32 64 128 256), losses := [] }

theorem u18644 : Upper (D 8) (R 8) [320,36,40,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18644 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18645 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 74 176 177 209 145 401), lower := (rows 321 38 44 74 176 32 64 128 256), losses := [] }

theorem u18645 : Upper (D 8) (R 8) [320,36,40,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18645 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18646 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 88 145 163 227 163 419), lower := (rows 321 38 44 88 145 32 64 128 256), losses := [] }

theorem u18646 : Upper (D 8) (R 8) [320,36,40,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18646 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18647 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 88 146 161 225 161 417), lower := (rows 321 38 44 88 146 32 64 128 256), losses := [] }

theorem u18647 : Upper (D 8) (R 8) [320,36,40,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18647 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18648 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 88 176 163 195 131 387), lower := (rows 321 38 44 88 176 32 64 128 256), losses := [] }

theorem u18648 : Upper (D 8) (R 8) [320,36,40,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18648 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18649 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 104 145 179 211 147 403), lower := (rows 321 38 44 104 145 32 64 128 256), losses := [] }

theorem u18649 : Upper (D 8) (R 8) [320,36,40,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18649 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18650 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 104 146 177 209 145 401), lower := (rows 321 38 44 104 146 32 64 128 256), losses := [] }

theorem u18650 : Upper (D 8) (R 8) [320,36,40,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18650 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18651 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 137 82 177 241 177 433), lower := (rows 321 38 44 137 82 32 64 128 256), losses := [] }

theorem u18651 : Upper (D 8) (R 8) [320,36,40,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18651 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18652 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 137 112 179 211 147 403), lower := (rows 321 38 44 137 112 32 64 128 256), losses := [] }

theorem u18652 : Upper (D 8) (R 8) [320,36,40,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18652 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18653 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 137 146 113 113 241 369), lower := (rows 321 38 44 137 146 32 64 128 256), losses := [] }

theorem u18653 : Upper (D 8) (R 8) [320,36,40,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18653 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18654 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 137 176 115 83 211 339), lower := (rows 321 38 44 137 176 32 64 128 256), losses := [] }

theorem u18654 : Upper (D 8) (R 8) [320,36,40,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18654 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18655 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 137 208 51 115 179 307), lower := (rows 321 38 44 137 208 32 64 128 256), losses := [] }

theorem u18655 : Upper (D 8) (R 8) [320,36,40,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18655 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18656 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 138 112 177 209 145 401), lower := (rows 321 38 44 138 112 32 64 128 256), losses := [] }

theorem u18656 : Upper (D 8) (R 8) [320,36,40,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18656 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18657 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 138 145 113 113 241 369), lower := (rows 321 38 44 138 145 32 64 128 256), losses := [] }

theorem u18657 : Upper (D 8) (R 8) [320,36,40,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18657 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18658 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 14, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 138 176 113 81 209 337), lower := (rows 321 38 44 138 176 32 64 128 256), losses := [] }

theorem u18658 : Upper (D 8) (R 8) [320,36,40,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18658 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18659 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 138 208 49 113 177 305), lower := (rows 321 38 44 138 208 32 64 128 256), losses := [] }

theorem u18659 : Upper (D 8) (R 8) [320,36,40,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18659 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u18659
end Delivery.IrregularNine14.P08
