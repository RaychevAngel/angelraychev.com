import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0115
import IrregularNine14P08C0116

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18660 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 152 82 161 225 161 417), lower := (rows 321 38 44 152 82 32 64 128 256), losses := [] }

theorem u18660 : Upper (D 8) (R 8) [320,36,40,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18660 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18661 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 152 112 163 195 131 387), lower := (rows 321 38 44 152 112 32 64 128 256), losses := [] }

theorem u18661 : Upper (D 8) (R 8) [320,36,40,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18661 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18662 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 168 82 177 209 145 401), lower := (rows 321 38 44 168 82 32 64 128 256), losses := [] }

theorem u18662 : Upper (D 8) (R 8) [320,36,40,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18662 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18663 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 168 145 115 83 211 339), lower := (rows 321 38 44 168 145 32 64 128 256), losses := [] }

theorem u18663 : Upper (D 8) (R 8) [320,36,40,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18663 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18664 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 168 146 113 81 209 337), lower := (rows 321 38 44 168 146 32 64 128 256), losses := [] }

theorem u18664 : Upper (D 8) (R 8) [320,36,40,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18664 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18665 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 168 208 51 83 147 275), lower := (rows 321 38 44 168 208 32 64 128 256), losses := [] }

theorem u18665 : Upper (D 8) (R 8) [320,36,40,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18665 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18666 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 200 145 51 115 179 307), lower := (rows 321 38 44 200 145 32 64 128 256), losses := [] }

theorem u18666 : Upper (D 8) (R 8) [320,36,40,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18666 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18667 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 200 146 49 113 177 305), lower := (rows 321 38 44 200 146 32 64 128 256), losses := [] }

theorem u18667 : Upper (D 8) (R 8) [320,36,40,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18667 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18668 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 200 176 51 83 147 275), lower := (rows 321 38 44 200 176 32 64 128 256), losses := [] }

theorem u18668 : Upper (D 8) (R 8) [320,36,40,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18668 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18669 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 186, targets := 64 }], pairs := [(1,6)], upper := (rows 321 38 69 56 145 170 234 170 426), lower := (rows 321 38 69 56 145 32 64 128 256), losses := [] }

theorem u18669 : Upper (D 8) (R 8) [320,36,65,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18669 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18670 : PairBound 9 := { available := 169, camps := [{ cop := 2, region := 186, targets := 64 }], pairs := [(1,6)], upper := (rows 321 38 69 56 146 169 233 169 425), lower := (rows 321 38 69 56 146 32 64 128 256), losses := [] }

theorem u18670 : Upper (D 8) (R 8) [320,36,65,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18670 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18671 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 321 38 69 56 152 163 227 163 419), lower := (rows 321 38 69 56 152 32 64 128 256), losses := [] }

theorem u18671 : Upper (D 8) (R 8) [320,36,65,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18671 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18672 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 186, targets := 64 }], pairs := [(1,6)], upper := (rows 321 38 69 137 146 56 120 184 312), lower := (rows 321 38 69 137 146 32 64 128 256), losses := [] }

theorem u18672 : Upper (D 8) (R 8) [320,36,65,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18672 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18673 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 186, targets := 64 }], pairs := [(1,6)], upper := (rows 321 38 69 137 176 58 122 186 314), lower := (rows 321 38 69 137 176 32 64 128 256), losses := [] }

theorem u18673 : Upper (D 8) (R 8) [320,36,65,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18673 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18674 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 186, targets := 64 }], pairs := [(1,6)], upper := (rows 321 38 69 138 176 57 121 185 313), lower := (rows 321 38 69 138 176 32 64 128 256), losses := [] }

theorem u18674 : Upper (D 8) (R 8) [320,36,65,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18674 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18675 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 38 70 56 145 169 233 169 425), lower := (rows 321 38 70 56 145 32 64 128 256), losses := [] }

theorem u18675 : Upper (D 8) (R 8) [320,36,66,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18675 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18676 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 38 70 56 152 161 225 161 417), lower := (rows 321 38 70 56 152 32 64 128 256), losses := [] }

theorem u18676 : Upper (D 8) (R 8) [320,36,66,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18676 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18677 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 38 70 137 176 57 121 185 313), lower := (rows 321 38 70 137 176 32 64 128 256), losses := [] }

theorem u18677 : Upper (D 8) (R 8) [320,36,66,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18677 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18678 : Route 9 := (fun mask => (mask,id))

def c18678 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18678 : Upper (D 8) (R 8) [320,36,72,48,129] 13 := by
  apply FastRouting.sound _ _ [320,36,72,48,129] 13 (by decide) (choices 1) [1,2,128] r18678 c18678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6956
  · exact u6957
  · exact u6958

def r18679 : Route 9 := (fun mask => (mask,id))

def c18679 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18679 : Upper (D 8) (R 8) [320,36,72,48,130] 13 := by
  apply FastRouting.sound _ _ [320,36,72,48,130] 13 (by decide) (choices 1) [1,128] r18679 c18679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6959
  · exact u6960

def b18680 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 321 38 76 56 176 163 195 131 387), lower := (rows 321 38 76 56 176 32 64 128 256), losses := [] }

theorem u18680 : Upper (D 8) (R 8) [320,36,72,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18680 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18681 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 321 38 76 137 145 50 114 178 306), lower := (rows 321 38 76 137 145 32 64 128 256), losses := [] }

theorem u18681 : Upper (D 8) (R 8) [320,36,72,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18681 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18682 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 76 137 146 49 113 177 305), lower := (rows 321 38 76 137 146 32 64 128 256), losses := [] }

theorem u18682 : Upper (D 8) (R 8) [320,36,72,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18682 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18683 : Route 9 := (fun mask => (mask,id))

def c18683 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18683 : Upper (D 8) (R 8) [320,36,72,129,160] 13 := by
  apply FastRouting.sound _ _ [320,36,72,129,160] 13 (by decide) (choices 1) [1,2,16] r18683 c18683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6961
  · exact u6962
  · exact u6963

def b18684 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 38 76 138 145 49 113 177 305), lower := (rows 321 38 76 138 145 32 64 128 256), losses := [] }

theorem u18684 : Upper (D 8) (R 8) [320,36,72,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18684 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18685 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 38 76 138 176 49 113 177 305), lower := (rows 321 38 76 138 176 32 64 128 256), losses := [] }

theorem u18685 : Upper (D 8) (R 8) [320,36,72,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18685 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18686 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 76 152 145 35 99 163 291), lower := (rows 321 38 76 152 145 32 64 128 256), losses := [] }

theorem u18686 : Upper (D 8) (R 8) [320,36,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18686 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18687 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 76 152 146 33 97 161 289), lower := (rows 321 38 76 152 146 32 64 128 256), losses := [] }

theorem u18687 : Upper (D 8) (R 8) [320,36,72,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18687 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18688 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 76 152 176 35 99 163 291), lower := (rows 321 38 76 152 176 32 64 128 256), losses := [] }

theorem u18688 : Upper (D 8) (R 8) [320,36,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18688 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18689 : Route 9 := (fun mask => (mask,id))

def c18689 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18689 : Upper (D 8) (R 8) [320,36,72,160,129] 13 := by
  apply FastRouting.sound _ _ [320,36,72,160,129] 13 (by decide) (choices 1) [1,2,16] r18689 c18689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6964
  · exact u6965
  · exact u6966

def b18690 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 76 168 146 49 113 177 305), lower := (rows 321 38 76 168 146 32 64 128 256), losses := [] }

theorem u18690 : Upper (D 8) (R 8) [320,36,72,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18690 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18691 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 321 38 76 168 176 51 83 147 275), lower := (rows 321 38 76 168 176 32 64 128 256), losses := [] }

theorem u18691 : Upper (D 8) (R 8) [320,36,72,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18691 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18692 : PairBound 9 := { available := 139, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 100 56 145 171 203 139 395), lower := (rows 321 38 100 56 145 32 64 128 256), losses := [] }

theorem u18692 : Upper (D 8) (R 8) [320,36,96,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18692 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18693 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 100 56 146 169 201 137 393), lower := (rows 321 38 100 56 146 32 64 128 256), losses := [] }

theorem u18693 : Upper (D 8) (R 8) [320,36,96,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18693 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18694 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 100 56 152 163 195 131 387), lower := (rows 321 38 100 56 152 32 64 128 256), losses := [] }

theorem u18694 : Upper (D 8) (R 8) [320,36,96,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18694 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18695 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 100 137 146 57 121 185 313), lower := (rows 321 38 100 137 146 32 64 128 256), losses := [] }

theorem u18695 : Upper (D 8) (R 8) [320,36,96,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18695 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18696 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 100 137 176 59 91 155 283), lower := (rows 321 38 100 137 176 32 64 128 256), losses := [] }

theorem u18696 : Upper (D 8) (R 8) [320,36,96,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18696 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18697 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 100 138 176 57 89 153 281), lower := (rows 321 38 100 138 176 32 64 128 256), losses := [] }

theorem u18697 : Upper (D 8) (R 8) [320,36,96,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18697 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18698 : PairBound 9 := { available := 106, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 321 38 133 56 145 106 106 234 362), lower := (rows 321 38 133 56 145 32 64 128 256), losses := [] }

theorem u18698 : Upper (D 8) (R 8) [320,36,129,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18698 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18699 : PairBound 9 := { available := 105, camps := [{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 133 56 146 105 105 233 361), lower := (rows 321 38 133 56 146 32 64 128 256), losses := [] }

theorem u18699 : Upper (D 8) (R 8) [320,36,129,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18699 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18700 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 133 56 152 99 99 227 355), lower := (rows 321 38 133 56 152 32 64 128 256), losses := [] }

theorem u18700 : Upper (D 8) (R 8) [320,36,129,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18700 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18701 : PairBound 9 := { available := 75, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 321 38 133 56 176 107 75 203 331), lower := (rows 321 38 133 56 176 32 64 128 256), losses := [] }

theorem u18701 : Upper (D 8) (R 8) [320,36,129,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18701 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18702 : Route 9 := (fun mask => (mask,id))

def c18702 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18702 : Upper (D 8) (R 8) [320,36,129,48,192] 13 := by
  apply FastRouting.sound _ _ [320,36,129,48,192] 13 (by decide) (choices 1) [1,2,8] r18702 c18702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6967
  · exact u6968
  · exact u6969

def b18703 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 38 133 73 152 50 114 178 306), lower := (rows 321 38 133 73 152 32 64 128 256), losses := [] }

theorem u18703 : Upper (D 8) (R 8) [320,36,129,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18703 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18704 : PairBound 9 := { available := 58, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 38 133 73 176 58 122 186 314), lower := (rows 321 38 133 73 176 32 64 128 256), losses := [] }

theorem u18704 : Upper (D 8) (R 8) [320,36,129,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18704 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18705 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 321 38 133 74 145 56 120 184 312), lower := (rows 321 38 133 74 145 32 64 128 256), losses := [] }

theorem u18705 : Upper (D 8) (R 8) [320,36,129,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18705 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18706 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 133 74 152 49 113 177 305), lower := (rows 321 38 133 74 152 32 64 128 256), losses := [] }

theorem u18706 : Upper (D 8) (R 8) [320,36,129,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18706 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18707 : Route 9 := (fun mask => (mask,id))

def c18707 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18707 : Upper (D 8) (R 8) [320,36,129,66,160] 13 := by
  apply FastRouting.sound _ _ [320,36,129,66,160] 13 (by decide) (choices 1) [1,8,16] r18707 c18707
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6970
  · exact u6971
  · exact u6972

def b18708 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 321 38 133 88 145 42 106 170 298), lower := (rows 321 38 133 88 145 32 64 128 256), losses := [] }

theorem u18708 : Upper (D 8) (R 8) [320,36,129,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18708 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18709 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 133 88 146 41 105 169 297), lower := (rows 321 38 133 88 146 32 64 128 256), losses := [] }

theorem u18709 : Upper (D 8) (R 8) [320,36,129,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18709 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18710 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 321 38 133 88 152 35 99 163 291), lower := (rows 321 38 133 88 152 32 64 128 256), losses := [] }

theorem u18710 : Upper (D 8) (R 8) [320,36,129,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18710 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18711 : Route 9 := (fun mask => (mask,id))

def c18711 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18711 : Upper (D 8) (R 8) [320,36,129,80,160] 13 := by
  apply FastRouting.sound _ _ [320,36,129,80,160] 13 (by decide) (choices 1) [1,2,8] r18711 c18711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6973
  · exact u6974
  · exact u6975

def b18712 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 321 38 133 104 145 58 122 186 314), lower := (rows 321 38 133 104 145 32 64 128 256), losses := [] }

theorem u18712 : Upper (D 8) (R 8) [320,36,129,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18712 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18713 : PairBound 9 := { available := 57, camps := [{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 133 104 146 57 121 185 313), lower := (rows 321 38 133 104 146 32 64 128 256), losses := [] }

theorem u18713 : Upper (D 8) (R 8) [320,36,129,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18713 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18714 : Route 9 := (fun mask => (mask,id))

def c18714 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18714 : Upper (D 8) (R 8) [320,36,129,96,136] 13 := by
  apply FastRouting.sound _ _ [320,36,129,96,136] 13 (by decide) (choices 1) [1,2,16] r18714 c18714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6976
  · exact u6977
  · exact u6978

def r18715 : Route 9 := (fun mask => (mask,id))

def c18715 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18715 : Upper (D 8) (R 8) [320,36,129,96,160] 13 := by
  apply FastRouting.sound _ _ [320,36,129,96,160] 13 (by decide) (choices 1) [1,2,8,16] r18715 c18715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6979
  · exact u6980
  · exact u6981
  · exact u6982

def b18716 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 134 56 152 97 97 225 353), lower := (rows 321 38 134 56 152 32 64 128 256), losses := [] }

theorem u18716 : Upper (D 8) (R 8) [320,36,130,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18716 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18717 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 134 56 176 105 73 201 329), lower := (rows 321 38 134 56 176 32 64 128 256), losses := [] }

theorem u18717 : Upper (D 8) (R 8) [320,36,130,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18717 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18718 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 297, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 134 56 208 41 105 169 297), lower := (rows 321 38 134 56 208 32 64 128 256), losses := [] }

theorem u18718 : Upper (D 8) (R 8) [320,36,130,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18718 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18719 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 134 88 145 41 105 169 297), lower := (rows 321 38 134 88 145 32 64 128 256), losses := [] }

theorem u18719 : Upper (D 8) (R 8) [320,36,130,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18719 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u18719
end Delivery.IrregularNine14.P08
