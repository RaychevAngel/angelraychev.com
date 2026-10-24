import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0083
import IrregularNine14P08C0084

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14640 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 133 104 400 59 91 155 283), lower := (rows 97 38 133 104 400 32 64 128 256), losses := [] }

theorem u14640 : Upper (D 8) (R 8) [96,36,129,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14640 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14641 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 97 38 133 137 274 120 120 248 376), lower := (rows 97 38 133 137 274 32 64 128 256), losses := [] }

theorem u14641 : Upper (D 8) (R 8) [96,36,129,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14641 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14642 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 97 38 133 137 280 114 114 242 370), lower := (rows 97 38 133 137 280 32 64 128 256), losses := [] }

theorem u14642 : Upper (D 8) (R 8) [96,36,129,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14642 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14643 : PairBound 9 := { available := 90, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 97 38 133 137 304 122 90 218 346), lower := (rows 97 38 133 137 304 32 64 128 256), losses := [] }

theorem u14643 : Upper (D 8) (R 8) [96,36,129,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14643 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14644 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 97 38 133 137 336 58 122 186 314), lower := (rows 97 38 133 137 336 32 64 128 256), losses := [] }

theorem u14644 : Upper (D 8) (R 8) [96,36,129,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14644 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14645 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 138 273 120 120 248 376), lower := (rows 97 38 133 138 273 32 64 128 256), losses := [] }

theorem u14645 : Upper (D 8) (R 8) [96,36,129,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14645 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14646 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 138 280 113 113 241 369), lower := (rows 97 38 133 138 280 32 64 128 256), losses := [] }

theorem u14646 : Upper (D 8) (R 8) [96,36,129,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14646 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14647 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 138 304 121 89 217 345), lower := (rows 97 38 133 138 304 32 64 128 256), losses := [] }

theorem u14647 : Upper (D 8) (R 8) [96,36,129,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14647 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14648 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 138 336 57 121 185 313), lower := (rows 97 38 133 138 336 32 64 128 256), losses := [] }

theorem u14648 : Upper (D 8) (R 8) [96,36,129,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14648 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14649 : Route 9 := (fun mask => (mask,id))

def c14649 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14649 : Upper (D 8) (R 8) [96,36,129,144,257] 13 := by
  apply FastRouting.sound _ _ [96,36,129,144,257] 13 (by decide) (choices 1) [2,8,64] r14649 c14649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4995
  · exact u4996
  · exact u4997

def b14650 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 152 274 105 105 233 361), lower := (rows 97 38 133 152 274 32 64 128 256), losses := [] }

theorem u14650 : Upper (D 8) (R 8) [96,36,129,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14650 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14651 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 152 280 99 99 227 355), lower := (rows 97 38 133 152 280 32 64 128 256), losses := [] }

theorem u14651 : Upper (D 8) (R 8) [96,36,129,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14651 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14652 : Route 9 := (fun mask => (mask,id))

def c14652 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14652 : Upper (D 8) (R 8) [96,36,129,144,288] 13 := by
  apply FastRouting.sound _ _ [96,36,129,144,288] 13 (by decide) (choices 1) [1,2,8,64] r14652 c14652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4998
  · exact u4999
  · exact u5000
  · exact u5001

def r14653 : Route 9 := (fun mask => (mask,id))

def c14653 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14653 : Upper (D 8) (R 8) [96,36,129,144,320] 13 := by
  apply FastRouting.sound _ _ [96,36,129,144,320] 13 (by decide) (choices 1) [1,2,8] r14653 c14653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5002
  · exact u5003
  · exact u5004

def r14654 : Route 9 := (fun mask => (mask,id))

def c14654 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14654 : Upper (D 8) (R 8) [96,36,129,160,257] 13 := by
  apply FastRouting.sound _ _ [96,36,129,160,257] 13 (by decide) (choices 1) [2,8,16,64] r14654 c14654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5005
  · exact u5006
  · exact u5007
  · exact u5008

def r14655 : Route 9 := (fun mask => (mask,id))

def c14655 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14655 : Upper (D 8) (R 8) [96,36,129,160,258] 13 := by
  apply FastRouting.sound _ _ [96,36,129,160,258] 13 (by decide) (choices 1) [1,8,16,64] r14655 c14655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5009
  · exact u5010
  · exact u5011
  · exact u5012

def r14656 : Route 9 := (fun mask => (mask,id))

def c14656 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14656 : Upper (D 8) (R 8) [96,36,129,160,264] 13 := by
  apply FastRouting.sound _ _ [96,36,129,160,264] 13 (by decide) (choices 1) [1,2,16,64] r14656 c14656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5013
  · exact u5014
  · exact u5015
  · exact u5016

def r14657 : Route 9 := (fun mask => (mask,id))

def c14657 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14657 : Upper (D 8) (R 8) [96,36,129,160,320] 13 := by
  apply FastRouting.sound _ _ [96,36,129,160,320] 13 (by decide) (choices 1) [1,2,8,16] r14657 c14657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5017
  · exact u5018
  · exact u5019
  · exact u5020

def r14658 : Route 9 := (fun mask => (mask,id))

def c14658 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14658 : Upper (D 8) (R 8) [96,36,129,192,257] 13 := by
  apply FastRouting.sound _ _ [96,36,129,192,257] 13 (by decide) (choices 1) [2,8,16] r14658 c14658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5021
  · exact u5022
  · exact u5023

def r14659 : Route 9 := (fun mask => (mask,id))

def c14659 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14659 : Upper (D 8) (R 8) [96,36,129,192,258] 13 := by
  apply FastRouting.sound _ _ [96,36,129,192,258] 13 (by decide) (choices 1) [1,8,16] r14659 c14659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5024
  · exact u5025
  · exact u5026

def r14660 : Route 9 := (fun mask => (mask,id))

def c14660 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14660 : Upper (D 8) (R 8) [96,36,129,192,264] 13 := by
  apply FastRouting.sound _ _ [96,36,129,192,264] 13 (by decide) (choices 1) [1,2,16] r14660 c14660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5027
  · exact u5028
  · exact u5029

def r14661 : Route 9 := (fun mask => (mask,id))

def c14661 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14661 : Upper (D 8) (R 8) [96,36,129,192,288] 13 := by
  apply FastRouting.sound _ _ [96,36,129,192,288] 13 (by decide) (choices 1) [1,2,8,16] r14661 c14661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5030
  · exact u5031
  · exact u5032
  · exact u5033

def b14662 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 134 56 152 353 321 449 321), lower := (rows 97 38 134 56 152 32 64 128 256), losses := [] }

theorem u14662 : Upper (D 8) (R 8) [96,36,130,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14662 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14663 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 297, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 134 56 208 297 329 393 265), lower := (rows 97 38 134 56 208 32 64 128 256), losses := [] }

theorem u14663 : Upper (D 8) (R 8) [96,36,130,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14663 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14664 : Route 9 := (fun mask => (mask,id))

def c14664 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14664 : Upper (D 8) (R 8) [96,36,130,48,257] 13 := by
  apply FastRouting.sound _ _ [96,36,130,48,257] 13 (by decide) (choices 1) [1,8,64,128] r14664 c14664
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5034
  · exact u5035
  · exact u5036
  · exact u5037

def r14665 : Route 9 := (fun mask => (mask,id))

def c14665 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14665 : Upper (D 8) (R 8) [96,36,130,48,264] 13 := by
  apply FastRouting.sound _ _ [96,36,130,48,264] 13 (by decide) (choices 1) [1,64,128] r14665 c14665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5038
  · exact u5039
  · exact u5040

def r14666 : Route 9 := (fun mask => (mask,id))

def c14666 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14666 : Upper (D 8) (R 8) [96,36,130,48,320] 13 := by
  apply FastRouting.sound _ _ [96,36,130,48,320] 13 (by decide) (choices 1) [1,8,128] r14666 c14666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5041
  · exact u5042
  · exact u5043

def b14667 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 134 56 400 105 73 201 329), lower := (rows 97 38 134 56 400 32 64 128 256), losses := [] }

theorem u14667 : Upper (D 8) (R 8) [96,36,130,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14667 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14668 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 134 73 273 184 248 184 440), lower := (rows 97 38 134 73 273 32 64 128 256), losses := [] }

theorem u14668 : Upper (D 8) (R 8) [96,36,130,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14668 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14669 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 134 73 280 177 241 177 433), lower := (rows 97 38 134 73 280 32 64 128 256), losses := [] }

theorem u14669 : Upper (D 8) (R 8) [96,36,130,65,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14669 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14670 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 134 73 304 185 217 153 409), lower := (rows 97 38 134 73 304 32 64 128 256), losses := [] }

theorem u14670 : Upper (D 8) (R 8) [96,36,130,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14670 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14671 : PairBound 9 := { available := 297, camps := [{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 134 88 145 297 361 425 297), lower := (rows 97 38 134 88 145 32 64 128 256), losses := [] }

theorem u14671 : Upper (D 8) (R 8) [96,36,130,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14671 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14672 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 134 88 152 289 353 417 289), lower := (rows 97 38 134 88 152 32 64 128 256), losses := [] }

theorem u14672 : Upper (D 8) (R 8) [96,36,130,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14672 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14673 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 134 88 176 297 329 393 265), lower := (rows 97 38 134 88 176 32 64 128 256), losses := [] }

theorem u14673 : Upper (D 8) (R 8) [96,36,130,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14673 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14674 : Route 9 := (fun mask => (mask,id))

def c14674 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14674 : Upper (D 8) (R 8) [96,36,130,80,257] 13 := by
  apply FastRouting.sound _ _ [96,36,130,80,257] 13 (by decide) (choices 1) [1,8,128] r14674 c14674
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5044
  · exact u5045
  · exact u5046

def b14675 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 134, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 134 88 280 161 225 161 417), lower := (rows 97 38 134 88 280 32 64 128 256), losses := [] }

theorem u14675 : Upper (D 8) (R 8) [96,36,130,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14675 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14676 : Route 9 := (fun mask => (mask,id))

def c14676 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14676 : Upper (D 8) (R 8) [96,36,130,80,288] 13 := by
  apply FastRouting.sound _ _ [96,36,130,80,288] 13 (by decide) (choices 1) [1,8,128] r14676 c14676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5047
  · exact u5048
  · exact u5049

def b14677 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 134 88 400 41 105 169 297), lower := (rows 97 38 134 88 400 32 64 128 256), losses := [] }

theorem u14677 : Upper (D 8) (R 8) [96,36,130,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14677 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14678 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 134 104 273 185 217 153 409), lower := (rows 97 38 134 104 273 32 64 128 256), losses := [] }

theorem u14678 : Upper (D 8) (R 8) [96,36,130,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14678 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14679 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 134 104 280 177 209 145 401), lower := (rows 97 38 134 104 280 32 64 128 256), losses := [] }

theorem u14679 : Upper (D 8) (R 8) [96,36,130,96,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14679 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14680 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 134 137 273 120 120 248 376), lower := (rows 97 38 134 137 273 32 64 128 256), losses := [] }

theorem u14680 : Upper (D 8) (R 8) [96,36,130,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14680 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14681 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 134 137 280 113 113 241 369), lower := (rows 97 38 134 137 280 32 64 128 256), losses := [] }

theorem u14681 : Upper (D 8) (R 8) [96,36,130,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14681 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14682 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 134 137 304 121 89 217 345), lower := (rows 97 38 134 137 304 32 64 128 256), losses := [] }

theorem u14682 : Upper (D 8) (R 8) [96,36,130,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14682 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14683 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 134 137 336 57 121 185 313), lower := (rows 97 38 134 137 336 32 64 128 256), losses := [] }

theorem u14683 : Upper (D 8) (R 8) [96,36,130,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14683 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14684 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 134 152 273 105 105 233 361), lower := (rows 97 38 134 152 273 32 64 128 256), losses := [] }

theorem u14684 : Upper (D 8) (R 8) [96,36,130,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14684 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14685 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 134 152 280 97 97 225 353), lower := (rows 97 38 134 152 280 32 64 128 256), losses := [] }

theorem u14685 : Upper (D 8) (R 8) [96,36,130,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14685 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14686 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 134 152 304 105 73 201 329), lower := (rows 97 38 134 152 304 32 64 128 256), losses := [] }

theorem u14686 : Upper (D 8) (R 8) [96,36,130,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14686 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14687 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 134 152 336 41 105 169 297), lower := (rows 97 38 134 152 336 32 64 128 256), losses := [] }

theorem u14687 : Upper (D 8) (R 8) [96,36,130,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14687 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14688 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 134 168 273 121 89 217 345), lower := (rows 97 38 134 168 273 32 64 128 256), losses := [] }

theorem u14688 : Upper (D 8) (R 8) [96,36,130,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14688 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14689 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 134 168 280 113 81 209 337), lower := (rows 97 38 134 168 280 32 64 128 256), losses := [] }

theorem u14689 : Upper (D 8) (R 8) [96,36,130,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14689 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14690 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 134 168 336 57 89 153 281), lower := (rows 97 38 134 168 336 32 64 128 256), losses := [] }

theorem u14690 : Upper (D 8) (R 8) [96,36,130,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14690 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14691 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 305, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 134 200 273 57 121 185 313), lower := (rows 97 38 134 200 273 32 64 128 256), losses := [] }

theorem u14691 : Upper (D 8) (R 8) [96,36,130,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14691 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14692 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 305, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 134 200 280 49 113 177 305), lower := (rows 97 38 134 200 280 32 64 128 256), losses := [] }

theorem u14692 : Upper (D 8) (R 8) [96,36,130,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14692 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14693 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 305, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 134 200 304 57 89 153 281), lower := (rows 97 38 134 200 304 32 64 128 256), losses := [] }

theorem u14693 : Upper (D 8) (R 8) [96,36,130,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14693 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14694 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 56 146 353 321 449 321), lower := (rows 97 38 140 56 146 32 64 128 256), losses := [] }

theorem u14694 : Upper (D 8) (R 8) [96,36,136,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14694 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14695 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 56 208 291 323 387 259), lower := (rows 97 38 140 56 208 32 64 128 256), losses := [] }

theorem u14695 : Upper (D 8) (R 8) [96,36,136,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14695 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14696 : Route 9 := (fun mask => (mask,id))

def c14696 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14696 : Upper (D 8) (R 8) [96,36,136,48,257] 13 := by
  apply FastRouting.sound _ _ [96,36,136,48,257] 13 (by decide) (choices 1) [1,2,64,128] r14696 c14696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5050
  · exact u5051
  · exact u5052
  · exact u5053

def r14697 : Route 9 := (fun mask => (mask,id))

def c14697 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14697 : Upper (D 8) (R 8) [96,36,136,48,258] 13 := by
  apply FastRouting.sound _ _ [96,36,136,48,258] 13 (by decide) (choices 1) [1,64,128] r14697 c14697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5054
  · exact u5055
  · exact u5056

def r14698 : Route 9 := (fun mask => (mask,id))

def c14698 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14698 : Upper (D 8) (R 8) [96,36,136,48,320] 13 := by
  apply FastRouting.sound _ _ [96,36,136,48,320] 13 (by decide) (choices 1) [1,2,128] r14698 c14698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5057
  · exact u5058
  · exact u5059

def b14699 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 56 400 99 67 195 323), lower := (rows 97 38 140 56 400 32 64 128 256), losses := [] }

theorem u14699 : Upper (D 8) (R 8) [96,36,136,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14699 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u14699
end Delivery.IrregularNine14.P08
