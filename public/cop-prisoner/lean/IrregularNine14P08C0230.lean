import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0077
import IrregularNine14P08C0078

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13800 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 14 38 73 273 176 240 176 432), lower := (rows 97 14 38 73 273 32 64 128 256), losses := [] }

theorem u13800 : Upper (D 8) (R 8) [96,12,34,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13800 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13801 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 14 38 73 304 177 209 145 401), lower := (rows 97 14 38 73 304 32 64 128 256), losses := [] }

theorem u13801 : Upper (D 8) (R 8) [96,12,34,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13801 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13802 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 14 38 73 400 177 241 177 433), lower := (rows 97 14 38 73 400 32 64 128 256), losses := [] }

theorem u13802 : Upper (D 8) (R 8) [96,12,34,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13802 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13803 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 38 88 145 417 481 417 417), lower := (rows 97 14 38 88 145 32 64 128 256), losses := [] }

theorem u13803 : Upper (D 8) (R 8) [96,12,34,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13803 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13804 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 38 88 176 417 449 385 385), lower := (rows 97 14 38 88 176 32 64 128 256), losses := [] }

theorem u13804 : Upper (D 8) (R 8) [96,12,34,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13804 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13805 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 38 88 273 161 225 161 417), lower := (rows 97 14 38 88 273 32 64 128 256), losses := [] }

theorem u13805 : Upper (D 8) (R 8) [96,12,34,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13805 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13806 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 38 88 304 161 193 129 385), lower := (rows 97 14 38 88 304 32 64 128 256), losses := [] }

theorem u13806 : Upper (D 8) (R 8) [96,12,34,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13806 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13807 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 38 88 400 161 225 161 417), lower := (rows 97 14 38 88 400 32 64 128 256), losses := [] }

theorem u13807 : Upper (D 8) (R 8) [96,12,34,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13807 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13808 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 38 104 145 433 465 401 401), lower := (rows 97 14 38 104 145 32 64 128 256), losses := [] }

theorem u13808 : Upper (D 8) (R 8) [96,12,34,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13808 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13809 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 38 104 273 177 209 145 401), lower := (rows 97 14 38 104 273 32 64 128 256), losses := [] }

theorem u13809 : Upper (D 8) (R 8) [96,12,34,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13809 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13810 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 38 104 400 177 209 145 401), lower := (rows 97 14 38 104 400 32 64 128 256), losses := [] }

theorem u13810 : Upper (D 8) (R 8) [96,12,34,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13810 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13811 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 38 137 49 496 464 464 464), lower := (rows 97 14 38 137 49 32 64 128 256), losses := [] }

theorem u13811 : Upper (D 8) (R 8) [96,12,34,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13811 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13812 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 38 137 81 432 496 432 432), lower := (rows 97 14 38 137 81 32 64 128 256), losses := [] }

theorem u13812 : Upper (D 8) (R 8) [96,12,34,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13812 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13813 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 38 137 112 433 465 401 401), lower := (rows 97 14 38 137 112 32 64 128 256), losses := [] }

theorem u13813 : Upper (D 8) (R 8) [96,12,34,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13813 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13814 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 14 38 137 145 368 368 496 368), lower := (rows 97 14 38 137 145 32 64 128 256), losses := [] }

theorem u13814 : Upper (D 8) (R 8) [96,12,34,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13814 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13815 : PairBound 9 := { available := 337, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 38 137 176 369 337 465 337), lower := (rows 97 14 38 137 176 32 64 128 256), losses := [] }

theorem u13815 : Upper (D 8) (R 8) [96,12,34,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13815 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13816 : PairBound 9 := { available := 305, camps := [{ cop := 4, region := 289, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 38 137 208 305 369 433 305), lower := (rows 97 14 38 137 208 32 64 128 256), losses := [] }

theorem u13816 : Upper (D 8) (R 8) [96,12,34,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13816 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13817 : Route 9 := (fun mask => (mask,id))

def c13817 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u13817 : Upper (D 8) (R 8) [96,12,34,129,257] 13 := by
  apply FastRouting.sound _ _ [96,12,34,129,257] 13 (by decide) (choices 1) [16,64,128] r13817 c13817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4654
  · exact u4655
  · exact u4656

def r13818 : Route 9 := (fun mask => (mask,id))

def c13818 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u13818 : Upper (D 8) (R 8) [96,12,34,129,288] 13 := by
  apply FastRouting.sound _ _ [96,12,34,129,288] 13 (by decide) (choices 1) [1,16,64,128] r13818 c13818
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4657
  · exact u4658
  · exact u4659
  · exact u4660

def r13819 : Route 9 := (fun mask => (mask,id))

def c13819 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13819 : Upper (D 8) (R 8) [96,12,34,129,320] 13 := by
  apply FastRouting.sound _ _ [96,12,34,129,320] 13 (by decide) (choices 1) [1,16,128] r13819 c13819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4661
  · exact u4662
  · exact u4663

def b13820 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 38 137 400 113 113 241 369), lower := (rows 97 14 38 137 400 32 64 128 256), losses := [] }

theorem u13820 : Upper (D 8) (R 8) [96,12,34,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13820 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13821 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 38 152 49 481 449 449 449), lower := (rows 97 14 38 152 49 32 64 128 256), losses := [] }

theorem u13821 : Upper (D 8) (R 8) [96,12,34,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13821 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13822 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 38 152 81 417 481 417 417), lower := (rows 97 14 38 152 81 32 64 128 256), losses := [] }

theorem u13822 : Upper (D 8) (R 8) [96,12,34,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13822 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13823 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 38 152 112 417 449 385 385), lower := (rows 97 14 38 152 112 32 64 128 256), losses := [] }

theorem u13823 : Upper (D 8) (R 8) [96,12,34,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13823 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13824 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 38 152 145 353 353 481 353), lower := (rows 97 14 38 152 145 32 64 128 256), losses := [] }

theorem u13824 : Upper (D 8) (R 8) [96,12,34,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13824 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13825 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 14, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 38 152 176 353 321 449 321), lower := (rows 97 14 38 152 176 32 64 128 256), losses := [] }

theorem u13825 : Upper (D 8) (R 8) [96,12,34,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13825 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13826 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 38 152 208 289 353 417 289), lower := (rows 97 14 38 152 208 32 64 128 256), losses := [] }

theorem u13826 : Upper (D 8) (R 8) [96,12,34,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13826 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13827 : Route 9 := (fun mask => (mask,id))

def c13827 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13827 : Upper (D 8) (R 8) [96,12,34,144,257] 13 := by
  apply FastRouting.sound _ _ [96,12,34,144,257] 13 (by decide) (choices 1) [1,64,128] r13827 c13827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4664
  · exact u4665
  · exact u4666

def r13828 : Route 9 := (fun mask => (mask,id))

def c13828 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13828 : Upper (D 8) (R 8) [96,12,34,144,288] 13 := by
  apply FastRouting.sound _ _ [96,12,34,144,288] 13 (by decide) (choices 1) [1,64,128] r13828 c13828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4667
  · exact u4668
  · exact u4669

def r13829 : Route 9 := (fun mask => (mask,id))

def c13829 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13829 : Upper (D 8) (R 8) [96,12,34,144,320] 13 := by
  apply FastRouting.sound _ _ [96,12,34,144,320] 13 (by decide) (choices 1) [1,128] r13829 c13829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4670
  · exact u4671

def b13830 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 38 152 400 97 97 225 353), lower := (rows 97 14 38 152 400 32 64 128 256), losses := [] }

theorem u13830 : Upper (D 8) (R 8) [96,12,34,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13830 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13831 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 38 168 145 369 337 465 337), lower := (rows 97 14 38 168 145 32 64 128 256), losses := [] }

theorem u13831 : Upper (D 8) (R 8) [96,12,34,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13831 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13832 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 38 168 208 305 337 401 273), lower := (rows 97 14 38 168 208 32 64 128 256), losses := [] }

theorem u13832 : Upper (D 8) (R 8) [96,12,34,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13832 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13833 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 38 168 273 241 209 209 465), lower := (rows 97 14 38 168 273 32 64 128 256), losses := [] }

theorem u13833 : Upper (D 8) (R 8) [96,12,34,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13833 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13834 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 38 168 336 177 209 145 401), lower := (rows 97 14 38 168 336 32 64 128 256), losses := [] }

theorem u13834 : Upper (D 8) (R 8) [96,12,34,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13834 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13835 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 38 168 400 113 81 209 337), lower := (rows 97 14 38 168 400 32 64 128 256), losses := [] }

theorem u13835 : Upper (D 8) (R 8) [96,12,34,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13835 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13836 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 38 200 145 305 369 433 305), lower := (rows 97 14 38 200 145 32 64 128 256), losses := [] }

theorem u13836 : Upper (D 8) (R 8) [96,12,34,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13836 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13837 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 38 200 176 305 337 401 273), lower := (rows 97 14 38 200 176 32 64 128 256), losses := [] }

theorem u13837 : Upper (D 8) (R 8) [96,12,34,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13837 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13838 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 38 200 273 177 241 177 433), lower := (rows 97 14 38 200 273 32 64 128 256), losses := [] }

theorem u13838 : Upper (D 8) (R 8) [96,12,34,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13838 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13839 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 38 200 304 177 209 145 401), lower := (rows 97 14 38 200 304 32 64 128 256), losses := [] }

theorem u13839 : Upper (D 8) (R 8) [96,12,34,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13839 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13840 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 38 200 400 49 113 177 305), lower := (rows 97 14 38 200 400 32 64 128 256), losses := [] }

theorem u13840 : Upper (D 8) (R 8) [96,12,34,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13840 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13841 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 38 265 49 240 208 208 464), lower := (rows 97 14 38 265 49 32 64 128 256), losses := [] }

theorem u13841 : Upper (D 8) (R 8) [96,12,34,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13841 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13842 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 38 265 81 176 240 176 432), lower := (rows 97 14 38 265 81 32 64 128 256), losses := [] }

theorem u13842 : Upper (D 8) (R 8) [96,12,34,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13842 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13843 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 38 265 112 177 209 145 401), lower := (rows 97 14 38 265 112 32 64 128 256), losses := [] }

theorem u13843 : Upper (D 8) (R 8) [96,12,34,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13843 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13844 : Route 9 := (fun mask => (mask,id))

def c13844 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u13844 : Upper (D 8) (R 8) [96,12,34,257,129] 13 := by
  apply FastRouting.sound _ _ [96,12,34,257,129] 13 (by decide) (choices 1) [16,64,128] r13844 c13844
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4672
  · exact u4673
  · exact u4674

def r13845 : Route 9 := (fun mask => (mask,id))

def c13845 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u13845 : Upper (D 8) (R 8) [96,12,34,257,160] 13 := by
  apply FastRouting.sound _ _ [96,12,34,257,160] 13 (by decide) (choices 1) [1,16,64,128] r13845 c13845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4675
  · exact u4676
  · exact u4677
  · exact u4678

def r13846 : Route 9 := (fun mask => (mask,id))

def c13846 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13846 : Upper (D 8) (R 8) [96,12,34,257,192] 13 := by
  apply FastRouting.sound _ _ [96,12,34,257,192] 13 (by decide) (choices 1) [1,16,128] r13846 c13846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4679
  · exact u4680
  · exact u4681

def b13847 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 38 280 49 225 193 193 449), lower := (rows 97 14 38 280 49 32 64 128 256), losses := [] }

theorem u13847 : Upper (D 8) (R 8) [96,12,34,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13847 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13848 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 38 280 81 161 225 161 417), lower := (rows 97 14 38 280 81 32 64 128 256), losses := [] }

theorem u13848 : Upper (D 8) (R 8) [96,12,34,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13848 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13849 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 38 280 112 161 193 129 385), lower := (rows 97 14 38 280 112 32 64 128 256), losses := [] }

theorem u13849 : Upper (D 8) (R 8) [96,12,34,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13849 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13850 : Route 9 := (fun mask => (mask,id))

def c13850 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13850 : Upper (D 8) (R 8) [96,12,34,272,129] 13 := by
  apply FastRouting.sound _ _ [96,12,34,272,129] 13 (by decide) (choices 1) [1,64,128] r13850 c13850
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4682
  · exact u4683
  · exact u4684

def r13851 : Route 9 := (fun mask => (mask,id))

def c13851 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13851 : Upper (D 8) (R 8) [96,12,34,272,160] 13 := by
  apply FastRouting.sound _ _ [96,12,34,272,160] 13 (by decide) (choices 1) [1,64,128] r13851 c13851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4685
  · exact u4686
  · exact u4687

def r13852 : Route 9 := (fun mask => (mask,id))

def c13852 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13852 : Upper (D 8) (R 8) [96,12,34,272,192] 13 := by
  apply FastRouting.sound _ _ [96,12,34,272,192] 13 (by decide) (choices 1) [1,128] r13852 c13852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4688
  · exact u4689

def b13853 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 38 296 145 241 209 209 465), lower := (rows 97 14 38 296 145 32 64 128 256), losses := [] }

theorem u13853 : Upper (D 8) (R 8) [96,12,34,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13853 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13854 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 38 296 208 177 209 145 401), lower := (rows 97 14 38 296 208 32 64 128 256), losses := [] }

theorem u13854 : Upper (D 8) (R 8) [96,12,34,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13854 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13855 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 38 328 145 177 241 177 433), lower := (rows 97 14 38 328 145 32 64 128 256), losses := [] }

theorem u13855 : Upper (D 8) (R 8) [96,12,34,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13855 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13856 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 38 328 176 177 209 145 401), lower := (rows 97 14 38 328 176 32 64 128 256), losses := [] }

theorem u13856 : Upper (D 8) (R 8) [96,12,34,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13856 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13857 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 38 392 49 241 209 209 465), lower := (rows 97 14 38 392 49 32 64 128 256), losses := [] }

theorem u13857 : Upper (D 8) (R 8) [96,12,34,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13857 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13858 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 38 392 81 177 241 177 433), lower := (rows 97 14 38 392 81 32 64 128 256), losses := [] }

theorem u13858 : Upper (D 8) (R 8) [96,12,34,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13858 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13859 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 38 392 112 177 209 145 401), lower := (rows 97 14 38 392 112 32 64 128 256), losses := [] }

theorem u13859 : Upper (D 8) (R 8) [96,12,34,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13859 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u13859
end Delivery.IrregularNine14.P08
