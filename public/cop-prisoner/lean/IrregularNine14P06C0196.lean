import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0033
import IrregularNine14P06C0034

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r11760 : Route 9 := (fun mask => (mask,id))

def c11760 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11760 : Upper (D 6) (R 6) [10,20,129,260,33,64] 13 := by
  apply FastRouting.sound _ _ [10,20,129,260,33,64] 13 (by decide) (choices 1) [2,32] r11760 c11760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2011
  · exact u2012

def r11761 : Route 9 := (fun mask => (mask,id))

def c11761 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11761 : Upper (D 6) (R 6) [10,20,129,260,96,1] 13 := by
  apply FastRouting.sound _ _ [10,20,129,260,96,1] 13 (by decide) (choices 1) [2,32] r11761 c11761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2013
  · exact u2014

theorem m11762_1 : Upper (D 6) (R 6) [10,20,129,260,96,2,1] 13 :=
  permutation_upper _ _ _ [10,20,129,260,96,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2013

def r11762 : Route 9 := (fun mask => (mask,id))

def c11762 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11762 : Upper (D 6) (R 6) [10,20,129,260,96,2] 13 := by
  apply FastRouting.sound _ _ [10,20,129,260,96,2] 13 (by decide) (choices 1) [1,32] r11762 c11762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m11762_1
  · exact u2015

def b11763 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 133 268 112 96 99 163 291), lower := (rows 11 22 133 268 112 96 64 128 256), losses := [] }

theorem u11763 : Upper (D 6) (R 6) [10,20,129,260,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11763 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11764 : Route 9 := (fun mask => (mask,id))

def c11764 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11764 : Upper (D 6) (R 6) [10,20,129,288,65,2] 13 := by
  apply FastRouting.sound _ _ [10,20,129,288,65,2] 13 (by decide) (choices 1) [4,32] r11764 c11764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2016
  · exact u2017

def r11765 : Route 9 := (fun mask => (mask,id))

def c11765 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11765 : Upper (D 6) (R 6) [10,20,129,288,65,4] 13 := by
  apply FastRouting.sound _ _ [10,20,129,288,65,4] 13 (by decide) (choices 1) [2,32] r11765 c11765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2018
  · exact u2019

def r11766 : Route 9 := (fun mask => (mask,id))

def c11766 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11766 : Upper (D 6) (R 6) [10,20,129,288,65,64] 13 := by
  apply FastRouting.sound _ _ [10,20,129,288,65,64] 13 (by decide) (choices 1) [2,4,32] r11766 c11766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2020
  · exact u2021
  · exact u2022

def r11767 : Route 9 := (fun mask => (mask,id))

def c11767 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11767 : Upper (D 6) (R 6) [10,20,129,288,66,1] 13 := by
  apply FastRouting.sound _ _ [10,20,129,288,66,1] 13 (by decide) (choices 1) [4,32] r11767 c11767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2023
  · exact u2024

def r11768 : Route 9 := (fun mask => (mask,id))

def c11768 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11768 : Upper (D 6) (R 6) [10,20,129,288,66,4] 13 := by
  apply FastRouting.sound _ _ [10,20,129,288,66,4] 13 (by decide) (choices 1) [1,32] r11768 c11768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2025
  · exact u2026

def r11769 : Route 9 := (fun mask => (mask,id))

def c11769 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11769 : Upper (D 6) (R 6) [10,20,129,288,66,64] 13 := by
  apply FastRouting.sound _ _ [10,20,129,288,66,64] 13 (by decide) (choices 1) [1,4,32] r11769 c11769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2027
  · exact u2028
  · exact u2029

def r11770 : Route 9 := (fun mask => (mask,id))

def c11770 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11770 : Upper (D 6) (R 6) [10,20,129,288,96,1] 13 := by
  apply FastRouting.sound _ _ [10,20,129,288,96,1] 13 (by decide) (choices 1) [2,4] r11770 c11770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2030
  · exact u2031

def r11771 : Route 9 := (fun mask => (mask,id))

def c11771 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11771 : Upper (D 6) (R 6) [10,20,129,288,96,2] 13 := by
  apply FastRouting.sound _ _ [10,20,129,288,96,2] 13 (by decide) (choices 1) [1,4] r11771 c11771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2032
  · exact u2033

def r11772 : Route 9 := (fun mask => (mask,id))

def c11772 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11772 : Upper (D 6) (R 6) [10,20,129,288,96,4] 13 := by
  apply FastRouting.sound _ _ [10,20,129,288,96,4] 13 (by decide) (choices 1) [1,2] r11772 c11772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2034
  · exact u2035

def b11773 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 133 296 112 96 71 135 263), lower := (rows 11 22 133 296 112 96 64 128 256), losses := [] }

theorem u11773 : Upper (D 6) (R 6) [10,20,129,288,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11774 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 22 134 41 112 33 324 452 324), lower := (rows 11 22 134 41 112 33 64 128 256), losses := [] }

theorem u11774 : Upper (D 6) (R 6) [10,20,130,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11774 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11775 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 3, region := 336, targets := 2 }], pairs := [(0,6),(3,6),(4,1)], upper := (rows 11 22 134 41 112 36 321 449 321), lower := (rows 11 22 134 41 112 36 64 128 256), losses := [] }

theorem u11775 : Upper (D 6) (R 6) [10,20,130,33,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11776 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 134 41 112 96 325 389 261), lower := (rows 11 22 134 41 112 96 64 128 256), losses := [] }

theorem u11776 : Upper (D 6) (R 6) [10,20,130,33,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11776 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11777 : Route 9 := (fun mask => (mask,id))

def c11777 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11777 : Upper (D 6) (R 6) [10,20,130,33,96,256] 13 := by
  apply FastRouting.sound _ _ [10,20,130,33,96,256] 13 (by decide) (choices 1) [1,4] r11777 c11777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2036
  · exact u2037

def b11778 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 22 134 41 304 33 68 196 324), lower := (rows 11 22 134 41 304 33 64 128 256), losses := [] }

theorem u11778 : Upper (D 6) (R 6) [10,20,130,33,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11778 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11779 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 3, region := 336, targets := 2 }], pairs := [(0,6),(3,6),(4,1)], upper := (rows 11 22 134 41 304 36 65 193 321), lower := (rows 11 22 134 41 304 36 64 128 256), losses := [] }

theorem u11779 : Upper (D 6) (R 6) [10,20,130,33,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11780 : Route 9 := (fun mask => (mask,id))

def c11780 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11780 : Upper (D 6) (R 6) [10,20,130,33,288,64] 13 := by
  apply FastRouting.sound _ _ [10,20,130,33,288,64] 13 (by decide) (choices 1) [1,4] r11780 c11780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2038
  · exact u2039

def b11781 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 22 134 41 336 33 100 228 356), lower := (rows 11 22 134 41 336 33 64 128 256), losses := [] }

theorem u11781 : Upper (D 6) (R 6) [10,20,130,33,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11782 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 3, region := 336, targets := 2 }], pairs := [(0,6),(3,6),(4,1)], upper := (rows 11 22 134 41 336 36 97 225 353), lower := (rows 11 22 134 41 336 36 64 128 256), losses := [] }

theorem u11782 : Upper (D 6) (R 6) [10,20,130,33,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11782 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11783 : PairBound 9 := { available := 37, camps := [], pairs := [(0,2),(2,6),(3,2)], upper := (rows 11 22 134 41 336 96 101 165 293), lower := (rows 11 22 134 41 336 96 64 128 256), losses := [{ target := 2, region := (rows 7 2 0 10 16 112 64 128 256), good := (rows 11 59 139 41 368 96 96 128 256) },{ target := 6, region := (rows 1 2 5 8 16 32 0 136 264), good := (rows 399 22 134 429 272 32 0 128 256) }] }

theorem u11783 : Upper (D 6) (R 6) [10,20,130,33,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11783 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11784 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 11 22 134 44 336 33 97 225 353), lower := (rows 11 22 134 44 336 33 64 128 256), losses := [] }

theorem u11784 : Upper (D 6) (R 6) [10,20,130,36,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11784 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11785 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 368, targets := 6 }], pairs := [(3,0),(4,1),(4,2)], upper := (rows 11 22 134 44 336 96 97 161 289), lower := (rows 11 22 134 44 336 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 112 64 128 256), good := (rows 10 62 142 44 368 96 96 128 256) }] }

theorem u11785 : Upper (D 6) (R 6) [10,20,130,36,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11785 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11786 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 22 134 104 49 33 324 452 324), lower := (rows 11 22 134 104 49 33 64 128 256), losses := [] }

theorem u11786 : Upper (D 6) (R 6) [10,20,130,96,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11786 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11787 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 328, targets := 6 },{ cop := 4, region := 454, targets := 32 }], pairs := [(1,5),(3,1),(3,2)], upper := (rows 11 22 134 104 49 36 321 449 321), lower := (rows 11 22 134 104 49 36 64 128 256), losses := [] }

theorem u11787 : Upper (D 6) (R 6) [10,20,130,96,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11787 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11788 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 134 104 49 96 325 389 261), lower := (rows 11 22 134 104 49 96 64 128 256), losses := [] }

theorem u11788 : Upper (D 6) (R 6) [10,20,130,96,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11788 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11789 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 11 22 134 104 49 288 69 197 325), lower := (rows 11 22 134 104 49 288 64 128 256), losses := [] }

theorem u11789 : Upper (D 6) (R 6) [10,20,130,96,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11789 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11790 : Route 9 := (fun mask => (mask,id))

def c11790 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11790 : Upper (D 6) (R 6) [10,20,130,96,257,1] 13 := by
  apply FastRouting.sound _ _ [10,20,130,96,257,1] 13 (by decide) (choices 1) [4,32] r11790 c11790
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2040
  · exact u2041

theorem m11791_1 : Upper (D 6) (R 6) [10,20,130,96,257,4,1] 13 :=
  permutation_upper _ _ _ [10,20,130,96,257,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2040

def r11791 : Route 9 := (fun mask => (mask,id))

def c11791 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11791 : Upper (D 6) (R 6) [10,20,130,96,257,4] 13 := by
  apply FastRouting.sound _ _ [10,20,130,96,257,4] 13 (by decide) (choices 1) [1,32] r11791 c11791
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m11791_1
  · exact u2042

def b11792 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 134 104 273 96 101 165 293), lower := (rows 11 22 134 104 273 96 64 128 256), losses := [] }

theorem u11792 : Upper (D 6) (R 6) [10,20,130,96,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11792 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11793 : Route 9 := (fun mask => (mask,id))

def c11793 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11793 : Upper (D 6) (R 6) [10,20,130,96,288,1] 13 := by
  apply FastRouting.sound _ _ [10,20,130,96,288,1] 13 (by decide) (choices 1) [1,4] r11793 c11793
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2043
  · exact u2044

def b11794 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(3,1),(4,1)], upper := (rows 11 22 134 104 304 36 65 193 321), lower := (rows 11 22 134 104 304 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 38 65 129 257), good := (rows 505 52 164 104 304 36 64 128 256) }] }

theorem u11794 : Upper (D 6) (R 6) [10,20,130,96,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11795 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 134 104 304 96 69 133 261), lower := (rows 11 22 134 104 304 96 64 128 256), losses := [] }

theorem u11795 : Upper (D 6) (R 6) [10,20,130,96,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11796 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 134 265 112 33 100 228 356), lower := (rows 11 22 134 265 112 33 64 128 256), losses := [] }

theorem u11796 : Upper (D 6) (R 6) [10,20,130,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m11797_1 : Upper (D 6) (R 6) [10,20,130,257,96,4,1] 13 :=
  permutation_upper _ _ _ [10,20,130,257,96,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2045

def r11797 : Route 9 := (fun mask => (mask,id))

def c11797 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11797 : Upper (D 6) (R 6) [10,20,130,257,96,4] 13 := by
  apply FastRouting.sound _ _ [10,20,130,257,96,4] 13 (by decide) (choices 1) [1,32] r11797 c11797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m11797_1
  · exact u2046

def b11798 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 134 265 112 96 101 165 293), lower := (rows 11 22 134 265 112 96 64 128 256), losses := [] }

theorem u11798 : Upper (D 6) (R 6) [10,20,130,257,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11799 : Route 9 := (fun mask => (mask,id))

def c11799 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11799 : Upper (D 6) (R 6) [10,20,130,260,96,1] 13 := by
  apply FastRouting.sound _ _ [10,20,130,260,96,1] 13 (by decide) (choices 1) [1,32] r11799 c11799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2047
  · exact u2048

def b11800 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 134 268 112 96 97 161 289), lower := (rows 11 22 134 268 112 96 64 128 256), losses := [] }

theorem u11800 : Upper (D 6) (R 6) [10,20,130,260,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11800 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11801 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 22 134 296 49 33 68 196 324), lower := (rows 11 22 134 296 49 33 64 128 256), losses := [] }

theorem u11801 : Upper (D 6) (R 6) [10,20,130,288,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11801 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11802 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 328, targets := 6 },{ cop := 4, region := 198, targets := 32 }], pairs := [(1,5),(3,1),(3,2)], upper := (rows 11 22 134 296 49 36 65 193 321), lower := (rows 11 22 134 296 49 36 64 128 256), losses := [] }

theorem u11802 : Upper (D 6) (R 6) [10,20,130,288,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11802 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11803 : Route 9 := (fun mask => (mask,id))

def c11803 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11803 : Upper (D 6) (R 6) [10,20,130,288,33,64] 13 := by
  apply FastRouting.sound _ _ [10,20,130,288,33,64] 13 (by decide) (choices 1) [1,4] r11803 c11803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2049
  · exact u2050

def r11804 : Route 9 := (fun mask => (mask,id))

def c11804 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11804 : Upper (D 6) (R 6) [10,20,130,288,65,1] 13 := by
  apply FastRouting.sound _ _ [10,20,130,288,65,1] 13 (by decide) (choices 1) [4,32] r11804 c11804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2051
  · exact u2052

def r11805 : Route 9 := (fun mask => (mask,id))

def c11805 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11805 : Upper (D 6) (R 6) [10,20,130,288,65,4] 13 := by
  apply FastRouting.sound _ _ [10,20,130,288,65,4] 13 (by decide) (choices 1) [1,32] r11805 c11805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2053
  · exact u2054

def r11806 : Route 9 := (fun mask => (mask,id))

def c11806 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11806 : Upper (D 6) (R 6) [10,20,130,288,65,64] 13 := by
  apply FastRouting.sound _ _ [10,20,130,288,65,64] 13 (by decide) (choices 1) [1,4,32] r11806 c11806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2055
  · exact u2056
  · exact u2057

def r11807 : Route 9 := (fun mask => (mask,id))

def c11807 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11807 : Upper (D 6) (R 6) [10,20,130,288,96,1] 13 := by
  apply FastRouting.sound _ _ [10,20,130,288,96,1] 13 (by decide) (choices 1) [1,4] r11807 c11807
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2058
  · exact u2059

def b11808 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(3,1),(4,1)], upper := (rows 11 22 134 296 112 36 65 193 321), lower := (rows 11 22 134 296 112 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 38 65 129 257), good := (rows 505 52 164 296 112 36 64 128 256) }] }

theorem u11808 : Upper (D 6) (R 6) [10,20,130,288,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11808 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11809 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 134 296 112 96 69 133 261), lower := (rows 11 22 134 296 112 96 64 128 256), losses := [] }

theorem u11809 : Upper (D 6) (R 6) [10,20,130,288,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11809 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11810 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 22 164 41 82 33 324 452 324), lower := (rows 11 22 164 41 82 33 64 128 256), losses := [] }

theorem u11810 : Upper (D 6) (R 6) [10,20,160,33,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11810 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11811 : PairBound 9 := { available := 321, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 22 164 41 82 36 321 449 321), lower := (rows 11 22 164 41 82 36 64 128 256), losses := [] }

theorem u11811 : Upper (D 6) (R 6) [10,20,160,33,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11811 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11812 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 4, region := 41, targets := 4 }], pairs := [(0,2),(2,1),(3,1)], upper := (rows 11 22 164 41 82 96 325 389 261), lower := (rows 11 22 164 41 82 96 64 128 256), losses := [] }

theorem u11812 : Upper (D 6) (R 6) [10,20,160,33,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11812 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11813 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 22 164 41 82 288 69 197 325), lower := (rows 11 22 164 41 82 288 64 128 256), losses := [] }

theorem u11813 : Upper (D 6) (R 6) [10,20,160,33,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11813 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11814 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 22 164 41 274 33 68 196 324), lower := (rows 11 22 164 41 274 33 64 128 256), losses := [] }

theorem u11814 : Upper (D 6) (R 6) [10,20,160,33,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11814 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11815 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 22 164 41 274 36 65 193 321), lower := (rows 11 22 164 41 274 36 64 128 256), losses := [] }

theorem u11815 : Upper (D 6) (R 6) [10,20,160,33,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11815 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11816 : Route 9 := (fun mask => (mask,id))

def c11816 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11816 : Upper (D 6) (R 6) [10,20,160,33,258,64] 13 := by
  apply FastRouting.sound _ _ [10,20,160,33,258,64] 13 (by decide) (choices 1) [1,4] r11816 c11816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2060
  · exact u2061

def b11817 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 22 164 41 336 33 70 198 326), lower := (rows 11 22 164 41 336 33 64 128 256), losses := [] }

theorem u11817 : Upper (D 6) (R 6) [10,20,160,33,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11818 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 22 164 41 336 34 69 197 325), lower := (rows 11 22 164 41 336 34 64 128 256), losses := [] }

theorem u11818 : Upper (D 6) (R 6) [10,20,160,33,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11818 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11819 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 22 164 41 336 36 67 195 323), lower := (rows 11 22 164 41 336 36 64 128 256), losses := [] }

theorem u11819 : Upper (D 6) (R 6) [10,20,160,33,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11819 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u11819
end Delivery.IrregularNine14.P06
