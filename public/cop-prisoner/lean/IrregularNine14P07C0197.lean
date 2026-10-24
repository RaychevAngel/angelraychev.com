import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0016

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r11820 : Route 9 := (fun mask => (mask,id))

def c11820 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11820 : Upper (D 7) (R 7) [6,9,96,288,192,128] 13 := by
  apply FastRouting.sound _ _ [6,9,96,288,192,128] 13 (by decide) (choices 1) [1,2,16] r11820 c11820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u966
  · exact u967
  · exact u968

def b11821 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 460, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 11 100 392 49 34 208 208 464), lower := (rows 7 11 100 392 49 34 64 128 256), losses := [] }

theorem u11821 : Upper (D 7) (R 7) [6,9,96,384,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11821 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11822 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 }], pairs := [(4,1),(4,6),(4,7)], upper := (rows 7 11 100 392 49 48 194 194 450), lower := (rows 7 11 100 392 49 48 64 128 256), losses := [] }

theorem u11822 : Upper (D 7) (R 7) [6,9,96,384,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11822 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11823 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 11 100 392 49 96 210 146 402), lower := (rows 7 11 100 392 49 96 64 128 256), losses := [] }

theorem u11823 : Upper (D 7) (R 7) [6,9,96,384,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11824 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(3,5),(4,1),(4,6)], upper := (rows 7 11 100 392 49 160 82 210 338), lower := (rows 7 11 100 392 49 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 18 168 64 128 256), good := (rows 21 57 100 424 49 160 64 160 256) },{ target := 6, region := (rows 1 2 4 8 18 168 0 128 256), good := (rows 23 59 36 424 49 160 0 160 256) }] }

theorem u11824 : Upper (D 7) (R 7) [6,9,96,384,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11825 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 460, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 11 100 392 50 33 208 208 464), lower := (rows 7 11 100 392 50 33 64 128 256), losses := [] }

theorem u11825 : Upper (D 7) (R 7) [6,9,96,384,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11825 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11826 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 48, targets := 193 }], pairs := [(4,0),(4,6),(4,7)], upper := (rows 7 11 100 392 50 48 193 193 449), lower := (rows 7 11 100 392 50 48 64 128 256), losses := [] }

theorem u11826 : Upper (D 7) (R 7) [6,9,96,384,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11826 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11827 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 11 100 392 50 96 209 145 401), lower := (rows 7 11 100 392 50 96 64 128 256), losses := [] }

theorem u11827 : Upper (D 7) (R 7) [6,9,96,384,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11827 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11828 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 69, targets := 128 }], pairs := [(0,7),(2,7),(4,0),(4,6)], upper := (rows 7 11 100 392 50 160 81 209 337), lower := (rows 7 11 100 392 50 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 168 64 128 256), good := (rows 22 58 100 424 50 160 64 160 256) },{ target := 6, region := (rows 1 2 4 8 18 168 0 128 256), good := (rows 23 59 36 424 50 160 0 160 256) }] }

theorem u11828 : Upper (D 7) (R 7) [6,9,96,384,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11828 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11829 : Route 9 := (fun mask => (mask,id))

def c11829 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11829 : Upper (D 7) (R 7) [6,9,96,384,129,2] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384,129,2] 13 (by decide) (choices 1) [16,32] r11829 c11829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u969
  · exact u970

theorem m11830_2 : Upper (D 7) (R 7) [6,9,96,384,129,16,2] 13 :=
  permutation_upper _ _ _ [6,9,96,384,129,2,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u969

def r11830 : Route 9 := (fun mask => (mask,id))

def c11830 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11830 : Upper (D 7) (R 7) [6,9,96,384,129,16] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384,129,16] 13 (by decide) (choices 1) [2,32] r11830 c11830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m11830_2
  · exact u971

def b11831 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 11 100 392 145 96 114 178 306), lower := (rows 7 11 100 392 145 96 64 128 256), losses := [] }

theorem u11831 : Upper (D 7) (R 7) [6,9,96,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11831 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11832 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 101, targets := 128 }], pairs := [(0,7),(2,1),(2,7),(3,1)], upper := (rows 7 11 100 392 146 33 112 240 368), lower := (rows 7 11 100 392 146 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 35 80 144 272), good := (rows 37 41 100 392 508 33 64 128 256) }] }

theorem u11832 : Upper (D 7) (R 7) [6,9,96,384,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11832 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m11833_1 : Upper (D 7) (R 7) [6,9,96,384,130,16,1] 13 :=
  permutation_upper _ _ _ [6,9,96,384,130,1,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u972

def r11833 : Route 9 := (fun mask => (mask,id))

def c11833 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11833 : Upper (D 7) (R 7) [6,9,96,384,130,16] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384,130,16] 13 (by decide) (choices 1) [1,32] r11833 c11833
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m11833_1
  · exact u973

def b11834 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 11 100 392 146 96 113 177 305), lower := (rows 7 11 100 392 146 96 64 128 256), losses := [] }

theorem u11834 : Upper (D 7) (R 7) [6,9,96,384,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11834 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11835 : Route 9 := (fun mask => (mask,id))

def c11835 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11835 : Upper (D 7) (R 7) [6,9,96,384,160,1] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384,160,1] 13 (by decide) (choices 1) [2,16] r11835 c11835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u974
  · exact u975

def r11836 : Route 9 := (fun mask => (mask,id))

def c11836 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11836 : Upper (D 7) (R 7) [6,9,96,384,160,2] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384,160,2] 13 (by decide) (choices 1) [1,16] r11836 c11836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u976
  · exact u977

def b11837 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 395, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 100 392 176 48 67 195 323), lower := (rows 7 11 100 392 176 48 64 128 256), losses := [] }

theorem u11837 : Upper (D 7) (R 7) [6,9,96,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11837 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11838 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 11 100 392 176 96 83 147 275), lower := (rows 7 11 100 392 176 96 64 128 256), losses := [] }

theorem u11838 : Upper (D 7) (R 7) [6,9,96,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11839 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 26 37 73 176 34 448 448 448), lower := (rows 7 26 37 73 176 34 64 128 256), losses := [] }

theorem u11839 : Upper (D 7) (R 7) [6,24,33,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11839 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11840 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 3, region := 36, targets := 130 }], pairs := [(1,0),(2,1),(2,7),(4,0)], upper := (rows 7 26 37 73 176 96 450 386 386), lower := (rows 7 26 37 73 176 96 64 128 256), losses := [] }

theorem u11840 : Upper (D 7) (R 7) [6,24,33,65,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11840 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11841 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 26 37 73 176 160 322 450 322), lower := (rows 7 26 37 73 176 160 64 128 256), losses := [] }

theorem u11841 : Upper (D 7) (R 7) [6,24,33,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11842 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 0, region := 200, targets := 32 }], pairs := [(1,0),(3,5),(4,0)], upper := (rows 7 26 37 73 176 288 194 194 450), lower := (rows 7 26 37 73 176 288 64 128 256), losses := [] }

theorem u11842 : Upper (D 7) (R 7) [6,24,33,65,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11842 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11843 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 26 37 73 304 34 192 192 448), lower := (rows 7 26 37 73 304 34 64 128 256), losses := [] }

theorem u11843 : Upper (D 7) (R 7) [6,24,33,65,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11843 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11844 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 3, region := 36, targets := 130 }], pairs := [(1,0),(2,1),(2,7),(4,0)], upper := (rows 7 26 37 73 304 96 194 130 386), lower := (rows 7 26 37 73 304 96 64 128 256), losses := [] }

theorem u11844 : Upper (D 7) (R 7) [6,24,33,65,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11844 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11845 : Route 9 := (fun mask => (mask,id))

def c11845 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11845 : Upper (D 7) (R 7) [6,24,33,65,288,128] 13 := by
  apply FastRouting.sound _ _ [6,24,33,65,288,128] 13 (by decide) (choices 1) [2,128] r11845 c11845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u978
  · exact u979

def b11846 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 26 37 73 400 34 224 224 480), lower := (rows 7 26 37 73 400 34 64 128 256), losses := [] }

theorem u11846 : Upper (D 7) (R 7) [6,24,33,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11847 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 3, region := 36, targets := 130 }], pairs := [(1,0),(2,1),(2,7),(4,0)], upper := (rows 7 26 37 73 400 96 226 162 418), lower := (rows 7 26 37 73 400 96 64 128 256), losses := [] }

theorem u11847 : Upper (D 7) (R 7) [6,24,33,65,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11848 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 434, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 7 26 37 73 400 160 98 226 354), lower := (rows 7 26 37 73 400 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 6 8 16 176 0 128 256), good := (rows 7 63 37 9 432 160 0 160 256) }] }

theorem u11848 : Upper (D 7) (R 7) [6,24,33,65,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11848 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11849 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 26 37 74 176 33 448 448 448), lower := (rows 7 26 37 74 176 33 64 128 256), losses := [] }

theorem u11849 : Upper (D 7) (R 7) [6,24,33,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11849 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11850 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,7),(2,1),(2,7),(4,1)], upper := (rows 7 26 37 74 176 96 449 385 385), lower := (rows 7 26 37 74 176 96 64 128 256), losses := [] }

theorem u11850 : Upper (D 7) (R 7) [6,24,33,66,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11851 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 26 37 74 176 160 321 449 321), lower := (rows 7 26 37 74 176 160 64 128 256), losses := [] }

theorem u11851 : Upper (D 7) (R 7) [6,24,33,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11851 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11852 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 26 37 74 176 288 193 193 449), lower := (rows 7 26 37 74 176 288 64 128 256), losses := [] }

theorem u11852 : Upper (D 7) (R 7) [6,24,33,66,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11852 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11853 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 26 37 74 304 33 192 192 448), lower := (rows 7 26 37 74 304 33 64 128 256), losses := [] }

theorem u11853 : Upper (D 7) (R 7) [6,24,33,66,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11853 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11854 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,7),(2,1),(2,7),(4,1)], upper := (rows 7 26 37 74 304 96 193 129 385), lower := (rows 7 26 37 74 304 96 64 128 256), losses := [] }

theorem u11854 : Upper (D 7) (R 7) [6,24,33,66,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11854 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11855 : Route 9 := (fun mask => (mask,id))

def c11855 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11855 : Upper (D 7) (R 7) [6,24,33,66,288,128] 13 := by
  apply FastRouting.sound _ _ [6,24,33,66,288,128] 13 (by decide) (choices 1) [1,128] r11855 c11855
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u980
  · exact u981

def b11856 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 26 37 74 400 33 224 224 480), lower := (rows 7 26 37 74 400 33 64 128 256), losses := [] }

theorem u11856 : Upper (D 7) (R 7) [6,24,33,66,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11856 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11857 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,7),(2,1),(2,7),(4,1)], upper := (rows 7 26 37 74 400 96 225 161 417), lower := (rows 7 26 37 74 400 96 64 128 256), losses := [] }

theorem u11857 : Upper (D 7) (R 7) [6,24,33,66,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11857 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11858 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(0,6),(2,1),(2,6),(4,1)], upper := (rows 7 26 37 74 400 160 97 225 353), lower := (rows 7 26 37 74 400 160 64 128 256), losses := [{ target := 6, region := (rows 11 2 6 8 16 176 0 128 256), good := (rows 7 63 37 15 432 160 0 160 256) }] }

theorem u11858 : Upper (D 7) (R 7) [6,24,33,66,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11858 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11859 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 7 26 37 104 208 33 450 386 386), lower := (rows 7 26 37 104 208 33 64 128 256), losses := [] }

theorem u11859 : Upper (D 7) (R 7) [6,24,33,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11859 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11860 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 26 37 104 208 34 449 385 385), lower := (rows 7 26 37 104 208 34 64 128 256), losses := [] }

theorem u11860 : Upper (D 7) (R 7) [6,24,33,96,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11861 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 4, region := 42, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 7 26 37 104 208 160 323 387 259), lower := (rows 7 26 37 104 208 160 64 128 256), losses := [] }

theorem u11861 : Upper (D 7) (R 7) [6,24,33,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11861 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11862 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,6),(2,6),(4,5)], upper := (rows 7 26 37 104 208 288 195 131 387), lower := (rows 7 26 37 104 208 288 64 128 256), losses := [] }

theorem u11862 : Upper (D 7) (R 7) [6,24,33,96,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11862 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11863 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 26 37 104 273 34 192 192 448), lower := (rows 7 26 37 104 273 34 64 128 256), losses := [] }

theorem u11863 : Upper (D 7) (R 7) [6,24,33,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11864 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 26 37 104 273 96 194 130 386), lower := (rows 7 26 37 104 273 96 64 128 256), losses := [] }

theorem u11864 : Upper (D 7) (R 7) [6,24,33,96,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11864 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11865 : Route 9 := (fun mask => (mask,id))

def c11865 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11865 : Upper (D 7) (R 7) [6,24,33,96,257,128] 13 := by
  apply FastRouting.sound _ _ [6,24,33,96,257,128] 13 (by decide) (choices 1) [2,128] r11865 c11865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u982
  · exact u983

def b11866 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 26 37 104 274 33 192 192 448), lower := (rows 7 26 37 104 274 33 64 128 256), losses := [] }

theorem u11866 : Upper (D 7) (R 7) [6,24,33,96,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11866 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11867 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 26 37 104 274 96 193 129 385), lower := (rows 7 26 37 104 274 96 64 128 256), losses := [] }

theorem u11867 : Upper (D 7) (R 7) [6,24,33,96,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11868 : Route 9 := (fun mask => (mask,id))

def c11868 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11868 : Upper (D 7) (R 7) [6,24,33,96,258,128] 13 := by
  apply FastRouting.sound _ _ [6,24,33,96,258,128] 13 (by decide) (choices 1) [1,128] r11868 c11868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u984
  · exact u985

def b11869 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 7 26 37 104 336 33 194 130 386), lower := (rows 7 26 37 104 336 33 64 128 256), losses := [] }

theorem u11869 : Upper (D 7) (R 7) [6,24,33,96,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11869 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11870 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 26 37 104 336 34 193 129 385), lower := (rows 7 26 37 104 336 34 64 128 256), losses := [] }

theorem u11870 : Upper (D 7) (R 7) [6,24,33,96,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11870 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11871 : Route 9 := (fun mask => (mask,id))

def c11871 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11871 : Upper (D 7) (R 7) [6,24,33,96,320,128] 13 := by
  apply FastRouting.sound _ _ [6,24,33,96,320,128] 13 (by decide) (choices 1) [1,2,128] r11871 c11871
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u986
  · exact u987
  · exact u988

def b11872 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 26 37 104 400 33 194 194 450), lower := (rows 7 26 37 104 400 33 64 128 256), losses := [] }

theorem u11872 : Upper (D 7) (R 7) [6,24,33,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11872 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11873 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 26 37 104 400 34 193 193 449), lower := (rows 7 26 37 104 400 34 64 128 256), losses := [] }

theorem u11873 : Upper (D 7) (R 7) [6,24,33,96,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11873 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11874 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 26 37 104 400 96 195 131 387), lower := (rows 7 26 37 104 400 96 64 128 256), losses := [] }

theorem u11874 : Upper (D 7) (R 7) [6,24,33,96,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11874 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11875 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(0,6),(2,6),(3,7),(4,5)], upper := (rows 7 26 37 104 400 160 67 195 323), lower := (rows 7 26 37 104 400 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 6 8 16 176 0 128 256), good := (rows 7 63 37 40 432 160 0 160 256) },{ target := 7, region := (rows 1 2 4 12 16 32 65 0 257), good := (rows 335 26 365 104 272 32 64 0 256) }] }

theorem u11875 : Upper (D 7) (R 7) [6,24,33,96,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11875 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11876 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 26 37 200 273 34 224 224 480), lower := (rows 7 26 37 200 273 34 64 128 256), losses := [] }

theorem u11876 : Upper (D 7) (R 7) [6,24,33,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11877 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 234, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 7 26 37 200 273 96 226 162 418), lower := (rows 7 26 37 200 273 96 64 128 256), losses := [{ target := 7, region := (rows 3 2 6 8 16 104 64 0 256), good := (rows 7 63 37 104 273 96 96 0 256) }] }

theorem u11877 : Upper (D 7) (R 7) [6,24,33,192,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11877 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11878 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 26 37 200 274 33 224 224 480), lower := (rows 7 26 37 200 274 33 64 128 256), losses := [] }

theorem u11878 : Upper (D 7) (R 7) [6,24,33,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11878 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11879 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(0,7),(2,1),(3,1),(4,6)], upper := (rows 7 26 37 200 274 96 225 161 417), lower := (rows 7 26 37 200 274 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 8 17 32 0 132 260), good := (rows 407 26 437 136 274 32 0 128 256) },{ target := 7, region := (rows 19 2 6 8 16 104 64 0 256), good := (rows 7 63 37 104 279 96 96 0 256) }] }

theorem u11879 : Upper (D 7) (R 7) [6,24,33,192,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11879 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u11879
end Delivery.IrregularNine14.P07
