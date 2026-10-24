import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0034
import IrregularNine14P06C0035

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11820 : PairBound 9 := { available := 7, camps := [], pairs := [(0,2),(2,6),(3,2)], upper := (rows 11 22 164 41 336 96 71 135 263), lower := (rows 11 22 164 41 336 96 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 10 16 112 64 128 256), good := (rows 11 59 160 41 368 96 96 128 256) },{ target := 6, region := (rows 1 2 12 8 16 32 0 129 257), good := (rows 399 22 164 429 272 32 0 128 256) }] }

theorem u11820 : Upper (D 6) (R 6) [10,20,160,33,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11820 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11821 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 5, region := 196, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 22 164 73 273 34 100 228 356), lower := (rows 11 22 164 73 273 34 64 128 256), losses := [] }

theorem u11821 : Upper (D 6) (R 6) [10,20,160,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11821 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11822 : PairBound 9 := { available := 98, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 22 164 73 273 36 98 226 354), lower := (rows 11 22 164 73 273 36 64 128 256), losses := [] }

theorem u11822 : Upper (D 6) (R 6) [10,20,160,65,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11822 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11823 : Route 9 := (fun mask => (mask,id))

def c11823 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11823 : Upper (D 6) (R 6) [10,20,160,65,257,64] 13 := by
  apply FastRouting.sound _ _ [10,20,160,65,257,64] 13 (by decide) (choices 1) [2,4,32] r11823 c11823
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2062
  · exact u2063
  · exact u2064

def b11824 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 164 73 274 33 100 228 356), lower := (rows 11 22 164 73 274 33 64 128 256), losses := [] }

theorem u11824 : Upper (D 6) (R 6) [10,20,160,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11824 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11825 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 22 164 73 274 36 97 225 353), lower := (rows 11 22 164 73 274 36 64 128 256), losses := [] }

theorem u11825 : Upper (D 6) (R 6) [10,20,160,65,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11825 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11826 : Route 9 := (fun mask => (mask,id))

def c11826 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11826 : Upper (D 6) (R 6) [10,20,160,65,258,64] 13 := by
  apply FastRouting.sound _ _ [10,20,160,65,258,64] 13 (by decide) (choices 1) [1,4,32] r11826 c11826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2065
  · exact u2066
  · exact u2067

def b11827 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 164 73 304 33 70 198 326), lower := (rows 11 22 164 73 304 33 64 128 256), losses := [] }

theorem u11827 : Upper (D 6) (R 6) [10,20,160,65,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11827 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11828 : Route 9 := (fun mask => (mask,id))

def c11828 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11828 : Upper (D 6) (R 6) [10,20,160,65,288,2] 13 := by
  apply FastRouting.sound _ _ [10,20,160,65,288,2] 13 (by decide) (choices 1) [1,4] r11828 c11828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2068
  · exact u2069

def b11829 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 22 164 73 304 36 67 195 323), lower := (rows 11 22 164 73 304 36 64 128 256), losses := [] }

theorem u11829 : Upper (D 6) (R 6) [10,20,160,65,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11829 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11830 : Route 9 := (fun mask => (mask,id))

def c11830 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11830 : Upper (D 6) (R 6) [10,20,160,65,288,64] 13 := by
  apply FastRouting.sound _ _ [10,20,160,65,288,64] 13 (by decide) (choices 1) [1,2,4] r11830 c11830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2070
  · exact u2071
  · exact u2072

def b11831 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 164 73 336 33 102 166 294), lower := (rows 11 22 164 73 336 33 64 128 256), losses := [] }

theorem u11831 : Upper (D 6) (R 6) [10,20,160,65,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11831 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11832 : Route 9 := (fun mask => (mask,id))

def c11832 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11832 : Upper (D 6) (R 6) [10,20,160,65,320,2] 13 := by
  apply FastRouting.sound _ _ [10,20,160,65,320,2] 13 (by decide) (choices 1) [1,4,32] r11832 c11832
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2073
  · exact u2074
  · exact u2075

def b11833 : PairBound 9 := { available := 35, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 22 164 73 336 36 99 163 291), lower := (rows 11 22 164 73 336 36 64 128 256), losses := [] }

theorem u11833 : Upper (D 6) (R 6) [10,20,160,65,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11833 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11834 : Route 9 := (fun mask => (mask,id))

def c11834 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11834 : Upper (D 6) (R 6) [10,20,160,68,257,1] 13 := by
  apply FastRouting.sound _ _ [10,20,160,68,257,1] 13 (by decide) (choices 1) [2,32] r11834 c11834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2076
  · exact u2077

def r11835 : Route 9 := (fun mask => (mask,id))

def c11835 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11835 : Upper (D 6) (R 6) [10,20,160,68,257,2] 13 := by
  apply FastRouting.sound _ _ [10,20,160,68,257,2] 13 (by decide) (choices 1) [1,32] r11835 c11835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2078
  · exact u2079

def r11836 : Route 9 := (fun mask => (mask,id))

def c11836 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11836 : Upper (D 6) (R 6) [10,20,160,68,257,64] 13 := by
  apply FastRouting.sound _ _ [10,20,160,68,257,64] 13 (by decide) (choices 1) [1,2,32] r11836 c11836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2080
  · exact u2081
  · exact u2082

def r11837 : Route 9 := (fun mask => (mask,id))

def c11837 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11837 : Upper (D 6) (R 6) [10,20,160,68,320,1] 13 := by
  apply FastRouting.sound _ _ [10,20,160,68,320,1] 13 (by decide) (choices 1) [1,2,32] r11837 c11837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2083
  · exact u2084
  · exact u2085

def r11838 : Route 9 := (fun mask => (mask,id))

def c11838 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11838 : Upper (D 6) (R 6) [10,20,160,68,320,2] 13 := by
  apply FastRouting.sound _ _ [10,20,160,68,320,2] 13 (by decide) (choices 1) [1,32] r11838 c11838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2086
  · exact u2087

def b11839 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 40, targets := 6 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(3,1),(3,2)], upper := (rows 11 22 164 104 81 33 326 390 262), lower := (rows 11 22 164 104 81 33 64 128 256), losses := [] }

theorem u11839 : Upper (D 6) (R 6) [10,20,160,96,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11839 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11840 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6),(3,0)], upper := (rows 11 22 164 104 81 34 325 389 261), lower := (rows 11 22 164 104 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 35 64 128 256), good := (rows 42 62 164 104 120 34 64 128 256) }] }

theorem u11840 : Upper (D 6) (R 6) [10,20,160,96,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11840 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11841 : PairBound 9 := { available := 259, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 22 164 104 81 36 323 387 259), lower := (rows 11 22 164 104 81 36 64 128 256), losses := [] }

theorem u11841 : Upper (D 6) (R 6) [10,20,160,96,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11841 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11842 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 22 164 104 81 288 71 135 263), lower := (rows 11 22 164 104 81 288 64 128 256), losses := [] }

theorem u11842 : Upper (D 6) (R 6) [10,20,160,96,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11842 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11843 : Route 9 := (fun mask => (mask,id))

def c11843 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11843 : Upper (D 6) (R 6) [10,20,160,96,257,1] 13 := by
  apply FastRouting.sound _ _ [10,20,160,96,257,1] 13 (by decide) (choices 1) [2,4] r11843 c11843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2088
  · exact u2089

def r11844 : Route 9 := (fun mask => (mask,id))

def c11844 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11844 : Upper (D 6) (R 6) [10,20,160,96,257,2] 13 := by
  apply FastRouting.sound _ _ [10,20,160,96,257,2] 13 (by decide) (choices 1) [1,4] r11844 c11844
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2090
  · exact u2091

def b11845 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 22 164 104 273 36 67 195 323), lower := (rows 11 22 164 104 273 36 64 128 256), losses := [] }

theorem u11845 : Upper (D 6) (R 6) [10,20,160,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11845 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11846 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 164 104 273 96 71 135 263), lower := (rows 11 22 164 104 273 96 64 128 256), losses := [] }

theorem u11846 : Upper (D 6) (R 6) [10,20,160,96,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11846 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11847 : Route 9 := (fun mask => (mask,id))

def c11847 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11847 : Upper (D 6) (R 6) [10,20,160,96,258,1] 13 := by
  apply FastRouting.sound _ _ [10,20,160,96,258,1] 13 (by decide) (choices 1) [1,4] r11847 c11847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2092
  · exact u2093

def b11848 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 22 164 104 274 36 65 193 321), lower := (rows 11 22 164 104 274 36 64 128 256), losses := [] }

theorem u11848 : Upper (D 6) (R 6) [10,20,160,96,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11848 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11849 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 164 104 274 96 69 133 261), lower := (rows 11 22 164 104 274 96 64 128 256), losses := [] }

theorem u11849 : Upper (D 6) (R 6) [10,20,160,96,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11850 : Route 9 := (fun mask => (mask,id))

def c11850 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11850 : Upper (D 6) (R 6) [10,20,160,96,320,1] 13 := by
  apply FastRouting.sound _ _ [10,20,160,96,320,1] 13 (by decide) (choices 1) [1,2,4] r11850 c11850
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2094
  · exact u2095
  · exact u2096

def r11851 : Route 9 := (fun mask => (mask,id))

def c11851 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11851 : Upper (D 6) (R 6) [10,20,160,96,320,2] 13 := by
  apply FastRouting.sound _ _ [10,20,160,96,320,2] 13 (by decide) (choices 1) [1,4] r11851 c11851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2097
  · exact u2098

def b11852 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 22 164 104 336 36 67 131 259), lower := (rows 11 22 164 104 336 36 64 128 256), losses := [] }

theorem u11852 : Upper (D 6) (R 6) [10,20,160,96,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11852 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11853 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 166, targets := 1 },{ cop := 5, region := 196, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 22 164 265 81 34 100 228 356), lower := (rows 11 22 164 265 81 34 64 128 256), losses := [] }

theorem u11853 : Upper (D 6) (R 6) [10,20,160,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11853 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11854 : PairBound 9 := { available := 98, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 22 164 265 81 36 98 226 354), lower := (rows 11 22 164 265 81 36 64 128 256), losses := [] }

theorem u11854 : Upper (D 6) (R 6) [10,20,160,257,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11854 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11855 : Route 9 := (fun mask => (mask,id))

def c11855 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11855 : Upper (D 6) (R 6) [10,20,160,257,65,64] 13 := by
  apply FastRouting.sound _ _ [10,20,160,257,65,64] 13 (by decide) (choices 1) [2,4,32] r11855 c11855
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2099
  · exact u2100
  · exact u2101

def b11856 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 164 265 82 33 100 228 356), lower := (rows 11 22 164 265 82 33 64 128 256), losses := [] }

theorem u11856 : Upper (D 6) (R 6) [10,20,160,257,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11856 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11857 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 22 164 265 82 36 97 225 353), lower := (rows 11 22 164 265 82 36 64 128 256), losses := [] }

theorem u11857 : Upper (D 6) (R 6) [10,20,160,257,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11857 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11858 : Route 9 := (fun mask => (mask,id))

def c11858 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11858 : Upper (D 6) (R 6) [10,20,160,257,66,64] 13 := by
  apply FastRouting.sound _ _ [10,20,160,257,66,64] 13 (by decide) (choices 1) [1,4,32] r11858 c11858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2102
  · exact u2103
  · exact u2104

def b11859 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 164 265 112 33 70 198 326), lower := (rows 11 22 164 265 112 33 64 128 256), losses := [] }

theorem u11859 : Upper (D 6) (R 6) [10,20,160,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11859 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11860 : Route 9 := (fun mask => (mask,id))

def c11860 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11860 : Upper (D 6) (R 6) [10,20,160,257,96,2] 13 := by
  apply FastRouting.sound _ _ [10,20,160,257,96,2] 13 (by decide) (choices 1) [1,4] r11860 c11860
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2105
  · exact u2106

def b11861 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 22 164 265 112 36 67 195 323), lower := (rows 11 22 164 265 112 36 64 128 256), losses := [] }

theorem u11861 : Upper (D 6) (R 6) [10,20,160,257,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11861 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11862 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 164 265 112 96 71 135 263), lower := (rows 11 22 164 265 112 96 64 128 256), losses := [] }

theorem u11862 : Upper (D 6) (R 6) [10,20,160,257,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11862 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11863 : Route 9 := (fun mask => (mask,id))

def c11863 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11863 : Upper (D 6) (R 6) [10,20,160,260,65,1] 13 := by
  apply FastRouting.sound _ _ [10,20,160,260,65,1] 13 (by decide) (choices 1) [2,32] r11863 c11863
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2107
  · exact u2108

def r11864 : Route 9 := (fun mask => (mask,id))

def c11864 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11864 : Upper (D 6) (R 6) [10,20,160,260,65,2] 13 := by
  apply FastRouting.sound _ _ [10,20,160,260,65,2] 13 (by decide) (choices 1) [1,32] r11864 c11864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2109
  · exact u2110

def r11865 : Route 9 := (fun mask => (mask,id))

def c11865 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11865 : Upper (D 6) (R 6) [10,20,160,260,65,64] 13 := by
  apply FastRouting.sound _ _ [10,20,160,260,65,64] 13 (by decide) (choices 1) [1,2,32] r11865 c11865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2111
  · exact u2112
  · exact u2113

def r11866 : Route 9 := (fun mask => (mask,id))

def c11866 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11866 : Upper (D 6) (R 6) [10,20,160,288,65,1] 13 := by
  apply FastRouting.sound _ _ [10,20,160,288,65,1] 13 (by decide) (choices 1) [2,4] r11866 c11866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2114
  · exact u2115

def r11867 : Route 9 := (fun mask => (mask,id))

def c11867 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11867 : Upper (D 6) (R 6) [10,20,160,288,65,2] 13 := by
  apply FastRouting.sound _ _ [10,20,160,288,65,2] 13 (by decide) (choices 1) [1,4] r11867 c11867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2116
  · exact u2117

def b11868 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 22 164 296 81 36 67 195 323), lower := (rows 11 22 164 296 81 36 64 128 256), losses := [] }

theorem u11868 : Upper (D 6) (R 6) [10,20,160,288,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11868 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11869 : Route 9 := (fun mask => (mask,id))

def c11869 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11869 : Upper (D 6) (R 6) [10,20,160,288,65,64] 13 := by
  apply FastRouting.sound _ _ [10,20,160,288,65,64] 13 (by decide) (choices 1) [1,2,4] r11869 c11869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2118
  · exact u2119
  · exact u2120

def r11870 : Route 9 := (fun mask => (mask,id))

def c11870 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11870 : Upper (D 6) (R 6) [10,20,160,288,66,1] 13 := by
  apply FastRouting.sound _ _ [10,20,160,288,66,1] 13 (by decide) (choices 1) [1,4] r11870 c11870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2121
  · exact u2122

def b11871 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 22 164 296 82 36 65 193 321), lower := (rows 11 22 164 296 82 36 64 128 256), losses := [] }

theorem u11871 : Upper (D 6) (R 6) [10,20,160,288,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11871 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11872 : Route 9 := (fun mask => (mask,id))

def c11872 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11872 : Upper (D 6) (R 6) [10,20,160,288,66,64] 13 := by
  apply FastRouting.sound _ _ [10,20,160,288,66,64] 13 (by decide) (choices 1) [1,4] r11872 c11872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2123
  · exact u2124

def b11873 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 22 164 328 49 33 70 198 326), lower := (rows 11 22 164 328 49 33 64 128 256), losses := [] }

theorem u11873 : Upper (D 6) (R 6) [10,20,160,320,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11873 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11874 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 48, targets := 68 },{ cop := 1, region := 329, targets := 32 }], pairs := [(0,5),(4,2),(4,6)], upper := (rows 11 22 164 328 49 34 69 197 325), lower := (rows 11 22 164 328 49 34 64 128 256), losses := [] }

theorem u11874 : Upper (D 6) (R 6) [10,20,160,320,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11874 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11875 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 22 164 328 49 36 67 195 323), lower := (rows 11 22 164 328 49 36 64 128 256), losses := [] }

theorem u11875 : Upper (D 6) (R 6) [10,20,160,320,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11875 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11876 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 329, targets := 32 },{ cop := 4, region := 134, targets := 64 }], pairs := [(0,5),(1,6),(3,5)], upper := (rows 11 22 164 328 49 96 71 135 263), lower := (rows 11 22 164 328 49 96 64 128 256), losses := [] }

theorem u11876 : Upper (D 6) (R 6) [10,20,160,320,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11876 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11877 : Route 9 := (fun mask => (mask,id))

def c11877 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11877 : Upper (D 6) (R 6) [10,20,160,320,65,1] 13 := by
  apply FastRouting.sound _ _ [10,20,160,320,65,1] 13 (by decide) (choices 1) [2,4,32] r11877 c11877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2125
  · exact u2126
  · exact u2127

def r11878 : Route 9 := (fun mask => (mask,id))

def c11878 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11878 : Upper (D 6) (R 6) [10,20,160,320,65,2] 13 := by
  apply FastRouting.sound _ _ [10,20,160,320,65,2] 13 (by decide) (choices 1) [1,4,32] r11878 c11878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2128
  · exact u2129
  · exact u2130

def b11879 : PairBound 9 := { available := 35, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 22 164 328 81 36 99 163 291), lower := (rows 11 22 164 328 81 36 64 128 256), losses := [] }

theorem u11879 : Upper (D 6) (R 6) [10,20,160,320,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11879 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u11879
end Delivery.IrregularNine14.P06
