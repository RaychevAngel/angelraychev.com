import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0048
import IrregularNine14P06C0049

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13800 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 196 28 304 96 67 131 259), lower := (rows 11 38 196 28 304 96 64 128 256), losses := [] }

theorem u13800 : Upper (D 6) (R 6) [10,36,192,20,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13800 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13801 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 11 38 196 56 81 33 326 390 262), lower := (rows 11 38 196 56 81 33 64 128 256), losses := [] }

theorem u13801 : Upper (D 6) (R 6) [10,36,192,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13801 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13802 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 196 56 81 34 325 389 261), lower := (rows 11 38 196 56 81 34 64 128 256), losses := [] }

theorem u13802 : Upper (D 6) (R 6) [10,36,192,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13802 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13803 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 56 81 36 323 387 259), lower := (rows 11 38 196 56 81 36 64 128 256), losses := [] }

theorem u13803 : Upper (D 6) (R 6) [10,36,192,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13803 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13804 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 196 56 81 288 71 135 263), lower := (rows 11 38 196 56 81 288 64 128 256), losses := [] }

theorem u13804 : Upper (D 6) (R 6) [10,36,192,48,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13804 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13805 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 11 38 196 56 273 33 70 198 326), lower := (rows 11 38 196 56 273 33 64 128 256), losses := [] }

theorem u13805 : Upper (D 6) (R 6) [10,36,192,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13805 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13806 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 196 56 273 34 69 197 325), lower := (rows 11 38 196 56 273 34 64 128 256), losses := [] }

theorem u13806 : Upper (D 6) (R 6) [10,36,192,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13806 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13807 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 56 273 36 67 195 323), lower := (rows 11 38 196 56 273 36 64 128 256), losses := [] }

theorem u13807 : Upper (D 6) (R 6) [10,36,192,48,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13807 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13808 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 196 56 273 96 71 135 263), lower := (rows 11 38 196 56 273 96 64 128 256), losses := [] }

theorem u13808 : Upper (D 6) (R 6) [10,36,192,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13808 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13809 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 196 56 276 33 67 195 323), lower := (rows 11 38 196 56 276 33 64 128 256), losses := [] }

theorem u13809 : Upper (D 6) (R 6) [10,36,192,48,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13809 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13810 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 196 56 276 34 65 193 321), lower := (rows 11 38 196 56 276 34 64 128 256), losses := [] }

theorem u13810 : Upper (D 6) (R 6) [10,36,192,48,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13810 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13811 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 196 56 276 96 67 131 259), lower := (rows 11 38 196 56 276 96 64 128 256), losses := [] }

theorem u13811 : Upper (D 6) (R 6) [10,36,192,48,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13811 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13812 : Route 9 := (fun mask => (mask,id))

def c13812 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13812 : Upper (D 6) (R 6) [10,36,192,48,320,1] 13 := by
  apply FastRouting.sound _ _ [10,36,192,48,320,1] 13 (by decide) (choices 1) [1,2,4] r13812 c13812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2935
  · exact u2936
  · exact u2937

def b13813 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 196 56 336 34 69 133 261), lower := (rows 11 38 196 56 336 34 64 128 256), losses := [] }

theorem u13813 : Upper (D 6) (R 6) [10,36,192,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13813 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13814 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 56 336 36 67 131 259), lower := (rows 11 38 196 56 336 36 64 128 256), losses := [] }

theorem u13814 : Upper (D 6) (R 6) [10,36,192,48,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13814 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13815 : PairBound 9 := { available := 276, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 38 196 73 49 34 340 404 276), lower := (rows 11 38 196 73 49 34 64 128 256), losses := [] }

theorem u13815 : Upper (D 6) (R 6) [10,36,192,65,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13815 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13816 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 73 49 36 338 402 274), lower := (rows 11 38 196 73 49 36 64 128 256), losses := [] }

theorem u13816 : Upper (D 6) (R 6) [10,36,192,65,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13816 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13817 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 196 73 49 48 326 390 262), lower := (rows 11 38 196 73 49 48 64 128 256), losses := [] }

theorem u13817 : Upper (D 6) (R 6) [10,36,192,65,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13817 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13818 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 198, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 38 196 73 49 288 86 150 278), lower := (rows 11 38 196 73 49 288 64 128 256), losses := [] }

theorem u13818 : Upper (D 6) (R 6) [10,36,192,65,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13818 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13819 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 4, region := 230, targets := 1 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 196 73 273 34 116 180 308), lower := (rows 11 38 196 73 273 34 64 128 256), losses := [] }

theorem u13819 : Upper (D 6) (R 6) [10,36,192,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13819 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13820 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 73 273 36 114 178 306), lower := (rows 11 38 196 73 273 36 64 128 256), losses := [] }

theorem u13820 : Upper (D 6) (R 6) [10,36,192,65,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13820 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13821 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 230, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 38 196 73 273 48 102 166 294), lower := (rows 11 38 196 73 273 48 64 128 256), losses := [] }

theorem u13821 : Upper (D 6) (R 6) [10,36,192,65,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13821 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13822 : PairBound 9 := { available := 52, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 196 73 274 33 116 180 308), lower := (rows 11 38 196 73 274 33 64 128 256), losses := [] }

theorem u13822 : Upper (D 6) (R 6) [10,36,192,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13822 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13823 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 73 274 36 113 177 305), lower := (rows 11 38 196 73 274 36 64 128 256), losses := [] }

theorem u13823 : Upper (D 6) (R 6) [10,36,192,65,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13823 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13824 : Route 9 := (fun mask => (mask,id))

def c13824 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13824 : Upper (D 6) (R 6) [10,36,192,65,258,16] 13 := by
  apply FastRouting.sound _ _ [10,36,192,65,258,16] 13 (by decide) (choices 1) [1,4,32] r13824 c13824
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2938
  · exact u2939
  · exact u2940

def b13825 : PairBound 9 := { available := 50, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 196 73 276 33 114 178 306), lower := (rows 11 38 196 73 276 33 64 128 256), losses := [] }

theorem u13825 : Upper (D 6) (R 6) [10,36,192,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13825 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13826 : Route 9 := (fun mask => (mask,id))

def c13826 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13826 : Upper (D 6) (R 6) [10,36,192,65,260,2] 13 := by
  apply FastRouting.sound _ _ [10,36,192,65,260,2] 13 (by decide) (choices 1) [1,16,32] r13826 c13826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2941
  · exact u2942
  · exact u2943

def b13827 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 196 73 276 48 99 163 291), lower := (rows 11 38 196 73 276 48 64 128 256), losses := [] }

theorem u13827 : Upper (D 6) (R 6) [10,36,192,65,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13827 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13828 : PairBound 9 := { available := 22, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 196 73 304 33 86 150 278), lower := (rows 11 38 196 73 304 33 64 128 256), losses := [] }

theorem u13828 : Upper (D 6) (R 6) [10,36,192,65,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13828 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13829 : Route 9 := (fun mask => (mask,id))

def c13829 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13829 : Upper (D 6) (R 6) [10,36,192,65,288,2] 13 := by
  apply FastRouting.sound _ _ [10,36,192,65,288,2] 13 (by decide) (choices 1) [1,4,16] r13829 c13829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2944
  · exact u2945
  · exact u2946

def b13830 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 73 304 36 83 147 275), lower := (rows 11 38 196 73 304 36 64 128 256), losses := [] }

theorem u13830 : Upper (D 6) (R 6) [10,36,192,65,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13830 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13831 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 38 196 73 304 48 71 135 263), lower := (rows 11 38 196 73 304 48 64 128 256), losses := [] }

theorem u13831 : Upper (D 6) (R 6) [10,36,192,65,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13831 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13832 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 38 196 88 49 33 326 390 262), lower := (rows 11 38 196 88 49 33 64 128 256), losses := [] }

theorem u13832 : Upper (D 6) (R 6) [10,36,192,80,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13832 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13833 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 38 196 88 49 34 325 389 261), lower := (rows 11 38 196 88 49 34 64 128 256), losses := [] }

theorem u13833 : Upper (D 6) (R 6) [10,36,192,80,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13833 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13834 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 88 49 36 323 387 259), lower := (rows 11 38 196 88 49 36 64 128 256), losses := [] }

theorem u13834 : Upper (D 6) (R 6) [10,36,192,80,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13834 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13835 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 11 38 196 88 49 288 71 135 263), lower := (rows 11 38 196 88 49 288 64 128 256), losses := [{ target := 5, region := (rows 1 2 21 24 16 0 65 129 257), good := (rows 463 6 196 92 477 256 64 128 256) }] }

theorem u13835 : Upper (D 6) (R 6) [10,36,192,80,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13835 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13836 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(2,0),(4,6)], upper := (rows 11 38 196 88 273 33 102 166 294), lower := (rows 11 38 196 88 273 33 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 8 17 49 0 130 258), good := (rows 443 422 132 56 305 49 0 128 256) }] }

theorem u13836 : Upper (D 6) (R 6) [10,36,192,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13836 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13837 : Route 9 := (fun mask => (mask,id))

def c13837 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13837 : Upper (D 6) (R 6) [10,36,192,80,257,2] 13 := by
  apply FastRouting.sound _ _ [10,36,192,80,257,2] 13 (by decide) (choices 1) [1,4,32] r13837 c13837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2947
  · exact u2948
  · exact u2949

def b13838 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 88 273 36 99 163 291), lower := (rows 11 38 196 88 273 36 64 128 256), losses := [] }

theorem u13838 : Upper (D 6) (R 6) [10,36,192,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13838 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13839 : Route 9 := (fun mask => (mask,id))

def c13839 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13839 : Upper (D 6) (R 6) [10,36,192,80,258,1] 13 := by
  apply FastRouting.sound _ _ [10,36,192,80,258,1] 13 (by decide) (choices 1) [1,4,32] r13839 c13839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2950
  · exact u2951
  · exact u2952

def b13840 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 88 274 36 97 161 289), lower := (rows 11 38 196 88 274 36 64 128 256), losses := [] }

theorem u13840 : Upper (D 6) (R 6) [10,36,192,80,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13840 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13841 : Route 9 := (fun mask => (mask,id))

def c13841 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13841 : Upper (D 6) (R 6) [10,36,192,80,260,1] 13 := by
  apply FastRouting.sound _ _ [10,36,192,80,260,1] 13 (by decide) (choices 1) [1,2,32] r13841 c13841
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2953
  · exact u2954
  · exact u2955

def b13842 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 34, targets := 65 }], pairs := [(0,6),(1,0),(1,6)], upper := (rows 11 38 196 88 276 34 97 161 289), lower := (rows 11 38 196 88 276 34 64 128 256), losses := [{ target := 6, region := (rows 9 22 4 8 16 63 0 137 265), good := (rows 427 38 166 443 310 34 0 128 256) }] }

theorem u13842 : Upper (D 6) (R 6) [10,36,192,80,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13842 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13843 : Route 9 := (fun mask => (mask,id))

def c13843 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13843 : Upper (D 6) (R 6) [10,36,192,80,288,1] 13 := by
  apply FastRouting.sound _ _ [10,36,192,80,288,1] 13 (by decide) (choices 1) [1,2,4] r13843 c13843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2956
  · exact u2957
  · exact u2958

def b13844 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 11 38 196 88 304 34 69 133 261), lower := (rows 11 38 196 88 304 34 64 128 256), losses := [] }

theorem u13844 : Upper (D 6) (R 6) [10,36,192,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13844 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13845 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 88 304 36 67 131 259), lower := (rows 11 38 196 88 304 36 64 128 256), losses := [] }

theorem u13845 : Upper (D 6) (R 6) [10,36,192,80,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13845 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13846 : Route 9 := (fun mask => (mask,id))

def c13846 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13846 : Upper (D 6) (R 6) [10,36,192,96,257,1] 13 := by
  apply FastRouting.sound _ _ [10,36,192,96,257,1] 13 (by decide) (choices 1) [2,4,16] r13846 c13846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2959
  · exact u2960
  · exact u2961

def b13847 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 196 104 273 34 85 149 277), lower := (rows 11 38 196 104 273 34 64 128 256), losses := [] }

theorem u13847 : Upper (D 6) (R 6) [10,36,192,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13847 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13848 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 104 273 36 83 147 275), lower := (rows 11 38 196 104 273 36 64 128 256), losses := [] }

theorem u13848 : Upper (D 6) (R 6) [10,36,192,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13848 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13849 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 196 104 273 48 71 135 263), lower := (rows 11 38 196 104 273 48 64 128 256), losses := [] }

theorem u13849 : Upper (D 6) (R 6) [10,36,192,96,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13849 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13850 : Route 9 := (fun mask => (mask,id))

def c13850 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13850 : Upper (D 6) (R 6) [10,36,192,96,258,1] 13 := by
  apply FastRouting.sound _ _ [10,36,192,96,258,1] 13 (by decide) (choices 1) [1,4,16] r13850 c13850
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2962
  · exact u2963
  · exact u2964

def b13851 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 104 274 36 81 145 273), lower := (rows 11 38 196 104 274 36 64 128 256), losses := [] }

theorem u13851 : Upper (D 6) (R 6) [10,36,192,96,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13851 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13852 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 196 104 274 48 69 133 261), lower := (rows 11 38 196 104 274 48 64 128 256), losses := [] }

theorem u13852 : Upper (D 6) (R 6) [10,36,192,96,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13852 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13853 : Route 9 := (fun mask => (mask,id))

def c13853 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13853 : Upper (D 6) (R 6) [10,36,192,96,260,1] 13 := by
  apply FastRouting.sound _ _ [10,36,192,96,260,1] 13 (by decide) (choices 1) [1,2,16] r13853 c13853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2965
  · exact u2966
  · exact u2967

def b13854 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 196 104 276 34 81 145 273), lower := (rows 11 38 196 104 276 34 64 128 256), losses := [] }

theorem u13854 : Upper (D 6) (R 6) [10,36,192,96,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13854 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13855 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 196 104 276 48 67 131 259), lower := (rows 11 38 196 104 276 48 64 128 256), losses := [] }

theorem u13855 : Upper (D 6) (R 6) [10,36,192,96,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13855 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13856 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 4, region := 230, targets := 1 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 196 265 21 34 112 240 368), lower := (rows 11 38 196 265 21 34 64 128 256), losses := [] }

theorem u13856 : Upper (D 6) (R 6) [10,36,192,257,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13856 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13857 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 329, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 196 265 21 48 98 226 354), lower := (rows 11 38 196 265 21 48 64 128 256), losses := [] }

theorem u13857 : Upper (D 6) (R 6) [10,36,192,257,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13857 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13858 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 196 265 21 96 114 178 306), lower := (rows 11 38 196 265 21 96 64 128 256), losses := [] }

theorem u13858 : Upper (D 6) (R 6) [10,36,192,257,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13858 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13859 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 38 196 265 49 34 84 212 340), lower := (rows 11 38 196 265 49 34 64 128 256), losses := [] }

theorem u13859 : Upper (D 6) (R 6) [10,36,192,257,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13859 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u13859
end Delivery.IrregularNine14.P06
