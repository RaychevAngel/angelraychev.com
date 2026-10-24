import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0092
import IrregularNine14P06C0093

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18900 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 196 74 273 36 99 163 291), lower := (rows 25 38 196 74 273 36 64 128 256), losses := [] }

theorem u18900 : Upper (D 6) (R 6) [24,36,192,66,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18900 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18901 : Route 9 := (fun mask => (mask,id))

def c18901 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18901 : Upper (D 6) (R 6) [24,36,192,66,258,1] 13 := by
  apply FastRouting.sound _ _ [24,36,192,66,258,1] 13 (by decide) (choices 1) [1,4,32] r18901 c18901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5577
  · exact u5578
  · exact u5579

def b18902 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 196 74 274 36 97 161 289), lower := (rows 25 38 196 74 274 36 64 128 256), losses := [] }

theorem u18902 : Upper (D 6) (R 6) [24,36,192,66,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18902 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18903 : Route 9 := (fun mask => (mask,id))

def c18903 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18903 : Upper (D 6) (R 6) [24,36,192,66,260,1] 13 := by
  apply FastRouting.sound _ _ [24,36,192,66,260,1] 13 (by decide) (choices 1) [1,2,32] r18903 c18903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5580
  · exact u5581
  · exact u5582

def b18904 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 42, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 25 38 196 74 276 34 97 161 289), lower := (rows 25 38 196 74 276 34 64 128 256), losses := [] }

theorem u18904 : Upper (D 6) (R 6) [24,36,192,66,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18904 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18905 : Route 9 := (fun mask => (mask,id))

def c18905 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18905 : Upper (D 6) (R 6) [24,36,192,66,288,1] 13 := by
  apply FastRouting.sound _ _ [24,36,192,66,288,1] 13 (by decide) (choices 1) [1,2,4] r18905 c18905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5583
  · exact u5584
  · exact u5585

def b18906 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 25 38 196 74 304 34 69 133 261), lower := (rows 25 38 196 74 304 34 64 128 256), losses := [] }

theorem u18906 : Upper (D 6) (R 6) [24,36,192,66,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18906 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18907 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 196 74 304 36 67 131 259), lower := (rows 25 38 196 74 304 36 64 128 256), losses := [] }

theorem u18907 : Upper (D 6) (R 6) [24,36,192,66,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18907 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18908 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 206, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 25 38 196 104 273 33 70 134 262), lower := (rows 25 38 196 104 273 33 64 128 256), losses := [] }

theorem u18908 : Upper (D 6) (R 6) [24,36,192,96,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18908 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18909 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 42, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 25 38 196 104 273 34 71 135 263), lower := (rows 25 38 196 104 273 34 64 128 256), losses := [] }

theorem u18909 : Upper (D 6) (R 6) [24,36,192,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18909 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18910 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 196 104 273 36 67 131 259), lower := (rows 25 38 196 104 273 36 64 128 256), losses := [] }

theorem u18910 : Upper (D 6) (R 6) [24,36,192,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18910 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18911 : Route 9 := (fun mask => (mask,id))

def c18911 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18911 : Upper (D 6) (R 6) [24,36,192,96,258,1] 13 := by
  apply FastRouting.sound _ _ [24,36,192,96,258,1] 13 (by decide) (choices 1) [1,2,4] r18911 c18911
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5586
  · exact u5587
  · exact u5588

def b18912 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 25 38 196 104 274 34 69 133 261), lower := (rows 25 38 196 104 274 34 64 128 256), losses := [] }

theorem u18912 : Upper (D 6) (R 6) [24,36,192,96,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18912 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18913 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 196 104 274 36 67 131 259), lower := (rows 25 38 196 104 274 36 64 128 256), losses := [] }

theorem u18913 : Upper (D 6) (R 6) [24,36,192,96,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18914 : Route 9 := (fun mask => (mask,id))

def c18914 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18914 : Upper (D 6) (R 6) [24,36,192,96,260,1] 13 := by
  apply FastRouting.sound _ _ [24,36,192,96,260,1] 13 (by decide) (choices 1) [1,2] r18914 c18914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5589
  · exact u5590

def b18915 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 42, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 25 38 196 104 276 34 67 131 259), lower := (rows 25 38 196 104 276 34 64 128 256), losses := [] }

theorem u18915 : Upper (D 6) (R 6) [24,36,192,96,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18915 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18916 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 1, region := 452, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 25 38 388 11 81 34 100 228 356), lower := (rows 25 38 388 11 81 34 64 128 256), losses := [] }

theorem u18916 : Upper (D 6) (R 6) [24,36,384,3,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18917 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 388 11 81 36 98 226 354), lower := (rows 25 38 388 11 81 36 64 128 256), losses := [] }

theorem u18917 : Upper (D 6) (R 6) [24,36,384,3,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18917 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18918 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 5, region := 390, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 388 11 81 96 102 166 294), lower := (rows 25 38 388 11 81 96 64 128 256), losses := [] }

theorem u18918 : Upper (D 6) (R 6) [24,36,384,3,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18918 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18919 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 38 388 11 84 33 98 226 354), lower := (rows 25 38 388 11 84 33 64 128 256), losses := [] }

theorem u18919 : Upper (D 6) (R 6) [24,36,384,3,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18919 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18920 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 38 388 11 84 34 97 225 353), lower := (rows 25 38 388 11 84 34 64 128 256), losses := [] }

theorem u18920 : Upper (D 6) (R 6) [24,36,384,3,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18920 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18921 : Route 9 := (fun mask => (mask,id))

def c18921 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18921 : Upper (D 6) (R 6) [24,36,384,3,68,64] 13 := by
  apply FastRouting.sound _ _ [24,36,384,3,68,64] 13 (by decide) (choices 1) [1,2,32] r18921 c18921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5591
  · exact u5592
  · exact u5593

def b18922 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 388 11 112 33 70 198 326), lower := (rows 25 38 388 11 112 33 64 128 256), losses := [] }

theorem u18922 : Upper (D 6) (R 6) [24,36,384,3,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18922 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18923 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 25 38 388 11 112 34 69 197 325), lower := (rows 25 38 388 11 112 34 64 128 256), losses := [] }

theorem u18923 : Upper (D 6) (R 6) [24,36,384,3,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18924 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 388 11 112 36 67 195 323), lower := (rows 25 38 388 11 112 36 64 128 256), losses := [] }

theorem u18924 : Upper (D 6) (R 6) [24,36,384,3,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18924 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18925 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 25 38 388 11 112 96 71 135 263), lower := (rows 25 38 388 11 112 96 64 128 256), losses := [] }

theorem u18925 : Upper (D 6) (R 6) [24,36,384,3,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18925 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18926 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 388 13 81 34 98 226 354), lower := (rows 25 38 388 13 81 34 64 128 256), losses := [] }

theorem u18926 : Upper (D 6) (R 6) [24,36,384,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18926 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18927 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 5, region := 390, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 388 13 81 96 98 162 290), lower := (rows 25 38 388 13 81 96 64 128 256), losses := [] }

theorem u18927 : Upper (D 6) (R 6) [24,36,384,5,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18927 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18928 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 388 13 82 33 98 226 354), lower := (rows 25 38 388 13 82 33 64 128 256), losses := [] }

theorem u18928 : Upper (D 6) (R 6) [24,36,384,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18928 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18929 : Route 9 := (fun mask => (mask,id))

def c18929 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18929 : Upper (D 6) (R 6) [24,36,384,5,66,2] 13 := by
  apply FastRouting.sound _ _ [24,36,384,5,66,2] 13 (by decide) (choices 1) [1,32] r18929 c18929
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5594
  · exact u5595

def r18930 : Route 9 := (fun mask => (mask,id))

def c18930 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18930 : Upper (D 6) (R 6) [24,36,384,5,66,64] 13 := by
  apply FastRouting.sound _ _ [24,36,384,5,66,64] 13 (by decide) (choices 1) [1,2,32] r18930 c18930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5596
  · exact u5597
  · exact u5598

def b18931 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 388 13 112 33 66 194 322), lower := (rows 25 38 388 13 112 33 64 128 256), losses := [] }

theorem u18931 : Upper (D 6) (R 6) [24,36,384,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18931 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18932 : Route 9 := (fun mask => (mask,id))

def c18932 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18932 : Upper (D 6) (R 6) [24,36,384,5,96,2] 13 := by
  apply FastRouting.sound _ _ [24,36,384,5,96,2] 13 (by decide) (choices 1) [1,2] r18932 c18932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5599
  · exact u5600

def b18933 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 25 38 388 13 112 96 67 131 259), lower := (rows 25 38 388 13 112 96 64 128 256), losses := [] }

theorem u18933 : Upper (D 6) (R 6) [24,36,384,5,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18934 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 25 38 388 41 82 33 70 198 326), lower := (rows 25 38 388 41 82 33 64 128 256), losses := [] }

theorem u18934 : Upper (D 6) (R 6) [24,36,384,33,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18934 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18935 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 25 38 388 41 82 34 69 197 325), lower := (rows 25 38 388 41 82 34 64 128 256), losses := [] }

theorem u18935 : Upper (D 6) (R 6) [24,36,384,33,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18935 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18936 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 388 41 82 36 67 195 323), lower := (rows 25 38 388 41 82 36 64 128 256), losses := [] }

theorem u18936 : Upper (D 6) (R 6) [24,36,384,33,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18936 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18937 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 25 38 388 41 82 96 71 135 263), lower := (rows 25 38 388 41 82 96 64 128 256), losses := [] }

theorem u18937 : Upper (D 6) (R 6) [24,36,384,33,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18937 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18938 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 25 38 388 41 84 33 66 194 322), lower := (rows 25 38 388 41 84 33 64 128 256), losses := [] }

theorem u18938 : Upper (D 6) (R 6) [24,36,384,33,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18938 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18939 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 38 388 41 84 34 67 195 323), lower := (rows 25 38 388 41 84 34 64 128 256), losses := [] }

theorem u18939 : Upper (D 6) (R 6) [24,36,384,33,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18939 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18940 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 25 38 388 41 84 96 67 131 259), lower := (rows 25 38 388 41 84 96 64 128 256), losses := [] }

theorem u18940 : Upper (D 6) (R 6) [24,36,384,33,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18940 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18941 : Route 9 := (fun mask => (mask,id))

def c18941 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18941 : Upper (D 6) (R 6) [24,36,384,66,68,1] 13 := by
  apply FastRouting.sound _ _ [24,36,384,66,68,1] 13 (by decide) (choices 1) [1,2,32] r18941 c18941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5601
  · exact u5602
  · exact u5603

def b18942 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 422, targets := 64 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(1,6),(2,6)], upper := (rows 25 38 388 74 84 34 97 161 289), lower := (rows 25 38 388 74 84 34 64 128 256), losses := [] }

theorem u18942 : Upper (D 6) (R 6) [24,36,384,66,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18942 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18943 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 38 388 74 112 33 71 135 263), lower := (rows 25 38 388 74 112 33 64 128 256), losses := [] }

theorem u18943 : Upper (D 6) (R 6) [24,36,384,66,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18943 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18944 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 388, targets := 34 },{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6),(2,1),(2,5)], upper := (rows 25 38 388 74 112 34 69 133 261), lower := (rows 25 38 388 74 112 34 64 128 256), losses := [] }

theorem u18944 : Upper (D 6) (R 6) [24,36,384,66,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18944 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18945 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 388 74 112 36 67 131 259), lower := (rows 25 38 388 74 112 36 64 128 256), losses := [] }

theorem u18945 : Upper (D 6) (R 6) [24,36,384,66,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18945 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18946 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 38 388 76 112 33 67 131 259), lower := (rows 25 38 388 76 112 33 64 128 256), losses := [] }

theorem u18946 : Upper (D 6) (R 6) [24,36,384,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18946 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18947 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 422, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(1,0),(1,6),(2,6)], upper := (rows 25 38 388 76 112 34 67 131 259), lower := (rows 25 38 388 76 112 34 64 128 256), losses := [] }

theorem u18947 : Upper (D 6) (R 6) [24,36,384,68,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18948 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 6, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 25 98 133 11 276 34 100 228 356), lower := (rows 25 98 133 11 276 34 64 128 256), losses := [] }

theorem u18948 : Upper (D 6) (R 6) [24,96,129,3,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18948 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18949 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 5, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 25 98 133 11 276 36 98 226 354), lower := (rows 25 98 133 11 276 36 64 128 256), losses := [] }

theorem u18949 : Upper (D 6) (R 6) [24,96,129,3,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18949 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18950 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 133 11 276 96 102 166 294), lower := (rows 25 98 133 11 276 96 64 128 256), losses := [] }

theorem u18950 : Upper (D 6) (R 6) [24,96,129,3,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18950 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18951 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 25 98 133 14 52 33 322 450 322), lower := (rows 25 98 133 14 52 33 64 128 256), losses := [] }

theorem u18951 : Upper (D 6) (R 6) [24,96,129,6,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18952 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 3, region := 49, targets := 64 }], pairs := [(0,6),(2,1),(2,5)], upper := (rows 25 98 133 14 52 34 321 449 321), lower := (rows 25 98 133 14 52 34 64 128 256), losses := [] }

theorem u18952 : Upper (D 6) (R 6) [24,96,129,6,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18952 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18953 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 133 14 52 96 323 387 259), lower := (rows 25 98 133 14 52 96 64 128 256), losses := [] }

theorem u18953 : Upper (D 6) (R 6) [24,96,129,6,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18953 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18954 : Route 9 := (fun mask => (mask,id))

def c18954 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18954 : Upper (D 6) (R 6) [24,96,129,6,36,256] 13 := by
  apply FastRouting.sound _ _ [24,96,129,6,36,256] 13 (by decide) (choices 1) [1,2] r18954 c18954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5604
  · exact u5605

def b18955 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 106, targets := 1 },{ cop := 6, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 25 98 133 14 273 34 100 228 356), lower := (rows 25 98 133 14 273 34 64 128 256), losses := [] }

theorem u18955 : Upper (D 6) (R 6) [24,96,129,6,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18955 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18956 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 106, targets := 1 },{ cop := 5, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 25 98 133 14 273 36 98 226 354), lower := (rows 25 98 133 14 273 36 64 128 256), losses := [] }

theorem u18956 : Upper (D 6) (R 6) [24,96,129,6,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18957 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 133 14 273 96 102 166 294), lower := (rows 25 98 133 14 273 96 64 128 256), losses := [] }

theorem u18957 : Upper (D 6) (R 6) [24,96,129,6,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18957 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18958 : Route 9 := (fun mask => (mask,id))

def c18958 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18958 : Upper (D 6) (R 6) [24,96,129,6,258,1] 13 := by
  apply FastRouting.sound _ _ [24,96,129,6,258,1] 13 (by decide) (choices 1) [4,32] r18958 c18958
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5606
  · exact u5607

theorem m18959_1 : Upper (D 6) (R 6) [24,96,129,6,258,4,1] 13 :=
  permutation_upper _ _ _ [24,96,129,6,258,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5606

def r18959 : Route 9 := (fun mask => (mask,id))

def c18959 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18959 : Upper (D 6) (R 6) [24,96,129,6,258,4] 13 := by
  apply FastRouting.sound _ _ [24,96,129,6,258,4] 13 (by decide) (choices 1) [1,32] r18959 c18959
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m18959_1
  · exact u5608

#print axioms u18959
end Delivery.IrregularNine14.P06
