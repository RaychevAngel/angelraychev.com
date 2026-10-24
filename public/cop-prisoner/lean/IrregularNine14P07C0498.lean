import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0193

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b29880 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 213, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 97 386 13 42 84 34 209 145 401), lower := (rows 97 386 13 42 84 34 64 128 256), losses := [] }

theorem u29880 : Upper (D 7) (R 7) [96,384,9,34,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29881 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 386 13 42 84 48 195 131 387), lower := (rows 97 386 13 42 84 48 64 128 256), losses := [] }

theorem u29881 : Upper (D 7) (R 7) [96,384,9,34,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29881 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29882 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 85, targets := 128 },{ cop := 1, region := 40, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 97 386 13 42 84 160 83 147 275), lower := (rows 97 386 13 42 84 160 64 128 256), losses := [] }

theorem u29882 : Upper (D 7) (R 7) [96,384,9,34,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29882 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29883 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 213, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 97 386 13 42 145 34 84 212 340), lower := (rows 97 386 13 42 145 34 64 128 256), losses := [] }

theorem u29883 : Upper (D 7) (R 7) [96,384,9,34,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29883 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29884 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 4, region := 322, targets := 1 }], pairs := [(1,0),(1,5),(4,5)], upper := (rows 97 386 13 42 145 36 82 210 338), lower := (rows 97 386 13 42 145 36 64 128 256), losses := [] }

theorem u29884 : Upper (D 7) (R 7) [96,384,9,34,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29884 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29885 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,7),(1,5),(4,5)], upper := (rows 97 386 13 42 145 48 70 198 326), lower := (rows 97 386 13 42 145 48 64 128 256), losses := [] }

theorem u29885 : Upper (D 7) (R 7) [96,384,9,34,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29885 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29886 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 13 42 145 96 86 150 278), lower := (rows 97 386 13 42 145 96 64 128 256), losses := [] }

theorem u29886 : Upper (D 7) (R 7) [96,384,9,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29886 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29887 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 386 13 42 148 33 82 210 338), lower := (rows 97 386 13 42 148 33 64 128 256), losses := [] }

theorem u29887 : Upper (D 7) (R 7) [96,384,9,34,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29887 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29888 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 213, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 97 386 13 42 148 34 81 209 337), lower := (rows 97 386 13 42 148 34 64 128 256), losses := [] }

theorem u29888 : Upper (D 7) (R 7) [96,384,9,34,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29888 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29889 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7),(1,5),(4,5)], upper := (rows 97 386 13 42 148 48 67 195 323), lower := (rows 97 386 13 42 148 48 64 128 256), losses := [] }

theorem u29889 : Upper (D 7) (R 7) [96,384,9,34,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29889 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29890 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 13 42 148 96 83 147 275), lower := (rows 97 386 13 42 148 96 64 128 256), losses := [] }

theorem u29890 : Upper (D 7) (R 7) [96,384,9,34,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29891 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 386 13 42 208 33 86 150 278), lower := (rows 97 386 13 42 208 33 64 128 256), losses := [] }

theorem u29891 : Upper (D 7) (R 7) [96,384,9,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29891 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29892 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 213, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 97 386 13 42 208 34 85 149 277), lower := (rows 97 386 13 42 208 34 64 128 256), losses := [] }

theorem u29892 : Upper (D 7) (R 7) [96,384,9,34,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29892 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29893 : Route 9 := (fun mask => (mask,id))

def c29893 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29893 : Upper (D 7) (R 7) [96,384,9,34,192,4] 13 := by
  apply FastRouting.sound _ _ [96,384,9,34,192,4] 13 (by decide) (choices 1) [1,2,16] r29893 c29893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11593
  · exact u11594
  · exact u11595

def b29894 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 386 13 42 208 48 71 135 263), lower := (rows 97 386 13 42 208 48 64 128 256), losses := [] }

theorem u29894 : Upper (D 7) (R 7) [96,384,9,34,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29894 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29895 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 386 13 56 22 33 194 194 450), lower := (rows 97 386 13 56 22 33 64 128 256), losses := [] }

theorem u29895 : Upper (D 7) (R 7) [96,384,9,48,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29895 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29896 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 40, targets := 193 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5),(3,0),(3,6),(3,7)], upper := (rows 97 386 13 56 22 34 193 193 449), lower := (rows 97 386 13 56 22 34 64 128 256), losses := [] }

theorem u29896 : Upper (D 7) (R 7) [96,384,9,48,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29896 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29897 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 13 56 22 96 195 131 387), lower := (rows 97 386 13 56 22 96 64 128 256), losses := [] }

theorem u29897 : Upper (D 7) (R 7) [96,384,9,48,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29897 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29898 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(3,0),(3,1),(4,5)], upper := (rows 97 386 13 56 22 160 67 195 323), lower := (rows 97 386 13 56 22 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 162 64 128 256), good := (rows 96 418 12 56 62 160 64 160 256) },{ target := 1, region := (rows 1 0 4 24 16 162 64 128 256), good := (rows 97 416 13 56 60 160 64 160 256) }] }

theorem u29898 : Upper (D 7) (R 7) [96,384,9,48,6,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29898 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29899 : PairBound 9 := { available := 134, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 386 13 56 82 33 198 134 390), lower := (rows 97 386 13 56 82 33 64 128 256), losses := [] }

theorem u29899 : Upper (D 7) (R 7) [96,384,9,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29899 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29900 : PairBound 9 := { available := 133, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 2, region := 386, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(3,7)], upper := (rows 97 386 13 56 82 34 197 133 389), lower := (rows 97 386 13 56 82 34 64 128 256), losses := [] }

theorem u29900 : Upper (D 7) (R 7) [96,384,9,48,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29900 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29901 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 386 13 56 82 36 195 131 387), lower := (rows 97 386 13 56 82 36 64 128 256), losses := [] }

theorem u29901 : Upper (D 7) (R 7) [96,384,9,48,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29901 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29902 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 2, region := 386, targets := 64 }], pairs := [(1,5),(1,6),(3,0),(4,5)], upper := (rows 97 386 13 56 82 160 71 135 263), lower := (rows 97 386 13 56 82 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 162 64 128 256), good := (rows 96 418 12 56 122 160 64 160 256) }] }

theorem u29902 : Upper (D 7) (R 7) [96,384,9,48,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29902 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29903 : Route 9 := (fun mask => (mask,id))

def c29903 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29903 : Upper (D 7) (R 7) [96,384,9,48,129,2] 13 := by
  apply FastRouting.sound _ _ [96,384,9,48,129,2] 13 (by decide) (choices 1) [2,4] r29903 c29903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11596
  · exact u11597

def b29904 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 44, targets := 194 }], pairs := [(2,1),(2,6),(2,7)], upper := (rows 97 386 13 56 145 36 66 194 322), lower := (rows 97 386 13 56 145 36 64 128 256), losses := [] }

theorem u29904 : Upper (D 7) (R 7) [96,384,9,48,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29904 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29905 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 13 56 145 96 70 134 262), lower := (rows 97 386 13 56 145 96 64 128 256), losses := [] }

theorem u29905 : Upper (D 7) (R 7) [96,384,9,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29905 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29906 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 386 13 56 148 33 66 194 322), lower := (rows 97 386 13 56 148 33 64 128 256), losses := [] }

theorem u29906 : Upper (D 7) (R 7) [96,384,9,48,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29906 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29907 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7),(1,5),(2,7),(4,5)], upper := (rows 97 386 13 56 148 34 67 195 323), lower := (rows 97 386 13 56 148 34 64 128 256), losses := [{ target := 7, region := (rows 43 2 12 8 16 34 98 0 290), good := (rows 353 355 13 381 20 355 64 0 256) }] }

theorem u29907 : Upper (D 7) (R 7) [96,384,9,48,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29907 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29908 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 13 56 148 96 67 131 259), lower := (rows 97 386 13 56 148 96 64 128 256), losses := [] }

theorem u29908 : Upper (D 7) (R 7) [96,384,9,48,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29908 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29909 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 386 13 56 208 33 70 134 262), lower := (rows 97 386 13 56 208 33 64 128 256), losses := [] }

theorem u29909 : Upper (D 7) (R 7) [96,384,9,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29910 : Route 9 := (fun mask => (mask,id))

def c29910 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29910 : Upper (D 7) (R 7) [96,384,9,48,192,2] 13 := by
  apply FastRouting.sound _ _ [96,384,9,48,192,2] 13 (by decide) (choices 1) [1,2,4] r29910 c29910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11598
  · exact u11599
  · exact u11600

def b29911 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 386 13 56 208 36 67 131 259), lower := (rows 97 386 13 56 208 36 64 128 256), losses := [] }

theorem u29911 : Upper (D 7) (R 7) [96,384,9,48,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29911 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29912 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 402, targets := 1 },{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7),(1,0),(4,0),(4,7)], upper := (rows 97 386 13 140 50 33 82 210 338), lower := (rows 97 386 13 140 50 33 64 128 256), losses := [] }

theorem u29912 : Upper (D 7) (R 7) [96,384,9,132,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29912 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29913 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 205, targets := 2 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,1),(2,1),(3,1),(4,0)], upper := (rows 97 386 13 140 50 34 81 209 337), lower := (rows 97 386 13 140 50 34 64 128 256), losses := [] }

theorem u29913 : Upper (D 7) (R 7) [96,384,9,132,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29914 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 386 13 140 50 48 67 195 323), lower := (rows 97 386 13 140 50 48 64 128 256), losses := [] }

theorem u29914 : Upper (D 7) (R 7) [96,384,9,132,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29914 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29915 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 13 140 50 96 83 147 275), lower := (rows 97 386 13 140 50 96 64 128 256), losses := [] }

theorem u29915 : Upper (D 7) (R 7) [96,384,9,132,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29915 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29916 : PairBound 9 := { available := 98, camps := [{ cop := 6, region := 33, targets := 130 },{ cop := 0, region := 386, targets := 1 }], pairs := [(0,1),(0,7),(1,0),(3,0)], upper := (rows 97 386 13 152 22 33 98 226 354), lower := (rows 97 386 13 152 22 33 64 128 256), losses := [{ target := 0, region := (rows 0 39 4 12 20 32 97 161 289), good := (rows 482 386 478 152 30 482 64 128 256) }] }

theorem u29916 : Upper (D 7) (R 7) [96,384,9,144,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29916 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m29917_1 : Upper (D 7) (R 7) [96,384,9,144,6,2,1] 13 :=
  permutation_upper _ _ _ [96,384,9,144,6,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11601

def r29917 : Route 9 := (fun mask => (mask,id))

def c29917 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29917 : Upper (D 7) (R 7) [96,384,9,144,6,2] 13 := by
  apply FastRouting.sound _ _ [96,384,9,144,6,2] 13 (by decide) (choices 1) [1,32] r29917 c29917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m29917_1
  · exact u11602

def b29918 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 13 152 22 96 99 163 291), lower := (rows 97 386 13 152 22 96 64 128 256), losses := [] }

theorem u29918 : Upper (D 7) (R 7) [96,384,9,144,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29918 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29919 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 450, targets := 33 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(1,5)], upper := (rows 97 386 13 152 50 33 70 198 326), lower := (rows 97 386 13 152 50 33 64 128 256), losses := [] }

theorem u29919 : Upper (D 7) (R 7) [96,384,9,144,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29919 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29920 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 56, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 97 386 13 152 50 34 69 197 325), lower := (rows 97 386 13 152 50 34 64 128 256), losses := [] }

theorem u29920 : Upper (D 7) (R 7) [96,384,9,144,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29920 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29921 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 386, targets := 32 },{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7),(1,5),(2,7)], upper := (rows 97 386 13 152 50 36 67 195 323), lower := (rows 97 386 13 152 50 36 64 128 256), losses := [{ target := 7, region := (rows 25 2 12 8 16 44 80 0 272), good := (rows 97 258 45 381 371 36 64 0 256) }] }

theorem u29921 : Upper (D 7) (R 7) [96,384,9,144,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29921 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29922 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 13 152 50 96 71 135 263), lower := (rows 97 386 13 152 50 96 64 128 256), losses := [] }

theorem u29922 : Upper (D 7) (R 7) [96,384,9,144,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29922 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29923 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 97 386 13 152 52 33 66 194 322), lower := (rows 97 386 13 152 52 33 64 128 256), losses := [] }

theorem u29923 : Upper (D 7) (R 7) [96,384,9,144,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29923 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29924 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 386, targets := 32 },{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7),(1,5),(2,7),(3,5)], upper := (rows 97 386 13 152 52 34 67 195 323), lower := (rows 97 386 13 152 52 34 64 128 256), losses := [{ target := 5, region := (rows 1 23 4 24 16 0 69 133 261), good := (rows 451 386 463 154 478 2 64 128 256) },{ target := 7, region := (rows 51 2 12 8 16 34 98 0 290), good := (rows 353 355 13 29 373 355 64 0 256) }] }

theorem u29924 : Upper (D 7) (R 7) [96,384,9,144,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29924 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29925 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 13 152 52 96 67 131 259), lower := (rows 97 386 13 152 52 96 64 128 256), losses := [] }

theorem u29925 : Upper (D 7) (R 7) [96,384,9,144,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29925 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29926 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 386 13 168 22 33 82 210 338), lower := (rows 97 386 13 168 22 33 64 128 256), losses := [] }

theorem u29926 : Upper (D 7) (R 7) [96,384,9,160,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29926 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29927 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 40, targets := 65 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(3,0),(3,6),(4,5)], upper := (rows 97 386 13 168 22 34 81 209 337), lower := (rows 97 386 13 168 22 34 64 128 256), losses := [] }

theorem u29927 : Upper (D 7) (R 7) [96,384,9,160,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29927 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29928 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7),(1,5),(4,5)], upper := (rows 97 386 13 168 22 48 67 195 323), lower := (rows 97 386 13 168 22 48 64 128 256), losses := [] }

theorem u29928 : Upper (D 7) (R 7) [96,384,9,160,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29928 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29929 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 13 168 22 96 83 147 275), lower := (rows 97 386 13 168 22 96 64 128 256), losses := [] }

theorem u29929 : Upper (D 7) (R 7) [96,384,9,160,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29929 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29930 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 386 13 168 82 33 86 150 278), lower := (rows 97 386 13 168 82 33 64 128 256), losses := [] }

theorem u29930 : Upper (D 7) (R 7) [96,384,9,160,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29930 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29931 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 40, targets := 65 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(3,0),(3,6),(4,5)], upper := (rows 97 386 13 168 82 34 85 149 277), lower := (rows 97 386 13 168 82 34 64 128 256), losses := [] }

theorem u29931 : Upper (D 7) (R 7) [96,384,9,160,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29931 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29932 : Route 9 := (fun mask => (mask,id))

def c29932 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29932 : Upper (D 7) (R 7) [96,384,9,160,66,4] 13 := by
  apply FastRouting.sound _ _ [96,384,9,160,66,4] 13 (by decide) (choices 1) [1,2,16] r29932 c29932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11603
  · exact u11604
  · exact u11605

def b29933 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 386 13 168 82 48 71 135 263), lower := (rows 97 386 13 168 82 48 64 128 256), losses := [] }

theorem u29933 : Upper (D 7) (R 7) [96,384,9,160,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29933 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29934 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 386 13 168 84 33 82 146 274), lower := (rows 97 386 13 168 84 33 64 128 256), losses := [] }

theorem u29934 : Upper (D 7) (R 7) [96,384,9,160,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29934 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29935 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 40, targets := 65 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(3,0),(3,6),(4,5)], upper := (rows 97 386 13 168 84 34 83 147 275), lower := (rows 97 386 13 168 84 34 64 128 256), losses := [] }

theorem u29935 : Upper (D 7) (R 7) [96,384,9,160,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29935 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29936 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 386 13 168 84 48 67 131 259), lower := (rows 97 386 13 168 84 48 64 128 256), losses := [] }

theorem u29936 : Upper (D 7) (R 7) [96,384,9,160,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29936 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29937 : PairBound 9 := { available := 98, camps := [{ cop := 6, region := 33, targets := 130 },{ cop := 0, region := 386, targets := 1 }], pairs := [(0,1),(0,7),(1,0),(2,0)], upper := (rows 97 386 14 28 145 33 98 226 354), lower := (rows 97 386 14 28 145 33 64 128 256), losses := [{ target := 0, region := (rows 0 51 28 24 16 32 97 161 289), good := (rows 482 386 14 30 478 482 64 128 256) }] }

theorem u29937 : Upper (D 7) (R 7) [96,384,10,20,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29937 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m29938_1 : Upper (D 7) (R 7) [96,384,10,20,129,2,1] 13 :=
  permutation_upper _ _ _ [96,384,10,20,129,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11606

def r29938 : Route 9 := (fun mask => (mask,id))

def c29938 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29938 : Upper (D 7) (R 7) [96,384,10,20,129,2] 13 := by
  apply FastRouting.sound _ _ [96,384,10,20,129,2] 13 (by decide) (choices 1) [1,32] r29938 c29938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m29938_1
  · exact u11607

def b29939 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 14 28 145 96 99 163 291), lower := (rows 97 386 14 28 145 96 64 128 256), losses := [] }

theorem u29939 : Upper (D 7) (R 7) [96,384,10,20,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29939 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u29939
end Delivery.IrregularNine14.P07
