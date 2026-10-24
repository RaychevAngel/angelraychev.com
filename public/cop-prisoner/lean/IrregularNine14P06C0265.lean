import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0064

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15900 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 134 37 73 112 36 338 402 274), lower := (rows 11 134 37 73 112 36 64 128 256), losses := [] }

theorem u15900 : Upper (D 6) (R 6) [10,132,33,65,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15900 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15901 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 37 73 112 48 326 390 262), lower := (rows 11 134 37 73 112 48 64 128 256), losses := [] }

theorem u15901 : Upper (D 6) (R 6) [10,132,33,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15901 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15902 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 134 37 73 112 288 86 150 278), lower := (rows 11 134 37 73 112 288 64 128 256), losses := [] }

theorem u15902 : Upper (D 6) (R 6) [10,132,33,65,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15902 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15903 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 134 37 73 274 36 112 240 368), lower := (rows 11 134 37 73 274 36 64 128 256), losses := [] }

theorem u15903 : Upper (D 6) (R 6) [10,132,33,65,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15903 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15904 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 134 37 73 274 48 100 228 356), lower := (rows 11 134 37 73 274 48 64 128 256), losses := [] }

theorem u15904 : Upper (D 6) (R 6) [10,132,33,65,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15904 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15905 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 402, targets := 1 },{ cop := 2, region := 402, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 134 37 73 274 96 116 180 308), lower := (rows 11 134 37 73 274 96 64 128 256), losses := [] }

theorem u15905 : Upper (D 6) (R 6) [10,132,33,65,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15905 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15906 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 2, region := 344, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 134 37 73 276 34 112 240 368), lower := (rows 11 134 37 73 276 34 64 128 256), losses := [] }

theorem u15906 : Upper (D 6) (R 6) [10,132,33,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15906 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15907 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 134 37 73 276 48 98 226 354), lower := (rows 11 134 37 73 276 48 64 128 256), losses := [] }

theorem u15907 : Upper (D 6) (R 6) [10,132,33,65,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15907 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15908 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 402, targets := 1 },{ cop := 2, region := 402, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 134 37 73 276 96 114 178 306), lower := (rows 11 134 37 73 276 96 64 128 256), losses := [] }

theorem u15908 : Upper (D 6) (R 6) [10,132,33,65,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15908 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15909 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 2, region := 344, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 134 37 73 304 34 84 212 340), lower := (rows 11 134 37 73 304 34 64 128 256), losses := [] }

theorem u15909 : Upper (D 6) (R 6) [10,132,33,65,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15909 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15910 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 134 37 73 304 36 82 210 338), lower := (rows 11 134 37 73 304 36 64 128 256), losses := [] }

theorem u15910 : Upper (D 6) (R 6) [10,132,33,65,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15910 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15911 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 134 37 73 304 48 70 198 326), lower := (rows 11 134 37 73 304 48 64 128 256), losses := [] }

theorem u15911 : Upper (D 6) (R 6) [10,132,33,65,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15911 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15912 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 402, targets := 1 },{ cop := 2, region := 402, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 134 37 73 304 96 86 150 278), lower := (rows 11 134 37 73 304 96 64 128 256), losses := [] }

theorem u15912 : Upper (D 6) (R 6) [10,132,33,65,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15912 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15913 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 2, region := 344, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 134 37 73 336 34 116 180 308), lower := (rows 11 134 37 73 336 34 64 128 256), losses := [] }

theorem u15913 : Upper (D 6) (R 6) [10,132,33,65,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15914 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 134 37 73 336 36 114 178 306), lower := (rows 11 134 37 73 336 36 64 128 256), losses := [] }

theorem u15914 : Upper (D 6) (R 6) [10,132,33,65,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15914 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15915 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 134 37 73 336 48 102 166 294), lower := (rows 11 134 37 73 336 48 64 128 256), losses := [] }

theorem u15915 : Upper (D 6) (R 6) [10,132,33,65,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15915 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15916 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 76 50 33 336 464 336), lower := (rows 11 134 37 76 50 33 64 128 256), losses := [] }

theorem u15916 : Upper (D 6) (R 6) [10,132,33,68,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15917 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 134 37 76 50 48 321 449 321), lower := (rows 11 134 37 76 50 48 64 128 256), losses := [] }

theorem u15917 : Upper (D 6) (R 6) [10,132,33,68,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15917 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15918 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 402, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,6),(4,2),(4,6)], upper := (rows 11 134 37 76 50 96 337 401 273), lower := (rows 11 134 37 76 50 96 64 128 256), losses := [] }

theorem u15918 : Upper (D 6) (R 6) [10,132,33,68,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15918 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15919 : Route 9 := (fun mask => (mask,id))

def c15919 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15919 : Upper (D 6) (R 6) [10,132,33,68,34,256] 13 := by
  apply FastRouting.sound _ _ [10,132,33,68,34,256] 13 (by decide) (choices 1) [1,16] r15919 c15919
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3858
  · exact u3859

def b15920 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 76 82 33 368 432 304), lower := (rows 11 134 37 76 82 33 64 128 256), losses := [] }

theorem u15920 : Upper (D 6) (R 6) [10,132,33,68,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15920 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15921 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 2, region := 328, targets := 2 }], pairs := [(3,1),(4,2)], upper := (rows 11 134 37 76 82 48 353 417 289), lower := (rows 11 134 37 76 82 48 64 128 256), losses := [] }

theorem u15921 : Upper (D 6) (R 6) [10,132,33,68,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15921 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15922 : Route 9 := (fun mask => (mask,id))

def c15922 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15922 : Upper (D 6) (R 6) [10,132,33,68,66,256] 13 := by
  apply FastRouting.sound _ _ [10,132,33,68,66,256] 13 (by decide) (choices 1) [1,16,32] r15922 c15922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3860
  · exact u3861
  · exact u3862

def b15923 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 76 112 33 338 402 274), lower := (rows 11 134 37 76 112 33 64 128 256), losses := [] }

theorem u15923 : Upper (D 6) (R 6) [10,132,33,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15924 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 11 134 37 76 112 34 337 401 273), lower := (rows 11 134 37 76 112 34 64 128 256), losses := [] }

theorem u15924 : Upper (D 6) (R 6) [10,132,33,68,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15924 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15925 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 37 76 112 48 323 387 259), lower := (rows 11 134 37 76 112 48 64 128 256), losses := [] }

theorem u15925 : Upper (D 6) (R 6) [10,132,33,68,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15925 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15926 : Route 9 := (fun mask => (mask,id))

def c15926 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15926 : Upper (D 6) (R 6) [10,132,33,68,96,256] 13 := by
  apply FastRouting.sound _ _ [10,132,33,68,96,256] 13 (by decide) (choices 1) [1,2,16] r15926 c15926
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3863
  · exact u3864
  · exact u3865

def b15927 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 11 134 37 76 273 34 112 240 368), lower := (rows 11 134 37 76 273 34 64 128 256), losses := [] }

theorem u15927 : Upper (D 6) (R 6) [10,132,33,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15927 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15928 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 11 134 37 76 273 48 98 226 354), lower := (rows 11 134 37 76 273 48 64 128 256), losses := [] }

theorem u15928 : Upper (D 6) (R 6) [10,132,33,68,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15928 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15929 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 402, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,6),(4,2),(4,6)], upper := (rows 11 134 37 76 273 96 114 178 306), lower := (rows 11 134 37 76 273 96 64 128 256), losses := [] }

theorem u15929 : Upper (D 6) (R 6) [10,132,33,68,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15929 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15930 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 76 274 33 112 240 368), lower := (rows 11 134 37 76 274 33 64 128 256), losses := [] }

theorem u15930 : Upper (D 6) (R 6) [10,132,33,68,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15930 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15931 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 2, region := 72, targets := 2 }], pairs := [(3,1),(4,2)], upper := (rows 11 134 37 76 274 48 97 225 353), lower := (rows 11 134 37 76 274 48 64 128 256), losses := [] }

theorem u15931 : Upper (D 6) (R 6) [10,132,33,68,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15931 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15932 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 402, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,6),(4,2),(4,6)], upper := (rows 11 134 37 76 274 96 113 177 305), lower := (rows 11 134 37 76 274 96 64 128 256), losses := [] }

theorem u15932 : Upper (D 6) (R 6) [10,132,33,68,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15932 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15933 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 76 304 33 82 210 338), lower := (rows 11 134 37 76 304 33 64 128 256), losses := [] }

theorem u15933 : Upper (D 6) (R 6) [10,132,33,68,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15934 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 11 134 37 76 304 34 81 209 337), lower := (rows 11 134 37 76 304 34 64 128 256), losses := [] }

theorem u15934 : Upper (D 6) (R 6) [10,132,33,68,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15934 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15935 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 134 37 76 304 48 67 195 323), lower := (rows 11 134 37 76 304 48 64 128 256), losses := [] }

theorem u15935 : Upper (D 6) (R 6) [10,132,33,68,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15935 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15936 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 402, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,6),(4,2),(4,6)], upper := (rows 11 134 37 76 304 96 83 147 275), lower := (rows 11 134 37 76 304 96 64 128 256), losses := [] }

theorem u15936 : Upper (D 6) (R 6) [10,132,33,68,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15936 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15937 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 76 336 33 114 178 306), lower := (rows 11 134 37 76 336 33 64 128 256), losses := [] }

theorem u15937 : Upper (D 6) (R 6) [10,132,33,68,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15937 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15938 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 11 134 37 76 336 34 113 177 305), lower := (rows 11 134 37 76 336 34 64 128 256), losses := [] }

theorem u15938 : Upper (D 6) (R 6) [10,132,33,68,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15938 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15939 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 2, region := 130, targets := 64 }], pairs := [(1,6),(4,2)], upper := (rows 11 134 37 76 336 48 99 163 291), lower := (rows 11 134 37 76 336 48 64 128 256), losses := [] }

theorem u15939 : Upper (D 6) (R 6) [10,132,33,68,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15939 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15940 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 88 50 33 324 452 324), lower := (rows 11 134 37 88 50 33 64 128 256), losses := [] }

theorem u15940 : Upper (D 6) (R 6) [10,132,33,80,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15940 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15941 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 134 37 88 50 36 321 449 321), lower := (rows 11 134 37 88 50 36 64 128 256), losses := [] }

theorem u15941 : Upper (D 6) (R 6) [10,132,33,80,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15941 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15942 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 402, targets := 64 },{ cop := 0, region := 356, targets := 2 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 134 37 88 50 96 325 389 261), lower := (rows 11 134 37 88 50 96 64 128 256), losses := [] }

theorem u15942 : Upper (D 6) (R 6) [10,132,33,80,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15942 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15943 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 356, targets := 2 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,1)], upper := (rows 11 134 37 88 50 288 69 197 325), lower := (rows 11 134 37 88 50 288 64 128 256), losses := [] }

theorem u15943 : Upper (D 6) (R 6) [10,132,33,80,34,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15943 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15944 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 134 37 88 273 34 100 228 356), lower := (rows 11 134 37 88 273 34 64 128 256), losses := [] }

theorem u15944 : Upper (D 6) (R 6) [10,132,33,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15944 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15945 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 134 37 88 273 36 98 226 354), lower := (rows 11 134 37 88 273 36 64 128 256), losses := [] }

theorem u15945 : Upper (D 6) (R 6) [10,132,33,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15945 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15946 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 402, targets := 64 },{ cop := 2, region := 130, targets := 1 }], pairs := [(1,0),(1,6),(4,6)], upper := (rows 11 134 37 88 273 96 102 166 294), lower := (rows 11 134 37 88 273 96 64 128 256), losses := [] }

theorem u15946 : Upper (D 6) (R 6) [10,132,33,80,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15946 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15947 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 88 274 33 100 228 356), lower := (rows 11 134 37 88 274 33 64 128 256), losses := [] }

theorem u15947 : Upper (D 6) (R 6) [10,132,33,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15948 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 36, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(0,2),(2,1),(2,6)], upper := (rows 11 134 37 88 274 36 97 225 353), lower := (rows 11 134 37 88 274 36 64 128 256), losses := [{ target := 2, region := (rows 19 2 0 10 18 32 68 132 260), good := (rows 27 475 481 89 283 480 64 128 256) }] }

theorem u15948 : Upper (D 6) (R 6) [10,132,33,80,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15948 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15949 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 402, targets := 64 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 134 37 88 274 96 101 165 293), lower := (rows 11 134 37 88 274 96 64 128 256), losses := [] }

theorem u15949 : Upper (D 6) (R 6) [10,132,33,80,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15949 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15950 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 88 276 33 98 226 354), lower := (rows 11 134 37 88 276 33 64 128 256), losses := [] }

theorem u15950 : Upper (D 6) (R 6) [10,132,33,80,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15950 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15951 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 134 37 88 276 34 97 225 353), lower := (rows 11 134 37 88 276 34 64 128 256), losses := [] }

theorem u15951 : Upper (D 6) (R 6) [10,132,33,80,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15952 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 402, targets := 64 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 134 37 88 276 96 99 163 291), lower := (rows 11 134 37 88 276 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 104 64 128 256), good := (rows 45 132 37 120 276 96 96 128 256) }] }

theorem u15952 : Upper (D 6) (R 6) [10,132,33,80,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15952 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15953 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 88 304 33 70 198 326), lower := (rows 11 134 37 88 304 33 64 128 256), losses := [] }

theorem u15953 : Upper (D 6) (R 6) [10,132,33,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15953 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15954 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 134 37 88 304 34 69 197 325), lower := (rows 11 134 37 88 304 34 64 128 256), losses := [] }

theorem u15954 : Upper (D 6) (R 6) [10,132,33,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15954 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15955 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,1),(2,6)], upper := (rows 11 134 37 88 304 36 67 195 323), lower := (rows 11 134 37 88 304 36 64 128 256), losses := [] }

theorem u15955 : Upper (D 6) (R 6) [10,132,33,80,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15955 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15956 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 402, targets := 64 },{ cop := 2, region := 130, targets := 32 }], pairs := [(1,5),(1,6),(4,6)], upper := (rows 11 134 37 88 304 96 71 135 263), lower := (rows 11 134 37 88 304 96 64 128 256), losses := [] }

theorem u15956 : Upper (D 6) (R 6) [10,132,33,80,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15957 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 104 82 33 340 404 276), lower := (rows 11 134 37 104 82 33 64 128 256), losses := [] }

theorem u15957 : Upper (D 6) (R 6) [10,132,33,96,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15957 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15958 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 134 37 104 82 36 337 401 273), lower := (rows 11 134 37 104 82 36 64 128 256), losses := [] }

theorem u15958 : Upper (D 6) (R 6) [10,132,33,96,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15958 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15959 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 37 104 82 48 325 389 261), lower := (rows 11 134 37 104 82 48 64 128 256), losses := [] }

theorem u15959 : Upper (D 6) (R 6) [10,132,33,96,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15959 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u15959
end Delivery.IrregularNine14.P06
