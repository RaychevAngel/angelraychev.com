import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0035

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11880 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 22 388 41 81 34 100 228 356), lower := (rows 11 22 388 41 81 34 64 128 256), losses := [] }

theorem u11880 : Upper (D 6) (R 6) [10,20,384,33,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11880 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11881 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 4, region := 422, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 22 388 41 81 36 98 226 354), lower := (rows 11 22 388 41 81 36 64 128 256), losses := [] }

theorem u11881 : Upper (D 6) (R 6) [10,20,384,33,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11881 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11882 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 4, region := 40, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 22 388 41 81 96 102 166 294), lower := (rows 11 22 388 41 81 96 64 128 256), losses := [] }

theorem u11882 : Upper (D 6) (R 6) [10,20,384,33,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11882 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11883 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 22 388 41 82 33 100 228 356), lower := (rows 11 22 388 41 82 33 64 128 256), losses := [] }

theorem u11883 : Upper (D 6) (R 6) [10,20,384,33,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11883 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11884 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 11 22 388 41 82 36 97 225 353), lower := (rows 11 22 388 41 82 36 64 128 256), losses := [] }

theorem u11884 : Upper (D 6) (R 6) [10,20,384,33,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11884 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11885 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 4, region := 41, targets := 4 }], pairs := [(0,2),(2,1),(3,1)], upper := (rows 11 22 388 41 82 96 101 165 293), lower := (rows 11 22 388 41 82 96 64 128 256), losses := [] }

theorem u11885 : Upper (D 6) (R 6) [10,20,384,33,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11885 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11886 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 22 388 41 112 33 70 198 326), lower := (rows 11 22 388 41 112 33 64 128 256), losses := [] }

theorem u11886 : Upper (D 6) (R 6) [10,20,384,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11886 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11887 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 22 388 41 112 34 69 197 325), lower := (rows 11 22 388 41 112 34 64 128 256), losses := [] }

theorem u11887 : Upper (D 6) (R 6) [10,20,384,33,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11888 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 0, region := 452, targets := 32 }], pairs := [(0,6),(2,5),(3,6)], upper := (rows 11 22 388 41 112 36 67 195 323), lower := (rows 11 22 388 41 112 36 64 128 256), losses := [] }

theorem u11888 : Upper (D 6) (R 6) [10,20,384,33,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11888 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11889 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 388 41 112 96 71 135 263), lower := (rows 11 22 388 41 112 96 64 128 256), losses := [] }

theorem u11889 : Upper (D 6) (R 6) [10,20,384,33,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11890 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(3,6),(4,2)], upper := (rows 11 22 388 44 81 33 98 226 354), lower := (rows 11 22 388 44 81 33 64 128 256), losses := [] }

theorem u11890 : Upper (D 6) (R 6) [10,20,384,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11890 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11891 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(3,6),(4,2)], upper := (rows 11 22 388 44 81 34 97 225 353), lower := (rows 11 22 388 44 81 34 64 128 256), losses := [] }

theorem u11891 : Upper (D 6) (R 6) [10,20,384,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11891 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11892 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 112, targets := 4 }], pairs := [(3,0),(3,1),(4,2)], upper := (rows 11 22 388 44 81 96 99 163 291), lower := (rows 11 22 388 44 81 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 112 64 128 256), good := (rows 10 62 388 44 112 96 96 128 256) },{ target := 1, region := (rows 1 0 4 10 16 112 64 128 256), good := (rows 9 60 388 44 113 96 96 128 256) }] }

theorem u11892 : Upper (D 6) (R 6) [10,20,384,36,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11892 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11893 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(3,6),(4,2)], upper := (rows 11 22 388 44 112 33 67 195 323), lower := (rows 11 22 388 44 112 33 64 128 256), losses := [] }

theorem u11893 : Upper (D 6) (R 6) [10,20,384,36,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11893 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11894 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(2,1),(2,5)], upper := (rows 11 22 388 44 112 34 65 193 321), lower := (rows 11 22 388 44 112 34 64 128 256), losses := [] }

theorem u11894 : Upper (D 6) (R 6) [10,20,384,36,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11894 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11895 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 388 44 112 96 67 131 259), lower := (rows 11 22 388 44 112 96 64 128 256), losses := [] }

theorem u11895 : Upper (D 6) (R 6) [10,20,384,36,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11895 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11896 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 22 388 104 49 33 70 198 326), lower := (rows 11 22 388 104 49 33 64 128 256), losses := [] }

theorem u11896 : Upper (D 6) (R 6) [10,20,384,96,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11896 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11897 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 0, region := 48, targets := 4 }], pairs := [(2,1),(2,5),(4,2)], upper := (rows 11 22 388 104 49 34 69 197 325), lower := (rows 11 22 388 104 49 34 64 128 256), losses := [] }

theorem u11897 : Upper (D 6) (R 6) [10,20,384,96,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11897 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11898 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(4,1)], upper := (rows 11 22 388 104 49 36 67 195 323), lower := (rows 11 22 388 104 49 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 38 64 128 256), good := (rows 57 52 420 104 49 36 64 128 256) }] }

theorem u11898 : Upper (D 6) (R 6) [10,20,384,96,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11898 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11899 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 388 104 49 96 71 135 263), lower := (rows 11 22 388 104 49 96 64 128 256), losses := [] }

theorem u11899 : Upper (D 6) (R 6) [10,20,384,96,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11899 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11900 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 22 76 176 33 324 452 324), lower := (rows 11 35 22 76 176 33 64 128 256), losses := [] }

theorem u11900 : Upper (D 6) (R 6) [10,33,18,68,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11900 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11901 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 329, targets := 32 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 22 76 176 36 321 449 321), lower := (rows 11 35 22 76 176 36 64 128 256), losses := [] }

theorem u11901 : Upper (D 6) (R 6) [10,33,18,68,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11901 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11902 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 2, region := 329, targets := 32 }], pairs := [(0,5),(2,6),(4,6)], upper := (rows 11 35 22 76 176 96 325 389 261), lower := (rows 11 35 22 76 176 96 64 128 256), losses := [] }

theorem u11902 : Upper (D 6) (R 6) [10,33,18,68,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11902 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11903 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 35 22 76 176 288 69 197 325), lower := (rows 11 35 22 76 176 288 64 128 256), losses := [] }

theorem u11903 : Upper (D 6) (R 6) [10,33,18,68,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11903 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11904 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 22 76 208 33 356 420 292), lower := (rows 11 35 22 76 208 33 64 128 256), losses := [] }

theorem u11904 : Upper (D 6) (R 6) [10,33,18,68,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11904 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11905 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 464, targets := 2 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 11 35 22 76 208 36 353 417 289), lower := (rows 11 35 22 76 208 36 64 128 256), losses := [] }

theorem u11905 : Upper (D 6) (R 6) [10,33,18,68,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11905 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11906 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 291, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 22 76 208 288 101 165 293), lower := (rows 11 35 22 76 208 288 64 128 256), losses := [] }

theorem u11906 : Upper (D 6) (R 6) [10,33,18,68,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11906 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11907 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 22 76 400 33 100 228 356), lower := (rows 11 35 22 76 400 33 64 128 256), losses := [] }

theorem u11907 : Upper (D 6) (R 6) [10,33,18,68,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11907 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11908 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 464, targets := 2 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 11 35 22 76 400 36 97 225 353), lower := (rows 11 35 22 76 400 36 64 128 256), losses := [] }

theorem u11908 : Upper (D 6) (R 6) [10,33,18,68,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11908 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11909 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 22 76 400 96 101 165 293), lower := (rows 11 35 22 76 400 96 64 128 256), losses := [] }

theorem u11909 : Upper (D 6) (R 6) [10,33,18,68,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11909 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11910 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 22 140 112 33 324 452 324), lower := (rows 11 35 22 140 112 33 64 128 256), losses := [] }

theorem u11910 : Upper (D 6) (R 6) [10,33,18,132,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11910 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11911 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 457, targets := 32 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 22 140 112 36 321 449 321), lower := (rows 11 35 22 140 112 36 64 128 256), losses := [] }

theorem u11911 : Upper (D 6) (R 6) [10,33,18,132,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11912 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 35 22 140 112 96 325 389 261), lower := (rows 11 35 22 140 112 96 64 128 256), losses := [] }

theorem u11912 : Upper (D 6) (R 6) [10,33,18,132,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11912 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11913 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 201, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 35 22 140 112 288 69 197 325), lower := (rows 11 35 22 140 112 288 64 128 256), losses := [] }

theorem u11913 : Upper (D 6) (R 6) [10,33,18,132,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11913 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11914 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 22 140 304 33 68 196 324), lower := (rows 11 35 22 140 304 33 64 128 256), losses := [] }

theorem u11914 : Upper (D 6) (R 6) [10,33,18,132,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11914 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11915 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 201, targets := 32 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 22 140 304 36 65 193 321), lower := (rows 11 35 22 140 304 36 64 128 256), losses := [] }

theorem u11915 : Upper (D 6) (R 6) [10,33,18,132,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11915 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11916 : Route 9 := (fun mask => (mask,id))

def c11916 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11916 : Upper (D 6) (R 6) [10,33,18,132,288,64] 13 := by
  apply FastRouting.sound _ _ [10,33,18,132,288,64] 13 (by decide) (choices 1) [1,4] r11916 c11916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2131
  · exact u2132

def b11917 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 22 140 336 33 100 228 356), lower := (rows 11 35 22 140 336 33 64 128 256), losses := [] }

theorem u11917 : Upper (D 6) (R 6) [10,33,18,132,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11917 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11918 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 336, targets := 2 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 11 35 22 140 336 36 97 225 353), lower := (rows 11 35 22 140 336 36 64 128 256), losses := [] }

theorem u11918 : Upper (D 6) (R 6) [10,33,18,132,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11918 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11919 : Route 9 := (fun mask => (mask,id))

def c11919 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11919 : Upper (D 6) (R 6) [10,33,18,132,320,64] 13 := by
  apply FastRouting.sound _ _ [10,33,18,132,320,64] 13 (by decide) (choices 1) [1,4,32] r11919 c11919
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2133
  · exact u2134
  · exact u2135

def b11920 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 22 200 84 33 356 420 292), lower := (rows 11 35 22 200 84 33 64 128 256), losses := [] }

theorem u11920 : Upper (D 6) (R 6) [10,33,18,192,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11920 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11921 : PairBound 9 := { available := 289, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 22 200 84 36 353 417 289), lower := (rows 11 35 22 200 84 36 64 128 256), losses := [] }

theorem u11921 : Upper (D 6) (R 6) [10,33,18,192,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11921 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11922 : Route 9 := (fun mask => (mask,id))

def c11922 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11922 : Upper (D 6) (R 6) [10,33,18,192,68,256] 13 := by
  apply FastRouting.sound _ _ [10,33,18,192,68,256] 13 (by decide) (choices 1) [1,4,32] r11922 c11922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2136
  · exact u2137
  · exact u2138

def b11923 : PairBound 9 := { available := 260, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 22 200 112 33 324 388 260), lower := (rows 11 35 22 200 112 33 64 128 256), losses := [] }

theorem u11923 : Upper (D 6) (R 6) [10,33,18,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11924 : Route 9 := (fun mask => (mask,id))

def c11924 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u11924 : Upper (D 6) (R 6) [10,33,18,192,96,4] 13 := by
  apply FastRouting.sound _ _ [10,33,18,192,96,4] 13 (by decide) (choices 1) [1,4,256] r11924 c11924
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2139
  · exact u2140
  · exact u2141

def b11925 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 201, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 35 22 200 112 288 69 133 261), lower := (rows 11 35 22 200 112 288 64 128 256), losses := [] }

theorem u11925 : Upper (D 6) (R 6) [10,33,18,192,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11925 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11926 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 232, targets := 3 },{ cop := 4, region := 38, targets := 64 }], pairs := [(1,6),(3,0),(3,1)], upper := (rows 11 35 22 200 273 36 100 228 356), lower := (rows 11 35 22 200 273 36 64 128 256), losses := [] }

theorem u11926 : Upper (D 6) (R 6) [10,33,18,192,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11926 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11927 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 276, targets := 64 },{ cop := 2, region := 232, targets := 1 }], pairs := [(2,6),(3,0),(4,6)], upper := (rows 11 35 22 200 273 96 100 164 292), lower := (rows 11 35 22 200 273 96 64 128 256), losses := [] }

theorem u11927 : Upper (D 6) (R 6) [10,33,18,192,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11927 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11928 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 22 200 276 33 100 228 356), lower := (rows 11 35 22 200 276 33 64 128 256), losses := [] }

theorem u11928 : Upper (D 6) (R 6) [10,33,18,192,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11928 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11929 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 22 200 276 36 97 225 353), lower := (rows 11 35 22 200 276 36 64 128 256), losses := [] }

theorem u11929 : Upper (D 6) (R 6) [10,33,18,192,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11929 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11930 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 276, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 22 200 276 96 101 165 293), lower := (rows 11 35 22 200 276 96 64 128 256), losses := [] }

theorem u11930 : Upper (D 6) (R 6) [10,33,18,192,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11930 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11931 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 22 200 304 33 68 196 324), lower := (rows 11 35 22 200 304 33 64 128 256), losses := [] }

theorem u11931 : Upper (D 6) (R 6) [10,33,18,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11931 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11932 : Route 9 := (fun mask => (mask,id))

def c11932 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11932 : Upper (D 6) (R 6) [10,33,18,192,288,4] 13 := by
  apply FastRouting.sound _ _ [10,33,18,192,288,4] 13 (by decide) (choices 1) [1,4] r11932 c11932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2142
  · exact u2143

def b11933 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 276, targets := 64 },{ cop := 2, region := 201, targets := 32 }], pairs := [(0,5),(2,6),(4,6)], upper := (rows 11 35 22 200 304 96 69 133 261), lower := (rows 11 35 22 200 304 96 64 128 256), losses := [] }

theorem u11933 : Upper (D 6) (R 6) [10,33,18,192,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11934 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 22 200 336 33 100 164 292), lower := (rows 11 35 22 200 336 33 64 128 256), losses := [] }

theorem u11934 : Upper (D 6) (R 6) [10,33,18,192,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11934 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11935 : Route 9 := (fun mask => (mask,id))

def c11935 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11935 : Upper (D 6) (R 6) [10,33,18,192,320,4] 13 := by
  apply FastRouting.sound _ _ [10,33,18,192,320,4] 13 (by decide) (choices 1) [1,4,32] r11935 c11935
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2144
  · exact u2145
  · exact u2146

def b11936 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 488, targets := 3 },{ cop := 4, region := 38, targets := 64 }], pairs := [(1,6),(3,0),(3,1)], upper := (rows 11 35 22 392 81 36 100 228 356), lower := (rows 11 35 22 392 81 36 64 128 256), losses := [] }

theorem u11936 : Upper (D 6) (R 6) [10,33,18,384,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11936 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11937 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 488, targets := 3 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(3,0),(3,1)], upper := (rows 11 35 22 392 81 96 100 164 292), lower := (rows 11 35 22 392 81 96 64 128 256), losses := [] }

theorem u11937 : Upper (D 6) (R 6) [10,33,18,384,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11937 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11938 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 22 392 84 33 100 228 356), lower := (rows 11 35 22 392 84 33 64 128 256), losses := [] }

theorem u11938 : Upper (D 6) (R 6) [10,33,18,384,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11938 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11939 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 22 392 84 36 97 225 353), lower := (rows 11 35 22 392 84 36 64 128 256), losses := [] }

theorem u11939 : Upper (D 6) (R 6) [10,33,18,384,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11939 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u11939
end Delivery.IrregularNine14.P06
