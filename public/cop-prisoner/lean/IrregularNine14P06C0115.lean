import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0008

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6900 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 131 268 104 81 36 80 134 262), lower := (rows 35 131 268 104 81 36 80 128 256), losses := [] }

theorem u6900 : Upper (D 6) (R 6) [34,129,264,96,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6900 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6901 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 268 104 82 36 65 148 276), lower := (rows 35 131 268 104 82 36 65 128 256), losses := [] }

theorem u6901 : Upper (D 6) (R 6) [34,129,264,96,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6901 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6902 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 268 104 82 36 68 145 273), lower := (rows 35 131 268 104 82 36 68 128 256), losses := [] }

theorem u6902 : Upper (D 6) (R 6) [34,129,264,96,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6902 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6903 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 35 131 268 104 82 36 80 133 261), lower := (rows 35 131 268 104 82 36 80 128 256), losses := [] }

theorem u6903 : Upper (D 6) (R 6) [34,129,264,96,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6903 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6904 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 131 292 13 22 96 72 208 336), lower := (rows 35 131 292 13 22 96 72 128 256), losses := [] }

theorem u6904 : Upper (D 6) (R 6) [34,129,288,5,6,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6904 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6905 : PairBound 9 := { available := 72, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 131 292 13 22 96 80 200 328), lower := (rows 35 131 292 13 22 96 80 128 256), losses := [] }

theorem u6905 : Upper (D 6) (R 6) [34,129,288,5,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6905 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6906 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 210, targets := 32 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,5),(4,5)], upper := (rows 35 131 292 13 84 96 66 152 280), lower := (rows 35 131 292 13 84 96 66 128 256), losses := [] }

theorem u6906 : Upper (D 6) (R 6) [34,129,288,5,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6906 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6907 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 292 13 84 96 72 146 274), lower := (rows 35 131 292 13 84 96 72 128 256), losses := [] }

theorem u6907 : Upper (D 6) (R 6) [34,129,288,5,68,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6907 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6908 : PairBound 9 := { available := 10, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 292 13 84 96 80 138 266), lower := (rows 35 131 292 13 84 96 80 128 256), losses := [] }

theorem u6908 : Upper (D 6) (R 6) [34,129,288,5,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6908 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6909 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 210, targets := 32 },{ cop := 4, region := 292, targets := 1 }], pairs := [(1,5),(2,0),(4,5)], upper := (rows 35 131 292 13 88 96 66 148 276), lower := (rows 35 131 292 13 88 96 66 128 256), losses := [] }

theorem u6909 : Upper (D 6) (R 6) [34,129,288,5,72,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6909 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6910 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 80, targets := 3 },{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,0),(4,1)], upper := (rows 35 131 292 13 88 96 68 146 274), lower := (rows 35 131 292 13 88 96 68 128 256), losses := [] }

theorem u6910 : Upper (D 6) (R 6) [34,129,288,5,72,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6910 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6911 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 292 13 88 96 80 134 262), lower := (rows 35 131 292 13 88 96 80 128 256), losses := [] }

theorem u6911 : Upper (D 6) (R 6) [34,129,288,5,72,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6911 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6912 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 356, targets := 3 }], pairs := [(1,5),(2,0),(2,1)], upper := (rows 35 131 292 14 25 96 68 208 336), lower := (rows 35 131 292 14 25 96 68 128 256), losses := [{ target := 5, region := (rows 1 18 4 8 16 0 76 144 272), good := (rows 3 131 324 78 475 64 68 128 256) }] }

theorem u6912 : Upper (D 6) (R 6) [34,129,288,6,9,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6912 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6913 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 113, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 131 292 14 25 96 80 196 324), lower := (rows 35 131 292 14 25 96 80 128 256), losses := [] }

theorem u6913 : Upper (D 6) (R 6) [34,129,288,6,9,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6913 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6914 : Route 9 := (fun mask => (mask,id))

def c6914 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6914 : Upper (D 6) (R 6) [34,129,288,6,65,64,4] 13 := by
  apply FastRouting.sound _ _ [34,129,288,6,65,64,4] 13 (by decide) (choices 1) [8,16] r6914 c6914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u523
  · exact u524

def b6915 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 113, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 131 292 14 81 96 72 148 276), lower := (rows 35 131 292 14 81 96 72 128 256), losses := [] }

theorem u6915 : Upper (D 6) (R 6) [34,129,288,6,65,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6915 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6916 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 292 14 81 96 80 140 268), lower := (rows 35 131 292 14 81 96 80 128 256), losses := [] }

theorem u6916 : Upper (D 6) (R 6) [34,129,288,6,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6916 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6917 : PairBound 9 := { available := 72, camps := [], pairs := [(2,1),(4,1)], upper := (rows 35 131 292 14 84 48 65 200 328), lower := (rows 35 131 292 14 84 48 65 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 24 56 67 136 264), good := (rows 97 193 292 508 116 48 65 128 256) }] }

theorem u6917 : Upper (D 6) (R 6) [34,129,288,6,68,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6917 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6918 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 35 131 292 14 84 48 72 193 321), lower := (rows 35 131 292 14 84 48 72 128 256), losses := [] }

theorem u6918 : Upper (D 6) (R 6) [34,129,288,6,68,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6918 [(5,4),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6919 : PairBound 9 := { available := 24, camps := [{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 292 14 84 96 65 152 280), lower := (rows 35 131 292 14 84 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 117 11 112 112 64 193 321), good := (rows 446 398 308 14 500 500 508 128 256) }] }

theorem u6919 : Upper (D 6) (R 6) [34,129,288,6,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6919 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6920 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 292 14 84 96 72 145 273), lower := (rows 35 131 292 14 84 96 72 128 256), losses := [] }

theorem u6920 : Upper (D 6) (R 6) [34,129,288,6,68,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6920 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6921 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 292 14 84 96 80 137 265), lower := (rows 35 131 292 14 84 96 80 128 256), losses := [] }

theorem u6921 : Upper (D 6) (R 6) [34,129,288,6,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6921 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6922 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 113, targets := 4 },{ cop := 4, region := 292, targets := 1 }], pairs := [(0,2),(2,0),(4,2)], upper := (rows 35 131 292 14 88 96 65 148 276), lower := (rows 35 131 292 14 88 96 65 128 256), losses := [] }

theorem u6922 : Upper (D 6) (R 6) [34,129,288,6,72,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6922 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6923 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 80, targets := 3 },{ cop := 4, region := 163, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 131 292 14 88 96 68 145 273), lower := (rows 35 131 292 14 88 96 68 128 256), losses := [] }

theorem u6923 : Upper (D 6) (R 6) [34,129,288,6,72,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6924 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 292 14 88 96 80 133 261), lower := (rows 35 131 292 14 88 96 80 128 256), losses := [] }

theorem u6924 : Upper (D 6) (R 6) [34,129,288,6,72,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6924 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6925 : PairBound 9 := { available := 12, camps := [{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 292 25 84 96 66 140 268), lower := (rows 35 131 292 25 84 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 123 67 136 264), good := (rows 98 226 292 508 116 96 98 128 256) }] }

theorem u6925 : Upper (D 6) (R 6) [34,129,288,17,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6925 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6926 : PairBound 9 := { available := 10, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 292 25 84 96 68 138 266), lower := (rows 35 131 292 25 84 96 68 128 256), losses := [] }

theorem u6926 : Upper (D 6) (R 6) [34,129,288,17,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6926 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6927 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 292 25 84 96 72 134 262), lower := (rows 35 131 292 25 84 96 72 128 256), losses := [] }

theorem u6927 : Upper (D 6) (R 6) [34,129,288,17,68,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6927 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6928 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 260, targets := 3 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 292 26 28 96 65 196 324), lower := (rows 35 131 292 26 28 96 65 128 256), losses := [] }

theorem u6928 : Upper (D 6) (R 6) [34,129,288,18,12,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6928 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6929 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 131, targets := 4 },{ cop := 8, region := 100, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 292 26 28 96 68 193 321), lower := (rows 35 131 292 26 28 96 68 128 256), losses := [] }

theorem u6929 : Upper (D 6) (R 6) [34,129,288,18,12,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6929 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6930 : PairBound 9 := { available := 12, camps := [{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 292 26 84 96 65 140 268), lower := (rows 35 131 292 26 84 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 125 9 112 112 64 203 331), good := (rows 446 398 308 446 500 500 508 128 256) }] }

theorem u6930 : Upper (D 6) (R 6) [34,129,288,18,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6930 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6931 : PairBound 9 := { available := 9, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 292 26 84 96 68 137 265), lower := (rows 35 131 292 26 84 96 68 128 256), losses := [] }

theorem u6931 : Upper (D 6) (R 6) [34,129,288,18,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6931 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6932 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 292 26 84 96 72 133 261), lower := (rows 35 131 292 26 84 96 72 128 256), losses := [] }

theorem u6932 : Upper (D 6) (R 6) [34,129,288,18,68,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6932 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6933 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 292 28 81 96 66 140 268), lower := (rows 35 131 292 28 81 96 66 128 256), losses := [] }

theorem u6933 : Upper (D 6) (R 6) [34,129,288,20,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6934 : PairBound 9 := { available := 10, camps := [{ cop := 8, region := 100, targets := 3 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 292 28 81 96 68 138 266), lower := (rows 35 131 292 28 81 96 68 128 256), losses := [{ target := 2, region := (rows 9 10 0 8 16 112 64 136 264), good := (rows 35 131 288 443 113 96 96 128 256) }] }

theorem u6934 : Upper (D 6) (R 6) [34,129,288,20,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6934 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6935 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 292 28 81 96 72 134 262), lower := (rows 35 131 292 28 81 96 72 128 256), losses := [] }

theorem u6935 : Upper (D 6) (R 6) [34,129,288,20,65,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6935 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6936 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 292 28 82 96 65 140 268), lower := (rows 35 131 292 28 82 96 65 128 256), losses := [] }

theorem u6936 : Upper (D 6) (R 6) [34,129,288,20,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6936 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6937 : PairBound 9 := { available := 9, camps := [{ cop := 8, region := 100, targets := 3 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 292 28 82 96 68 137 265), lower := (rows 35 131 292 28 82 96 68 128 256), losses := [] }

theorem u6937 : Upper (D 6) (R 6) [34,129,288,20,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6937 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6938 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 292 28 82 96 72 133 261), lower := (rows 35 131 292 28 82 96 72 128 256), losses := [] }

theorem u6938 : Upper (D 6) (R 6) [34,129,288,20,66,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6938 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6939 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 308, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 292 73 84 48 66 140 268), lower := (rows 35 131 292 73 84 48 66 128 256), losses := [] }

theorem u6939 : Upper (D 6) (R 6) [34,129,288,65,68,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6939 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6940 : PairBound 9 := { available := 10, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 292 73 84 48 68 138 266), lower := (rows 35 131 292 73 84 48 68 128 256), losses := [] }

theorem u6940 : Upper (D 6) (R 6) [34,129,288,65,68,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6940 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6941 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 72, targets := 2 }], pairs := [(3,1)], upper := (rows 35 131 292 73 84 48 72 134 262), lower := (rows 35 131 292 73 84 48 72 128 256), losses := [] }

theorem u6941 : Upper (D 6) (R 6) [34,129,288,65,68,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6941 [(5,4),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6942 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 308, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 292 74 84 48 65 140 268), lower := (rows 35 131 292 74 84 48 65 128 256), losses := [] }

theorem u6942 : Upper (D 6) (R 6) [34,129,288,66,68,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6942 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6943 : PairBound 9 := { available := 9, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 292 74 84 48 68 137 265), lower := (rows 35 131 292 74 84 48 68 128 256), losses := [] }

theorem u6943 : Upper (D 6) (R 6) [34,129,288,66,68,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6943 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6944 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 72, targets := 1 }], pairs := [(3,0)], upper := (rows 35 131 292 74 84 48 72 133 261), lower := (rows 35 131 292 74 84 48 72 128 256), losses := [] }

theorem u6944 : Upper (D 6) (R 6) [34,129,288,66,68,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6944 [(5,4),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6945 : PairBound 9 := { available := 48, camps := [], pairs := [(0,2),(1,2)], upper := (rows 35 131 324 13 22 96 72 176 304), lower := (rows 35 131 324 13 22 96 72 128 256), losses := [{ target := 2, region := (rows 17 18 0 8 16 108 72 144 272), good := (rows 35 131 352 105 435 96 104 128 256) }] }

theorem u6945 : Upper (D 6) (R 6) [34,129,320,5,6,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6945 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6946 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 97, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 131 324 13 22 96 80 168 296), lower := (rows 35 131 324 13 22 96 80 128 256), losses := [{ target := 2, region := (rows 25 10 0 8 16 116 80 136 264), good := (rows 35 131 352 427 115 96 113 128 256) }] }

theorem u6946 : Upper (D 6) (R 6) [34,129,320,5,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6946 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6947 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 146, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 35 131 324 13 22 96 96 152 280), lower := (rows 35 131 324 13 22 96 96 128 256), losses := [] }

theorem u6947 : Upper (D 6) (R 6) [34,129,320,5,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6948 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 356, targets := 3 },{ cop := 8, region := 68, targets := 32 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 131 324 13 26 96 68 176 304), lower := (rows 35 131 324 13 26 96 68 128 256), losses := [] }

theorem u6948 : Upper (D 6) (R 6) [34,129,320,5,10,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6948 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6949 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 356, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 324 13 26 96 80 164 292), lower := (rows 35 131 324 13 26 96 80 128 256), losses := [] }

theorem u6949 : Upper (D 6) (R 6) [34,129,320,5,10,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6949 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6950 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 146, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 35 131 324 13 26 96 96 148 276), lower := (rows 35 131 324 13 26 96 96 128 256), losses := [] }

theorem u6950 : Upper (D 6) (R 6) [34,129,320,5,10,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6950 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6951 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 292, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 324 13 82 36 72 176 304), lower := (rows 35 131 324 13 82 36 72 128 256), losses := [] }

theorem u6951 : Upper (D 6) (R 6) [34,129,320,5,66,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6951 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6952 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 35 131 324 13 82 36 80 168 296), lower := (rows 35 131 324 13 82 36 80 128 256), losses := [] }

theorem u6952 : Upper (D 6) (R 6) [34,129,320,5,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6952 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6953 : PairBound 9 := { available := 24, camps := [{ cop := 8, region := 100, targets := 3 },{ cop := 0, region := 80, targets := 1 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 324 13 82 36 96 152 280), lower := (rows 35 131 324 13 82 36 96 128 256), losses := [] }

theorem u6953 : Upper (D 6) (R 6) [34,129,320,5,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6953 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6954 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 292, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 324 13 88 36 66 176 304), lower := (rows 35 131 324 13 88 36 66 128 256), losses := [{ target := 0, region := (rows 0 2 28 8 24 60 67 152 280), good := (rows 98 194 356 508 508 36 66 128 256) }] }

theorem u6954 : Upper (D 6) (R 6) [34,129,320,5,72,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6954 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6955 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 324 13 88 36 80 162 290), lower := (rows 35 131 324 13 88 36 80 128 256), losses := [] }

theorem u6955 : Upper (D 6) (R 6) [34,129,320,5,72,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6955 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6956 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 112, targets := 3 },{ cop := 8, region := 100, targets := 1 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 35 131 324 13 88 36 96 146 274), lower := (rows 35 131 324 13 88 36 96 128 256), losses := [] }

theorem u6956 : Upper (D 6) (R 6) [34,129,320,5,72,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6957 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 0, region := 80, targets := 4 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 35 131 324 13 112 36 66 152 280), lower := (rows 35 131 324 13 112 36 66 128 256), losses := [] }

theorem u6957 : Upper (D 6) (R 6) [34,129,320,5,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6957 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6958 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 131, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 324 13 112 36 72 146 274), lower := (rows 35 131 324 13 112 36 72 128 256), losses := [] }

theorem u6958 : Upper (D 6) (R 6) [34,129,320,5,96,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6958 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6959 : PairBound 9 := { available := 10, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 324 13 112 36 80 138 266), lower := (rows 35 131 324 13 112 36 80 128 256), losses := [] }

theorem u6959 : Upper (D 6) (R 6) [34,129,320,5,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6959 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u6959
end Delivery.IrregularNine14.P06
