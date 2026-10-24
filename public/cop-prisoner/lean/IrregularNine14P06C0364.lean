import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0106
import IrregularNine14P06C0107

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21840 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 368, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 70 13 276 48 104 232 360), lower := (rows 35 131 70 13 276 48 64 128 256), losses := [] }

theorem u21840 : Upper (D 6) (R 6) [34,129,66,5,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21840 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21841 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 368, targets := 3 },{ cop := 2, region := 33, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 131 70 13 276 96 120 184 312), lower := (rows 35 131 70 13 276 96 64 128 256), losses := [] }

theorem u21841 : Upper (D 6) (R 6) [34,129,66,5,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21841 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21842 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 41, targets := 64 },{ cop := 3, region := 368, targets := 1 }], pairs := [(0,6),(3,6),(4,0)], upper := (rows 35 131 70 13 280 36 112 240 368), lower := (rows 35 131 70 13 280 36 64 128 256), losses := [] }

theorem u21842 : Upper (D 6) (R 6) [34,129,66,5,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21842 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21843 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 368, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 70 13 280 48 100 228 356), lower := (rows 35 131 70 13 280 48 64 128 256), losses := [] }

theorem u21843 : Upper (D 6) (R 6) [34,129,66,5,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21843 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21844 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 368, targets := 3 },{ cop := 2, region := 33, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 131 70 13 280 96 116 180 308), lower := (rows 35 131 70 13 280 96 64 128 256), losses := [] }

theorem u21844 : Upper (D 6) (R 6) [34,129,66,5,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21844 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21845 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 41, targets := 64 },{ cop := 3, region := 368, targets := 1 }], pairs := [(0,6),(3,6),(4,0)], upper := (rows 35 131 70 13 304 36 88 216 344), lower := (rows 35 131 70 13 304 36 64 128 256), losses := [] }

theorem u21845 : Upper (D 6) (R 6) [34,129,66,5,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21845 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21846 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 70 13 304 40 84 212 340), lower := (rows 35 131 70 13 304 40 64 128 256), losses := [] }

theorem u21846 : Upper (D 6) (R 6) [34,129,66,5,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21846 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21847 : PairBound 9 := { available := 76, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 70 13 304 48 76 204 332), lower := (rows 35 131 70 13 304 48 64 128 256), losses := [] }

theorem u21847 : Upper (D 6) (R 6) [34,129,66,5,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21847 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21848 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 368, targets := 3 },{ cop := 2, region := 33, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 131 70 13 304 96 92 156 284), lower := (rows 35 131 70 13 304 96 64 128 256), losses := [] }

theorem u21848 : Upper (D 6) (R 6) [34,129,66,5,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21848 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21849 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 41, targets := 64 },{ cop := 3, region := 368, targets := 1 }], pairs := [(0,6),(3,6),(4,0)], upper := (rows 35 131 70 13 336 36 120 184 312), lower := (rows 35 131 70 13 336 36 64 128 256), losses := [] }

theorem u21849 : Upper (D 6) (R 6) [34,129,66,5,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21850 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 70 13 336 40 116 180 308), lower := (rows 35 131 70 13 336 40 64 128 256), losses := [] }

theorem u21850 : Upper (D 6) (R 6) [34,129,66,5,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21850 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21851 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 368, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 70 13 336 48 108 172 300), lower := (rows 35 131 70 13 336 48 64 128 256), losses := [] }

theorem u21851 : Upper (D 6) (R 6) [34,129,66,5,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21851 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21852 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 131 70 25 28 36 352 480 352), lower := (rows 35 131 70 25 28 36 64 128 256), losses := [] }

theorem u21852 : Upper (D 6) (R 6) [34,129,66,17,12,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21852 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21853 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 324, targets := 1 },{ cop := 2, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 131 70 25 28 96 356 420 292), lower := (rows 35 131 70 25 28 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 8 24 127 95 159 287), good := (rows 486 486 486 508 508 96 96 128 256) }] }

theorem u21853 : Upper (D 6) (R 6) [34,129,66,17,12,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21853 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21854 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 70 25 28 288 100 228 356), lower := (rows 35 131 70 25 28 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 8 24 319 95 159 287), good := (rows 486 486 486 508 508 288 64 128 288) }] }

theorem u21854 : Upper (D 6) (R 6) [34,129,66,17,12,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21854 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21855 : PairBound 9 := { available := 328, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 131 70 25 52 36 328 456 328), lower := (rows 35 131 70 25 52 36 64 128 256), losses := [] }

theorem u21855 : Upper (D 6) (R 6) [34,129,66,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21855 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21856 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 131 70 25 52 40 324 452 324), lower := (rows 35 131 70 25 52 40 64 128 256), losses := [] }

theorem u21856 : Upper (D 6) (R 6) [34,129,66,17,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21856 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21857 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 70 25 52 96 332 396 268), lower := (rows 35 131 70 25 52 96 64 128 256), losses := [] }

theorem u21857 : Upper (D 6) (R 6) [34,129,66,17,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21857 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21858 : PairBound 9 := { available := 76, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 70 25 52 288 76 204 332), lower := (rows 35 131 70 25 52 288 64 128 256), losses := [] }

theorem u21858 : Upper (D 6) (R 6) [34,129,66,17,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21858 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21859 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(4,0),(4,1)], upper := (rows 35 131 70 25 112 36 332 396 268), lower := (rows 35 131 70 25 112 36 64 128 256), losses := [] }

theorem u21859 : Upper (D 6) (R 6) [34,129,66,17,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21859 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21860 : PairBound 9 := { available := 260, camps := [{ cop := 2, region := 57, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 131 70 25 112 40 324 388 260), lower := (rows 35 131 70 25 112 40 64 128 256), losses := [] }

theorem u21860 : Upper (D 6) (R 6) [34,129,66,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21860 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21861 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 70 25 112 288 76 140 268), lower := (rows 35 131 70 25 112 288 64 128 256), losses := [] }

theorem u21861 : Upper (D 6) (R 6) [34,129,66,17,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21861 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21862 : Route 9 := (fun mask => (mask,id))

def c21862 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21862 : Upper (D 6) (R 6) [34,129,66,17,260,4] 13 := by
  apply FastRouting.sound _ _ [34,129,66,17,260,4] 13 (by decide) (choices 1) [8,32] r21862 c21862
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6416
  · exact u6417

def b21863 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 70 25 276 40 100 228 356), lower := (rows 35 131 70 25 276 40 64 128 256), losses := [] }

theorem u21863 : Upper (D 6) (R 6) [34,129,66,17,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21863 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21864 : Route 9 := (fun mask => (mask,id))

def c21864 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21864 : Upper (D 6) (R 6) [34,129,66,17,260,64] 13 := by
  apply FastRouting.sound _ _ [34,129,66,17,260,64] 13 (by decide) (choices 1) [4,8,32] r21864 c21864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6418
  · exact u6419
  · exact u6420

def b21865 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(4,0)], upper := (rows 35 131 70 25 280 36 100 228 356), lower := (rows 35 131 70 25 280 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 8 24 47 111 175 303), good := (rows 486 486 486 508 504 484 64 128 256) }] }

theorem u21865 : Upper (D 6) (R 6) [34,129,66,17,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21865 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21866 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 2, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 131 70 25 280 96 100 164 292), lower := (rows 35 131 70 25 280 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 8 24 127 79 143 271), good := (rows 486 486 486 508 504 96 96 128 256) }] }

theorem u21866 : Upper (D 6) (R 6) [34,129,66,17,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21866 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21867 : PairBound 9 := { available := 76, camps := [{ cop := 3, region := 198, targets := 32 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,5),(2,5)], upper := (rows 35 131 70 25 304 36 76 204 332), lower := (rows 35 131 70 25 304 36 64 128 256), losses := [] }

theorem u21867 : Upper (D 6) (R 6) [34,129,66,17,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21867 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21868 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 70 25 304 40 68 196 324), lower := (rows 35 131 70 25 304 40 64 128 256), losses := [] }

theorem u21868 : Upper (D 6) (R 6) [34,129,66,17,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21868 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21869 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 198, targets := 32 },{ cop := 2, region := 33, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 35 131 70 25 304 96 76 140 268), lower := (rows 35 131 70 25 304 96 64 128 256), losses := [] }

theorem u21869 : Upper (D 6) (R 6) [34,129,66,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21869 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21870 : Route 9 := (fun mask => (mask,id))

def c21870 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21870 : Upper (D 6) (R 6) [34,129,66,17,320,4] 13 := by
  apply FastRouting.sound _ _ [34,129,66,17,320,4] 13 (by decide) (choices 1) [4,8,32] r21870 c21870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6421
  · exact u6422
  · exact u6423

def b21871 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 70 25 336 40 100 164 292), lower := (rows 35 131 70 25 336 40 64 128 256), losses := [] }

theorem u21871 : Upper (D 6) (R 6) [34,129,66,17,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21871 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21872 : PairBound 9 := { available := 324, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 70 28 56 33 324 452 324), lower := (rows 35 131 70 28 56 33 64 128 256), losses := [] }

theorem u21872 : Upper (D 6) (R 6) [34,129,66,20,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21872 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21873 : PairBound 9 := { available := 321, camps := [{ cop := 5, region := 24, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 131 70 28 56 36 321 449 321), lower := (rows 35 131 70 28 56 36 64 128 256), losses := [] }

theorem u21873 : Upper (D 6) (R 6) [34,129,66,20,40,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21873 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21874 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 131 70 28 56 96 325 389 261), lower := (rows 35 131 70 28 56 96 64 128 256), losses := [] }

theorem u21874 : Upper (D 6) (R 6) [34,129,66,20,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21874 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21875 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 70 28 56 288 69 197 325), lower := (rows 35 131 70 28 56 288 64 128 256), losses := [] }

theorem u21875 : Upper (D 6) (R 6) [34,129,66,20,40,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21875 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21876 : Route 9 := (fun mask => (mask,id))

def c21876 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u21876 : Upper (D 6) (R 6) [34,129,66,20,65,4] 13 := by
  apply FastRouting.sound _ _ [34,129,66,20,65,4] 13 (by decide) (choices 1) [8,32,256] r21876 c21876
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6424
  · exact u6425
  · exact u6426

def b21877 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 70 28 81 40 356 420 292), lower := (rows 35 131 70 28 81 40 64 128 256), losses := [] }

theorem u21877 : Upper (D 6) (R 6) [34,129,66,20,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21877 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21878 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 70 28 81 288 108 172 300), lower := (rows 35 131 70 28 81 288 64 128 256), losses := [] }

theorem u21878 : Upper (D 6) (R 6) [34,129,66,20,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21878 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21879 : PairBound 9 := { available := 268, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 70 28 112 33 332 396 268), lower := (rows 35 131 70 28 112 33 64 128 256), losses := [] }

theorem u21879 : Upper (D 6) (R 6) [34,129,66,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21879 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21880 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 131 70 28 112 36 329 393 265), lower := (rows 35 131 70 28 112 36 64 128 256), losses := [] }

theorem u21880 : Upper (D 6) (R 6) [34,129,66,20,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21880 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21881 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 70 28 112 40 325 389 261), lower := (rows 35 131 70 28 112 40 64 128 256), losses := [] }

theorem u21881 : Upper (D 6) (R 6) [34,129,66,20,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21881 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21882 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 70 28 112 288 77 141 269), lower := (rows 35 131 70 28 112 288 64 128 256), losses := [] }

theorem u21882 : Upper (D 6) (R 6) [34,129,66,20,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21882 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21883 : Route 9 := (fun mask => (mask,id))

def c21883 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21883 : Upper (D 6) (R 6) [34,129,66,20,257,4] 13 := by
  apply FastRouting.sound _ _ [34,129,66,20,257,4] 13 (by decide) (choices 1) [8,32] r21883 c21883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6427
  · exact u6428

def b21884 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 70 28 273 40 100 228 356), lower := (rows 35 131 70 28 273 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 56 89 153 281), good := (rows 486 454 70 508 508 488 64 128 256) }] }

theorem u21884 : Upper (D 6) (R 6) [34,129,66,20,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21884 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21885 : Route 9 := (fun mask => (mask,id))

def c21885 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21885 : Upper (D 6) (R 6) [34,129,66,20,257,64] 13 := by
  apply FastRouting.sound _ _ [34,129,66,20,257,64] 13 (by decide) (choices 1) [4,8,32] r21885 c21885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6429
  · exact u6430
  · exact u6431

def b21886 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 70 28 280 33 100 228 356), lower := (rows 35 131 70 28 280 33 64 128 256), losses := [] }

theorem u21886 : Upper (D 6) (R 6) [34,129,66,20,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21886 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21887 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 195, targets := 4 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 70 28 280 36 97 225 353), lower := (rows 35 131 70 28 280 36 64 128 256), losses := [] }

theorem u21887 : Upper (D 6) (R 6) [34,129,66,20,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21888 : Route 9 := (fun mask => (mask,id))

def c21888 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21888 : Upper (D 6) (R 6) [34,129,66,20,264,64] 13 := by
  apply FastRouting.sound _ _ [34,129,66,20,264,64] 13 (by decide) (choices 1) [1,4,32] r21888 c21888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6432
  · exact u6433
  · exact u6434

def b21889 : PairBound 9 := { available := 76, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 70 28 304 33 76 204 332), lower := (rows 35 131 70 28 304 33 64 128 256), losses := [] }

theorem u21889 : Upper (D 6) (R 6) [34,129,66,20,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21890 : Route 9 := (fun mask => (mask,id))

def c21890 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21890 : Upper (D 6) (R 6) [34,129,66,20,288,4] 13 := by
  apply FastRouting.sound _ _ [34,129,66,20,288,4] 13 (by decide) (choices 1) [1,8] r21890 c21890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6435
  · exact u6436

def b21891 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 70 28 304 40 69 197 325), lower := (rows 35 131 70 28 304 40 64 128 256), losses := [] }

theorem u21891 : Upper (D 6) (R 6) [34,129,66,20,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21891 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21892 : Route 9 := (fun mask => (mask,id))

def c21892 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21892 : Upper (D 6) (R 6) [34,129,66,20,288,64] 13 := by
  apply FastRouting.sound _ _ [34,129,66,20,288,64] 13 (by decide) (choices 1) [1,4,8] r21892 c21892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6437
  · exact u6438
  · exact u6439

def b21893 : PairBound 9 := { available := 44, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 70 28 336 33 108 172 300), lower := (rows 35 131 70 28 336 33 64 128 256), losses := [] }

theorem u21893 : Upper (D 6) (R 6) [34,129,66,20,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21893 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21894 : Route 9 := (fun mask => (mask,id))

def c21894 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21894 : Upper (D 6) (R 6) [34,129,66,20,320,4] 13 := by
  apply FastRouting.sound _ _ [34,129,66,20,320,4] 13 (by decide) (choices 1) [1,8,32] r21894 c21894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6440
  · exact u6441
  · exact u6442

def b21895 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 70 28 336 40 101 165 293), lower := (rows 35 131 70 28 336 40 64 128 256), losses := [] }

theorem u21895 : Upper (D 6) (R 6) [34,129,66,20,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21895 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21896 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 70 44 81 36 344 408 280), lower := (rows 35 131 70 44 81 36 64 128 256), losses := [] }

theorem u21896 : Upper (D 6) (R 6) [34,129,66,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21896 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21897 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 70 44 81 40 340 404 276), lower := (rows 35 131 70 44 81 40 64 128 256), losses := [] }

theorem u21897 : Upper (D 6) (R 6) [34,129,66,36,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21897 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21898 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 70 44 81 48 332 396 268), lower := (rows 35 131 70 44 81 48 64 128 256), losses := [] }

theorem u21898 : Upper (D 6) (R 6) [34,129,66,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21898 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21899 : Route 9 := (fun mask => (mask,id))

def c21899 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21899 : Upper (D 6) (R 6) [34,129,66,36,65,256] 13 := by
  apply FastRouting.sound _ _ [34,129,66,36,65,256] 13 (by decide) (choices 1) [4,8,16] r21899 c21899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6443
  · exact u6444
  · exact u6445

#print axioms u21899
end Delivery.IrregularNine14.P06
