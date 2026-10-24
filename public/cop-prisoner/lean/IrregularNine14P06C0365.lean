import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0107
import IrregularNine14P06C0108

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21900 : PairBound 9 := { available := 276, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 70 44 88 33 340 404 276), lower := (rows 35 131 70 44 88 33 64 128 256), losses := [] }

theorem u21900 : Upper (D 6) (R 6) [34,129,66,36,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21900 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21901 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 131 70 44 88 36 337 401 273), lower := (rows 35 131 70 44 88 36 64 128 256), losses := [] }

theorem u21901 : Upper (D 6) (R 6) [34,129,66,36,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21901 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21902 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 70 44 88 48 325 389 261), lower := (rows 35 131 70 44 88 48 64 128 256), losses := [] }

theorem u21902 : Upper (D 6) (R 6) [34,129,66,36,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21902 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21903 : Route 9 := (fun mask => (mask,id))

def c21903 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21903 : Upper (D 6) (R 6) [34,129,66,36,72,256] 13 := by
  apply FastRouting.sound _ _ [34,129,66,36,72,256] 13 (by decide) (choices 1) [1,4,16] r21903 c21903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6446
  · exact u6447
  · exact u6448

def b21904 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 70 44 273 36 88 216 344), lower := (rows 35 131 70 44 273 36 64 128 256), losses := [] }

theorem u21904 : Upper (D 6) (R 6) [34,129,66,36,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21904 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21905 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 70 44 273 40 84 212 340), lower := (rows 35 131 70 44 273 40 64 128 256), losses := [] }

theorem u21905 : Upper (D 6) (R 6) [34,129,66,36,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21905 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21906 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 76, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 70 44 273 48 76 204 332), lower := (rows 35 131 70 44 273 48 64 128 256), losses := [] }

theorem u21906 : Upper (D 6) (R 6) [34,129,66,36,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21906 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21907 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 131 70 44 273 96 92 156 284), lower := (rows 35 131 70 44 273 96 64 128 256), losses := [] }

theorem u21907 : Upper (D 6) (R 6) [34,129,66,36,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21907 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21908 : PairBound 9 := { available := 88, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 70 44 276 33 88 216 344), lower := (rows 35 131 70 44 276 33 64 128 256), losses := [] }

theorem u21908 : Upper (D 6) (R 6) [34,129,66,36,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21908 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21909 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 70 44 276 40 81 209 337), lower := (rows 35 131 70 44 276 40 64 128 256), losses := [] }

theorem u21909 : Upper (D 6) (R 6) [34,129,66,36,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21909 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21910 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 70 44 276 48 73 201 329), lower := (rows 35 131 70 44 276 48 64 128 256), losses := [] }

theorem u21910 : Upper (D 6) (R 6) [34,129,66,36,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21910 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21911 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 131 70 44 276 96 89 153 281), lower := (rows 35 131 70 44 276 96 64 128 256), losses := [] }

theorem u21911 : Upper (D 6) (R 6) [34,129,66,36,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21912 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 70 44 280 33 84 212 340), lower := (rows 35 131 70 44 280 33 64 128 256), losses := [] }

theorem u21912 : Upper (D 6) (R 6) [34,129,66,36,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21912 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21913 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 70 44 280 36 81 209 337), lower := (rows 35 131 70 44 280 36 64 128 256), losses := [] }

theorem u21913 : Upper (D 6) (R 6) [34,129,66,36,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21914 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 70 44 280 48 69 197 325), lower := (rows 35 131 70 44 280 48 64 128 256), losses := [] }

theorem u21914 : Upper (D 6) (R 6) [34,129,66,36,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21914 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21915 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 131 70 44 280 96 85 149 277), lower := (rows 35 131 70 44 280 96 64 128 256), losses := [] }

theorem u21915 : Upper (D 6) (R 6) [34,129,66,36,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21915 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21916 : PairBound 9 := { available := 28, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 70 44 336 33 92 156 284), lower := (rows 35 131 70 44 336 33 64 128 256), losses := [] }

theorem u21916 : Upper (D 6) (R 6) [34,129,66,36,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21917 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 70 44 336 36 89 153 281), lower := (rows 35 131 70 44 336 36 64 128 256), losses := [] }

theorem u21917 : Upper (D 6) (R 6) [34,129,66,36,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21917 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21918 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 70 44 336 40 85 149 277), lower := (rows 35 131 70 44 336 40 64 128 256), losses := [] }

theorem u21918 : Upper (D 6) (R 6) [34,129,66,36,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21918 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21919 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 70 44 336 48 77 141 269), lower := (rows 35 131 70 44 336 48 64 128 256), losses := [] }

theorem u21919 : Upper (D 6) (R 6) [34,129,66,36,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21919 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21920 : Route 9 := (fun mask => (mask,id))

def c21920 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u21920 : Upper (D 6) (R 6) [34,129,66,48,65,4] 13 := by
  apply FastRouting.sound _ _ [34,129,66,48,65,4] 13 (by decide) (choices 1) [4,8,256] r21920 c21920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6449
  · exact u6450
  · exact u6451

def b21921 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 70 56 81 40 324 388 260), lower := (rows 35 131 70 56 81 40 64 128 256), losses := [] }

theorem u21921 : Upper (D 6) (R 6) [34,129,66,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21921 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21922 : Route 9 := (fun mask => (mask,id))

def c21922 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21922 : Upper (D 6) (R 6) [34,129,66,48,65,256] 13 := by
  apply FastRouting.sound _ _ [34,129,66,48,65,256] 13 (by decide) (choices 1) [4,8] r21922 c21922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6452
  · exact u6453

def r21923 : Route 9 := (fun mask => (mask,id))

def c21923 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21923 : Upper (D 6) (R 6) [34,129,66,48,257,4] 13 := by
  apply FastRouting.sound _ _ [34,129,66,48,257,4] 13 (by decide) (choices 1) [4,8] r21923 c21923
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6454
  · exact u6455

def b21924 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 70 56 273 40 68 196 324), lower := (rows 35 131 70 56 273 40 64 128 256), losses := [] }

theorem u21924 : Upper (D 6) (R 6) [34,129,66,48,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21924 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21925 : Route 9 := (fun mask => (mask,id))

def c21925 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21925 : Upper (D 6) (R 6) [34,129,66,48,257,64] 13 := by
  apply FastRouting.sound _ _ [34,129,66,48,257,64] 13 (by decide) (choices 1) [4,8] r21925 c21925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6456
  · exact u6457

def b21926 : PairBound 9 := { available := 76, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 70 56 276 33 76 204 332), lower := (rows 35 131 70 56 276 33 64 128 256), losses := [] }

theorem u21926 : Upper (D 6) (R 6) [34,129,66,48,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21926 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21927 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 131 70 56 276 36 73 201 329), lower := (rows 35 131 70 56 276 36 64 128 256), losses := [] }

theorem u21927 : Upper (D 6) (R 6) [34,129,66,48,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21927 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21928 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 70 56 276 40 69 197 325), lower := (rows 35 131 70 56 276 40 64 128 256), losses := [] }

theorem u21928 : Upper (D 6) (R 6) [34,129,66,48,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21928 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21929 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 33, targets := 4 }], pairs := [(0,2),(3,0),(3,1)], upper := (rows 35 131 70 56 276 96 77 141 269), lower := (rows 35 131 70 56 276 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 100 64 128 256), good := (rows 34 130 102 56 316 96 96 128 256) },{ target := 1, region := (rows 1 0 4 24 16 100 64 128 256), good := (rows 33 129 100 56 316 96 96 128 256) }] }

theorem u21929 : Upper (D 6) (R 6) [34,129,66,48,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21929 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21930 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 70 56 280 33 68 196 324), lower := (rows 35 131 70 56 280 33 64 128 256), losses := [] }

theorem u21930 : Upper (D 6) (R 6) [34,129,66,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21930 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21931 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 198, targets := 32 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,5),(2,5)], upper := (rows 35 131 70 56 280 36 69 197 325), lower := (rows 35 131 70 56 280 36 64 128 256), losses := [] }

theorem u21931 : Upper (D 6) (R 6) [34,129,66,48,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21931 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21932 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 198, targets := 32 },{ cop := 2, region := 33, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 35 131 70 56 280 96 69 133 261), lower := (rows 35 131 70 56 280 96 64 128 256), losses := [] }

theorem u21932 : Upper (D 6) (R 6) [34,129,66,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21932 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21933 : PairBound 9 := { available := 12, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 70 56 336 33 76 140 268), lower := (rows 35 131 70 56 336 33 64 128 256), losses := [] }

theorem u21933 : Upper (D 6) (R 6) [34,129,66,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21934 : Route 9 := (fun mask => (mask,id))

def c21934 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21934 : Upper (D 6) (R 6) [34,129,66,48,320,4] 13 := by
  apply FastRouting.sound _ _ [34,129,66,48,320,4] 13 (by decide) (choices 1) [1,4,8] r21934 c21934
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6458
  · exact u6459
  · exact u6460

def b21935 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 70 56 336 40 69 133 261), lower := (rows 35 131 70 56 336 40 64 128 256), losses := [] }

theorem u21935 : Upper (D 6) (R 6) [34,129,66,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21935 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21936 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 131 70 73 276 36 120 184 312), lower := (rows 35 131 70 73 276 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 11 52 52 69 133 261), good := (rows 505 457 508 457 500 500 64 128 256) }] }

theorem u21936 : Upper (D 6) (R 6) [34,129,66,65,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21936 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21937 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 70 73 276 40 116 180 308), lower := (rows 35 131 70 73 276 40 64 128 256), losses := [] }

theorem u21937 : Upper (D 6) (R 6) [34,129,66,65,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21937 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21938 : Route 9 := (fun mask => (mask,id))

def c21938 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21938 : Upper (D 6) (R 6) [34,129,66,65,260,16] 13 := by
  apply FastRouting.sound _ _ [34,129,66,65,260,16] 13 (by decide) (choices 1) [4,8,32] r21938 c21938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6461
  · exact u6462
  · exact u6463

def r21939 : Route 9 := (fun mask => (mask,id))

def c21939 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21939 : Upper (D 6) (R 6) [34,129,66,65,264,4] 13 := by
  apply FastRouting.sound _ _ [34,129,66,65,264,4] 13 (by decide) (choices 1) [4,16,32] r21939 c21939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6464
  · exact u6465
  · exact u6466

def b21940 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 70 73 280 48 100 164 292), lower := (rows 35 131 70 73 280 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 8 24 56 73 137 265), good := (rows 486 454 70 508 504 48 64 128 256) }] }

theorem u21940 : Upper (D 6) (R 6) [34,129,66,65,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21940 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21941 : Route 9 := (fun mask => (mask,id))

def c21941 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21941 : Upper (D 6) (R 6) [34,129,66,65,288,4] 13 := by
  apply FastRouting.sound _ _ [34,129,66,65,288,4] 13 (by decide) (choices 1) [4,8,16] r21941 c21941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6467
  · exact u6468
  · exact u6469

def b21942 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 70 73 304 40 84 148 276), lower := (rows 35 131 70 73 304 40 64 128 256), losses := [] }

theorem u21942 : Upper (D 6) (R 6) [34,129,66,65,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21942 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21943 : PairBound 9 := { available := 12, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 70 73 304 48 76 140 268), lower := (rows 35 131 70 73 304 48 64 128 256), losses := [] }

theorem u21943 : Upper (D 6) (R 6) [34,129,66,65,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21943 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21944 : Route 9 := (fun mask => (mask,id))

def c21944 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21944 : Upper (D 6) (R 6) [34,129,66,80,257,4] 13 := by
  apply FastRouting.sound _ _ [34,129,66,80,257,4] 13 (by decide) (choices 1) [4,8,32] r21944 c21944
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6470
  · exact u6471
  · exact u6472

def b21945 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 70 88 273 40 100 164 292), lower := (rows 35 131 70 88 273 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 56 81 145 273), good := (rows 486 454 70 504 508 40 64 128 256) }] }

theorem u21945 : Upper (D 6) (R 6) [34,129,66,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21945 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21946 : PairBound 9 := { available := 44, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 70 88 276 33 108 172 300), lower := (rows 35 131 70 88 276 33 64 128 256), losses := [] }

theorem u21946 : Upper (D 6) (R 6) [34,129,66,80,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21946 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21947 : Route 9 := (fun mask => (mask,id))

def c21947 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21947 : Upper (D 6) (R 6) [34,129,66,80,260,4] 13 := by
  apply FastRouting.sound _ _ [34,129,66,80,260,4] 13 (by decide) (choices 1) [1,8,32] r21947 c21947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6473
  · exact u6474
  · exact u6475

def r21948 : Route 9 := (fun mask => (mask,id))

def c21948 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21948 : Upper (D 6) (R 6) [34,129,66,80,260,8] 13 := by
  apply FastRouting.sound _ _ [34,129,66,80,260,8] 13 (by decide) (choices 1) [1,4,32] r21948 c21948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6476
  · exact u6477
  · exact u6478

def b21949 : PairBound 9 := { available := 36, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 70 88 280 33 100 164 292), lower := (rows 35 131 70 88 280 33 64 128 256), losses := [] }

theorem u21949 : Upper (D 6) (R 6) [34,129,66,80,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21949 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21950 : Route 9 := (fun mask => (mask,id))

def c21950 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21950 : Upper (D 6) (R 6) [34,129,66,80,264,4] 13 := by
  apply FastRouting.sound _ _ [34,129,66,80,264,4] 13 (by decide) (choices 1) [1,4,32] r21950 c21950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6479
  · exact u6480
  · exact u6481

def b21951 : PairBound 9 := { available := 12, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 70 88 304 33 76 140 268), lower := (rows 35 131 70 88 304 33 64 128 256), losses := [] }

theorem u21951 : Upper (D 6) (R 6) [34,129,66,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21952 : Route 9 := (fun mask => (mask,id))

def c21952 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21952 : Upper (D 6) (R 6) [34,129,66,80,288,4] 13 := by
  apply FastRouting.sound _ _ [34,129,66,80,288,4] 13 (by decide) (choices 1) [1,4,8] r21952 c21952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6482
  · exact u6483
  · exact u6484

def b21953 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 70 88 304 40 69 133 261), lower := (rows 35 131 70 88 304 40 64 128 256), losses := [] }

theorem u21953 : Upper (D 6) (R 6) [34,129,66,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21953 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21954 : PairBound 9 := { available := 28, camps := [{ cop := 2, region := 40, targets := 3 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,0),(3,1)], upper := (rows 35 131 70 104 273 36 92 156 284), lower := (rows 35 131 70 104 273 36 64 128 256), losses := [] }

theorem u21954 : Upper (D 6) (R 6) [34,129,66,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21954 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21955 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 70 104 273 40 84 148 276), lower := (rows 35 131 70 104 273 40 64 128 256), losses := [] }

theorem u21955 : Upper (D 6) (R 6) [34,129,66,96,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21955 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21956 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 76, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 70 104 273 48 76 140 268), lower := (rows 35 131 70 104 273 48 64 128 256), losses := [] }

theorem u21956 : Upper (D 6) (R 6) [34,129,66,96,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21956 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21957 : PairBound 9 := { available := 28, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 70 104 276 33 92 156 284), lower := (rows 35 131 70 104 276 33 64 128 256), losses := [] }

theorem u21957 : Upper (D 6) (R 6) [34,129,66,96,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21957 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21958 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 40, targets := 3 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,0),(3,1)], upper := (rows 35 131 70 104 276 36 89 153 281), lower := (rows 35 131 70 104 276 36 64 128 256), losses := [] }

theorem u21958 : Upper (D 6) (R 6) [34,129,66,96,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21958 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21959 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 70 104 276 40 85 149 277), lower := (rows 35 131 70 104 276 40 64 128 256), losses := [] }

theorem u21959 : Upper (D 6) (R 6) [34,129,66,96,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21959 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u21959
end Delivery.IrregularNine14.P06
