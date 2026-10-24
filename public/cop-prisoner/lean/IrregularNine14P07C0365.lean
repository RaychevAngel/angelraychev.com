import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0109

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21900 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 322 28 73 145 34 228 164 420), lower := (rows 35 322 28 73 145 34 64 128 256), losses := [] }

theorem u21900 : Upper (D 7) (R 7) [34,320,24,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21900 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21901 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 450, targets := 1 },{ cop := 0, region := 144, targets := 64 }], pairs := [(1,0),(2,6),(4,6)], upper := (rows 35 322 28 73 145 36 226 162 418), lower := (rows 35 322 28 73 145 36 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 25 44 0 129 257), good := (rows 435 258 60 445 401 36 0 128 256) }] }

theorem u21901 : Upper (D 7) (R 7) [34,320,24,65,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21901 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21902 : Route 9 := (fun mask => (mask,id))

def c21902 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21902 : Upper (D 7) (R 7) [34,320,24,65,129,128] 13 := by
  apply FastRouting.sound _ _ [34,320,24,65,129,128] 13 (by decide) (choices 1) [2,4,32] r21902 c21902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6555
  · exact u6556
  · exact u6557

def b21903 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 41, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 322 28 73 146 33 228 164 420), lower := (rows 35 322 28 73 146 33 64 128 256), losses := [{ target := 7, region := (rows 19 2 20 10 16 63 64 0 256), good := (rows 43 363 61 105 63 33 64 0 256) }] }

theorem u21903 : Upper (D 7) (R 7) [34,320,24,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21903 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21904 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 200, targets := 2 },{ cop := 0, region := 144, targets := 64 }], pairs := [(2,6),(3,1),(4,6)], upper := (rows 35 322 28 73 146 36 225 161 417), lower := (rows 35 322 28 73 146 36 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 17 44 0 137 265), good := (rows 435 258 444 445 146 36 0 128 256) }] }

theorem u21904 : Upper (D 7) (R 7) [34,320,24,65,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21904 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21905 : Route 9 := (fun mask => (mask,id))

def c21905 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21905 : Upper (D 7) (R 7) [34,320,24,65,130,128] 13 := by
  apply FastRouting.sound _ _ [34,320,24,65,130,128] 13 (by decide) (choices 1) [1,4,32] r21905 c21905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6558
  · exact u6559
  · exact u6560

def b21906 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 41, targets := 128 },{ cop := 0, region := 450, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,0),(3,7)], upper := (rows 35 322 28 73 148 33 226 162 418), lower := (rows 35 322 28 73 148 33 64 128 256), losses := [] }

theorem u21906 : Upper (D 7) (R 7) [34,320,24,65,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21906 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21907 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 322 28 73 148 34 225 161 417), lower := (rows 35 322 28 73 148 34 64 128 256), losses := [] }

theorem u21907 : Upper (D 7) (R 7) [34,320,24,65,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21907 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21908 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 331, targets := 128 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(3,7)], upper := (rows 35 322 28 73 148 160 99 163 291), lower := (rows 35 322 28 73 148 160 64 128 256), losses := [] }

theorem u21908 : Upper (D 7) (R 7) [34,320,24,65,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21908 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21909 : PairBound 9 := { available := 134, camps := [{ cop := 1, region := 41, targets := 128 },{ cop := 2, region := 450, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(3,7)], upper := (rows 35 322 28 73 176 33 198 134 390), lower := (rows 35 322 28 73 176 33 64 128 256), losses := [] }

theorem u21909 : Upper (D 7) (R 7) [34,320,24,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21910 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 322 28 73 176 34 197 133 389), lower := (rows 35 322 28 73 176 34 64 128 256), losses := [] }

theorem u21910 : Upper (D 7) (R 7) [34,320,24,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21910 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21911 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 0, region := 144, targets := 64 }], pairs := [(1,5),(3,5),(4,6)], upper := (rows 35 322 28 73 176 36 195 131 387), lower := (rows 35 322 28 73 176 36 64 128 256), losses := [] }

theorem u21911 : Upper (D 7) (R 7) [34,320,24,65,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21911 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21912 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 322 28 73 176 160 71 135 263), lower := (rows 35 322 28 73 176 160 64 128 256), losses := [] }

theorem u21912 : Upper (D 7) (R 7) [34,320,24,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21912 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21913 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 0, region := 450, targets := 1 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(4,6)], upper := (rows 35 322 28 76 145 33 226 162 418), lower := (rows 35 322 28 76 145 33 64 128 256), losses := [] }

theorem u21913 : Upper (D 7) (R 7) [34,320,24,68,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21914 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 28 76 145 34 225 161 417), lower := (rows 35 322 28 76 145 34 64 128 256), losses := [] }

theorem u21914 : Upper (D 7) (R 7) [34,320,24,68,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21915 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 5, region := 323, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 322 28 76 145 160 99 163 291), lower := (rows 35 322 28 76 145 160 64 128 256), losses := [] }

theorem u21915 : Upper (D 7) (R 7) [34,320,24,68,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21915 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21916 : Route 9 := (fun mask => (mask,id))

def c21916 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u21916 : Upper (D 7) (R 7) [34,320,24,68,130,1] 13 := by
  apply FastRouting.sound _ _ [34,320,24,68,130,1] 13 (by decide) (choices 1) [1,32,128] r21916 c21916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6561
  · exact u6562
  · exact u6563

def b21917 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 5, region := 323, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 322 28 76 146 160 97 161 289), lower := (rows 35 322 28 76 146 160 64 128 256), losses := [] }

theorem u21917 : Upper (D 7) (R 7) [34,320,24,68,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21917 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21918 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 0, region := 450, targets := 32 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,5),(4,6)], upper := (rows 35 322 28 76 176 33 195 131 387), lower := (rows 35 322 28 76 176 33 64 128 256), losses := [] }

theorem u21918 : Upper (D 7) (R 7) [34,320,24,68,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21918 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21919 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 28 76 176 34 193 129 385), lower := (rows 35 322 28 76 176 34 64 128 256), losses := [] }

theorem u21919 : Upper (D 7) (R 7) [34,320,24,68,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21919 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21920 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 322 28 76 176 160 67 131 259), lower := (rows 35 322 28 76 176 160 64 128 256), losses := [] }

theorem u21920 : Upper (D 7) (R 7) [34,320,24,68,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21920 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21921 : PairBound 9 := { available := 134, camps := [{ cop := 1, region := 41, targets := 128 },{ cop := 2, region := 450, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(3,7)], upper := (rows 35 322 28 104 145 33 198 134 390), lower := (rows 35 322 28 104 145 33 64 128 256), losses := [] }

theorem u21921 : Upper (D 7) (R 7) [34,320,24,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21921 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21922 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 322 28 104 145 34 197 133 389), lower := (rows 35 322 28 104 145 34 64 128 256), losses := [] }

theorem u21922 : Upper (D 7) (R 7) [34,320,24,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21922 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21923 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 144, targets := 64 }], pairs := [(1,5),(4,5),(4,6)], upper := (rows 35 322 28 104 145 36 195 131 387), lower := (rows 35 322 28 104 145 36 64 128 256), losses := [] }

theorem u21923 : Upper (D 7) (R 7) [34,320,24,96,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21923 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21924 : Route 9 := (fun mask => (mask,id))

def c21924 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21924 : Upper (D 7) (R 7) [34,320,24,96,129,128] 13 := by
  apply FastRouting.sound _ _ [34,320,24,96,129,128] 13 (by decide) (choices 1) [1,2,4] r21924 c21924
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6564
  · exact u6565
  · exact u6566

def b21925 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 41, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 322 28 104 146 33 197 133 389), lower := (rows 35 322 28 104 146 33 64 128 256), losses := [{ target := 7, region := (rows 19 2 20 10 16 55 64 0 256), good := (rows 43 363 61 104 63 33 64 0 256) }] }

theorem u21925 : Upper (D 7) (R 7) [34,320,24,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21925 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21926 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 200, targets := 2 }], pairs := [(1,5),(3,1),(4,5)], upper := (rows 35 322 28 104 146 36 193 129 385), lower := (rows 35 322 28 104 146 36 64 128 256), losses := [] }

theorem u21926 : Upper (D 7) (R 7) [34,320,24,96,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21926 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21927 : Route 9 := (fun mask => (mask,id))

def c21927 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21927 : Upper (D 7) (R 7) [34,320,24,96,130,128] 13 := by
  apply FastRouting.sound _ _ [34,320,24,96,130,128] 13 (by decide) (choices 1) [1,4] r21927 c21927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6567
  · exact u6568

def b21928 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 41, targets := 128 },{ cop := 0, region := 450, targets := 32 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,5),(3,7)], upper := (rows 35 322 28 104 148 33 195 131 387), lower := (rows 35 322 28 104 148 33 64 128 256), losses := [] }

theorem u21928 : Upper (D 7) (R 7) [34,320,24,96,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21928 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21929 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 322 28 104 148 34 193 129 385), lower := (rows 35 322 28 104 148 34 64 128 256), losses := [] }

theorem u21929 : Upper (D 7) (R 7) [34,320,24,96,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21929 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21930 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 331, targets := 128 },{ cop := 0, region := 322, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(3,7)], upper := (rows 35 322 28 104 148 160 67 131 259), lower := (rows 35 322 28 104 148 160 64 128 256), losses := [] }

theorem u21930 : Upper (D 7) (R 7) [34,320,24,96,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21930 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21931 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(3,6)], upper := (rows 35 322 28 137 146 33 100 228 356), lower := (rows 35 322 28 137 146 33 64 128 256), losses := [] }

theorem u21931 : Upper (D 7) (R 7) [34,320,24,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21931 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21932 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 322 28 137 146 36 97 225 353), lower := (rows 35 322 28 137 146 36 64 128 256), losses := [] }

theorem u21932 : Upper (D 7) (R 7) [34,320,24,129,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21932 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21933 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 322 28 137 146 96 101 165 293), lower := (rows 35 322 28 137 146 96 64 128 256), losses := [] }

theorem u21933 : Upper (D 7) (R 7) [34,320,24,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21933 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21934 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 52, targets := 66 }], pairs := [(2,1),(2,6),(4,1),(4,6)], upper := (rows 35 322 28 137 176 33 70 198 326), lower := (rows 35 322 28 137 176 33 64 128 256), losses := [] }

theorem u21934 : Upper (D 7) (R 7) [34,320,24,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21934 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21935 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 28 137 176 34 69 197 325), lower := (rows 35 322 28 137 176 34 64 128 256), losses := [] }

theorem u21935 : Upper (D 7) (R 7) [34,320,24,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21935 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21936 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 322 28 137 176 36 67 195 323), lower := (rows 35 322 28 137 176 36 64 128 256), losses := [] }

theorem u21936 : Upper (D 7) (R 7) [34,320,24,129,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21936 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21937 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 322 28 137 176 96 71 135 263), lower := (rows 35 322 28 137 176 96 64 128 256), losses := [] }

theorem u21937 : Upper (D 7) (R 7) [34,320,24,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21937 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21938 : Route 9 := (fun mask => (mask,id))

def c21938 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21938 : Upper (D 7) (R 7) [34,320,24,129,192,1] 13 := by
  apply FastRouting.sound _ _ [34,320,24,129,192,1] 13 (by decide) (choices 1) [2,4,32] r21938 c21938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6569
  · exact u6570
  · exact u6571

def b21939 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 28 137 208 34 101 165 293), lower := (rows 35 322 28 137 208 34 64 128 256), losses := [] }

theorem u21939 : Upper (D 7) (R 7) [34,320,24,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21939 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21940 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 136, targets := 64 }], pairs := [(0,7),(1,7),(3,6)], upper := (rows 35 322 28 137 208 36 99 163 291), lower := (rows 35 322 28 137 208 36 64 128 256), losses := [] }

theorem u21940 : Upper (D 7) (R 7) [34,320,24,129,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21940 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21941 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 53, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(4,6)], upper := (rows 35 322 28 138 176 33 69 197 325), lower := (rows 35 322 28 138 176 33 64 128 256), losses := [] }

theorem u21941 : Upper (D 7) (R 7) [34,320,24,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21941 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21942 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 322 28 138 176 36 65 193 321), lower := (rows 35 322 28 138 176 36 64 128 256), losses := [] }

theorem u21942 : Upper (D 7) (R 7) [34,320,24,130,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21942 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21943 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 322 28 138 176 96 69 133 261), lower := (rows 35 322 28 138 176 96 64 128 256), losses := [] }

theorem u21943 : Upper (D 7) (R 7) [34,320,24,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21943 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21944 : Route 9 := (fun mask => (mask,id))

def c21944 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21944 : Upper (D 7) (R 7) [34,320,24,130,192,1] 13 := by
  apply FastRouting.sound _ _ [34,320,24,130,192,1] 13 (by decide) (choices 1) [1,4,32] r21944 c21944
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6572
  · exact u6573
  · exact u6574

def b21945 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,7),(1,7),(4,1)], upper := (rows 35 322 28 138 208 36 97 161 289), lower := (rows 35 322 28 138 208 36 64 128 256), losses := [] }

theorem u21945 : Upper (D 7) (R 7) [34,320,24,130,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21945 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21946 : Route 9 := (fun mask => (mask,id))

def c21946 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21946 : Upper (D 7) (R 7) [34,320,24,160,192,1] 13 := by
  apply FastRouting.sound _ _ [34,320,24,160,192,1] 13 (by decide) (choices 1) [1,2,4] r21946 c21946
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6575
  · exact u6576
  · exact u6577

def b21947 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 28 168 208 34 69 133 261), lower := (rows 35 322 28 168 208 34 64 128 256), losses := [] }

theorem u21947 : Upper (D 7) (R 7) [34,320,24,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21947 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21948 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 322 28 168 208 36 67 131 259), lower := (rows 35 322 28 168 208 36 64 128 256), losses := [] }

theorem u21948 : Upper (D 7) (R 7) [34,320,24,160,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21948 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21949 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 322 44 73 145 34 212 148 404), lower := (rows 35 322 44 73 145 34 64 128 256), losses := [] }

theorem u21949 : Upper (D 7) (R 7) [34,320,40,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21949 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21950 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 322 44 73 145 36 210 146 402), lower := (rows 35 322 44 73 145 36 64 128 256), losses := [] }

theorem u21950 : Upper (D 7) (R 7) [34,320,40,65,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21950 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21951 : Route 9 := (fun mask => (mask,id))

def c21951 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21951 : Upper (D 7) (R 7) [34,320,40,65,129,16] 13 := by
  apply FastRouting.sound _ _ [34,320,40,65,129,16] 13 (by decide) (choices 1) [2,4,128] r21951 c21951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6578
  · exact u6579
  · exact u6580

def r21952 : Route 9 := (fun mask => (mask,id))

def c21952 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21952 : Upper (D 7) (R 7) [34,320,40,65,129,128] 13 := by
  apply FastRouting.sound _ _ [34,320,40,65,129,128] 13 (by decide) (choices 1) [2,4,16] r21952 c21952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6581
  · exact u6582
  · exact u6583

def b21953 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 322 44 73 146 33 212 148 404), lower := (rows 35 322 44 73 146 33 64 128 256), losses := [] }

theorem u21953 : Upper (D 7) (R 7) [34,320,40,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21953 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21954 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 322 44 73 146 36 209 145 401), lower := (rows 35 322 44 73 146 36 64 128 256), losses := [] }

theorem u21954 : Upper (D 7) (R 7) [34,320,40,65,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21954 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21955 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 322 44 73 146 48 197 133 389), lower := (rows 35 322 44 73 146 48 64 128 256), losses := [] }

theorem u21955 : Upper (D 7) (R 7) [34,320,40,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21955 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21956 : Route 9 := (fun mask => (mask,id))

def c21956 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21956 : Upper (D 7) (R 7) [34,320,40,65,130,128] 13 := by
  apply FastRouting.sound _ _ [34,320,40,65,130,128] 13 (by decide) (choices 1) [1,4,16] r21956 c21956
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6584
  · exact u6585
  · exact u6586

def b21957 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 322 44 73 148 33 210 146 402), lower := (rows 35 322 44 73 148 33 64 128 256), losses := [] }

theorem u21957 : Upper (D 7) (R 7) [34,320,40,65,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21957 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21958 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 322 44 73 148 34 209 145 401), lower := (rows 35 322 44 73 148 34 64 128 256), losses := [] }

theorem u21958 : Upper (D 7) (R 7) [34,320,40,65,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21958 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21959 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 322 44 73 148 48 195 131 387), lower := (rows 35 322 44 73 148 48 64 128 256), losses := [{ target := 5, region := (rows 1 15 4 9 20 0 73 137 265), good := (rows 459 322 478 459 150 16 64 128 256) }] }

theorem u21959 : Upper (D 7) (R 7) [34,320,40,65,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21959 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u21959
end Delivery.IrregularNine14.P07
