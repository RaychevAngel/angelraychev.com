import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0003

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b900 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 206, targets := 1 }], pairs := [(1,0)], upper := (rows 305 14 84 168 17 33 194 194 450), lower := (rows 305 14 84 168 17 33 64 128 256), losses := [] }

theorem u900 : Upper (D 0) (R 0) [304,12,80,160,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b900
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b901 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 305 14 84 168 17 34 193 193 449), lower := (rows 305 14 84 168 17 34 64 128 256), losses := [] }

theorem u901 : Upper (D 0) (R 0) [304,12,80,160,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b901
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r902 : Route 9 := (fun mask => (mask,id))

def c902 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u902 : Upper (D 0) (R 0) [304,12,80,160,1,64] 13 := by
  apply FastRouting.sound _ _ [304,12,80,160,1,64] 13 (by decide) (choices 1) [1,2,128] r902 c902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u180
  · exact u181
  · exact u182

def b903 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 305 14 84 168 17 160 67 195 323), lower := (rows 305 14 84 168 17 160 64 128 256), losses := [] }

theorem u903 : Upper (D 0) (R 0) [304,12,80,160,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b903
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b904 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 305 14 84 168 18 96 193 129 385), lower := (rows 305 14 84 168 18 96 64 128 256), losses := [] }

theorem u904 : Upper (D 0) (R 0) [304,12,80,160,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b904
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r905 : Route 9 := (fun mask => (mask,id))

def c905 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u905 : Upper (D 0) (R 0) [304,12,80,160,128,64] 13 := by
  apply FastRouting.sound _ _ [304,12,80,160,128,64] 13 (by decide) (choices 1) [1,2] r905 c905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u183
  · exact u184

def b906 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 305 22 44 73 144 33 194 194 450), lower := (rows 305 22 44 73 144 33 64 128 256), losses := [] }

theorem u906 : Upper (D 0) (R 0) [304,20,40,65,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b906
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b907 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 305 22 44 73 144 34 193 193 449), lower := (rows 305 22 44 73 144 34 64 128 256), losses := [] }

theorem u907 : Upper (D 0) (R 0) [304,20,40,65,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b907
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b908 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 305 22 44 73 144 96 195 131 387), lower := (rows 305 22 44 73 144 96 64 128 256), losses := [] }

theorem u908 : Upper (D 0) (R 0) [304,20,40,65,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b908
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b909 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 305 22 44 73 144 160 67 195 323), lower := (rows 305 22 44 73 144 160 64 128 256), losses := [] }

theorem u909 : Upper (D 0) (R 0) [304,20,40,65,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b909
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b910 : PairBound 9 := { available := 193, camps := [], pairs := [(1,5)], upper := (rows 305 22 44 74 144 33 193 193 449), lower := (rows 305 22 44 74 144 33 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 12 181 0 97 161 289), good := (rows 465 30 478 74 144 465 64 144 256) }] }

theorem u910 : Upper (D 0) (R 0) [304,20,40,66,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b910
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b911 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 305 22 44 74 144 96 193 129 385), lower := (rows 305 22 44 74 144 96 64 128 256), losses := [] }

theorem u911 : Upper (D 0) (R 0) [304,20,40,66,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b911
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b912 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 305 22 44 74 144 160 65 193 321), lower := (rows 305 22 44 74 144 160 64 128 256), losses := [] }

theorem u912 : Upper (D 0) (R 0) [304,20,40,66,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b912
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b913 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 206, targets := 1 }], pairs := [(1,0)], upper := (rows 305 22 44 200 17 33 194 194 450), lower := (rows 305 22 44 200 17 33 64 128 256), losses := [] }

theorem u913 : Upper (D 0) (R 0) [304,20,40,192,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b913
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b914 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 305 22 44 200 17 34 193 193 449), lower := (rows 305 22 44 200 17 34 64 128 256), losses := [] }

theorem u914 : Upper (D 0) (R 0) [304,20,40,192,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b914
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b915 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 305 22 44 200 17 96 195 131 387), lower := (rows 305 22 44 200 17 96 64 128 256), losses := [] }

theorem u915 : Upper (D 0) (R 0) [304,20,40,192,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b915
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b916 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 40, targets := 16 }], pairs := [(3,4)], upper := (rows 305 22 69 104 144 33 202 138 394), lower := (rows 305 22 69 104 144 33 64 128 256), losses := [] }

theorem u916 : Upper (D 0) (R 0) [304,20,65,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b916
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b917 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 305 22 69 104 144 34 201 137 393), lower := (rows 305 22 69 104 144 34 64 128 256), losses := [] }

theorem u917 : Upper (D 0) (R 0) [304,20,65,96,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b917
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b918 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 305 22 69 104 144 40 195 131 387), lower := (rows 305 22 69 104 144 40 64 128 256), losses := [] }

theorem u918 : Upper (D 0) (R 0) [304,20,65,96,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b918
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b919 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 305 22 69 104 144 160 75 139 267), lower := (rows 305 22 69 104 144 160 64 128 256), losses := [] }

theorem u919 : Upper (D 0) (R 0) [304,20,65,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b919
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b920 : PairBound 9 := { available := 104, camps := [], pairs := [], upper := (rows 305 22 69 137 144 34 104 232 360), lower := (rows 305 22 69 137 144 34 64 128 256), losses := [] }

theorem u920 : Upper (D 0) (R 0) [304,20,65,129,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b920
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b921 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 305 22 69 137 144 40 98 226 354), lower := (rows 305 22 69 137 144 40 64 128 256), losses := [] }

theorem u921 : Upper (D 0) (R 0) [304,20,65,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b921
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r922 : Route 9 := (fun mask => (mask,id))

def c922 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u922 : Upper (D 0) (R 0) [304,20,65,129,128,64] 13 := by
  apply FastRouting.sound _ _ [304,20,65,129,128,64] 13 (by decide) (choices 1) [2,8,32] r922 c922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u185
  · exact u186
  · exact u187

def b923 : PairBound 9 := { available := 104, camps := [], pairs := [(3,4)], upper := (rows 305 22 69 138 144 33 104 232 360), lower := (rows 305 22 69 138 144 33 64 128 256), losses := [{ target := 4, region := (rows 1 2 4 10 0 37 66 130 258), good := (rows 289 494 101 458 128 33 64 128 256) }] }

theorem u923 : Upper (D 0) (R 0) [304,20,65,130,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b923
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b924 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 305 22 69 138 144 40 97 225 353), lower := (rows 305 22 69 138 144 40 64 128 256), losses := [] }

theorem u924 : Upper (D 0) (R 0) [304,20,65,130,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b924
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r925 : Route 9 := (fun mask => (mask,id))

def c925 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u925 : Upper (D 0) (R 0) [304,20,65,130,128,64] 13 := by
  apply FastRouting.sound _ _ [304,20,65,130,128,64] 13 (by decide) (choices 1) [1,8,32] r925 c925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u188
  · exact u189
  · exact u190

def b926 : PairBound 9 := { available := 74, camps := [], pairs := [(3,4)], upper := (rows 305 22 69 168 144 33 74 202 330), lower := (rows 305 22 69 168 144 33 64 128 256), losses := [{ target := 4, region := (rows 1 2 4 10 0 37 66 130 258), good := (rows 289 494 101 168 128 33 64 128 256) }] }

theorem u926 : Upper (D 0) (R 0) [304,20,65,160,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b926
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b927 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 305 22 69 168 144 34 73 201 329), lower := (rows 305 22 69 168 144 34 64 128 256), losses := [] }

theorem u927 : Upper (D 0) (R 0) [304,20,65,160,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b927
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b928 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 305 22 69 168 144 40 67 195 323), lower := (rows 305 22 69 168 144 40 64 128 256), losses := [] }

theorem u928 : Upper (D 0) (R 0) [304,20,65,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b928
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r929 : Route 9 := (fun mask => (mask,id))

def c929 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u929 : Upper (D 0) (R 0) [304,20,65,160,128,64] 13 := by
  apply FastRouting.sound _ _ [304,20,65,160,128,64] 13 (by decide) (choices 1) [1,2,8] r929 c929
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u191
  · exact u192
  · exact u193

def b930 : PairBound 9 := { available := 42, camps := [], pairs := [(3,4)], upper := (rows 305 22 69 200 144 33 106 170 298), lower := (rows 305 22 69 200 144 33 64 128 256), losses := [{ target := 4, region := (rows 1 2 4 10 0 37 66 130 258), good := (rows 289 494 101 200 128 33 64 128 256) }] }

theorem u930 : Upper (D 0) (R 0) [304,20,65,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b930
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b931 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 305 22 69 200 144 34 105 169 297), lower := (rows 305 22 69 200 144 34 64 128 256), losses := [] }

theorem u931 : Upper (D 0) (R 0) [304,20,65,192,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b931
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b932 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 305 22 69 200 144 40 99 163 291), lower := (rows 305 22 69 200 144 40 64 128 256), losses := [] }

theorem u932 : Upper (D 0) (R 0) [304,20,65,192,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b932
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b933 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 206, targets := 1 }], pairs := [(1,0)], upper := (rows 305 22 76 168 17 33 194 194 450), lower := (rows 305 22 76 168 17 33 64 128 256), losses := [] }

theorem u933 : Upper (D 0) (R 0) [304,20,72,160,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b933
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b934 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 305 22 76 168 17 34 193 193 449), lower := (rows 305 22 76 168 17 34 64 128 256), losses := [] }

theorem u934 : Upper (D 0) (R 0) [304,20,72,160,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b934
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r935 : Route 9 := (fun mask => (mask,id))

def c935 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u935 : Upper (D 0) (R 0) [304,20,72,160,1,64] 13 := by
  apply FastRouting.sound _ _ [304,20,72,160,1,64] 13 (by decide) (choices 1) [1,2,128] r935 c935
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u194
  · exact u195
  · exact u196

def b936 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 305 22 76 168 17 160 67 195 323), lower := (rows 305 22 76 168 17 160 64 128 256), losses := [] }

theorem u936 : Upper (D 0) (R 0) [304,20,72,160,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b936
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b937 : PairBound 9 := { available := 136, camps := [], pairs := [], upper := (rows 305 22 100 73 17 34 200 136 392), lower := (rows 305 22 100 73 17 34 64 128 256), losses := [] }

theorem u937 : Upper (D 0) (R 0) [304,20,96,65,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b937
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b938 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 305 22 100 73 17 40 194 130 386), lower := (rows 305 22 100 73 17 40 64 128 256), losses := [] }

theorem u938 : Upper (D 0) (R 0) [304,20,96,65,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b938
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r939 : Route 9 := (fun mask => (mask,id))

def c939 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u939 : Upper (D 0) (R 0) [304,20,96,65,1,128] 13 := by
  apply FastRouting.sound _ _ [304,20,96,65,1,128] 13 (by decide) (choices 1) [2,8,128] r939 c939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u197
  · exact u198
  · exact u199

def b940 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 305 22 100 73 144 33 202 138 394), lower := (rows 305 22 100 73 144 33 64 128 256), losses := [] }

theorem u940 : Upper (D 0) (R 0) [304,20,96,65,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b940
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b941 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 305 22 100 73 144 34 201 137 393), lower := (rows 305 22 100 73 144 34 64 128 256), losses := [] }

theorem u941 : Upper (D 0) (R 0) [304,20,96,65,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b941
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b942 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 305 22 100 73 144 40 195 131 387), lower := (rows 305 22 100 73 144 40 64 128 256), losses := [] }

theorem u942 : Upper (D 0) (R 0) [304,20,96,65,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b942
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b943 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 305 22 100 73 144 160 75 139 267), lower := (rows 305 22 100 73 144 160 64 128 256), losses := [] }

theorem u943 : Upper (D 0) (R 0) [304,20,96,65,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b943
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b944 : PairBound 9 := { available := 200, camps := [], pairs := [], upper := (rows 305 22 100 137 17 34 200 200 456), lower := (rows 305 22 100 137 17 34 64 128 256), losses := [] }

theorem u944 : Upper (D 0) (R 0) [304,20,96,129,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b944
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b945 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 305 22 100 137 17 40 194 194 450), lower := (rows 305 22 100 137 17 40 64 128 256), losses := [] }

theorem u945 : Upper (D 0) (R 0) [304,20,96,129,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b945
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b946 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 305 22 100 137 17 96 202 138 394), lower := (rows 305 22 100 137 17 96 64 128 256), losses := [] }

theorem u946 : Upper (D 0) (R 0) [304,20,96,129,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b946
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r947 : Route 9 := (fun mask => (mask,id))

def c947 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u947 : Upper (D 0) (R 0) [304,20,96,129,1,128] 13 := by
  apply FastRouting.sound _ _ [304,20,96,129,1,128] 13 (by decide) (choices 1) [2,8] r947 c947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u200
  · exact u201

def r948 : Route 9 := (fun mask => (mask,id))

def c948 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u948 : Upper (D 0) (R 0) [304,20,96,129,128,1] 13 := by
  apply FastRouting.sound _ _ [304,20,96,129,128,1] 13 (by decide) (choices 1) [2,8] r948 c948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u202
  · exact u203

def b949 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 305 22 100 137 144 34 73 201 329), lower := (rows 305 22 100 137 144 34 64 128 256), losses := [] }

theorem u949 : Upper (D 0) (R 0) [304,20,96,129,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b949
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b950 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 305 22 100 137 144 40 67 195 323), lower := (rows 305 22 100 137 144 40 64 128 256), losses := [] }

theorem u950 : Upper (D 0) (R 0) [304,20,96,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b950
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b951 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 305 22 100 137 144 96 75 139 267), lower := (rows 305 22 100 137 144 96 64 128 256), losses := [] }

theorem u951 : Upper (D 0) (R 0) [304,20,96,129,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b951
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b952 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 206, targets := 1 }], pairs := [(1,0)], upper := (rows 305 22 100 138 17 33 200 200 456), lower := (rows 305 22 100 138 17 33 64 128 256), losses := [] }

theorem u952 : Upper (D 0) (R 0) [304,20,96,130,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b952
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b953 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 305 22 100 138 17 40 193 193 449), lower := (rows 305 22 100 138 17 40 64 128 256), losses := [] }

theorem u953 : Upper (D 0) (R 0) [304,20,96,130,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b953
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b954 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 305 22 100 138 17 96 201 137 393), lower := (rows 305 22 100 138 17 96 64 128 256), losses := [] }

theorem u954 : Upper (D 0) (R 0) [304,20,96,130,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b954
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r955 : Route 9 := (fun mask => (mask,id))

def c955 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u955 : Upper (D 0) (R 0) [304,20,96,130,1,128] 13 := by
  apply FastRouting.sound _ _ [304,20,96,130,1,128] 13 (by decide) (choices 1) [1,8] r955 c955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u204
  · exact u205

def r956 : Route 9 := (fun mask => (mask,id))

def c956 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u956 : Upper (D 0) (R 0) [304,20,96,130,128,1] 13 := by
  apply FastRouting.sound _ _ [304,20,96,130,128,1] 13 (by decide) (choices 1) [1,8] r956 c956
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u206
  · exact u207

def b957 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 305 22 100 138 144 40 65 193 321), lower := (rows 305 22 100 138 144 40 64 128 256), losses := [] }

theorem u957 : Upper (D 0) (R 0) [304,20,96,130,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b957
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b958 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 305 22 100 138 144 96 73 137 265), lower := (rows 305 22 100 138 144 96 64 128 256), losses := [] }

theorem u958 : Upper (D 0) (R 0) [304,20,96,130,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b958
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b959 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 206, targets := 1 }], pairs := [(1,0)], upper := (rows 305 22 100 200 17 33 202 138 394), lower := (rows 305 22 100 200 17 33 64 128 256), losses := [] }

theorem u959 : Upper (D 0) (R 0) [304,20,96,192,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b959
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u959
end Delivery.IrregularNine14.P00
