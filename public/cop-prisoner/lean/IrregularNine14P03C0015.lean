import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0002

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b900 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 69 137 112 33 464 400 400), lower := (rows 35 14 69 137 112 33 64 128 256), losses := [] }

theorem u900 : Upper (D 3) (R 3) [34,12,65,129,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b900
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b901 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 35 14 69 137 112 48 449 385 385), lower := (rows 35 14 69 137 112 48 64 128 256), losses := [] }

theorem u901 : Upper (D 3) (R 3) [34,12,65,129,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b901
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b902 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 340, targets := 128 }], pairs := [(2,7)], upper := (rows 35 14 69 137 112 160 337 401 273), lower := (rows 35 14 69 137 112 160 64 128 256), losses := [] }

theorem u902 : Upper (D 3) (R 3) [34,12,65,129,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b902
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b903 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 14 69 137 112 288 209 145 401), lower := (rows 35 14 69 137 112 288 64 128 256), losses := [] }

theorem u903 : Upper (D 3) (R 3) [34,12,65,129,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b903
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b904 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 69 137 208 33 368 432 304), lower := (rows 35 14 69 137 208 33 64 128 256), losses := [] }

theorem u904 : Upper (D 3) (R 3) [34,12,65,129,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b904
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b905 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 35 14 69 137 208 48 353 417 289), lower := (rows 35 14 69 137 208 48 64 128 256), losses := [] }

theorem u905 : Upper (D 3) (R 3) [34,12,65,129,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b905
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b906 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 14 69 137 208 288 113 177 305), lower := (rows 35 14 69 137 208 288 64 128 256), losses := [] }

theorem u906 : Upper (D 3) (R 3) [34,12,65,129,192,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b906
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b907 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 35 14 69 137 273 48 224 224 480), lower := (rows 35 14 69 137 273 48 64 128 256), losses := [] }

theorem u907 : Upper (D 3) (R 3) [34,12,65,129,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b907
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b908 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 14 69 137 273 96 240 176 432), lower := (rows 35 14 69 137 273 96 64 128 256), losses := [] }

theorem u908 : Upper (D 3) (R 3) [34,12,65,129,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b908
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b909 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 69 137 304 33 208 208 464), lower := (rows 35 14 69 137 304 33 64 128 256), losses := [] }

theorem u909 : Upper (D 3) (R 3) [34,12,65,129,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b909
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b910 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 14 69 137 304 48 193 193 449), lower := (rows 35 14 69 137 304 48 64 128 256), losses := [] }

theorem u910 : Upper (D 3) (R 3) [34,12,65,129,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b910
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b911 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 14 69 137 304 96 209 145 401), lower := (rows 35 14 69 137 304 96 64 128 256), losses := [] }

theorem u911 : Upper (D 3) (R 3) [34,12,65,129,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b911
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b912 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 69 137 336 33 240 176 432), lower := (rows 35 14 69 137 336 33 64 128 256), losses := [] }

theorem u912 : Upper (D 3) (R 3) [34,12,65,129,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b912
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b913 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 14 69 137 336 48 225 161 417), lower := (rows 35 14 69 137 336 48 64 128 256), losses := [] }

theorem u913 : Upper (D 3) (R 3) [34,12,65,129,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b913
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b914 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 340, targets := 128 }], pairs := [(2,7)], upper := (rows 35 14 69 137 336 160 113 177 305), lower := (rows 35 14 69 137 336 160 64 128 256), losses := [] }

theorem u914 : Upper (D 3) (R 3) [34,12,65,129,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b914
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b915 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 69 152 273 33 224 224 480), lower := (rows 35 14 69 152 273 33 64 128 256), losses := [] }

theorem u915 : Upper (D 3) (R 3) [34,12,65,144,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b915
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b916 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 14 69 152 273 96 225 161 417), lower := (rows 35 14 69 152 273 96 64 128 256), losses := [] }

theorem u916 : Upper (D 3) (R 3) [34,12,65,144,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b916
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b917 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 68, targets := 128 }], pairs := [(2,7)], upper := (rows 35 14 69 152 273 160 97 225 353), lower := (rows 35 14 69 152 273 160 64 128 256), losses := [] }

theorem u917 : Upper (D 3) (R 3) [34,12,65,144,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b917
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b918 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 69 265 112 33 208 144 400), lower := (rows 35 14 69 265 112 33 64 128 256), losses := [] }

theorem u918 : Upper (D 3) (R 3) [34,12,65,257,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b918
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b919 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 14 69 265 112 48 193 129 385), lower := (rows 35 14 69 265 112 48 64 128 256), losses := [] }

theorem u919 : Upper (D 3) (R 3) [34,12,65,257,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b919
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r920 : Route 9 := (fun mask => (mask,id))

def c920 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u920 : Upper (D 3) (R 3) [34,12,65,257,96,128] 13 := by
  apply FastRouting.sound _ _ [34,12,65,257,96,128] 13 (by decide) (choices 1) [1,16,128] r920 c920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u135
  · exact u136
  · exact u137

def b921 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 35 14 69 265 145 48 224 224 480), lower := (rows 35 14 69 265 145 48 64 128 256), losses := [] }

theorem u921 : Upper (D 3) (R 3) [34,12,65,257,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b921
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b922 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 14 69 265 145 96 240 176 432), lower := (rows 35 14 69 265 145 96 64 128 256), losses := [] }

theorem u922 : Upper (D 3) (R 3) [34,12,65,257,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b922
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r923 : Route 9 := (fun mask => (mask,id))

def c923 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u923 : Upper (D 3) (R 3) [34,12,65,257,129,128] 13 := by
  apply FastRouting.sound _ _ [34,12,65,257,129,128] 13 (by decide) (choices 1) [16,32] r923 c923
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u138
  · exact u139

def b924 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 69 265 176 33 208 208 464), lower := (rows 35 14 69 265 176 33 64 128 256), losses := [] }

theorem u924 : Upper (D 3) (R 3) [34,12,65,257,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b924
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b925 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 14 69 265 176 48 193 193 449), lower := (rows 35 14 69 265 176 48 64 128 256), losses := [] }

theorem u925 : Upper (D 3) (R 3) [34,12,65,257,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b925
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b926 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 14 69 265 176 96 209 145 401), lower := (rows 35 14 69 265 176 96 64 128 256), losses := [] }

theorem u926 : Upper (D 3) (R 3) [34,12,65,257,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b926
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b927 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 69 265 176 160 81 209 337), lower := (rows 35 14 69 265 176 160 64 128 256), losses := [] }

theorem u927 : Upper (D 3) (R 3) [34,12,65,257,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b927
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b928 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 69 265 208 33 240 176 432), lower := (rows 35 14 69 265 208 33 64 128 256), losses := [] }

theorem u928 : Upper (D 3) (R 3) [34,12,65,257,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b928
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b929 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 14 69 265 208 48 225 161 417), lower := (rows 35 14 69 265 208 48 64 128 256), losses := [] }

theorem u929 : Upper (D 3) (R 3) [34,12,65,257,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b929
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r930 : Route 9 := (fun mask => (mask,id))

def c930 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u930 : Upper (D 3) (R 3) [34,12,65,257,192,128] 13 := by
  apply FastRouting.sound _ _ [34,12,65,257,192,128] 13 (by decide) (choices 1) [1,16,32] r930 c930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u140
  · exact u141
  · exact u142

def b931 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 69 280 145 33 224 224 480), lower := (rows 35 14 69 280 145 33 64 128 256), losses := [] }

theorem u931 : Upper (D 3) (R 3) [34,12,65,272,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b931
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b932 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 14 69 280 145 96 225 161 417), lower := (rows 35 14 69 280 145 96 64 128 256), losses := [] }

theorem u932 : Upper (D 3) (R 3) [34,12,65,272,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b932
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b933 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 68, targets := 128 }], pairs := [(2,7)], upper := (rows 35 14 69 280 145 160 97 225 353), lower := (rows 35 14 69 280 145 160 64 128 256), losses := [] }

theorem u933 : Upper (D 3) (R 3) [34,12,65,272,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b933
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b934 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 69 392 112 33 209 145 401), lower := (rows 35 14 69 392 112 33 64 128 256), losses := [] }

theorem u934 : Upper (D 3) (R 3) [34,12,65,384,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b934
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b935 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 14 69 392 112 48 193 129 385), lower := (rows 35 14 69 392 112 48 64 128 256), losses := [] }

theorem u935 : Upper (D 3) (R 3) [34,12,65,384,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b935
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b936 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 84, targets := 128 }], pairs := [(2,7)], upper := (rows 35 14 69 392 112 160 81 145 273), lower := (rows 35 14 69 392 112 160 64 128 256), losses := [] }

theorem u936 : Upper (D 3) (R 3) [34,12,65,384,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b936
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b937 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 69 392 176 33 81 209 337), lower := (rows 35 14 69 392 176 33 64 128 256), losses := [] }

theorem u937 : Upper (D 3) (R 3) [34,12,65,384,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b937
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b938 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 35 14 69 392 176 48 65 193 321), lower := (rows 35 14 69 392 176 48 64 128 256), losses := [] }

theorem u938 : Upper (D 3) (R 3) [34,12,65,384,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b938
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b939 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 14 69 392 176 96 81 145 273), lower := (rows 35 14 69 392 176 96 64 128 256), losses := [] }

theorem u939 : Upper (D 3) (R 3) [34,12,65,384,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b939
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b940 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 69 392 208 33 113 177 305), lower := (rows 35 14 69 392 208 33 64 128 256), losses := [] }

theorem u940 : Upper (D 3) (R 3) [34,12,65,384,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b940
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b941 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 14 69 392 208 48 97 161 289), lower := (rows 35 14 69 392 208 48 64 128 256), losses := [] }

theorem u941 : Upper (D 3) (R 3) [34,12,65,384,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b941
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b942 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 265 145 33 224 224 480), lower := (rows 35 14 84 265 145 33 64 128 256), losses := [] }

theorem u942 : Upper (D 3) (R 3) [34,12,80,257,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b942
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b943 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 35 14 84 265 145 96 225 161 417), lower := (rows 35 14 84 265 145 96 64 128 256), losses := [] }

theorem u943 : Upper (D 3) (R 3) [34,12,80,257,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b943
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b944 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(3,7)], upper := (rows 35 14 84 265 145 160 97 225 353), lower := (rows 35 14 84 265 145 160 64 128 256), losses := [] }

theorem u944 : Upper (D 3) (R 3) [34,12,80,257,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b944
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b945 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 196 265 112 33 209 145 401), lower := (rows 35 14 196 265 112 33 64 128 256), losses := [] }

theorem u945 : Upper (D 3) (R 3) [34,12,192,257,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b945
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b946 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 14 196 265 112 48 193 129 385), lower := (rows 35 14 196 265 112 48 64 128 256), losses := [] }

theorem u946 : Upper (D 3) (R 3) [34,12,192,257,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b946
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b947 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 14 196 265 112 160 81 145 273), lower := (rows 35 14 196 265 112 160 64 128 256), losses := [] }

theorem u947 : Upper (D 3) (R 3) [34,12,192,257,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b947
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b948 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 13 28 400 33 224 224 480), lower := (rows 35 67 13 28 400 33 64 128 256), losses := [] }

theorem u948 : Upper (D 3) (R 3) [34,65,9,20,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b948
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b949 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 28 400 96 225 161 417), lower := (rows 35 67 13 28 400 96 64 128 256), losses := [] }

theorem u949 : Upper (D 3) (R 3) [34,65,9,20,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b949
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b950 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 28 400 160 97 225 353), lower := (rows 35 67 13 28 400 160 64 128 256), losses := [] }

theorem u950 : Upper (D 3) (R 3) [34,65,9,20,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b950
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b951 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 35 67 13 140 273 48 224 224 480), lower := (rows 35 67 13 140 273 48 64 128 256), losses := [] }

theorem u951 : Upper (D 3) (R 3) [34,65,9,132,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b951
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b952 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 140 273 96 240 176 432), lower := (rows 35 67 13 140 273 96 64 128 256), losses := [] }

theorem u952 : Upper (D 3) (R 3) [34,65,9,132,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b952
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b953 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 140 273 160 112 240 368), lower := (rows 35 67 13 140 273 160 64 128 256), losses := [] }

theorem u953 : Upper (D 3) (R 3) [34,65,9,132,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b953
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b954 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 13 140 304 33 208 208 464), lower := (rows 35 67 13 140 304 33 64 128 256), losses := [] }

theorem u954 : Upper (D 3) (R 3) [34,65,9,132,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b954
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b955 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 67 13 140 304 48 193 193 449), lower := (rows 35 67 13 140 304 48 64 128 256), losses := [] }

theorem u955 : Upper (D 3) (R 3) [34,65,9,132,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b955
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b956 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 140 304 96 209 145 401), lower := (rows 35 67 13 140 304 96 64 128 256), losses := [] }

theorem u956 : Upper (D 3) (R 3) [34,65,9,132,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b956
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b957 : PairBound 9 := { available := 81, camps := [{ cop := 5, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 140 304 160 81 209 337), lower := (rows 35 67 13 140 304 160 64 128 256), losses := [] }

theorem u957 : Upper (D 3) (R 3) [34,65,9,132,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b957
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b958 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 13 140 336 33 240 176 432), lower := (rows 35 67 13 140 336 33 64 128 256), losses := [] }

theorem u958 : Upper (D 3) (R 3) [34,65,9,132,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b958
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b959 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 67 13 140 336 48 225 161 417), lower := (rows 35 67 13 140 336 48 64 128 256), losses := [] }

theorem u959 : Upper (D 3) (R 3) [34,65,9,132,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b959
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u959
end Delivery.IrregularNine14.P03
