import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0001
import IrregularNine14P01C0002

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b900 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 53 194 268 73 18 34 240 176 432), lower := (rows 53 194 268 73 18 34 64 128 256), losses := [] }

theorem u900 : Upper (D 1) (R 1) [52,192,264,65,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b900
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b901 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 268 73 18 48 226 162 418), lower := (rows 53 194 268 73 18 48 64 128 256), losses := [] }

theorem u901 : Upper (D 1) (R 1) [52,192,264,65,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b901
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r902 : Route 9 := (fun mask => (mask,id))

def c902 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u902 : Upper (D 1) (R 1) [52,192,264,65,2,128] 13 := by
  apply FastRouting.sound _ _ [52,192,264,65,2,128] 13 (by decide) (choices 1) [2,16,32] r902 c902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u113
  · exact u114
  · exact u115

def b903 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 268 73 48 160 82 146 274), lower := (rows 53 194 268 73 48 160 64 128 256), losses := [] }

theorem u903 : Upper (D 1) (R 1) [52,192,264,65,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b903
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b904 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 53 194 324 11 18 40 240 176 432), lower := (rows 53 194 324 11 18 40 64 128 256), losses := [] }

theorem u904 : Upper (D 1) (R 1) [52,192,320,3,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b904
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b905 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 202, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 324 11 18 48 232 168 424), lower := (rows 53 194 324 11 18 48 64 128 256), losses := [] }

theorem u905 : Upper (D 1) (R 1) [52,192,320,3,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b905
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r906 : Route 9 := (fun mask => (mask,id))

def c906 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u906 : Upper (D 1) (R 1) [52,192,320,3,2,128] 13 := by
  apply FastRouting.sound _ _ [52,192,320,3,2,128] 13 (by decide) (choices 1) [8,16,32] r906 c906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u116
  · exact u117
  · exact u118

def b907 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 53 194 324 11 24 160 114 178 306), lower := (rows 53 194 324 11 24 160 64 128 256), losses := [] }

theorem u907 : Upper (D 1) (R 1) [52,192,320,3,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b907
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b908 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 324 11 48 160 90 154 282), lower := (rows 53 194 324 11 48 160 64 128 256), losses := [] }

theorem u908 : Upper (D 1) (R 1) [52,192,320,3,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b908
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b909 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 53 194 324 137 18 34 120 184 312), lower := (rows 53 194 324 137 18 34 64 128 256), losses := [] }

theorem u909 : Upper (D 1) (R 1) [52,192,320,129,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b909
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b910 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 53 194 324 137 18 40 114 178 306), lower := (rows 53 194 324 137 18 40 64 128 256), losses := [] }

theorem u910 : Upper (D 1) (R 1) [52,192,320,129,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b910
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b911 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 202, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 324 137 18 48 106 170 298), lower := (rows 53 194 324 137 18 48 64 128 256), losses := [] }

theorem u911 : Upper (D 1) (R 1) [52,192,320,129,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b911
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b912 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 259 70 88 144 34 232 168 424), lower := (rows 53 259 70 88 144 34 64 128 256), losses := [] }

theorem u912 : Upper (D 1) (R 1) [52,257,66,80,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b912
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b913 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 259 70 88 144 40 226 162 418), lower := (rows 53 259 70 88 144 40 64 128 256), losses := [] }

theorem u913 : Upper (D 1) (R 1) [52,257,66,80,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b913
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b914 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 259 70 88 144 160 106 170 298), lower := (rows 53 259 70 88 144 160 64 128 256), losses := [] }

theorem u914 : Upper (D 1) (R 1) [52,257,66,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b914
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b915 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 53 259 70 138 24 160 112 240 368), lower := (rows 53 259 70 138 24 160 64 128 256), losses := [] }

theorem u915 : Upper (D 1) (R 1) [52,257,66,130,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b915
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b916 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 259 70 138 48 160 88 216 344), lower := (rows 53 259 70 138 48 160 64 128 256), losses := [] }

theorem u916 : Upper (D 1) (R 1) [52,257,66,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b916
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b917 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 259 70 138 80 160 120 184 312), lower := (rows 53 259 70 138 80 160 64 128 256), losses := [] }

theorem u917 : Upper (D 1) (R 1) [52,257,66,130,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b917
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b918 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 259 70 200 18 160 120 184 312), lower := (rows 53 259 70 200 18 160 64 128 256), losses := [] }

theorem u918 : Upper (D 1) (R 1) [52,257,66,192,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b918
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b919 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 53 259 70 200 24 160 114 178 306), lower := (rows 53 259 70 200 24 160 64 128 256), losses := [] }

theorem u919 : Upper (D 1) (R 1) [52,257,66,192,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b919
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b920 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 259 70 200 48 160 90 154 282), lower := (rows 53 259 70 200 48 160 64 128 256), losses := [] }

theorem u920 : Upper (D 1) (R 1) [52,257,66,192,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b920
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b921 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 259 76 138 18 48 224 224 480), lower := (rows 53 259 76 138 18 48 64 128 256), losses := [] }

theorem u921 : Upper (D 1) (R 1) [52,257,72,130,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b921
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b922 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 386, targets := 64 }], pairs := [(1,6)], upper := (rows 53 259 76 138 18 96 240 176 432), lower := (rows 53 259 76 138 18 96 64 128 256), losses := [] }

theorem u922 : Upper (D 1) (R 1) [52,257,72,130,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b922
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b923 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(1,7)], upper := (rows 53 259 76 138 18 160 112 240 368), lower := (rows 53 259 76 138 18 160 64 128 256), losses := [] }

theorem u923 : Upper (D 1) (R 1) [52,257,72,130,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b923
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b924 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 53 259 196 74 18 40 240 176 432), lower := (rows 53 259 196 74 18 40 64 128 256), losses := [] }

theorem u924 : Upper (D 1) (R 1) [52,257,192,66,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b924
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b925 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 53 259 196 74 18 48 232 168 424), lower := (rows 53 259 196 74 18 48 64 128 256), losses := [] }

theorem u925 : Upper (D 1) (R 1) [52,257,192,66,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b925
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b926 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 259 196 74 18 160 120 184 312), lower := (rows 53 259 196 74 18 160 64 128 256), losses := [] }

theorem u926 : Upper (D 1) (R 1) [52,257,192,66,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b926
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b927 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 53 259 196 88 18 34 232 168 424), lower := (rows 53 259 196 88 18 34 64 128 256), losses := [] }

theorem u927 : Upper (D 1) (R 1) [52,257,192,80,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b927
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b928 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 259 196 88 18 40 226 162 418), lower := (rows 53 259 196 88 18 40 64 128 256), losses := [] }

theorem u928 : Upper (D 1) (R 1) [52,257,192,80,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b928
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b929 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 259 196 88 18 160 106 170 298), lower := (rows 53 259 196 88 18 160 64 128 256), losses := [] }

theorem u929 : Upper (D 1) (R 1) [52,257,192,80,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b929
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b930 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 266 7 200 18 96 240 176 432), lower := (rows 53 266 7 200 18 96 64 128 256), losses := [] }

theorem u930 : Upper (D 1) (R 1) [52,264,3,192,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b930
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b931 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 266 7 200 48 96 210 146 402), lower := (rows 53 266 7 200 48 96 64 128 256), losses := [] }

theorem u931 : Upper (D 1) (R 1) [52,264,3,192,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b931
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r932 : Route 9 := (fun mask => (mask,id))

def c932 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u932 : Upper (D 1) (R 1) [52,264,3,192,64,128] 13 := by
  apply FastRouting.sound _ _ [52,264,3,192,64,128] 13 (by decide) (choices 1) [2,16,32] r932 c932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u119
  · exact u120
  · exact u121

def b933 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 229, targets := 2 }], pairs := [(0,1)], upper := (rows 53 266 69 138 18 160 112 240 368), lower := (rows 53 266 69 138 18 160 64 128 256), losses := [] }

theorem u933 : Upper (D 1) (R 1) [52,264,65,130,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b933
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b934 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 266 69 138 48 160 82 210 338), lower := (rows 53 266 69 138 48 160 64 128 256), losses := [] }

theorem u934 : Upper (D 1) (R 1) [52,264,65,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b934
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b935 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 266 69 138 80 160 114 178 306), lower := (rows 53 266 69 138 80 160 64 128 256), losses := [] }

theorem u935 : Upper (D 1) (R 1) [52,264,65,130,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b935
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b936 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 266 70 137 18 160 112 240 368), lower := (rows 53 266 70 137 18 160 64 128 256), losses := [] }

theorem u936 : Upper (D 1) (R 1) [52,264,66,129,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b936
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b937 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 266 70 137 48 160 82 210 338), lower := (rows 53 266 70 137 48 160 64 128 256), losses := [] }

theorem u937 : Upper (D 1) (R 1) [52,264,66,129,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b937
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b938 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 266 70 137 80 160 114 178 306), lower := (rows 53 266 70 137 80 160 64 128 256), losses := [] }

theorem u938 : Upper (D 1) (R 1) [52,264,66,129,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b938
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b939 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 266 196 88 18 33 226 162 418), lower := (rows 53 266 196 88 18 33 64 128 256), losses := [] }

theorem u939 : Upper (D 1) (R 1) [52,264,192,80,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b939
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b940 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1)], upper := (rows 53 266 196 88 18 34 225 161 417), lower := (rows 53 266 196 88 18 34 64 128 256), losses := [] }

theorem u940 : Upper (D 1) (R 1) [52,264,192,80,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b940
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b941 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 266 196 88 18 160 99 163 291), lower := (rows 53 266 196 88 18 160 64 128 256), losses := [] }

theorem u941 : Upper (D 1) (R 1) [52,264,192,80,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b941
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b942 : PairBound 9 := { available := 200, camps := [], pairs := [], upper := (rows 53 274 70 42 144 33 200 200 456), lower := (rows 53 274 70 42 144 33 64 128 256), losses := [] }

theorem u942 : Upper (D 1) (R 1) [52,272,66,34,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b942
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b943 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 53 274 70 42 144 40 193 193 449), lower := (rows 53 274 70 42 144 40 64 128 256), losses := [] }

theorem u943 : Upper (D 1) (R 1) [52,272,66,34,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b943
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b944 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 274 70 42 144 96 201 137 393), lower := (rows 53 274 70 42 144 96 64 128 256), losses := [] }

theorem u944 : Upper (D 1) (R 1) [52,272,66,34,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b944
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b945 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 274 70 42 144 160 73 201 329), lower := (rows 53 274 70 42 144 160 64 128 256), losses := [] }

theorem u945 : Upper (D 1) (R 1) [52,272,66,34,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b945
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b946 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 53 274 70 104 144 33 202 138 394), lower := (rows 53 274 70 104 144 33 64 128 256), losses := [] }

theorem u946 : Upper (D 1) (R 1) [52,272,66,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b946
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b947 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 40, targets := 16 }], pairs := [(3,4)], upper := (rows 53 274 70 104 144 34 201 137 393), lower := (rows 53 274 70 104 144 34 64 128 256), losses := [] }

theorem u947 : Upper (D 1) (R 1) [52,272,66,96,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b947
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b948 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 53 274 70 104 144 40 195 131 387), lower := (rows 53 274 70 104 144 40 64 128 256), losses := [] }

theorem u948 : Upper (D 1) (R 1) [52,272,66,96,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b948
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b949 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 274 70 104 144 160 75 139 267), lower := (rows 53 274 70 104 144 160 64 128 256), losses := [] }

theorem u949 : Upper (D 1) (R 1) [52,272,66,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b949
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b950 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 274 70 137 144 34 104 232 360), lower := (rows 53 274 70 137 144 34 64 128 256), losses := [] }

theorem u950 : Upper (D 1) (R 1) [52,272,66,129,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b950
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b951 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 53 274 70 137 144 40 98 226 354), lower := (rows 53 274 70 137 144 40 64 128 256), losses := [] }

theorem u951 : Upper (D 1) (R 1) [52,272,66,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b951
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b952 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 274 70 137 144 96 106 170 298), lower := (rows 53 274 70 137 144 96 64 128 256), losses := [] }

theorem u952 : Upper (D 1) (R 1) [52,272,66,129,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b952
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b953 : PairBound 9 := { available := 104, camps := [], pairs := [], upper := (rows 53 274 70 138 144 33 104 232 360), lower := (rows 53 274 70 138 144 33 64 128 256), losses := [] }

theorem u953 : Upper (D 1) (R 1) [52,272,66,130,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b953
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b954 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 53 274 70 138 144 40 97 225 353), lower := (rows 53 274 70 138 144 40 64 128 256), losses := [] }

theorem u954 : Upper (D 1) (R 1) [52,272,66,130,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b954
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b955 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 274 70 138 144 96 105 169 297), lower := (rows 53 274 70 138 144 96 64 128 256), losses := [] }

theorem u955 : Upper (D 1) (R 1) [52,272,66,130,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b955
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b956 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 53 274 70 168 144 33 74 202 330), lower := (rows 53 274 70 168 144 33 64 128 256), losses := [] }

theorem u956 : Upper (D 1) (R 1) [52,272,66,160,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b956
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b957 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 274 70 168 144 34 73 201 329), lower := (rows 53 274 70 168 144 34 64 128 256), losses := [] }

theorem u957 : Upper (D 1) (R 1) [52,272,66,160,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b957
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b958 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 53 274 70 168 144 40 67 195 323), lower := (rows 53 274 70 168 144 40 64 128 256), losses := [] }

theorem u958 : Upper (D 1) (R 1) [52,272,66,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b958
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b959 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 274 70 168 144 96 75 139 267), lower := (rows 53 274 70 168 144 96 64 128 256), losses := [] }

theorem u959 : Upper (D 1) (R 1) [52,272,66,160,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b959
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u959
end Delivery.IrregularNine14.P01
