import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0003

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b900 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 152 304 40 321 449 321), lower := (rows 35 70 164 152 304 40 64 128 256), losses := [] }

theorem u900 : Upper (D 10) (R 10) [34,68,160,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b900 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b901 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 164 152 304 96 329 393 265), lower := (rows 35 70 164 152 304 96 64 128 256), losses := [] }

theorem u901 : Upper (D 10) (R 10) [34,68,160,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b901 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b902 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 164 152 304 288 73 201 329), lower := (rows 35 70 164 152 304 288 64 128 256), losses := [] }

theorem u902 : Upper (D 10) (R 10) [34,68,160,144,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b902 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b903 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 152 336 33 360 424 296), lower := (rows 35 70 164 152 336 33 64 128 256), losses := [] }

theorem u903 : Upper (D 10) (R 10) [34,68,160,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b903 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b904 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 152 336 40 353 417 289), lower := (rows 35 70 164 152 336 40 64 128 256), losses := [] }

theorem u904 : Upper (D 10) (R 10) [34,68,160,144,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b904 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r905 : Route 9 := (fun mask => (mask,id))

def c905 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u905 : Upper (D 10) (R 10) [34,68,160,144,320,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,144,320,256] 13 (by decide) (choices 1) [1,8,32] r905 c905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u217
  · exact u218
  · exact u219

def b906 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 200 273 40 368 432 304), lower := (rows 35 70 164 200 273 40 64 128 256), losses := [] }

theorem u906 : Upper (D 10) (R 10) [34,68,160,192,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b906 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r907 : Route 9 := (fun mask => (mask,id))

def c907 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u907 : Upper (D 10) (R 10) [34,68,160,192,257,16] 13 := by
  apply FastRouting.sound _ _ [34,68,160,192,257,16] 13 (by decide) (choices 1) [8,32,256] r907 c907
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u220
  · exact u221
  · exact u222

def r908 : Route 9 := (fun mask => (mask,id))

def c908 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u908 : Upper (D 10) (R 10) [34,68,160,192,257,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,192,257,256] 13 (by decide) (choices 1) [8,16,32] r908 c908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u223
  · exact u224
  · exact u225

def b909 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 200 280 33 368 432 304), lower := (rows 35 70 164 200 280 33 64 128 256), losses := [] }

theorem u909 : Upper (D 10) (R 10) [34,68,160,192,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b909 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b910 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 200 280 48 353 417 289), lower := (rows 35 70 164 200 280 48 64 128 256), losses := [] }

theorem u910 : Upper (D 10) (R 10) [34,68,160,192,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b910 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r911 : Route 9 := (fun mask => (mask,id))

def c911 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u911 : Upper (D 10) (R 10) [34,68,160,192,264,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,192,264,256] 13 (by decide) (choices 1) [1,16,32] r911 c911
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u226
  · exact u227
  · exact u228

def b912 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 200 304 33 344 408 280), lower := (rows 35 70 164 200 304 33 64 128 256), losses := [] }

theorem u912 : Upper (D 10) (R 10) [34,68,160,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b912 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b913 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 200 304 40 337 401 273), lower := (rows 35 70 164 200 304 40 64 128 256), losses := [] }

theorem u913 : Upper (D 10) (R 10) [34,68,160,192,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b913 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b914 : PairBound 9 := { available := 265, camps := [{ cop := 8, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 164 200 304 48 329 393 265), lower := (rows 35 70 164 200 304 48 64 128 256), losses := [] }

theorem u914 : Upper (D 10) (R 10) [34,68,160,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b914 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b915 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 164 200 304 288 89 153 281), lower := (rows 35 70 164 200 304 288 64 128 256), losses := [] }

theorem u915 : Upper (D 10) (R 10) [34,68,160,192,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b915 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b916 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 199, targets := 256 }], pairs := [(0,8)], upper := (rows 35 70 164 265 304 40 208 208 464), lower := (rows 35 70 164 265 304 40 64 128 256), losses := [] }

theorem u916 : Upper (D 10) (R 10) [34,68,160,257,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b916 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b917 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 164 265 304 48 200 200 456), lower := (rows 35 70 164 265 304 48 64 128 256), losses := [] }

theorem u917 : Upper (D 10) (R 10) [34,68,160,257,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b917 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b918 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 164 265 304 96 216 152 408), lower := (rows 35 70 164 265 304 96 64 128 256), losses := [] }

theorem u918 : Upper (D 10) (R 10) [34,68,160,257,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b918 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b919 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 164 265 304 160 88 216 344), lower := (rows 35 70 164 265 304 160 64 128 256), losses := [] }

theorem u919 : Upper (D 10) (R 10) [34,68,160,257,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b919 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r920 : Route 9 := (fun mask => (mask,id))

def c920 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u920 : Upper (D 10) (R 10) [34,68,160,257,320,8] 13 := by
  apply FastRouting.sound _ _ [34,68,160,257,320,8] 13 (by decide) (choices 1) [16,32,128] r920 c920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u229
  · exact u230
  · exact u231

def b921 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 265 336 48 232 168 424), lower := (rows 35 70 164 265 336 48 64 128 256), losses := [] }

theorem u921 : Upper (D 10) (R 10) [34,68,160,257,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b921 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b922 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 164 265 336 160 120 184 312), lower := (rows 35 70 164 265 336 160 64 128 256), losses := [] }

theorem u922 : Upper (D 10) (R 10) [34,68,160,257,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b922 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r923 : Route 9 := (fun mask => (mask,id))

def c923 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u923 : Upper (D 10) (R 10) [34,68,160,257,384,8] 13 := by
  apply FastRouting.sound _ _ [34,68,160,257,384,8] 13 (by decide) (choices 1) [16,32] r923 c923
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u232
  · exact u233

def b924 : PairBound 9 := { available := 104, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 265 400 48 104 232 360), lower := (rows 35 70 164 265 400 48 64 128 256), losses := [] }

theorem u924 : Upper (D 10) (R 10) [34,68,160,257,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b924 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b925 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 164 265 400 96 120 184 312), lower := (rows 35 70 164 265 400 96 64 128 256), losses := [] }

theorem u925 : Upper (D 10) (R 10) [34,68,160,257,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b925 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b926 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 296 336 33 216 152 408), lower := (rows 35 70 164 296 336 33 64 128 256), losses := [] }

theorem u926 : Upper (D 10) (R 10) [34,68,160,288,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b926 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b927 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 164 296 336 40 209 145 401), lower := (rows 35 70 164 296 336 40 64 128 256), losses := [] }

theorem u927 : Upper (D 10) (R 10) [34,68,160,288,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b927 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b928 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8)], upper := (rows 35 70 164 296 336 48 201 137 393), lower := (rows 35 70 164 296 336 48 64 128 256), losses := [] }

theorem u928 : Upper (D 10) (R 10) [34,68,160,288,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b928 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b929 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 164 296 336 160 89 153 281), lower := (rows 35 70 164 296 336 160 64 128 256), losses := [] }

theorem u929 : Upper (D 10) (R 10) [34,68,160,288,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b929 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b930 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 296 400 33 88 216 344), lower := (rows 35 70 164 296 400 33 64 128 256), losses := [] }

theorem u930 : Upper (D 10) (R 10) [34,68,160,288,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b930 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b931 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 44, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 296 400 40 81 209 337), lower := (rows 35 70 164 296 400 40 64 128 256), losses := [] }

theorem u931 : Upper (D 10) (R 10) [34,68,160,288,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b931 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b932 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 296 400 48 73 201 329), lower := (rows 35 70 164 296 400 48 64 128 256), losses := [] }

theorem u932 : Upper (D 10) (R 10) [34,68,160,288,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b932 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b933 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 164 296 400 96 89 153 281), lower := (rows 35 70 164 296 400 96 64 128 256), losses := [] }

theorem u933 : Upper (D 10) (R 10) [34,68,160,288,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b933 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b934 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 328 400 33 120 184 312), lower := (rows 35 70 164 328 400 33 64 128 256), losses := [] }

theorem u934 : Upper (D 10) (R 10) [34,68,160,320,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b934 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b935 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 328 400 40 113 177 305), lower := (rows 35 70 164 328 400 40 64 128 256), losses := [] }

theorem u935 : Upper (D 10) (R 10) [34,68,160,320,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b935 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b936 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 328 400 48 105 169 297), lower := (rows 35 70 164 328 400 48 64 128 256), losses := [] }

theorem u936 : Upper (D 10) (R 10) [34,68,160,320,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b936 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b937 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 388 56 208 33 360 424 296), lower := (rows 35 70 388 56 208 33 64 128 256), losses := [] }

theorem u937 : Upper (D 10) (R 10) [34,68,384,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b937 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b938 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 388 56 208 40 353 417 289), lower := (rows 35 70 388 56 208 40 64 128 256), losses := [] }

theorem u938 : Upper (D 10) (R 10) [34,68,384,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b938 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b939 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 216, targets := 256 }], pairs := [(3,8),(4,8)], upper := (rows 35 70 388 56 208 288 105 169 297), lower := (rows 35 70 388 56 208 288 64 128 256), losses := [] }

theorem u939 : Upper (D 10) (R 10) [34,68,384,48,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b939 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b940 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 388 88 176 33 360 424 296), lower := (rows 35 70 388 88 176 33 64 128 256), losses := [] }

theorem u940 : Upper (D 10) (R 10) [34,68,384,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b940 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b941 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 388 88 176 40 353 417 289), lower := (rows 35 70 388 88 176 40 64 128 256), losses := [] }

theorem u941 : Upper (D 10) (R 10) [34,68,384,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b941 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b942 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 216, targets := 256 }], pairs := [(3,8),(4,8)], upper := (rows 35 70 388 88 176 288 105 169 297), lower := (rows 35 70 388 88 176 288 64 128 256), losses := [] }

theorem u942 : Upper (D 10) (R 10) [34,68,384,80,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b942 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b943 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 388 104 145 40 368 432 304), lower := (rows 35 70 388 104 145 40 64 128 256), losses := [] }

theorem u943 : Upper (D 10) (R 10) [34,68,384,96,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b943 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b944 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 388 104 145 48 360 424 296), lower := (rows 35 70 388 104 145 48 64 128 256), losses := [] }

theorem u944 : Upper (D 10) (R 10) [34,68,384,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b944 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b945 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 216, targets := 256 }], pairs := [(3,8),(4,8)], upper := (rows 35 70 388 104 145 288 120 184 312), lower := (rows 35 70 388 104 145 288 64 128 256), losses := [] }

theorem u945 : Upper (D 10) (R 10) [34,68,384,96,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b945 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b946 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 388 104 152 33 368 432 304), lower := (rows 35 70 388 104 152 33 64 128 256), losses := [] }

theorem u946 : Upper (D 10) (R 10) [34,68,384,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b946 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b947 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 388 104 152 48 353 417 289), lower := (rows 35 70 388 104 152 48 64 128 256), losses := [] }

theorem u947 : Upper (D 10) (R 10) [34,68,384,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b947 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b948 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 216, targets := 256 }], pairs := [(3,8),(4,8)], upper := (rows 35 70 388 104 152 288 113 177 305), lower := (rows 35 70 388 104 152 288 64 128 256), losses := [] }

theorem u948 : Upper (D 10) (R 10) [34,68,384,96,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b948 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b949 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 388 104 176 33 344 408 280), lower := (rows 35 70 388 104 176 33 64 128 256), losses := [] }

theorem u949 : Upper (D 10) (R 10) [34,68,384,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b949 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b950 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 388 104 176 40 337 401 273), lower := (rows 35 70 388 104 176 40 64 128 256), losses := [] }

theorem u950 : Upper (D 10) (R 10) [34,68,384,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b950 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b951 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 388 104 176 48 329 393 265), lower := (rows 35 70 388 104 176 48 64 128 256), losses := [] }

theorem u951 : Upper (D 10) (R 10) [34,68,384,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b951 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b952 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 216, targets := 256 }], pairs := [(3,8),(4,8)], upper := (rows 35 70 388 104 176 288 89 153 281), lower := (rows 35 70 388 104 176 288 64 128 256), losses := [] }

theorem u952 : Upper (D 10) (R 10) [34,68,384,96,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b952 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b953 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 200, targets := 256 }], pairs := [(3,8)], upper := (rows 35 70 388 137 280 48 96 224 352), lower := (rows 35 70 388 137 280 48 64 128 256), losses := [] }

theorem u953 : Upper (D 10) (R 10) [34,68,384,129,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b953 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b954 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 388 137 280 96 112 176 304), lower := (rows 35 70 388 137 280 96 64 128 256), losses := [] }

theorem u954 : Upper (D 10) (R 10) [34,68,384,129,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b954 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b955 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 336, targets := 128 }], pairs := [(4,7)], upper := (rows 35 70 388 137 304 40 112 240 368), lower := (rows 35 70 388 137 304 40 64 128 256), losses := [] }

theorem u955 : Upper (D 10) (R 10) [34,68,384,129,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b955 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b956 : PairBound 9 := { available := 104, camps := [{ cop := 2, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 388 137 304 48 104 232 360), lower := (rows 35 70 388 137 304 48 64 128 256), losses := [] }

theorem u956 : Upper (D 10) (R 10) [34,68,384,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b956 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b957 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 388 137 304 96 120 184 312), lower := (rows 35 70 388 137 304 96 64 128 256), losses := [] }

theorem u957 : Upper (D 10) (R 10) [34,68,384,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b957 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b958 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 336, targets := 128 }], pairs := [(4,7)], upper := (rows 35 70 388 137 336 40 112 176 304), lower := (rows 35 70 388 137 336 40 64 128 256), losses := [] }

theorem u958 : Upper (D 10) (R 10) [34,68,384,129,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b958 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b959 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 388 137 336 48 104 168 296), lower := (rows 35 70 388 137 336 48 64 128 256), losses := [] }

theorem u959 : Upper (D 10) (R 10) [34,68,384,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b959 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u959
end Delivery.IrregularNine14.P10
