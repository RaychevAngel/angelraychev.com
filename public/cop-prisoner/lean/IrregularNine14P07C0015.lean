import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0000

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b900 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 11 52 104 336 160 192 131 259), lower := (rows 7 11 52 104 336 160 192 128 256), losses := [] }

theorem u900 : Upper (D 7) (R 7) [6,9,48,96,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b900 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b901 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 11 52 200 81 160 66 416 288), lower := (rows 7 11 52 200 81 160 66 128 256), losses := [] }

theorem u901 : Upper (D 7) (R 7) [6,9,48,192,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b901 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b902 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 394, targets := 32 },{ cop := 5, region := 72, targets := 3 }], pairs := [(1,5),(3,0),(3,1),(3,5)], upper := (rows 7 11 52 200 81 160 96 386 258), lower := (rows 7 11 52 200 81 160 96 128 256), losses := [] }

theorem u902 : Upper (D 7) (R 7) [6,9,48,192,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b902 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b903 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 488, targets := 1 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 7 11 52 200 81 160 320 162 290), lower := (rows 7 11 52 200 81 160 320 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 187 339 131 259), good := (rows 494 490 124 232 508 160 320 160 320) },{ target := 6, region := (rows 1 2 20 8 16 187 0 131 259), good := (rows 423 427 52 168 437 160 256 160 256) }] }

theorem u903 : Upper (D 7) (R 7) [6,9,48,192,65,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b903 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b904 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 136, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 11 52 200 273 96 66 160 416), lower := (rows 7 11 52 200 273 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 123 16 123 67 255 383), good := (rows 494 490 444 488 508 488 490 128 256) },{ target := 1, region := (rows 1 0 70 104 19 104 64 238 366), good := (rows 405 445 444 492 273 492 508 128 256) }] }

theorem u904 : Upper (D 7) (R 7) [6,9,48,192,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b904 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b905 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 100, targets := 131 },{ cop := 0, region := 400, targets := 32 }], pairs := [(2,0),(2,1),(2,7),(4,5)], upper := (rows 7 11 52 200 273 96 96 130 386), lower := (rows 7 11 52 200 273 96 96 128 256), losses := [] }

theorem u905 : Upper (D 7) (R 7) [6,9,48,192,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b905 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b906 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 11 52 200 273 96 192 162 290), lower := (rows 7 11 52 200 273 96 192 128 256), losses := [] }

theorem u906 : Upper (D 7) (R 7) [6,9,48,192,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b906 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b907 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 101, targets := 128 },{ cop := 5, region := 136, targets := 3 }], pairs := [(0,7),(2,7),(3,0),(3,1)], upper := (rows 7 11 52 200 274 96 65 160 416), lower := (rows 7 11 52 200 274 96 65 128 256), losses := [] }

theorem u907 : Upper (D 7) (R 7) [6,9,48,192,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b907 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b908 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 400, targets := 96 },{ cop := 4, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(4,5),(4,6)], upper := (rows 7 11 52 200 274 96 96 129 385), lower := (rows 7 11 52 200 274 96 96 128 256), losses := [] }

theorem u908 : Upper (D 7) (R 7) [6,9,48,192,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b908 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b909 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 11 52 200 274 96 192 161 289), lower := (rows 7 11 52 200 274 96 192 128 256), losses := [] }

theorem u909 : Upper (D 7) (R 7) [6,9,48,192,258,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b910 : PairBound 9 := { available := 160, camps := [], pairs := [(2,0),(2,1),(3,0),(4,0)], upper := (rows 7 11 52 200 336 33 66 160 416), lower := (rows 7 11 52 200 336 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 36 41 49 32 67 164 292), good := (rows 478 90 444 200 336 508 66 128 256) },{ target := 1, region := (rows 1 0 70 88 88 35 64 231 359), good := (rows 421 445 444 476 476 417 508 128 256) }] }

theorem u910 : Upper (D 7) (R 7) [6,9,48,192,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b910 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r911 : Route 9 := (fun mask => (mask,id))

def c911 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u911 : Upper (D 7) (R 7) [6,9,48,192,320,1,32] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,320,1,32] 13 (by decide) (choices 1) [2] r911 c911
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u2

def b912 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 11 52 200 336 33 192 162 290), lower := (rows 7 11 52 200 336 33 192 128 256), losses := [] }

theorem u912 : Upper (D 7) (R 7) [6,9,48,192,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b912 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b913 : PairBound 9 := { available := 160, camps := [], pairs := [(2,0),(2,1),(3,0),(4,0)], upper := (rows 7 11 52 200 336 34 65 160 416), lower := (rows 7 11 52 200 336 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 70 88 88 35 64 231 359), good := (rows 422 446 444 476 476 422 508 128 256) },{ target := 1, region := (rows 1 0 36 41 49 32 67 164 292), good := (rows 477 89 444 200 336 508 89 128 256) }] }

theorem u913 : Upper (D 7) (R 7) [6,9,48,192,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r914 : Route 9 := (fun mask => (mask,id))

def c914 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u914 : Upper (D 7) (R 7) [6,9,48,192,320,2,32] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,320,2,32] 13 (by decide) (choices 1) [1] r914 c914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u3

def b915 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 11 52 200 336 34 192 161 289), lower := (rows 7 11 52 200 336 34 192 128 256), losses := [] }

theorem u915 : Upper (D 7) (R 7) [6,9,48,192,320,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b915 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b916 : PairBound 9 := { available := 34, camps := [], pairs := [(2,0),(2,6),(3,0),(4,0)], upper := (rows 7 11 52 200 336 160 65 162 290), lower := (rows 7 11 52 200 336 160 65 128 256), losses := [{ target := 0, region := (rows 0 2 92 72 80 235 64 131 259), good := (rows 422 430 52 252 380 160 508 160 256) },{ target := 6, region := (rows 1 2 20 8 16 235 0 131 259), good := (rows 423 427 52 168 308 160 417 160 256) }] }

theorem u916 : Upper (D 7) (R 7) [6,9,48,192,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b916 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b917 : PairBound 9 := { available := 33, camps := [], pairs := [(2,1),(2,6),(3,1),(4,1)], upper := (rows 7 11 52 200 336 160 66 161 289), lower := (rows 7 11 52 200 336 160 66 128 256), losses := [{ target := 1, region := (rows 1 0 92 72 80 235 64 131 259), good := (rows 421 429 52 252 380 160 508 160 256) },{ target := 6, region := (rows 1 2 20 8 16 235 0 131 259), good := (rows 423 427 52 168 308 160 418 160 256) }] }

theorem u917 : Upper (D 7) (R 7) [6,9,48,192,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b917 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r918 : Route 9 := (fun mask => (mask,id))

def c918 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u918 : Upper (D 7) (R 7) [6,9,48,192,320,128,32] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,320,128,32] 13 (by decide) (choices 1) [1,2] r918 c918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4
  · exact u5

def b919 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 11 52 296 81 160 66 192 448), lower := (rows 7 11 52 296 81 160 66 128 256), losses := [] }

theorem u919 : Upper (D 7) (R 7) [6,9,48,288,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b919 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b920 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 488, targets := 1 },{ cop := 0, region := 208, targets := 32 }], pairs := [(2,0),(2,1),(3,0),(4,5)], upper := (rows 7 11 52 296 81 160 192 194 322), lower := (rows 7 11 52 296 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 243 243 131 259), good := (rows 494 490 124 360 508 224 224 224 256) },{ target := 1, region := (rows 1 0 20 8 16 224 224 128 256), good := (rows 5 9 116 360 117 224 224 224 256) }] }

theorem u920 : Upper (D 7) (R 7) [6,9,48,288,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b920 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b921 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 11 52 296 82 160 65 192 448), lower := (rows 7 11 52 296 82 160 65 128 256), losses := [] }

theorem u921 : Upper (D 7) (R 7) [6,9,48,288,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b921 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b922 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 488, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(2,0),(2,1),(3,1),(4,5)], upper := (rows 7 11 52 296 82 160 192 193 321), lower := (rows 7 11 52 296 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 224 224 128 256), good := (rows 6 10 116 360 118 224 224 224 256) },{ target := 1, region := (rows 1 0 20 27 16 243 243 131 259), good := (rows 493 489 124 360 508 224 224 224 256) }] }

theorem u922 : Upper (D 7) (R 7) [6,9,48,288,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b922 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b923 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 11 52 328 81 160 66 160 416), lower := (rows 7 11 52 328 81 160 66 128 256), losses := [] }

theorem u923 : Upper (D 7) (R 7) [6,9,48,320,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b923 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b924 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 394, targets := 32 },{ cop := 0, region := 488, targets := 1 }], pairs := [(1,5),(2,0),(3,0),(3,5)], upper := (rows 7 11 52 328 81 160 96 130 386), lower := (rows 7 11 52 328 81 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 179 247 131 259), good := (rows 494 490 124 328 508 224 96 224 256) }] }

theorem u924 : Upper (D 7) (R 7) [6,9,48,320,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b924 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b925 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 488, targets := 1 }], pairs := [(2,0),(2,1),(2,6),(3,0)], upper := (rows 7 11 52 328 81 160 192 162 290), lower := (rows 7 11 52 328 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 243 243 131 259), good := (rows 494 490 124 360 508 224 224 224 256) },{ target := 1, region := (rows 1 0 20 8 16 224 224 128 256), good := (rows 5 9 116 360 117 224 224 224 256) },{ target := 6, region := (rows 1 2 20 8 16 243 0 131 259), good := (rows 423 427 52 296 437 160 160 160 256) }] }

theorem u925 : Upper (D 7) (R 7) [6,9,48,320,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b925 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b926 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 392, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 11 52 328 145 96 66 160 416), lower := (rows 7 11 52 328 145 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 123 16 123 67 255 383), good := (rows 494 490 444 488 508 488 490 128 256) },{ target := 1, region := (rows 1 0 70 104 19 104 64 238 366), good := (rows 405 445 444 492 145 492 508 128 256) }] }

theorem u926 : Upper (D 7) (R 7) [6,9,48,320,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b926 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b927 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 100, targets := 131 },{ cop := 8, region := 104, targets := 1 }], pairs := [(2,0),(2,1),(2,7),(3,0)], upper := (rows 7 11 52 328 145 96 96 130 386), lower := (rows 7 11 52 328 145 96 96 128 256), losses := [] }

theorem u927 : Upper (D 7) (R 7) [6,9,48,320,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b927 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r928 : Route 9 := (fun mask => (mask,id))

def c928 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u928 : Upper (D 7) (R 7) [6,9,48,320,129,64,128] 13 := by
  apply FastRouting.sound _ _ [6,9,48,320,129,64,128] 13 (by decide) (choices 1) [2,32] r928 c928
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6
  · exact u7

def b929 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 101, targets := 128 },{ cop := 5, region := 392, targets := 3 }], pairs := [(0,7),(2,7),(3,0),(3,1)], upper := (rows 7 11 52 328 146 96 65 160 416), lower := (rows 7 11 52 328 146 96 65 128 256), losses := [] }

theorem u929 : Upper (D 7) (R 7) [6,9,48,320,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b929 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b930 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 104, targets := 131 },{ cop := 0, region := 144, targets := 32 }], pairs := [(3,0),(3,1),(3,7),(4,5)], upper := (rows 7 11 52 328 146 96 96 129 385), lower := (rows 7 11 52 328 146 96 96 128 256), losses := [] }

theorem u930 : Upper (D 7) (R 7) [6,9,48,320,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b930 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r931 : Route 9 := (fun mask => (mask,id))

def c931 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u931 : Upper (D 7) (R 7) [6,9,48,320,130,64,128] 13 := by
  apply FastRouting.sound _ _ [6,9,48,320,130,64,128] 13 (by decide) (choices 1) [1,32] r931 c931
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8
  · exact u9

def b932 : PairBound 9 := { available := 160, camps := [], pairs := [(2,0),(2,1),(3,0),(4,0)], upper := (rows 7 11 52 328 208 33 66 160 416), lower := (rows 7 11 52 328 208 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 36 41 49 32 67 164 292), good := (rows 478 90 444 328 208 508 66 128 256) },{ target := 1, region := (rows 1 0 70 88 88 35 64 231 359), good := (rows 421 445 444 476 476 417 508 128 256) }] }

theorem u932 : Upper (D 7) (R 7) [6,9,48,320,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b932 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r933 : Route 9 := (fun mask => (mask,id))

def c933 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u933 : Upper (D 7) (R 7) [6,9,48,320,192,1,32] 13 := by
  apply FastRouting.sound _ _ [6,9,48,320,192,1,32] 13 (by decide) (choices 1) [2] r933 c933
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u10

def b934 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 11 52 328 208 33 192 162 290), lower := (rows 7 11 52 328 208 33 192 128 256), losses := [] }

theorem u934 : Upper (D 7) (R 7) [6,9,48,320,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b934 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b935 : PairBound 9 := { available := 160, camps := [], pairs := [(2,0),(2,1),(3,0),(4,0)], upper := (rows 7 11 52 328 208 34 65 160 416), lower := (rows 7 11 52 328 208 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 70 88 88 35 64 231 359), good := (rows 422 446 444 476 476 422 508 128 256) },{ target := 1, region := (rows 1 0 36 41 49 32 67 164 292), good := (rows 477 89 444 328 208 508 89 128 256) }] }

theorem u935 : Upper (D 7) (R 7) [6,9,48,320,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b935 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r936 : Route 9 := (fun mask => (mask,id))

def c936 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u936 : Upper (D 7) (R 7) [6,9,48,320,192,2,32] 13 := by
  apply FastRouting.sound _ _ [6,9,48,320,192,2,32] 13 (by decide) (choices 1) [1] r936 c936
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u11

def b937 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 11 52 328 208 34 192 161 289), lower := (rows 7 11 52 328 208 34 192 128 256), losses := [] }

theorem u937 : Upper (D 7) (R 7) [6,9,48,320,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b937 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b938 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 11 100 168 82 288 65 144 400), lower := (rows 7 11 100 168 82 288 65 128 256), losses := [] }

theorem u938 : Upper (D 7) (R 7) [6,9,96,160,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b938 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b939 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 11 100 168 82 288 80 129 385), lower := (rows 7 11 100 168 82 288 80 128 256), losses := [] }

theorem u939 : Upper (D 7) (R 7) [6,9,96,160,66,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b939 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b940 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 68, targets := 3 },{ cop := 4, region := 293, targets := 128 }], pairs := [(0,7),(2,0),(2,1)], upper := (rows 7 11 100 168 82 288 192 145 273), lower := (rows 7 11 100 168 82 288 192 128 256), losses := [] }

theorem u940 : Upper (D 7) (R 7) [6,9,96,160,66,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b940 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b941 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 11 100 168 208 288 65 146 274), lower := (rows 7 11 100 168 208 288 65 128 256), losses := [] }

theorem u941 : Upper (D 7) (R 7) [6,9,96,160,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b941 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b942 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 11 100 168 208 288 66 145 273), lower := (rows 7 11 100 168 208 288 66 128 256), losses := [] }

theorem u942 : Upper (D 7) (R 7) [6,9,96,160,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b942 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b943 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 84, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 100 168 208 288 80 131 259), lower := (rows 7 11 100 168 208 288 80 128 256), losses := [] }

theorem u943 : Upper (D 7) (R 7) [6,9,96,160,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b943 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b944 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 267, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 11 100 266 145 48 192 224 352), lower := (rows 7 11 100 266 145 48 192 128 256), losses := [] }

theorem u944 : Upper (D 7) (R 7) [6,9,96,258,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b944 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b945 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 11 100 266 145 96 192 176 304), lower := (rows 7 11 100 266 145 96 192 128 256), losses := [] }

theorem u945 : Upper (D 7) (R 7) [6,9,96,258,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b945 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b946 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 69, targets := 128 },{ cop := 6, region := 164, targets := 3 }], pairs := [(0,7),(2,0),(2,1),(2,7)], upper := (rows 7 11 100 280 50 160 65 192 448), lower := (rows 7 11 100 280 50 160 65 128 256), losses := [] }

theorem u946 : Upper (D 7) (R 7) [6,9,96,272,34,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b946 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b947 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 11 100 280 50 160 192 193 321), lower := (rows 7 11 100 280 50 160 192 128 256), losses := [] }

theorem u947 : Upper (D 7) (R 7) [6,9,96,272,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b947 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b948 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 196, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 11 100 280 145 34 192 224 352), lower := (rows 7 11 100 280 145 34 192 128 256), losses := [{ target := 0, region := (rows 0 2 55 24 16 35 255 183 311), good := (rows 486 494 484 476 508 486 192 192 256) },{ target := 1, region := (rows 1 0 36 9 17 32 245 164 292), good := (rows 477 89 484 344 217 484 192 192 256) }] }

theorem u948 : Upper (D 7) (R 7) [6,9,96,272,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b948 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b949 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 11 100 280 145 96 192 162 290), lower := (rows 7 11 100 280 145 96 192 128 256), losses := [] }

theorem u949 : Upper (D 7) (R 7) [6,9,96,272,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b949 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b950 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 196, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(4,0)], upper := (rows 7 11 100 280 146 33 192 224 352), lower := (rows 7 11 100 280 146 33 192 128 256), losses := [{ target := 0, region := (rows 0 2 36 41 17 32 245 164 292), good := (rows 478 90 492 344 210 508 192 192 256) }] }

theorem u950 : Upper (D 7) (R 7) [6,9,96,272,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b950 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b951 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 11 100 280 146 96 192 161 289), lower := (rows 7 11 100 280 146 96 192 128 256), losses := [] }

theorem u951 : Upper (D 7) (R 7) [6,9,96,272,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b951 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b952 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 408, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 11 100 280 176 33 66 192 448), lower := (rows 7 11 100 280 176 33 66 128 256), losses := [] }

theorem u952 : Upper (D 7) (R 7) [6,9,96,272,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b952 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b953 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(4,0)], upper := (rows 7 11 100 280 176 33 192 194 322), lower := (rows 7 11 100 280 176 33 192 128 256), losses := [{ target := 0, region := (rows 0 2 52 40 48 32 243 131 259), good := (rows 454 458 124 348 252 508 192 192 256) }] }

theorem u953 : Upper (D 7) (R 7) [6,9,96,272,160,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b953 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b954 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 408, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 11 100 280 176 34 65 192 448), lower := (rows 7 11 100 280 176 34 65 128 256), losses := [] }

theorem u954 : Upper (D 7) (R 7) [6,9,96,272,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b954 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b955 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(3,1),(4,1)], upper := (rows 7 11 100 280 176 34 192 193 321), lower := (rows 7 11 100 280 176 34 192 128 256), losses := [{ target := 1, region := (rows 1 0 52 40 48 32 243 131 259), good := (rows 453 457 124 348 252 508 192 192 256) }] }

theorem u955 : Upper (D 7) (R 7) [6,9,96,272,160,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b955 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b956 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 11 100 296 81 160 66 144 400), lower := (rows 7 11 100 296 81 160 66 128 256), losses := [] }

theorem u956 : Upper (D 7) (R 7) [6,9,96,288,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b956 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b957 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 11 100 296 81 160 80 130 386), lower := (rows 7 11 100 296 81 160 80 128 256), losses := [] }

theorem u957 : Upper (D 7) (R 7) [6,9,96,288,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b957 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b958 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 11 100 296 81 160 192 146 274), lower := (rows 7 11 100 296 81 160 192 128 256), losses := [] }

theorem u958 : Upper (D 7) (R 7) [6,9,96,288,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b958 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b959 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 11 100 296 82 160 65 144 400), lower := (rows 7 11 100 296 82 160 65 128 256), losses := [] }

theorem u959 : Upper (D 7) (R 7) [6,9,96,288,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u959
end Delivery.IrregularNine14.P07
