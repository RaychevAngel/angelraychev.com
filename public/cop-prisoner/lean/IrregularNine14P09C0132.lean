import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0089

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r7920 : Route 9 := (fun mask => (mask,id))

def c7920 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7920 : Upper (D 9) (R 9) [34,192,96,257,384] 13 := by
  apply FastRouting.sound _ _ [34,192,96,257,384] 13 (by decide) (choices 1) [1,4,8,16] r7920 c7920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5348
  · exact u5349
  · exact u5350
  · exact u5351

def b7921 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 16, targets := 225 },{ cop := 4, region := 227, targets := 256 }], pairs := [(0,8),(4,0),(4,5),(4,6),(4,7)], upper := (rows 35 194 100 268 280 177 209 145 401), lower := (rows 35 194 100 268 280 32 64 128 256), losses := [] }

theorem u7921 : Upper (D 9) (R 9) [34,192,96,260,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7921 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7922 : Route 9 := (fun mask => (mask,id))

def c7922 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7922 : Upper (D 9) (R 9) [34,192,96,260,384] 13 := by
  apply FastRouting.sound _ _ [34,192,96,260,384] 13 (by decide) (choices 1) [1,8,16] r7922 c7922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5352
  · exact u5353
  · exact u5354

def b7923 : PairBound 9 := { available := 133, camps := [{ cop := 8, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7),(4,0)], upper := (rows 35 194 100 280 280 165 197 133 389), lower := (rows 35 194 100 280 280 32 64 128 256), losses := [] }

theorem u7923 : Upper (D 9) (R 9) [34,192,96,272,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7923 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7924 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 194 100 280 400 45 77 141 269), lower := (rows 35 194 100 280 400 32 64 128 256), losses := [] }

theorem u7924 : Upper (D 9) (R 9) [34,192,96,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7924 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7925 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 4, targets := 289 },{ cop := 2, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5),(2,8)], upper := (rows 35 194 196 265 276 57 121 185 313), lower := (rows 35 194 196 265 276 32 64 128 256), losses := [] }

theorem u7925 : Upper (D 9) (R 9) [34,192,192,257,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7925 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7926 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 4, targets := 289 },{ cop := 2, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5),(2,8)], upper := (rows 35 194 196 265 304 61 93 157 285), lower := (rows 35 194 196 265 304 32 64 128 256), losses := [] }

theorem u7926 : Upper (D 9) (R 9) [34,192,192,257,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7926 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7927 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 4, targets := 289 },{ cop := 2, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5),(2,8)], upper := (rows 35 194 196 268 304 57 89 153 281), lower := (rows 35 194 196 268 304 32 64 128 256), losses := [] }

theorem u7927 : Upper (D 9) (R 9) [34,192,192,260,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7927 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7928 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 7 56 152 480 448 448 448), lower := (rows 97 7 7 56 152 32 64 128 256), losses := [] }

theorem u7928 : Upper (D 9) (R 9) [96,5,3,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7928 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7929 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 6, targets := 480 }], pairs := [(1,5),(1,6),(1,7),(1,8),(2,5)], upper := (rows 97 7 7 56 208 424 456 392 392), lower := (rows 97 7 7 56 208 32 64 128 256), losses := [] }

theorem u7929 : Upper (D 9) (R 9) [96,5,3,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7929 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7930 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 6, targets := 480 }], pairs := [(1,5),(1,6),(1,7),(1,8),(2,5)], upper := (rows 97 7 7 56 400 488 456 456 456), lower := (rows 97 7 7 56 400 32 64 128 256), losses := [] }

theorem u7930 : Upper (D 9) (R 9) [96,5,3,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7930 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7931 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 6, targets := 480 }], pairs := [(1,5),(1,6),(1,7),(1,8),(2,5)], upper := (rows 97 7 7 152 280 480 480 480 480), lower := (rows 97 7 7 152 280 32 64 128 256), losses := [] }

theorem u7931 : Upper (D 9) (R 9) [96,5,3,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7931 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7932 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 6, targets := 480 }], pairs := [(1,5),(1,6),(1,7),(1,8),(2,5)], upper := (rows 97 7 7 152 304 488 456 456 456), lower := (rows 97 7 7 152 304 32 64 128 256), losses := [] }

theorem u7932 : Upper (D 9) (R 9) [96,5,3,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7932 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7933 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 6, targets := 480 }], pairs := [(1,5),(1,6),(1,7),(1,8),(2,5)], upper := (rows 97 7 7 168 208 312 344 408 280), lower := (rows 97 7 7 168 208 32 64 128 256), losses := [] }

theorem u7933 : Upper (D 9) (R 9) [96,5,3,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7933 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7934 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 6, targets := 480 }], pairs := [(1,5),(1,6),(1,7),(1,8),(2,5)], upper := (rows 97 7 7 168 336 440 472 408 408), lower := (rows 97 7 7 168 336 32 64 128 256), losses := [] }

theorem u7934 : Upper (D 9) (R 9) [96,5,3,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7934 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7935 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 6, targets := 480 }], pairs := [(1,5),(1,6),(1,7),(1,8),(2,5)], upper := (rows 97 7 7 168 400 376 344 472 344), lower := (rows 97 7 7 168 400 32 64 128 256), losses := [] }

theorem u7935 : Upper (D 9) (R 9) [96,5,3,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7935 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7936 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 2, targets := 448 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,6),(1,7),(1,8),(3,0),(4,0)], upper := (rows 97 7 13 26 176 480 448 448 448), lower := (rows 97 7 13 26 176 32 64 128 256), losses := [] }

theorem u7936 : Upper (D 9) (R 9) [96,5,9,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7936 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7937 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 13 26 400 480 480 480 480), lower := (rows 97 7 13 26 400 32 64 128 256), losses := [] }

theorem u7937 : Upper (D 9) (R 9) [96,5,9,18,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7937 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7938 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 14, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 13 42 208 432 464 400 400), lower := (rows 97 7 13 42 208 32 64 128 256), losses := [] }

theorem u7938 : Upper (D 9) (R 9) [96,5,9,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7938 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7939 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 14, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 13 42 400 496 464 464 464), lower := (rows 97 7 13 42 400 32 64 128 256), losses := [] }

theorem u7939 : Upper (D 9) (R 9) [96,5,9,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7939 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7940 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 30, targets := 384 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,7)], upper := (rows 97 7 13 56 82 416 448 384 384), lower := (rows 97 7 13 56 82 32 64 128 256), losses := [] }

theorem u7940 : Upper (D 9) (R 9) [96,5,9,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7940 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7941 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 2, targets := 448 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,6),(1,7),(1,8),(3,0),(4,0)], upper := (rows 97 7 13 56 146 480 448 448 448), lower := (rows 97 7 13 56 146 32 64 128 256), losses := [] }

theorem u7941 : Upper (D 9) (R 9) [96,5,9,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7941 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7942 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 504, targets := 1 },{ cop := 2, region := 466, targets := 32 },{ cop := 2, region := 2, targets := 128 }], pairs := [(1,5),(1,7),(3,0),(4,0),(4,5)], upper := (rows 97 7 13 56 208 418 450 386 386), lower := (rows 97 7 13 56 208 32 64 128 256), losses := [] }

theorem u7942 : Upper (D 9) (R 9) [96,5,9,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7942 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7943 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 2, targets := 448 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,6),(1,7),(1,8),(3,0),(4,0)], upper := (rows 97 7 13 56 400 482 450 450 450), lower := (rows 97 7 13 56 400 32 64 128 256), losses := [] }

theorem u7943 : Upper (D 9) (R 9) [96,5,9,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7943 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7944 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 13 138 176 368 336 464 336), lower := (rows 97 7 13 138 176 32 64 128 256), losses := [] }

theorem u7944 : Upper (D 9) (R 9) [96,5,9,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7944 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7945 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 13 138 304 496 464 464 464), lower := (rows 97 7 13 138 304 32 64 128 256), losses := [] }

theorem u7945 : Upper (D 9) (R 9) [96,5,9,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7945 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7946 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 13 138 400 368 368 496 368), lower := (rows 97 7 13 138 400 32 64 128 256), losses := [] }

theorem u7946 : Upper (D 9) (R 9) [96,5,9,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7946 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7947 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 2, targets := 448 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,6),(1,7),(1,8),(3,0),(4,0)], upper := (rows 97 7 13 152 50 480 448 448 448), lower := (rows 97 7 13 152 50 32 64 128 256), losses := [] }

theorem u7947 : Upper (D 9) (R 9) [96,5,9,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7947 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7948 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 13 152 274 480 480 480 480), lower := (rows 97 7 13 152 274 32 64 128 256), losses := [] }

theorem u7948 : Upper (D 9) (R 9) [96,5,9,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7948 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7949 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 2, targets := 448 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,6),(1,7),(1,8),(3,0),(4,0)], upper := (rows 97 7 13 152 304 482 450 450 450), lower := (rows 97 7 13 152 304 32 64 128 256), losses := [] }

theorem u7949 : Upper (D 9) (R 9) [96,5,9,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7949 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7950 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 2, targets := 448 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,6),(1,7),(1,8),(3,0),(4,0)], upper := (rows 97 7 13 168 82 432 464 400 400), lower := (rows 97 7 13 168 82 32 64 128 256), losses := [] }

theorem u7950 : Upper (D 9) (R 9) [96,5,9,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7950 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7951 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 2, targets := 448 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,6),(1,7),(1,8),(3,0),(4,0)], upper := (rows 97 7 13 168 146 368 336 464 336), lower := (rows 97 7 13 168 146 32 64 128 256), losses := [] }

theorem u7951 : Upper (D 9) (R 9) [96,5,9,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7951 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7952 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 2, targets := 448 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,6),(1,7),(1,8),(3,0),(4,0)], upper := (rows 97 7 13 168 208 306 338 402 274), lower := (rows 97 7 13 168 208 32 64 128 256), losses := [] }

theorem u7952 : Upper (D 9) (R 9) [96,5,9,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7952 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7953 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 2, targets := 448 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,6),(1,7),(1,8),(3,0),(4,0)], upper := (rows 97 7 13 168 274 496 464 464 464), lower := (rows 97 7 13 168 274 32 64 128 256), losses := [] }

theorem u7953 : Upper (D 9) (R 9) [96,5,9,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7953 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7954 : PairBound 9 := { available := 402, camps := [{ cop := 2, region := 2, targets := 448 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,6),(1,7),(1,8),(3,0),(4,0)], upper := (rows 97 7 13 168 336 434 466 402 402), lower := (rows 97 7 13 168 336 32 64 128 256), losses := [] }

theorem u7954 : Upper (D 9) (R 9) [96,5,9,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7954 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7955 : PairBound 9 := { available := 338, camps := [{ cop := 2, region := 2, targets := 448 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,6),(1,7),(1,8),(3,0),(4,0)], upper := (rows 97 7 13 168 400 370 338 466 338), lower := (rows 97 7 13 168 400 32 64 128 256), losses := [] }

theorem u7955 : Upper (D 9) (R 9) [96,5,9,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7955 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7956 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 13 392 50 496 464 464 464), lower := (rows 97 7 13 392 50 32 64 128 256), losses := [] }

theorem u7956 : Upper (D 9) (R 9) [96,5,9,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7956 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7957 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 13 392 146 368 368 496 368), lower := (rows 97 7 13 392 146 32 64 128 256), losses := [] }

theorem u7957 : Upper (D 9) (R 9) [96,5,9,384,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7957 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7958 : PairBound 9 := { available := 338, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 13 392 176 370 338 466 338), lower := (rows 97 7 13 392 176 32 64 128 256), losses := [] }

theorem u7958 : Upper (D 9) (R 9) [96,5,9,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7958 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7959 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 14 25 176 480 448 448 448), lower := (rows 97 7 14 25 176 32 64 128 256), losses := [] }

theorem u7959 : Upper (D 9) (R 9) [96,5,10,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7959 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7960 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 6, targets := 480 }], pairs := [(1,5),(1,6),(1,7),(1,8),(2,5)], upper := (rows 97 7 14 25 400 480 480 480 480), lower := (rows 97 7 14 25 400 32 64 128 256), losses := [] }

theorem u7960 : Upper (D 9) (R 9) [96,5,10,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7960 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7961 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 14, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 14 41 208 432 464 400 400), lower := (rows 97 7 14 41 208 32 64 128 256), losses := [] }

theorem u7961 : Upper (D 9) (R 9) [96,5,10,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7961 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7962 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 14, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 14 41 400 496 464 464 464), lower := (rows 97 7 14 41 400 32 64 128 256), losses := [] }

theorem u7962 : Upper (D 9) (R 9) [96,5,10,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7962 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7963 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 30, targets := 384 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,7)], upper := (rows 97 7 14 56 81 416 448 384 384), lower := (rows 97 7 14 56 81 32 64 128 256), losses := [] }

theorem u7963 : Upper (D 9) (R 9) [96,5,10,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7963 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7964 : Route 9 := (fun mask => (mask,id))

def c7964 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7964 : Upper (D 9) (R 9) [96,5,10,48,129] 13 := by
  apply FastRouting.sound _ _ [96,5,10,48,129] 13 (by decide) (choices 1) [64,128,256] r7964 c7964
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5355
  · exact u5356
  · exact u5357

def r7965 : Route 9 := (fun mask => (mask,id))

def c7965 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7965 : Upper (D 9) (R 9) [96,5,10,48,192] 13 := by
  apply FastRouting.sound _ _ [96,5,10,48,192] 13 (by decide) (choices 1) [1,128,256] r7965 c7965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5358
  · exact u5359
  · exact u5360

def r7966 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7966 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7966 : Upper (D 9) (R 9) [96,5,10,48,384] 13 := by
  apply FastRouting.sound _ _ [96,5,10,48,384] 13 (by decide) (choices 1) [1,64,128] r7966 c7966
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5361
  · exact u5362
  · exact u5363

def b7967 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 14, targets := 384 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,7)], upper := (rows 97 7 14 104 145 432 464 400 400), lower := (rows 97 7 14 104 145 32 64 128 256), losses := [] }

theorem u7967 : Upper (D 9) (R 9) [96,5,10,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7967 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7968 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 14, targets := 384 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,7)], upper := (rows 97 7 14 104 400 433 465 401 401), lower := (rows 97 7 14 104 400 32 64 128 256), losses := [] }

theorem u7968 : Upper (D 9) (R 9) [96,5,10,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7968 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7969 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 6, targets := 480 }], pairs := [(1,5),(1,6),(1,7),(1,8),(2,5)], upper := (rows 97 7 14 137 176 368 336 464 336), lower := (rows 97 7 14 137 176 32 64 128 256), losses := [] }

theorem u7969 : Upper (D 9) (R 9) [96,5,10,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7969 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7970 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 6, targets := 480 }], pairs := [(1,5),(1,6),(1,7),(1,8),(2,5)], upper := (rows 97 7 14 137 304 496 464 464 464), lower := (rows 97 7 14 137 304 32 64 128 256), losses := [] }

theorem u7970 : Upper (D 9) (R 9) [96,5,10,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7970 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7971 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 6, targets := 480 }], pairs := [(1,5),(1,6),(1,7),(1,8),(2,5)], upper := (rows 97 7 14 137 400 368 368 496 368), lower := (rows 97 7 14 137 400 32 64 128 256), losses := [] }

theorem u7971 : Upper (D 9) (R 9) [96,5,10,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7971 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7972 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 16, targets := 448 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(4,6),(4,7),(4,8)], upper := (rows 97 7 14 152 49 480 448 448 448), lower := (rows 97 7 14 152 49 32 64 128 256), losses := [] }

theorem u7972 : Upper (D 9) (R 9) [96,5,10,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7972 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7973 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 16, targets := 384 },{ cop := 4, region := 1, targets := 384 },{ cop := 0, region := 16, targets := 1 }], pairs := [(0,7),(0,8),(4,0),(4,7),(4,8)], upper := (rows 97 7 14 152 112 417 449 385 385), lower := (rows 97 7 14 152 112 32 64 128 256), losses := [] }

theorem u7973 : Upper (D 9) (R 9) [96,5,10,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7973 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7974 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 14, targets := 352 }], pairs := [(1,5),(1,6),(1,8),(2,5),(2,6)], upper := (rows 97 7 14 152 145 352 352 480 352), lower := (rows 97 7 14 152 145 32 64 128 256), losses := [] }

theorem u7974 : Upper (D 9) (R 9) [96,5,10,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7974 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7975 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 97 7 14 152 176 353 321 449 321), lower := (rows 97 7 14 152 176 32 64 128 256), losses := [] }

theorem u7975 : Upper (D 9) (R 9) [96,5,10,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7975 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7976 : Route 9 := (fun mask => (mask,id))

def c7976 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7976 : Upper (D 9) (R 9) [96,5,10,144,257] 13 := by
  apply FastRouting.sound _ _ [96,5,10,144,257] 13 (by decide) (choices 1) [64,128,256] r7976 c7976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5364
  · exact u5365
  · exact u5366

def r7977 : Route 9 := (fun mask => (mask,id))

def c7977 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7977 : Upper (D 9) (R 9) [96,5,10,144,288] 13 := by
  apply FastRouting.sound _ _ [96,5,10,144,288] 13 (by decide) (choices 1) [1,64,128,256] r7977 c7977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5367
  · exact u5368
  · exact u5369
  · exact u5370

def b7978 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 97 7 14 152 400 353 353 481 353), lower := (rows 97 7 14 152 400 32 64 128 256), losses := [] }

theorem u7978 : Upper (D 9) (R 9) [96,5,10,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7978 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7979 : PairBound 9 := { available := 400, camps := [{ cop := 4, region := 430, targets := 64 },{ cop := 0, region := 16, targets := 384 }], pairs := [(1,6),(2,6),(3,6),(4,7),(4,8)], upper := (rows 97 7 14 168 81 432 464 400 400), lower := (rows 97 7 14 168 81 32 64 128 256), losses := [] }

theorem u7979 : Upper (D 9) (R 9) [96,5,10,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7979 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u7979
end Delivery.IrregularNine14.P09
