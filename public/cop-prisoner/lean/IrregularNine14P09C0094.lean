import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0036
import IrregularNine14P09C0037

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5640 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 468, targets := 33 },{ cop := 4, region := 33, targets := 256 }], pairs := [(0,8),(2,0),(2,5),(4,0),(4,5)], upper := (rows 97 7 140 42 208 33 336 400 272), lower := (rows 97 7 140 42 208 33 64 128 256), losses := [] }

theorem u5640 : Upper (D 9) (R 9) [96,5,136,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5640 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5641 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 7 140 42 208 48 321 385 257), lower := (rows 97 7 140 42 208 48 64 128 256), losses := [] }

theorem u5641 : Upper (D 9) (R 9) [96,5,136,34,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5641 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5642 : Route 9 := (fun mask => (mask,id))

def c5642 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5642 : Upper (D 9) (R 9) [96,5,136,34,192,256] 13 := by
  apply FastRouting.sound _ _ [96,5,136,34,192,256] 13 (by decide) (choices 1) [1,16,256] r5642 c5642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2196
  · exact u2197
  · exact u2198

def r5643 : Route 9 := (fun mask => (mask,id))

def c5643 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5643 : Upper (D 9) (R 9) [96,5,136,34,257,16] 13 := by
  apply FastRouting.sound _ _ [96,5,136,34,257,16] 13 (by decide) (choices 1) [128,256] r5643 c5643
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2199
  · exact u2200

def b5644 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 42 273 96 464 400 400), lower := (rows 97 7 140 42 273 96 64 128 256), losses := [] }

theorem u5644 : Upper (D 9) (R 9) [96,5,136,34,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5644 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5645 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 337, targets := 128 },{ cop := 0, region := 272, targets := 32 }], pairs := [(0,7),(2,5),(3,0),(4,5),(4,7)], upper := (rows 97 7 140 42 273 160 336 464 336), lower := (rows 97 7 140 42 273 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 180 80 144 272), good := (rows 96 46 172 42 496 160 64 160 256) },{ target := 5, region := (rows 1 2 12 8 19 0 91 155 283), good := (rows 465 471 460 478 465 128 64 128 256) }] }

theorem u5645 : Upper (D 9) (R 9) [96,5,136,34,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5645 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5646 : Route 9 := (fun mask => (mask,id))

def c5646 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5646 : Upper (D 9) (R 9) [96,5,136,34,257,256] 13 := by
  apply FastRouting.sound _ _ [96,5,136,34,257,256] 13 (by decide) (choices 1) [16,128] r5646 c5646
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2201
  · exact u2202

def b5647 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 468, targets := 33 },{ cop := 1, region := 40, targets := 64 }], pairs := [(2,0),(2,5),(3,6),(4,0),(4,5)], upper := (rows 97 7 140 42 336 33 464 400 400), lower := (rows 97 7 140 42 336 33 64 128 256), losses := [] }

theorem u5647 : Upper (D 9) (R 9) [96,5,136,34,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5647 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5648 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 7 140 42 336 48 449 385 385), lower := (rows 97 7 140 42 336 48 64 128 256), losses := [] }

theorem u5648 : Upper (D 9) (R 9) [96,5,136,34,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5648 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5649 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 337, targets := 128 },{ cop := 0, region := 272, targets := 32 }], pairs := [(0,7),(2,5),(3,0),(4,5),(4,7)], upper := (rows 97 7 140 42 336 160 337 401 273), lower := (rows 97 7 140 42 336 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 164 64 128 256), good := (rows 96 46 172 42 336 160 64 160 256) },{ target := 5, region := (rows 1 2 12 8 27 0 67 131 259), good := (rows 465 471 156 478 336 128 64 128 256) }] }

theorem u5649 : Upper (D 9) (R 9) [96,5,136,34,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5649 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5650 : Route 9 := (fun mask => (mask,id))

def c5650 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5650 : Upper (D 9) (R 9) [96,5,136,34,320,256] 13 := by
  apply FastRouting.sound _ _ [96,5,136,34,320,256] 13 (by decide) (choices 1) [1,16,128] r5650 c5650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2203
  · exact u2204
  · exact u2205

def b5651 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 468, targets := 33 },{ cop := 1, region := 40, targets := 64 }], pairs := [(2,0),(2,5),(3,6),(4,0),(4,5)], upper := (rows 97 7 140 42 400 33 336 464 336), lower := (rows 97 7 140 42 400 33 64 128 256), losses := [] }

theorem u5651 : Upper (D 9) (R 9) [96,5,136,34,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5651 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5652 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 400, targets := 32 },{ cop := 3, region := 321, targets := 128 }], pairs := [(0,7),(1,7),(2,5),(4,5)], upper := (rows 97 7 140 42 400 48 321 449 321), lower := (rows 97 7 140 42 400 48 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 27 0 67 131 259), good := (rows 465 471 156 478 400 16 64 128 256) },{ target := 7, region := (rows 57 6 4 8 16 48 127 0 319), good := (rows 353 327 335 363 369 369 64 0 256) }] }

theorem u5652 : Upper (D 9) (R 9) [96,5,136,34,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5652 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5653 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 42 400 96 337 401 273), lower := (rows 97 7 140 42 400 96 64 128 256), losses := [] }

theorem u5653 : Upper (D 9) (R 9) [96,5,136,34,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5653 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5654 : Route 9 := (fun mask => (mask,id))

def c5654 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5654 : Upper (D 9) (R 9) [96,5,136,34,384,256] 13 := by
  apply FastRouting.sound _ _ [96,5,136,34,384,256] 13 (by decide) (choices 1) [1,16] r5654 c5654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2206
  · exact u2207

def b5655 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 41, targets := 384 },{ cop := 1, region := 464, targets := 1 }], pairs := [(0,7),(0,8),(3,7),(3,8),(4,0)], upper := (rows 97 7 140 56 82 33 448 384 384), lower := (rows 97 7 140 56 82 33 64 128 256), losses := [] }

theorem u5655 : Upper (D 9) (R 9) [96,5,136,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5655 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5656 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 336, targets := 32 },{ cop := 1, region := 336, targets := 128 },{ cop := 3, region := 321, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,5),(4,7)], upper := (rows 97 7 140 56 82 160 321 385 257), lower := (rows 97 7 140 56 82 160 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 24 16 183 0 131 259), good := (rows 417 423 172 60 446 160 0 160 256) }] }

theorem u5656 : Upper (D 9) (R 9) [96,5,136,48,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5656 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5657 : Route 9 := (fun mask => (mask,id))

def c5657 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5657 : Upper (D 9) (R 9) [96,5,136,48,66,256] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48,66,256] 13 (by decide) (choices 1) [1,128,256] r5657 c5657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2208
  · exact u2209
  · exact u2210

def b5658 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 46, targets := 320 }], pairs := [(1,6),(1,8),(2,6),(2,8)], upper := (rows 97 7 140 56 145 34 320 448 320), lower := (rows 97 7 140 56 145 34 64 128 256), losses := [] }

theorem u5658 : Upper (D 9) (R 9) [96,5,136,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5658 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5659 : PairBound 9 := { available := 258, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 56 145 96 322 386 258), lower := (rows 97 7 140 56 145 96 64 128 256), losses := [] }

theorem u5659 : Upper (D 9) (R 9) [96,5,136,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5659 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5660 : Route 9 := (fun mask => (mask,id))

def c5660 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5660 : Upper (D 9) (R 9) [96,5,136,48,129,256] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48,129,256] 13 (by decide) (choices 1) [2,256] r5660 c5660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2211
  · exact u2212

def b5661 : PairBound 9 := { available := 320, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 452, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,0),(4,5)], upper := (rows 97 7 140 56 146 33 320 448 320), lower := (rows 97 7 140 56 146 33 64 128 256), losses := [] }

theorem u5661 : Upper (D 9) (R 9) [96,5,136,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5661 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5662 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 56 146 96 321 385 257), lower := (rows 97 7 140 56 146 96 64 128 256), losses := [] }

theorem u5662 : Upper (D 9) (R 9) [96,5,136,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5662 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5663 : Route 9 := (fun mask => (mask,id))

def c5663 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5663 : Upper (D 9) (R 9) [96,5,136,48,130,256] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48,130,256] 13 (by decide) (choices 1) [1,256] r5663 c5663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2213
  · exact u2214

def b5664 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 1, region := 464, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 97 7 140 56 208 33 322 386 258), lower := (rows 97 7 140 56 208 33 64 128 256), losses := [] }

theorem u5664 : Upper (D 9) (R 9) [96,5,136,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5664 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5665 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 7 140 56 208 34 321 385 257), lower := (rows 97 7 140 56 208 34 64 128 256), losses := [] }

theorem u5665 : Upper (D 9) (R 9) [96,5,136,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5665 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5666 : Route 9 := (fun mask => (mask,id))

def c5666 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5666 : Upper (D 9) (R 9) [96,5,136,48,192,256] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48,192,256] 13 (by decide) (choices 1) [1,2,256] r5666 c5666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2215
  · exact u2216
  · exact u2217

def r5667 : Route 9 := (fun mask => (mask,id))

def c5667 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5667 : Upper (D 9) (R 9) [96,5,136,48,257,2] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48,257,2] 13 (by decide) (choices 1) [128,256] r5667 c5667
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2218
  · exact u2219

def b5668 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 56 273 96 450 386 386), lower := (rows 97 7 140 56 273 96 64 128 256), losses := [] }

theorem u5668 : Upper (D 9) (R 9) [96,5,136,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5668 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5669 : Route 9 := (fun mask => (mask,id))

def c5669 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5669 : Upper (D 9) (R 9) [96,5,136,48,257,128] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48,257,128] 13 (by decide) (choices 1) [2,256] r5669 c5669
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2220
  · exact u2221

def b5670 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 65 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,6)], upper := (rows 97 7 140 56 273 288 194 194 450), lower := (rows 97 7 140 56 273 288 64 128 256), losses := [] }

theorem u5670 : Upper (D 9) (R 9) [96,5,136,48,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5670 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5671 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 3, region := 452, targets := 33 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(4,0),(4,5)], upper := (rows 97 7 140 56 274 33 448 448 448), lower := (rows 97 7 140 56 274 33 64 128 256), losses := [] }

theorem u5671 : Upper (D 9) (R 9) [96,5,136,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5671 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5672 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 56 274 96 449 385 385), lower := (rows 97 7 140 56 274 96 64 128 256), losses := [] }

theorem u5672 : Upper (D 9) (R 9) [96,5,136,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5672 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5673 : Route 9 := (fun mask => (mask,id))

def c5673 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5673 : Upper (D 9) (R 9) [96,5,136,48,258,128] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48,258,128] 13 (by decide) (choices 1) [1,256] r5673 c5673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2222
  · exact u2223

def b5674 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 65 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,6)], upper := (rows 97 7 140 56 274 288 193 193 449), lower := (rows 97 7 140 56 274 288 64 128 256), losses := [] }

theorem u5674 : Upper (D 9) (R 9) [96,5,136,48,258,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5674 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5675 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 41, targets := 384 },{ cop := 1, region := 464, targets := 1 }], pairs := [(0,7),(0,8),(3,7),(3,8),(4,0)], upper := (rows 97 7 140 56 336 33 450 386 386), lower := (rows 97 7 140 56 336 33 64 128 256), losses := [] }

theorem u5675 : Upper (D 9) (R 9) [96,5,136,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5675 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5676 : Route 9 := (fun mask => (mask,id))

def c5676 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5676 : Upper (D 9) (R 9) [96,5,136,48,320,2] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48,320,2] 13 (by decide) (choices 1) [1,128,256] r5676 c5676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2224
  · exact u2225
  · exact u2226

def r5677 : Route 9 := (fun mask => (mask,id))

def c5677 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5677 : Upper (D 9) (R 9) [96,5,136,48,320,128] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48,320,128] 13 (by decide) (choices 1) [1,2,256] r5677 c5677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2227
  · exact u2228
  · exact u2229

def b5678 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 65 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,6)], upper := (rows 97 7 140 56 336 288 195 131 387), lower := (rows 97 7 140 56 336 288 64 128 256), losses := [] }

theorem u5678 : Upper (D 9) (R 9) [96,5,136,48,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5678 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5679 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 2, region := 355, targets := 128 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(4,0),(4,5)], upper := (rows 97 7 140 56 400 33 322 450 322), lower := (rows 97 7 140 56 400 33 64 128 256), losses := [] }

theorem u5679 : Upper (D 9) (R 9) [96,5,136,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5679 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5680 : Route 9 := (fun mask => (mask,id))

def c5680 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5680 : Upper (D 9) (R 9) [96,5,136,48,384,2] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48,384,2] 13 (by decide) (choices 1) [1,256] r5680 c5680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2230
  · exact u2231

def b5681 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 56 400 96 323 387 259), lower := (rows 97 7 140 56 400 96 64 128 256), losses := [] }

theorem u5681 : Upper (D 9) (R 9) [96,5,136,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5681 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5682 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 44, targets := 65 },{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8),(2,0),(2,6),(3,0),(3,6)], upper := (rows 97 7 140 56 400 288 67 195 323), lower := (rows 97 7 140 56 400 288 64 128 256), losses := [] }

theorem u5682 : Upper (D 9) (R 9) [96,5,136,48,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5682 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5683 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 1, region := 48, targets := 64 }], pairs := [(1,5),(2,5),(3,5),(4,6)], upper := (rows 97 7 140 265 50 48 448 448 448), lower := (rows 97 7 140 265 50 48 64 128 256), losses := [] }

theorem u5683 : Upper (D 9) (R 9) [96,5,136,257,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5683 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5684 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 265 50 96 464 400 400), lower := (rows 97 7 140 265 50 96 64 128 256), losses := [] }

theorem u5684 : Upper (D 9) (R 9) [96,5,136,257,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5684 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5685 : PairBound 9 := { available := 336, camps := [{ cop := 4, region := 329, targets := 128 },{ cop := 1, region := 496, targets := 1 }], pairs := [(0,7),(3,7),(4,0),(4,6),(4,8)], upper := (rows 97 7 140 265 50 160 336 464 336), lower := (rows 97 7 140 265 50 160 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 8 18 164 0 128 256), good := (rows 33 55 172 265 50 160 0 160 256) },{ target := 8, region := (rows 1 2 4 8 18 164 64 128 0), good := (rows 97 55 172 9 50 160 64 160 0) }] }

theorem u5685 : Upper (D 9) (R 9) [96,5,136,257,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5685 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5686 : Route 9 := (fun mask => (mask,id))

def c5686 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5686 : Upper (D 9) (R 9) [96,5,136,257,34,256] 13 := by
  apply FastRouting.sound _ _ [96,5,136,257,34,256] 13 (by decide) (choices 1) [16,128] r5686 c5686
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2232
  · exact u2233

def b5687 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 361, targets := 128 },{ cop := 1, region := 496, targets := 1 }], pairs := [(0,7),(2,0),(3,7),(4,0)], upper := (rows 97 7 140 265 146 48 352 480 352), lower := (rows 97 7 140 265 146 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 18 50 115 179 307), good := (rows 480 502 140 460 498 496 64 128 256) }] }

theorem u5687 : Upper (D 9) (R 9) [96,5,136,257,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5687 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5688 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 265 146 96 368 432 304), lower := (rows 97 7 140 265 146 96 64 128 256), losses := [] }

theorem u5688 : Upper (D 9) (R 9) [96,5,136,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5688 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m5689_16 : Upper (D 9) (R 9) [96,5,136,257,130,256,16] 13 :=
  permutation_upper _ _ _ [96,5,136,257,130,16,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2234

theorem m5689_32 : Upper (D 9) (R 9) [96,5,136,257,130,256,32] 13 :=
  permutation_upper _ _ _ [96,5,136,257,130,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2235

def r5689 : Route 9 := (fun mask => (mask,id))

def c5689 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5689 : Upper (D 9) (R 9) [96,5,136,257,130,256] 13 := by
  apply FastRouting.sound _ _ [96,5,136,257,130,256] 13 (by decide) (choices 1) [16,32] r5689 c5689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m5689_16
  · exact m5689_32

def b5690 : PairBound 9 := { available := 336, camps := [{ cop := 4, region := 329, targets := 128 },{ cop := 0, region := 400, targets := 1 }], pairs := [(0,7),(2,0),(3,7),(4,0)], upper := (rows 97 7 140 265 176 34 336 464 336), lower := (rows 97 7 140 265 176 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 51 34 123 187 315), good := (rows 496 502 460 476 496 498 64 128 256) }] }

theorem u5690 : Upper (D 9) (R 9) [96,5,136,257,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5690 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5691 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 2, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 97 7 140 265 176 48 322 450 322), lower := (rows 97 7 140 265 176 48 64 128 256), losses := [] }

theorem u5691 : Upper (D 9) (R 9) [96,5,136,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5691 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5692 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 265 176 96 338 402 274), lower := (rows 97 7 140 265 176 96 64 128 256), losses := [] }

theorem u5692 : Upper (D 9) (R 9) [96,5,136,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5692 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5693 : Route 9 := (fun mask => (mask,id))

def c5693 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5693 : Upper (D 9) (R 9) [96,5,136,257,160,256] 13 := by
  apply FastRouting.sound _ _ [96,5,136,257,160,256] 13 (by decide) (choices 1) [2,16] r5693 c5693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2236
  · exact u2237

def b5694 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 496, targets := 1 },{ cop := 4, region := 225, targets := 256 }], pairs := [(0,8),(1,8),(2,0),(4,0)], upper := (rows 97 7 140 265 274 48 224 224 480), lower := (rows 97 7 140 265 274 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 18 50 115 179 307), good := (rows 480 502 140 460 498 496 64 128 256) },{ target := 8, region := (rows 49 10 12 8 16 48 113 177 0), good := (rows 225 199 142 207 243 241 64 128 0) }] }

theorem u5694 : Upper (D 9) (R 9) [96,5,136,257,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5694 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5695 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 265 274 96 240 176 432), lower := (rows 97 7 140 265 274 96 64 128 256), losses := [] }

theorem u5695 : Upper (D 9) (R 9) [96,5,136,257,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5695 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m5696_16 : Upper (D 9) (R 9) [96,5,136,257,258,128,16] 13 :=
  permutation_upper _ _ _ [96,5,136,257,258,16,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2238

theorem m5696_32 : Upper (D 9) (R 9) [96,5,136,257,258,128,32] 13 :=
  permutation_upper _ _ _ [96,5,136,257,258,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2239

def r5696 : Route 9 := (fun mask => (mask,id))

def c5696 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5696 : Upper (D 9) (R 9) [96,5,136,257,258,128] 13 := by
  apply FastRouting.sound _ _ [96,5,136,257,258,128] 13 (by decide) (choices 1) [16,32] r5696 c5696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m5696_16
  · exact m5696_32

def r5697 : Route 9 := (fun mask => (mask,id))

def c5697 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5697 : Upper (D 9) (R 9) [96,5,136,257,288,2] 13 := by
  apply FastRouting.sound _ _ [96,5,136,257,288,2] 13 (by decide) (choices 1) [16,128] r5697 c5697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2240
  · exact u2241

def b5698 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 97 7 140 265 304 48 194 194 450), lower := (rows 97 7 140 265 304 48 64 128 256), losses := [] }

theorem u5698 : Upper (D 9) (R 9) [96,5,136,257,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5698 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5699 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 265 304 96 210 146 402), lower := (rows 97 7 140 265 304 96 64 128 256), losses := [] }

theorem u5699 : Upper (D 9) (R 9) [96,5,136,257,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5699 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u5699
end Delivery.IrregularNine14.P09
