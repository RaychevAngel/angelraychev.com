import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0042

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6120 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 152 273 96 354 418 290), lower := (rows 97 14 133 152 273 96 64 128 256), losses := [] }

theorem u6120 : Upper (D 9) (R 9) [96,12,129,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6120 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m6121_2 : Upper (D 9) (R 9) [96,12,129,144,257,256,2] 13 :=
  permutation_upper _ _ _ [96,12,129,144,257,2,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2540

theorem m6121_32 : Upper (D 9) (R 9) [96,12,129,144,257,256,32] 13 :=
  permutation_upper _ _ _ [96,12,129,144,257,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2541

def r6121 : Route 9 := (fun mask => (mask,id))

def c6121 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6121 : Upper (D 9) (R 9) [96,12,129,144,257,256] 13 := by
  apply FastRouting.sound _ _ [96,12,129,144,257,256] 13 (by decide) (choices 1) [2,32] r6121 c6121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m6121_2
  · exact m6121_32

def b6122 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,0),(3,0),(4,7)], upper := (rows 97 14 133 152 274 33 352 480 352), lower := (rows 97 14 133 152 274 33 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 20 32 97 161 289), good := (rows 480 30 478 152 274 480 64 128 256) }] }

theorem u6122 : Upper (D 9) (R 9) [96,12,129,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6122 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6123 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 152 274 96 353 417 289), lower := (rows 97 14 133 152 274 96 64 128 256), losses := [] }

theorem u6123 : Upper (D 9) (R 9) [96,12,129,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6123 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m6124_1 : Upper (D 9) (R 9) [96,12,129,144,258,256,1] 13 :=
  permutation_upper _ _ _ [96,12,129,144,258,1,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2542

theorem m6124_32 : Upper (D 9) (R 9) [96,12,129,144,258,256,32] 13 :=
  permutation_upper _ _ _ [96,12,129,144,258,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2543

def r6124 : Route 9 := (fun mask => (mask,id))

def c6124 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6124 : Upper (D 9) (R 9) [96,12,129,144,258,256] 13 := by
  apply FastRouting.sound _ _ [96,12,129,144,258,256] 13 (by decide) (choices 1) [1,32] r6124 c6124
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m6124_1
  · exact m6124_32

def r6125 : Route 9 := (fun mask => (mask,id))

def c6125 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6125 : Upper (D 9) (R 9) [96,12,129,144,288,1] 13 := by
  apply FastRouting.sound _ _ [96,12,129,144,288,1] 13 (by decide) (choices 1) [2,256] r6125 c6125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2544
  · exact u2545

def r6126 : Route 9 := (fun mask => (mask,id))

def c6126 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6126 : Upper (D 9) (R 9) [96,12,129,144,288,2] 13 := by
  apply FastRouting.sound _ _ [96,12,129,144,288,2] 13 (by decide) (choices 1) [1,256] r6126 c6126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2546
  · exact u2547

def b6127 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 152 304 96 323 387 259), lower := (rows 97 14 133 152 304 96 64 128 256), losses := [] }

theorem u6127 : Upper (D 9) (R 9) [96,12,129,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6127 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6128 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 97 14 133 152 304 288 67 195 323), lower := (rows 97 14 133 152 304 288 64 128 256), losses := [] }

theorem u6128 : Upper (D 9) (R 9) [96,12,129,144,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6128 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6129 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 42, targets := 320 },{ cop := 1, region := 336, targets := 1 }], pairs := [(1,6),(1,8),(3,6),(3,8),(4,0)], upper := (rows 97 14 133 168 82 33 336 400 272), lower := (rows 97 14 133 168 82 33 64 128 256), losses := [] }

theorem u6129 : Upper (D 9) (R 9) [96,12,129,160,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6129 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6130 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 14 133 168 82 48 321 385 257), lower := (rows 97 14 133 168 82 48 64 128 256), losses := [] }

theorem u6130 : Upper (D 9) (R 9) [96,12,129,160,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6130 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6131 : Route 9 := (fun mask => (mask,id))

def c6131 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6131 : Upper (D 9) (R 9) [96,12,129,160,66,256] 13 := by
  apply FastRouting.sound _ _ [96,12,129,160,66,256] 13 (by decide) (choices 1) [1,16,256] r6131 c6131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2548
  · exact u2549
  · exact u2550

def b6132 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 42, targets := 321 }], pairs := [(1,0),(1,6),(1,8),(3,0)], upper := (rows 97 14 133 168 273 34 336 464 336), lower := (rows 97 14 133 168 273 34 64 128 256), losses := [] }

theorem u6132 : Upper (D 9) (R 9) [96,12,129,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6132 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6133 : Route 9 := (fun mask => (mask,id))

def c6133 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6133 : Upper (D 9) (R 9) [96,12,129,160,257,16] 13 := by
  apply FastRouting.sound _ _ [96,12,129,160,257,16] 13 (by decide) (choices 1) [2,256] r6133 c6133
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2551
  · exact u2552

def b6134 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 168 273 96 338 402 274), lower := (rows 97 14 133 168 273 96 64 128 256), losses := [] }

theorem u6134 : Upper (D 9) (R 9) [96,12,129,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6134 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6135 : Route 9 := (fun mask => (mask,id))

def c6135 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6135 : Upper (D 9) (R 9) [96,12,129,160,257,256] 13 := by
  apply FastRouting.sound _ _ [96,12,129,160,257,256] 13 (by decide) (choices 1) [2,16] r6135 c6135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2553
  · exact u2554

def b6136 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 42, targets := 320 },{ cop := 1, region := 336, targets := 1 }], pairs := [(1,6),(1,8),(3,6),(3,8),(4,0)], upper := (rows 97 14 133 168 274 33 336 464 336), lower := (rows 97 14 133 168 274 33 64 128 256), losses := [] }

theorem u6136 : Upper (D 9) (R 9) [96,12,129,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6136 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6137 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 0, region := 388, targets := 32 }], pairs := [(0,7),(2,5),(4,5),(4,7)], upper := (rows 97 14 133 168 274 48 321 449 321), lower := (rows 97 14 133 168 274 48 64 128 256), losses := [{ target := 5, region := (rows 1 2 5 8 18 0 69 133 261), good := (rows 453 478 453 136 274 16 64 128 256) }] }

theorem u6137 : Upper (D 9) (R 9) [96,12,129,160,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6137 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6138 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 168 274 96 337 401 273), lower := (rows 97 14 133 168 274 96 64 128 256), losses := [] }

theorem u6138 : Upper (D 9) (R 9) [96,12,129,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6138 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6139 : Route 9 := (fun mask => (mask,id))

def c6139 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6139 : Upper (D 9) (R 9) [96,12,129,160,258,256] 13 := by
  apply FastRouting.sound _ _ [96,12,129,160,258,256] 13 (by decide) (choices 1) [1,16] r6139 c6139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2555
  · exact u2556

def b6140 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 42, targets := 320 },{ cop := 1, region := 336, targets := 1 }], pairs := [(1,6),(1,8),(3,6),(3,8),(4,0)], upper := (rows 97 14 133 168 336 33 338 402 274), lower := (rows 97 14 133 168 336 33 64 128 256), losses := [] }

theorem u6140 : Upper (D 9) (R 9) [96,12,129,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6140 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6141 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 42, targets := 321 }], pairs := [(1,0),(1,6),(1,8),(3,0)], upper := (rows 97 14 133 168 336 34 337 401 273), lower := (rows 97 14 133 168 336 34 64 128 256), losses := [] }

theorem u6141 : Upper (D 9) (R 9) [96,12,129,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6141 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6142 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 14 133 168 336 48 323 387 259), lower := (rows 97 14 133 168 336 48 64 128 256), losses := [] }

theorem u6142 : Upper (D 9) (R 9) [96,12,129,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6142 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6143 : Route 9 := (fun mask => (mask,id))

def c6143 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6143 : Upper (D 9) (R 9) [96,12,129,160,320,256] 13 := by
  apply FastRouting.sound _ _ [96,12,129,160,320,256] 13 (by decide) (choices 1) [1,2,16] r6143 c6143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2557
  · exact u2558
  · exact u2559

def b6144 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 1, region := 48, targets := 64 }], pairs := [(1,5),(2,5),(3,5),(4,6)], upper := (rows 97 14 133 265 50 48 448 448 448), lower := (rows 97 14 133 265 50 48 64 128 256), losses := [] }

theorem u6144 : Upper (D 9) (R 9) [96,12,129,257,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6144 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6145 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 265 50 96 464 400 400), lower := (rows 97 14 133 265 50 96 64 128 256), losses := [] }

theorem u6145 : Upper (D 9) (R 9) [96,12,129,257,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6145 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6146 : PairBound 9 := { available := 336, camps := [{ cop := 4, region := 329, targets := 128 },{ cop := 1, region := 496, targets := 1 }], pairs := [(0,7),(3,7),(4,0),(4,6),(4,8)], upper := (rows 97 14 133 265 50 160 336 464 336), lower := (rows 97 14 133 265 50 160 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 8 18 164 0 128 256), good := (rows 33 62 165 265 50 160 0 160 256) },{ target := 8, region := (rows 1 2 4 8 18 164 64 128 0), good := (rows 97 62 165 9 50 160 64 160 0) }] }

theorem u6146 : Upper (D 9) (R 9) [96,12,129,257,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6146 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6147 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 361, targets := 128 },{ cop := 1, region := 496, targets := 1 }], pairs := [(0,7),(1,7),(3,7),(4,0)], upper := (rows 97 14 133 265 146 48 352 480 352), lower := (rows 97 14 133 265 146 48 64 128 256), losses := [{ target := 7, region := (rows 49 6 4 61 16 48 113 0 305), good := (rows 361 14 335 329 379 377 64 0 256) }] }

theorem u6147 : Upper (D 9) (R 9) [96,12,129,257,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6147 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6148 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 265 146 96 368 432 304), lower := (rows 97 14 133 265 146 96 64 128 256), losses := [] }

theorem u6148 : Upper (D 9) (R 9) [96,12,129,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6148 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m6149_16 : Upper (D 9) (R 9) [96,12,129,257,130,256,16] 13 :=
  permutation_upper _ _ _ [96,12,129,257,130,16,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2560

theorem m6149_32 : Upper (D 9) (R 9) [96,12,129,257,130,256,32] 13 :=
  permutation_upper _ _ _ [96,12,129,257,130,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2561

def r6149 : Route 9 := (fun mask => (mask,id))

def c6149 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6149 : Upper (D 9) (R 9) [96,12,129,257,130,256] 13 := by
  apply FastRouting.sound _ _ [96,12,129,257,130,256] 13 (by decide) (choices 1) [16,32] r6149 c6149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m6149_16
  · exact m6149_32

def r6150 : Route 9 := (fun mask => (mask,id))

def c6150 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6150 : Upper (D 9) (R 9) [96,12,129,257,160,2] 13 := by
  apply FastRouting.sound _ _ [96,12,129,257,160,2] 13 (by decide) (choices 1) [16,256] r6150 c6150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2562
  · exact u2563

def b6151 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 2, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 97 14 133 265 176 48 322 450 322), lower := (rows 97 14 133 265 176 48 64 128 256), losses := [] }

theorem u6151 : Upper (D 9) (R 9) [96,12,129,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6151 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6152 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 265 176 96 338 402 274), lower := (rows 97 14 133 265 176 96 64 128 256), losses := [] }

theorem u6152 : Upper (D 9) (R 9) [96,12,129,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6152 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6153 : Route 9 := (fun mask => (mask,id))

def c6153 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6153 : Upper (D 9) (R 9) [96,12,129,257,160,256] 13 := by
  apply FastRouting.sound _ _ [96,12,129,257,160,256] 13 (by decide) (choices 1) [2,16] r6153 c6153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2564
  · exact u2565

def r6154 : Route 9 := (fun mask => (mask,id))

def c6154 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6154 : Upper (D 9) (R 9) [96,12,129,257,384,2] 13 := by
  apply FastRouting.sound _ _ [96,12,129,257,384,2] 13 (by decide) (choices 1) [16,32] r6154 c6154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2566
  · exact u2567

theorem m6155_2 : Upper (D 9) (R 9) [96,12,129,257,384,16,2] 13 :=
  permutation_upper _ _ _ [96,12,129,257,384,2,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2566

def r6155 : Route 9 := (fun mask => (mask,id))

def c6155 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6155 : Upper (D 9) (R 9) [96,12,129,257,384,16] 13 := by
  apply FastRouting.sound _ _ [96,12,129,257,384,16] 13 (by decide) (choices 1) [2,32] r6155 c6155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m6155_2
  · exact u2568

def b6156 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 265 400 96 114 178 306), lower := (rows 97 14 133 265 400 96 64 128 256), losses := [] }

theorem u6156 : Upper (D 9) (R 9) [96,12,129,257,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6156 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6157 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 48, targets := 320 },{ cop := 6, region := 33, targets := 384 },{ cop := 0, region := 400, targets := 1 }], pairs := [(0,7),(0,8),(4,0),(4,6),(4,8)], upper := (rows 97 14 133 266 176 33 336 464 336), lower := (rows 97 14 133 266 176 33 64 128 256), losses := [] }

theorem u6157 : Upper (D 9) (R 9) [96,12,129,258,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6157 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6158 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 2, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 97 14 133 266 176 48 321 449 321), lower := (rows 97 14 133 266 176 48 64 128 256), losses := [] }

theorem u6158 : Upper (D 9) (R 9) [96,12,129,258,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6158 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6159 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 266 176 96 337 401 273), lower := (rows 97 14 133 266 176 96 64 128 256), losses := [] }

theorem u6159 : Upper (D 9) (R 9) [96,12,129,258,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6159 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6160 : Route 9 := (fun mask => (mask,id))

def c6160 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6160 : Upper (D 9) (R 9) [96,12,129,258,160,256] 13 := by
  apply FastRouting.sound _ _ [96,12,129,258,160,256] 13 (by decide) (choices 1) [1,16] r6160 c6160
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2569
  · exact u2570

def b6161 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 229, targets := 256 }], pairs := [(0,8),(1,0),(2,8),(3,0)], upper := (rows 97 14 133 266 273 48 224 224 480), lower := (rows 97 14 133 266 273 48 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 16 48 113 177 305), good := (rows 480 14 462 266 496 496 64 128 256) }] }

theorem u6161 : Upper (D 9) (R 9) [96,12,129,258,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6161 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6162 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 225, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 266 273 96 240 176 432), lower := (rows 97 14 133 266 273 96 64 128 256), losses := [] }

theorem u6162 : Upper (D 9) (R 9) [96,12,129,258,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6162 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6163 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 229, targets := 256 },{ cop := 5, region := 337, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(2,8),(4,7)], upper := (rows 97 14 133 266 273 160 112 240 368), lower := (rows 97 14 133 266 273 160 64 128 256), losses := [{ target := 7, region := (rows 33 6 4 12 53 32 97 0 289), good := (rows 369 30 351 266 337 369 64 0 256) }] }

theorem u6163 : Upper (D 9) (R 9) [96,12,129,258,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6163 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6164 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 197, targets := 256 },{ cop := 0, region := 400, targets := 1 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7),(0,8),(1,0),(2,8),(4,0)], upper := (rows 97 14 133 266 304 33 208 208 464), lower := (rows 97 14 133 266 304 33 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 14 49 32 117 181 309), good := (rows 496 462 478 266 496 496 64 128 256) }] }

theorem u6164 : Upper (D 9) (R 9) [96,12,129,258,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6164 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6165 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 97 14 133 266 304 48 193 193 449), lower := (rows 97 14 133 266 304 48 64 128 256), losses := [] }

theorem u6165 : Upper (D 9) (R 9) [96,12,129,258,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6165 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6166 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 193, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 266 304 96 209 145 401), lower := (rows 97 14 133 266 304 96 64 128 256), losses := [] }

theorem u6166 : Upper (D 9) (R 9) [96,12,129,258,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6166 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6167 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 197, targets := 256 },{ cop := 5, region := 337, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(2,8),(4,7)], upper := (rows 97 14 133 266 304 160 81 209 337), lower := (rows 97 14 133 266 304 160 64 128 256), losses := [{ target := 7, region := (rows 49 6 4 14 49 32 117 0 309), good := (rows 369 334 351 266 369 369 64 0 256) }] }

theorem u6167 : Upper (D 9) (R 9) [96,12,129,258,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6167 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6168 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 101, targets := 256 },{ cop := 0, region := 400, targets := 1 },{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7),(0,8),(1,0),(2,8),(4,0)], upper := (rows 97 14 133 266 400 33 112 240 368), lower := (rows 97 14 133 266 400 33 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 53 32 97 161 289), good := (rows 496 30 478 266 400 496 64 128 256) }] }

theorem u6168 : Upper (D 9) (R 9) [96,12,129,258,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6168 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6169 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 101, targets := 256 },{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(2,8)], upper := (rows 97 14 133 266 400 48 97 225 353), lower := (rows 97 14 133 266 400 48 64 128 256), losses := [{ target := 7, region := (rows 49 6 4 12 16 48 113 0 305), good := (rows 353 14 335 266 369 369 64 0 256) }] }

theorem u6169 : Upper (D 9) (R 9) [96,12,129,258,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6169 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6170 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 97, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 266 400 96 113 177 305), lower := (rows 97 14 133 266 400 96 64 128 256), losses := [] }

theorem u6170 : Upper (D 9) (R 9) [96,12,129,258,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6170 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6171 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 456, targets := 33 },{ cop := 6, region := 33, targets := 384 },{ cop := 0, region := 388, targets := 32 }], pairs := [(0,7),(0,8),(2,5),(3,0),(3,5)], upper := (rows 97 14 133 280 50 33 448 448 448), lower := (rows 97 14 133 280 50 33 64 128 256), losses := [] }

theorem u6171 : Upper (D 9) (R 9) [96,12,129,272,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6171 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6172 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 280 50 96 449 385 385), lower := (rows 97 14 133 280 50 96 64 128 256), losses := [] }

theorem u6172 : Upper (D 9) (R 9) [96,12,129,272,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6172 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6173 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 329, targets := 128 },{ cop := 0, region := 388, targets := 32 }], pairs := [(0,7),(2,5),(3,7),(4,0),(4,6)], upper := (rows 97 14 133 280 50 160 321 449 321), lower := (rows 97 14 133 280 50 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 164 64 128 256), good := (rows 96 62 164 280 50 160 64 160 256) },{ target := 6, region := (rows 1 2 4 8 18 164 0 128 256), good := (rows 33 62 165 280 50 160 0 160 256) }] }

theorem u6173 : Upper (D 9) (R 9) [96,12,129,272,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6173 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6174 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 197, targets := 256 },{ cop := 0, region := 132, targets := 32 }], pairs := [(0,8),(2,5),(2,8),(4,0),(4,6)], upper := (rows 97 14 133 280 50 288 193 193 449), lower := (rows 97 14 133 280 50 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 296 64 128 256), good := (rows 96 62 132 312 50 288 64 128 288) },{ target := 6, region := (rows 1 2 4 8 18 296 0 128 256), good := (rows 33 62 133 312 50 288 0 128 288) }] }

theorem u6174 : Upper (D 9) (R 9) [96,12,129,272,34,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6174 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6175 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 361, targets := 128 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,0),(3,0),(3,7)], upper := (rows 97 14 133 280 146 33 352 480 352), lower := (rows 97 14 133 280 146 33 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 20 32 97 161 289), good := (rows 480 30 478 280 146 480 64 128 256) }] }

theorem u6175 : Upper (D 9) (R 9) [96,12,129,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6175 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6176 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 280 146 96 353 417 289), lower := (rows 97 14 133 280 146 96 64 128 256), losses := [] }

theorem u6176 : Upper (D 9) (R 9) [96,12,129,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6176 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m6177_1 : Upper (D 9) (R 9) [96,12,129,272,130,256,1] 13 :=
  permutation_upper _ _ _ [96,12,129,272,130,1,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2571

theorem m6177_32 : Upper (D 9) (R 9) [96,12,129,272,130,256,32] 13 :=
  permutation_upper _ _ _ [96,12,129,272,130,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2572

def r6177 : Route 9 := (fun mask => (mask,id))

def c6177 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6177 : Upper (D 9) (R 9) [96,12,129,272,130,256] 13 := by
  apply FastRouting.sound _ _ [96,12,129,272,130,256] 13 (by decide) (choices 1) [1,32] r6177 c6177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m6177_1
  · exact m6177_32

def r6178 : Route 9 := (fun mask => (mask,id))

def c6178 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6178 : Upper (D 9) (R 9) [96,12,129,272,160,1] 13 := by
  apply FastRouting.sound _ _ [96,12,129,272,160,1] 13 (by decide) (choices 1) [2,256] r6178 c6178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2573
  · exact u2574

def r6179 : Route 9 := (fun mask => (mask,id))

def c6179 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6179 : Upper (D 9) (R 9) [96,12,129,272,160,2] 13 := by
  apply FastRouting.sound _ _ [96,12,129,272,160,2] 13 (by decide) (choices 1) [1,256] r6179 c6179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2575
  · exact u2576

#print axioms u6179
end Delivery.IrregularNine14.P09
