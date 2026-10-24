import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0042
import IrregularNine14P09C0043

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6180 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 280 176 96 323 387 259), lower := (rows 97 14 133 280 176 96 64 128 256), losses := [] }

theorem u6180 : Upper (D 9) (R 9) [96,12,129,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6180 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6181 : Route 9 := (fun mask => (mask,id))

def c6181 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6181 : Upper (D 9) (R 9) [96,12,129,272,160,256] 13 := by
  apply FastRouting.sound _ _ [96,12,129,272,160,256] 13 (by decide) (choices 1) [1,2] r6181 c6181
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2577
  · exact u2578

def r6182 : Route 9 := (fun mask => (mask,id))

def c6182 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u6182 : Upper (D 9) (R 9) [96,12,129,288,66,1] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288,66,1] 13 (by decide) (choices 1) [16,128,256] r6182 c6182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2579
  · exact u2580
  · exact u2581

def b6183 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 14 133 296 82 48 449 385 385), lower := (rows 97 14 133 296 82 48 64 128 256), losses := [] }

theorem u6183 : Upper (D 9) (R 9) [96,12,129,288,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6183 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6184 : Route 9 := (fun mask => (mask,id))

def c6184 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6184 : Upper (D 9) (R 9) [96,12,129,288,66,128] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288,66,128] 13 (by decide) (choices 1) [1,16,256] r6184 c6184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2582
  · exact u2583
  · exact u2584

def b6185 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 215, targets := 256 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 97 14 133 296 82 288 209 145 401), lower := (rows 97 14 133 296 82 288 64 128 256), losses := [] }

theorem u6185 : Upper (D 9) (R 9) [96,12,129,288,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6185 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6186 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 4, region := 361, targets := 128 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(3,7),(4,0),(4,5)], upper := (rows 97 14 133 296 146 33 336 464 336), lower := (rows 97 14 133 296 146 33 64 128 256), losses := [] }

theorem u6186 : Upper (D 9) (R 9) [96,12,129,288,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6186 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6187 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 361, targets := 128 },{ cop := 0, region := 388, targets := 32 }], pairs := [(0,7),(2,5),(3,7),(4,5)], upper := (rows 97 14 133 296 146 48 321 449 321), lower := (rows 97 14 133 296 146 48 64 128 256), losses := [{ target := 5, region := (rows 1 2 5 8 18 0 69 133 261), good := (rows 453 478 453 264 146 16 64 128 256) }] }

theorem u6187 : Upper (D 9) (R 9) [96,12,129,288,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6187 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6188 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 296 146 96 337 401 273), lower := (rows 97 14 133 296 146 96 64 128 256), losses := [] }

theorem u6188 : Upper (D 9) (R 9) [96,12,129,288,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6188 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6189 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 215, targets := 256 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 97 14 133 296 146 288 81 209 337), lower := (rows 97 14 133 296 146 288 64 128 256), losses := [] }

theorem u6189 : Upper (D 9) (R 9) [96,12,129,288,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6189 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6190 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 4, region := 37, targets := 256 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(0,8),(2,8),(4,0),(4,5)], upper := (rows 97 14 133 296 208 33 338 402 274), lower := (rows 97 14 133 296 208 33 64 128 256), losses := [] }

theorem u6190 : Upper (D 9) (R 9) [96,12,129,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6190 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6191 : Route 9 := (fun mask => (mask,id))

def c6191 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6191 : Upper (D 9) (R 9) [96,12,129,288,192,2] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288,192,2] 13 (by decide) (choices 1) [1,16,256] r6191 c6191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2585
  · exact u2586
  · exact u2587

def b6192 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 4, region := 33, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6)], upper := (rows 97 14 133 296 208 48 323 387 259), lower := (rows 97 14 133 296 208 48 64 128 256), losses := [] }

theorem u6192 : Upper (D 9) (R 9) [96,12,129,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6192 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6193 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 215, targets := 256 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 97 14 133 296 208 288 83 147 275), lower := (rows 97 14 133 296 208 288 64 128 256), losses := [] }

theorem u6193 : Upper (D 9) (R 9) [96,12,129,288,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6193 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6194 : Route 9 := (fun mask => (mask,id))

def c6194 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6194 : Upper (D 9) (R 9) [96,12,129,288,257,2] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288,257,2] 13 (by decide) (choices 1) [16,128] r6194 c6194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2588
  · exact u2589

def b6195 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 97 14 133 296 273 48 194 194 450), lower := (rows 97 14 133 296 273 48 64 128 256), losses := [] }

theorem u6195 : Upper (D 9) (R 9) [96,12,129,288,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6195 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6196 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 296 273 96 210 146 402), lower := (rows 97 14 133 296 273 96 64 128 256), losses := [] }

theorem u6196 : Upper (D 9) (R 9) [96,12,129,288,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6196 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6197 : Route 9 := (fun mask => (mask,id))

def c6197 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6197 : Upper (D 9) (R 9) [96,12,129,288,257,128] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288,257,128] 13 (by decide) (choices 1) [2,16] r6197 c6197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2590
  · exact u2591

def b6198 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 4, region := 229, targets := 256 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7),(0,8),(2,8),(4,0),(4,5)], upper := (rows 97 14 133 296 274 33 208 208 464), lower := (rows 97 14 133 296 274 33 64 128 256), losses := [] }

theorem u6198 : Upper (D 9) (R 9) [96,12,129,288,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6198 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6199 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 97 14 133 296 274 48 193 193 449), lower := (rows 97 14 133 296 274 48 64 128 256), losses := [] }

theorem u6199 : Upper (D 9) (R 9) [96,12,129,288,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6199 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6200 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 225, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 296 274 96 209 145 401), lower := (rows 97 14 133 296 274 96 64 128 256), losses := [] }

theorem u6200 : Upper (D 9) (R 9) [96,12,129,288,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6200 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6201 : Route 9 := (fun mask => (mask,id))

def c6201 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6201 : Upper (D 9) (R 9) [96,12,129,288,258,128] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288,258,128] 13 (by decide) (choices 1) [1,16] r6201 c6201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2592
  · exact u2593

def b6202 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 4, region := 41, targets := 128 },{ cop := 4, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(3,7),(4,0),(4,5)], upper := (rows 97 14 133 296 336 33 210 146 402), lower := (rows 97 14 133 296 336 33 64 128 256), losses := [] }

theorem u6202 : Upper (D 9) (R 9) [96,12,129,288,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6202 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6203 : Route 9 := (fun mask => (mask,id))

def c6203 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6203 : Upper (D 9) (R 9) [96,12,129,288,320,2] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288,320,2] 13 (by decide) (choices 1) [1,16,128] r6203 c6203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2594
  · exact u2595
  · exact u2596

def b6204 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6)], upper := (rows 97 14 133 296 336 48 195 131 387), lower := (rows 97 14 133 296 336 48 64 128 256), losses := [] }

theorem u6204 : Upper (D 9) (R 9) [96,12,129,288,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6204 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6205 : Route 9 := (fun mask => (mask,id))

def c6205 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6205 : Upper (D 9) (R 9) [96,12,129,288,320,128] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288,320,128] 13 (by decide) (choices 1) [1,2,16] r6205 c6205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2597
  · exact u2598
  · exact u2599

def r6206 : Route 9 := (fun mask => (mask,id))

def c6206 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6206 : Upper (D 9) (R 9) [96,12,129,288,384,1] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288,384,1] 13 (by decide) (choices 1) [2,16] r6206 c6206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2600
  · exact u2601

def r6207 : Route 9 := (fun mask => (mask,id))

def c6207 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6207 : Upper (D 9) (R 9) [96,12,129,288,384,2] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288,384,2] 13 (by decide) (choices 1) [1,16] r6207 c6207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2602
  · exact u2603

def b6208 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 97 14 133 296 400 48 67 195 323), lower := (rows 97 14 133 296 400 48 64 128 256), losses := [] }

theorem u6208 : Upper (D 9) (R 9) [96,12,129,288,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6208 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6209 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 296 400 96 83 147 275), lower := (rows 97 14 133 296 400 96 64 128 256), losses := [] }

theorem u6209 : Upper (D 9) (R 9) [96,12,129,288,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6209 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6210 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 4, region := 456, targets := 33 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(3,0),(3,5),(4,7)], upper := (rows 97 14 133 392 50 33 336 464 336), lower := (rows 97 14 133 392 50 33 64 128 256), losses := [] }

theorem u6210 : Upper (D 9) (R 9) [96,12,129,384,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6210 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6211 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 1, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 97 14 133 392 50 48 321 449 321), lower := (rows 97 14 133 392 50 48 64 128 256), losses := [] }

theorem u6211 : Upper (D 9) (R 9) [96,12,129,384,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6211 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6212 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 392 50 96 337 401 273), lower := (rows 97 14 133 392 50 96 64 128 256), losses := [] }

theorem u6212 : Upper (D 9) (R 9) [96,12,129,384,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6212 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6213 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 4, region := 197, targets := 256 }], pairs := [(0,7),(0,8),(2,8),(4,0),(4,7)], upper := (rows 97 14 133 392 50 288 81 209 337), lower := (rows 97 14 133 392 50 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 296 64 128 256), good := (rows 96 62 132 424 50 288 64 128 288) }] }

theorem u6213 : Upper (D 9) (R 9) [96,12,129,384,34,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6213 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6214 : Route 9 := (fun mask => (mask,id))

def c6214 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6214 : Upper (D 9) (R 9) [96,12,129,384,257,2] 13 := by
  apply FastRouting.sound _ _ [96,12,129,384,257,2] 13 (by decide) (choices 1) [16,32] r6214 c6214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2604
  · exact u2605

theorem m6215_2 : Upper (D 9) (R 9) [96,12,129,384,257,16,2] 13 :=
  permutation_upper _ _ _ [96,12,129,384,257,2,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2604

def r6215 : Route 9 := (fun mask => (mask,id))

def c6215 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6215 : Upper (D 9) (R 9) [96,12,129,384,257,16] 13 := by
  apply FastRouting.sound _ _ [96,12,129,384,257,16] 13 (by decide) (choices 1) [2,32] r6215 c6215
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m6215_2
  · exact u2606

def b6216 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 392 273 96 114 178 306), lower := (rows 97 14 133 392 273 96 64 128 256), losses := [] }

theorem u6216 : Upper (D 9) (R 9) [96,12,129,384,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6216 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6217 : Route 9 := (fun mask => (mask,id))

def c6217 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6217 : Upper (D 9) (R 9) [96,12,129,384,258,1] 13 := by
  apply FastRouting.sound _ _ [96,12,129,384,258,1] 13 (by decide) (choices 1) [16,32] r6217 c6217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2607
  · exact u2608

def b6218 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 4, region := 229, targets := 256 }], pairs := [(0,7),(0,8),(2,8),(4,7)], upper := (rows 97 14 133 392 274 48 97 225 353), lower := (rows 97 14 133 392 274 48 64 128 256), losses := [] }

theorem u6218 : Upper (D 9) (R 9) [96,12,129,384,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6218 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6219 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 392 274 96 113 177 305), lower := (rows 97 14 133 392 274 96 64 128 256), losses := [] }

theorem u6219 : Upper (D 9) (R 9) [96,12,129,384,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6219 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6220 : Route 9 := (fun mask => (mask,id))

def c6220 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6220 : Upper (D 9) (R 9) [96,12,129,384,288,1] 13 := by
  apply FastRouting.sound _ _ [96,12,129,384,288,1] 13 (by decide) (choices 1) [2,16] r6220 c6220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2609
  · exact u2610

def b6221 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 4, region := 197, targets := 256 }], pairs := [(0,7),(0,8),(2,8),(4,7)], upper := (rows 97 14 133 392 304 34 81 209 337), lower := (rows 97 14 133 392 304 34 64 128 256), losses := [] }

theorem u6221 : Upper (D 9) (R 9) [96,12,129,384,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6221 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6222 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 97 14 133 392 304 48 67 195 323), lower := (rows 97 14 133 392 304 48 64 128 256), losses := [] }

theorem u6222 : Upper (D 9) (R 9) [96,12,129,384,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6222 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6223 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 392 304 96 83 147 275), lower := (rows 97 14 133 392 304 96 64 128 256), losses := [] }

theorem u6223 : Upper (D 9) (R 9) [96,12,129,384,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6223 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6224 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 361, targets := 128 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,0),(2,0),(3,7)], upper := (rows 97 14 134 280 145 33 352 480 352), lower := (rows 97 14 134 280 145 33 64 128 256), losses := [{ target := 0, region := (rows 0 26 20 24 16 32 97 161 289), good := (rows 480 14 134 286 478 480 64 128 256) }] }

theorem u6224 : Upper (D 9) (R 9) [96,12,130,272,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6224 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6225 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 134 280 145 96 353 417 289), lower := (rows 97 14 134 280 145 96 64 128 256), losses := [] }

theorem u6225 : Upper (D 9) (R 9) [96,12,130,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6225 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m6226_1 : Upper (D 9) (R 9) [96,12,130,272,129,256,1] 13 :=
  permutation_upper _ _ _ [96,12,130,272,129,1,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2611

theorem m6226_32 : Upper (D 9) (R 9) [96,12,130,272,129,256,32] 13 :=
  permutation_upper _ _ _ [96,12,130,272,129,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2612

def r6226 : Route 9 := (fun mask => (mask,id))

def c6226 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6226 : Upper (D 9) (R 9) [96,12,130,272,129,256] 13 := by
  apply FastRouting.sound _ _ [96,12,130,272,129,256] 13 (by decide) (choices 1) [1,32] r6226 c6226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m6226_1
  · exact m6226_32

def b6227 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 329, targets := 128 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,5),(2,5),(3,7)], upper := (rows 97 14 134 280 176 33 321 449 321), lower := (rows 97 14 134 280 176 33 64 128 256), losses := [{ target := 5, region := (rows 1 26 20 24 16 0 97 161 289), good := (rows 449 14 134 286 478 449 64 128 256) }] }

theorem u6227 : Upper (D 9) (R 9) [96,12,130,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6227 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6228 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 134 280 176 96 321 385 257), lower := (rows 97 14 134 280 176 96 64 128 256), losses := [] }

theorem u6228 : Upper (D 9) (R 9) [96,12,130,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6228 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6229 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 329, targets := 128 },{ cop := 5, region := 209, targets := 256 }], pairs := [(0,7),(0,8),(1,8),(3,7),(4,8)], upper := (rows 97 14 134 280 176 288 65 193 321), lower := (rows 97 14 134 280 176 288 64 128 256), losses := [{ target := 8, region := (rows 49 10 14 8 49 32 121 185 0), good := (rows 241 206 134 223 241 241 64 128 0) }] }

theorem u6229 : Upper (D 9) (R 9) [96,12,130,272,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6229 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6230 : PairBound 9 := { available := 336, camps := [{ cop := 4, region := 361, targets := 128 },{ cop := 0, region := 400, targets := 32 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,5),(3,7),(4,5)], upper := (rows 97 14 134 296 145 33 336 464 336), lower := (rows 97 14 134 296 145 33 64 128 256), losses := [{ target := 5, region := (rows 1 10 14 8 49 0 121 185 313), good := (rows 465 462 134 478 465 465 64 128 256) }] }

theorem u6230 : Upper (D 9) (R 9) [96,12,130,288,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6230 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6231 : Route 9 := (fun mask => (mask,id))

def c6231 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6231 : Upper (D 9) (R 9) [96,12,130,288,129,16] 13 := by
  apply FastRouting.sound _ _ [96,12,130,288,129,16] 13 (by decide) (choices 1) [1,256] r6231 c6231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2613
  · exact u2614

def b6232 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 134 296 145 96 337 401 273), lower := (rows 97 14 134 296 145 96 64 128 256), losses := [] }

theorem u6232 : Upper (D 9) (R 9) [96,12,130,288,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6232 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6233 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 215, targets := 256 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 97 14 134 296 145 288 81 209 337), lower := (rows 97 14 134 296 145 288 64 128 256), losses := [] }

theorem u6233 : Upper (D 9) (R 9) [96,12,130,288,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6233 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6234 : PairBound 9 := { available := 273, camps := [{ cop := 4, region := 297, targets := 128 },{ cop := 0, region := 400, targets := 32 },{ cop := 4, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,5),(3,7),(4,5)], upper := (rows 97 14 134 296 208 33 337 401 273), lower := (rows 97 14 134 296 208 33 64 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 57 0 97 161 289), good := (rows 465 30 134 478 208 465 64 128 256) }] }

theorem u6234 : Upper (D 9) (R 9) [96,12,130,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6234 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6235 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 14 134 296 208 48 321 385 257), lower := (rows 97 14 134 296 208 48 64 128 256), losses := [] }

theorem u6235 : Upper (D 9) (R 9) [96,12,130,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6235 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6236 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 215, targets := 256 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 97 14 134 296 208 288 81 145 273), lower := (rows 97 14 134 296 208 288 64 128 256), losses := [] }

theorem u6236 : Upper (D 9) (R 9) [96,12,130,288,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6236 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6237 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 40, targets := 192 },{ cop := 6, region := 33, targets := 384 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,7),(0,8),(3,6),(3,7),(4,5)], upper := (rows 97 14 134 296 273 33 208 208 464), lower := (rows 97 14 134 296 273 33 64 128 256), losses := [] }

theorem u6237 : Upper (D 9) (R 9) [96,12,130,288,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6237 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6238 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 97 14 134 296 273 48 193 193 449), lower := (rows 97 14 134 296 273 48 64 128 256), losses := [] }

theorem u6238 : Upper (D 9) (R 9) [96,12,130,288,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6238 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6239 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 134 296 273 96 209 145 401), lower := (rows 97 14 134 296 273 96 64 128 256), losses := [] }

theorem u6239 : Upper (D 9) (R 9) [96,12,130,288,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6239 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u6239
end Delivery.IrregularNine14.P09
