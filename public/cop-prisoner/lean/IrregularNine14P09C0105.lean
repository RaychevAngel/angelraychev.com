import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0044
import IrregularNine14P09C0045

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6300 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 38, targets := 65 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 14 164 392 82 288 81 145 273), lower := (rows 97 14 164 392 82 288 64 128 256), losses := [] }

theorem u6300 : Upper (D 9) (R 9) [96,12,160,384,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6300 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6301 : Route 9 := (fun mask => (mask,id))

def c6301 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6301 : Upper (D 9) (R 9) [96,12,160,384,257,1] 13 := by
  apply FastRouting.sound _ _ [96,12,160,384,257,1] 13 (by decide) (choices 1) [2,16] r6301 c6301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2654
  · exact u2655

def b6302 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 38, targets := 321 }], pairs := [(1,0),(1,6),(1,8),(2,0)], upper := (rows 97 14 164 392 273 34 81 209 337), lower := (rows 97 14 164 392 273 34 64 128 256), losses := [] }

theorem u6302 : Upper (D 9) (R 9) [96,12,160,384,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6302 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6303 : Route 9 := (fun mask => (mask,id))

def c6303 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6303 : Upper (D 9) (R 9) [96,12,160,384,257,16] 13 := by
  apply FastRouting.sound _ _ [96,12,160,384,257,16] 13 (by decide) (choices 1) [1,2] r6303 c6303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2656
  · exact u2657

def b6304 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 164 392 273 96 83 147 275), lower := (rows 97 14 164 392 273 96 64 128 256), losses := [] }

theorem u6304 : Upper (D 9) (R 9) [96,12,160,384,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6304 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6305 : Route 9 := (fun mask => (mask,id))

def c6305 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6305 : Upper (D 9) (R 9) [96,12,160,384,258,1] 13 := by
  apply FastRouting.sound _ _ [96,12,160,384,258,1] 13 (by decide) (choices 1) [1,16] r6305 c6305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2658
  · exact u2659

def b6306 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 54, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 14 164 392 274 48 65 193 321), lower := (rows 97 14 164 392 274 48 64 128 256), losses := [] }

theorem u6306 : Upper (D 9) (R 9) [96,12,160,384,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6306 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6307 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 164 392 274 96 81 145 273), lower := (rows 97 14 164 392 274 96 64 128 256), losses := [] }

theorem u6307 : Upper (D 9) (R 9) [96,12,160,384,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6307 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6308 : Route 9 := (fun mask => (mask,id))

def c6308 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6308 : Upper (D 9) (R 9) [96,12,160,384,320,1] 13 := by
  apply FastRouting.sound _ _ [96,12,160,384,320,1] 13 (by decide) (choices 1) [1,2,16] r6308 c6308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2660
  · exact u2661
  · exact u2662

def b6309 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 38, targets := 321 }], pairs := [(1,0),(1,6),(1,8),(2,0)], upper := (rows 97 14 164 392 336 34 81 145 273), lower := (rows 97 14 164 392 336 34 64 128 256), losses := [] }

theorem u6309 : Upper (D 9) (R 9) [96,12,160,384,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6309 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6310 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 14 164 392 336 48 67 131 259), lower := (rows 97 14 164 392 336 48 64 128 256), losses := [] }

theorem u6310 : Upper (D 9) (R 9) [96,12,160,384,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6310 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6311 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 1, region := 400, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,0)], upper := (rows 97 38 76 137 146 33 336 400 272), lower := (rows 97 38 76 137 146 33 64 128 256), losses := [] }

theorem u6311 : Upper (D 9) (R 9) [96,36,72,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6311 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6312 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 396, targets := 32 },{ cop := 0, region := 392, targets := 64 },{ cop := 1, region := 321, targets := 128 }], pairs := [(0,7),(2,5),(3,5),(3,6)], upper := (rows 97 38 76 137 146 48 321 385 257), lower := (rows 97 38 76 137 146 48 64 128 256), losses := [] }

theorem u6312 : Upper (D 9) (R 9) [96,36,72,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6312 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6313 : Route 9 := (fun mask => (mask,id))

def c6313 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6313 : Upper (D 9) (R 9) [96,36,72,129,130,256] 13 := by
  apply FastRouting.sound _ _ [96,36,72,129,130,256] 13 (by decide) (choices 1) [1,16,256] r6313 c6313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2663
  · exact u2664
  · exact u2665

def b6314 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 38 76 137 273 34 464 400 400), lower := (rows 97 38 76 137 273 34 64 128 256), losses := [] }

theorem u6314 : Upper (D 9) (R 9) [96,36,72,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6314 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6315 : Route 9 := (fun mask => (mask,id))

def c6315 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u6315 : Upper (D 9) (R 9) [96,36,72,129,257,16] 13 := by
  apply FastRouting.sound _ _ [96,36,72,129,257,16] 13 (by decide) (choices 1) [2,128,256] r6315 c6315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2666
  · exact u2667
  · exact u2668

def b6316 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7),(0,8),(1,0),(1,6),(4,7)], upper := (rows 97 38 76 137 273 160 338 402 274), lower := (rows 97 38 76 137 273 160 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 168 64 128 256), good := (rows 96 38 110 168 272 160 64 160 256) },{ target := 6, region := (rows 1 6 4 8 16 168 0 128 256), good := (rows 33 38 46 169 273 160 0 160 256) },{ target := 8, region := (rows 5 6 4 8 16 168 64 128 0), good := (rows 97 39 111 169 17 160 64 160 0) }] }

theorem u6316 : Upper (D 9) (R 9) [96,36,72,129,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6316 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6317 : Route 9 := (fun mask => (mask,id))

def c6317 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6317 : Upper (D 9) (R 9) [96,36,72,129,257,256] 13 := by
  apply FastRouting.sound _ _ [96,36,72,129,257,256] 13 (by decide) (choices 1) [2,16,128] r6317 c6317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2669
  · exact u2670
  · exact u2671

def b6318 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 1, region := 400, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,0)], upper := (rows 97 38 76 137 274 33 464 400 400), lower := (rows 97 38 76 137 274 33 64 128 256), losses := [] }

theorem u6318 : Upper (D 9) (R 9) [96,36,72,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6318 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6319 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 396, targets := 32 },{ cop := 0, region := 392, targets := 64 }], pairs := [(1,6),(2,5),(3,5),(3,6)], upper := (rows 97 38 76 137 274 48 449 385 385), lower := (rows 97 38 76 137 274 48 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 9 20 54 0 137 265), good := (rows 425 54 446 393 306 48 0 128 256) }] }

theorem u6319 : Upper (D 9) (R 9) [96,36,72,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6319 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6320 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7),(0,8),(1,0),(1,6),(4,7)], upper := (rows 97 38 76 137 274 160 337 401 273), lower := (rows 97 38 76 137 274 160 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 168 64 128 256), good := (rows 96 38 110 168 274 160 64 160 256) },{ target := 6, region := (rows 1 6 4 8 16 168 0 128 256), good := (rows 33 38 46 169 274 160 0 160 256) },{ target := 8, region := (rows 5 6 4 8 16 168 64 128 0), good := (rows 97 39 111 169 18 160 64 160 0) }] }

theorem u6320 : Upper (D 9) (R 9) [96,36,72,129,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6320 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6321 : Route 9 := (fun mask => (mask,id))

def c6321 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6321 : Upper (D 9) (R 9) [96,36,72,129,258,256] 13 := by
  apply FastRouting.sound _ _ [96,36,72,129,258,256] 13 (by decide) (choices 1) [1,16,128] r6321 c6321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2672
  · exact u2673
  · exact u2674

def b6322 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 1, region := 400, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,0)], upper := (rows 97 38 76 137 400 33 338 402 274), lower := (rows 97 38 76 137 400 33 64 128 256), losses := [] }

theorem u6322 : Upper (D 9) (R 9) [96,36,72,129,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6322 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6323 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 38 76 137 400 34 337 401 273), lower := (rows 97 38 76 137 400 34 64 128 256), losses := [] }

theorem u6323 : Upper (D 9) (R 9) [96,36,72,129,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6323 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6324 : Route 9 := (fun mask => (mask,id))

def c6324 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6324 : Upper (D 9) (R 9) [96,36,72,129,384,16] 13 := by
  apply FastRouting.sound _ _ [96,36,72,129,384,16] 13 (by decide) (choices 1) [1,2,256] r6324 c6324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2675
  · exact u2676
  · exact u2677

def r6325 : Route 9 := (fun mask => (mask,id))

def c6325 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6325 : Upper (D 9) (R 9) [96,36,72,129,384,256] 13 := by
  apply FastRouting.sound _ _ [96,36,72,129,384,256] 13 (by decide) (choices 1) [1,2,16] r6325 c6325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2678
  · exact u2679
  · exact u2680

def b6326 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,5)], upper := (rows 97 38 76 138 145 33 336 400 272), lower := (rows 97 38 76 138 145 33 64 128 256), losses := [] }

theorem u6326 : Upper (D 9) (R 9) [96,36,72,130,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6326 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6327 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 400, targets := 32 },{ cop := 0, region := 400, targets := 64 },{ cop := 1, region := 321, targets := 128 }], pairs := [(0,7),(2,7),(4,5),(4,6)], upper := (rows 97 38 76 138 145 48 321 385 257), lower := (rows 97 38 76 138 145 48 64 128 256), losses := [{ target := 7, region := (rows 51 2 12 8 16 48 123 0 315), good := (rows 353 359 332 335 369 369 64 0 256) }] }

theorem u6327 : Upper (D 9) (R 9) [96,36,72,130,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6327 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6328 : Route 9 := (fun mask => (mask,id))

def c6328 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6328 : Upper (D 9) (R 9) [96,36,72,130,129,256] 13 := by
  apply FastRouting.sound _ _ [96,36,72,130,129,256] 13 (by decide) (choices 1) [1,16,256] r6328 c6328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2681
  · exact u2682
  · exact u2683

def b6329 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,5)], upper := (rows 97 38 76 138 273 33 464 400 400), lower := (rows 97 38 76 138 273 33 64 128 256), losses := [] }

theorem u6329 : Upper (D 9) (R 9) [96,36,72,130,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6329 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6330 : Route 9 := (fun mask => (mask,id))

def c6330 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u6330 : Upper (D 9) (R 9) [96,36,72,130,257,16] 13 := by
  apply FastRouting.sound _ _ [96,36,72,130,257,16] 13 (by decide) (choices 1) [1,128,256] r6330 c6330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2684
  · exact u2685
  · exact u2686

def b6331 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 337, targets := 128 },{ cop := 0, region := 272, targets := 32 },{ cop := 0, region := 272, targets := 64 }], pairs := [(0,7),(1,0),(4,5),(4,6),(4,7)], upper := (rows 97 38 76 138 273 160 337 401 273), lower := (rows 97 38 76 138 273 160 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 168 64 128 256), good := (rows 96 38 110 170 272 160 64 160 256) }] }

theorem u6331 : Upper (D 9) (R 9) [96,36,72,130,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6331 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6332 : Route 9 := (fun mask => (mask,id))

def c6332 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6332 : Upper (D 9) (R 9) [96,36,72,130,257,256] 13 := by
  apply FastRouting.sound _ _ [96,36,72,130,257,256] 13 (by decide) (choices 1) [1,16,128] r6332 c6332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2687
  · exact u2688
  · exact u2689

def b6333 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,5)], upper := (rows 97 38 76 138 400 33 337 401 273), lower := (rows 97 38 76 138 400 33 64 128 256), losses := [] }

theorem u6333 : Upper (D 9) (R 9) [96,36,72,130,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6333 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6334 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 400, targets := 32 },{ cop := 0, region := 400, targets := 64 },{ cop := 1, region := 321, targets := 128 }], pairs := [(0,7),(2,7),(4,5),(4,6)], upper := (rows 97 38 76 138 400 48 321 385 257), lower := (rows 97 38 76 138 400 48 64 128 256), losses := [{ target := 7, region := (rows 51 2 12 8 16 48 123 0 315), good := (rows 353 359 332 335 369 369 64 0 256) }] }

theorem u6334 : Upper (D 9) (R 9) [96,36,72,130,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6334 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6335 : Route 9 := (fun mask => (mask,id))

def c6335 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6335 : Upper (D 9) (R 9) [96,36,72,130,384,256] 13 := by
  apply FastRouting.sound _ _ [96,36,72,130,384,256] 13 (by decide) (choices 1) [1,16] r6335 c6335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2690
  · exact u2691

def r6336 : Route 9 := (fun mask => (mask,id))

def c6336 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u6336 : Upper (D 9) (R 9) [96,36,72,144,257,1] 13 := by
  apply FastRouting.sound _ _ [96,36,72,144,257,1] 13 (by decide) (choices 1) [2,128,256] r6336 c6336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2692
  · exact u2693
  · exact u2694

def b6337 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 38 76 152 273 34 449 385 385), lower := (rows 97 38 76 152 273 34 64 128 256), losses := [] }

theorem u6337 : Upper (D 9) (R 9) [96,36,72,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6337 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6338 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7),(0,8),(1,0),(1,6),(4,7)], upper := (rows 97 38 76 152 273 160 323 387 259), lower := (rows 97 38 76 152 273 160 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 168 64 128 256), good := (rows 96 38 110 184 272 160 64 160 256) },{ target := 6, region := (rows 1 6 4 8 16 168 0 128 256), good := (rows 33 38 46 184 273 160 0 160 256) },{ target := 8, region := (rows 5 6 4 8 16 168 64 128 0), good := (rows 97 39 111 184 17 160 64 160 0) }] }

theorem u6338 : Upper (D 9) (R 9) [96,36,72,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6338 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6339 : Route 9 := (fun mask => (mask,id))

def c6339 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6339 : Upper (D 9) (R 9) [96,36,72,144,257,256] 13 := by
  apply FastRouting.sound _ _ [96,36,72,144,257,256] 13 (by decide) (choices 1) [1,2,128] r6339 c6339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2695
  · exact u2696
  · exact u2697

def b6340 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 97 38 76 152 274 33 449 385 385), lower := (rows 97 38 76 152 274 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 6 10 18 0 97 161 289), good := (rows 449 478 76 152 286 449 64 128 256) }] }

theorem u6340 : Upper (D 9) (R 9) [96,36,72,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6340 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6341 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(2,7),(4,7)], upper := (rows 97 38 76 152 274 160 321 385 257), lower := (rows 97 38 76 152 274 160 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 168 64 128 256), good := (rows 96 38 110 184 274 160 64 160 256) },{ target := 6, region := (rows 1 6 4 8 16 169 0 129 257), good := (rows 417 38 46 184 274 160 0 160 256) },{ target := 7, region := (rows 35 2 12 8 18 32 115 0 307), good := (rows 353 375 76 348 339 353 64 0 256) }] }

theorem u6341 : Upper (D 9) (R 9) [96,36,72,144,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6341 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6342 : Route 9 := (fun mask => (mask,id))

def c6342 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6342 : Upper (D 9) (R 9) [96,36,72,144,258,256] 13 := by
  apply FastRouting.sound _ _ [96,36,72,144,258,256] 13 (by decide) (choices 1) [1,128] r6342 c6342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2698
  · exact u2699

def r6343 : Route 9 := (fun mask => (mask,id))

def c6343 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6343 : Upper (D 9) (R 9) [96,36,72,384,129,1] 13 := by
  apply FastRouting.sound _ _ [96,36,72,384,129,1] 13 (by decide) (choices 1) [2,16,256] r6343 c6343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2700
  · exact u2701
  · exact u2702

def b6344 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 38 76 392 145 34 337 401 273), lower := (rows 97 38 76 392 145 34 64 128 256), losses := [] }

theorem u6344 : Upper (D 9) (R 9) [96,36,72,384,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6344 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6345 : Route 9 := (fun mask => (mask,id))

def c6345 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6345 : Upper (D 9) (R 9) [96,36,72,384,129,16] 13 := by
  apply FastRouting.sound _ _ [96,36,72,384,129,16] 13 (by decide) (choices 1) [1,2,256] r6345 c6345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2703
  · exact u2704
  · exact u2705

def b6346 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 209, targets := 256 }], pairs := [(0,7),(0,8),(1,0),(1,6),(4,8)], upper := (rows 97 38 76 392 145 288 83 147 275), lower := (rows 97 38 76 392 145 288 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 296 64 128 256), good := (rows 96 38 110 424 144 288 64 128 288) },{ target := 6, region := (rows 1 6 4 8 16 296 0 128 256), good := (rows 33 38 46 424 145 288 0 128 288) },{ target := 7, region := (rows 5 6 4 8 16 296 64 0 256), good := (rows 97 39 111 296 17 288 64 0 288) }] }

theorem u6346 : Upper (D 9) (R 9) [96,36,72,384,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6346 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6347 : Route 9 := (fun mask => (mask,id))

def c6347 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6347 : Upper (D 9) (R 9) [96,36,72,384,130,1] 13 := by
  apply FastRouting.sound _ _ [96,36,72,384,130,1] 13 (by decide) (choices 1) [1,16,256] r6347 c6347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2706
  · exact u2707
  · exact u2708

def b6348 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 396, targets := 32 },{ cop := 0, region := 392, targets := 64 },{ cop := 1, region := 321, targets := 128 }], pairs := [(0,7),(2,5),(3,5),(3,6)], upper := (rows 97 38 76 392 146 48 321 385 257), lower := (rows 97 38 76 392 146 48 64 128 256), losses := [] }

theorem u6348 : Upper (D 9) (R 9) [96,36,72,384,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6348 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6349 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 209, targets := 256 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(0,8),(1,0),(1,6),(4,8)], upper := (rows 97 38 76 392 146 288 81 145 273), lower := (rows 97 38 76 392 146 288 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 296 64 128 256), good := (rows 96 38 110 424 146 288 64 128 288) },{ target := 6, region := (rows 1 6 4 8 16 296 0 128 256), good := (rows 33 38 46 424 146 288 0 128 288) }] }

theorem u6349 : Upper (D 9) (R 9) [96,36,72,384,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6349 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6350 : PairBound 9 := { available := 264, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 38 133 88 146 33 328 392 264), lower := (rows 97 38 133 88 146 33 64 128 256), losses := [] }

theorem u6350 : Upper (D 9) (R 9) [96,36,129,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6350 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6351 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(4,6)], upper := (rows 97 38 133 88 146 40 321 385 257), lower := (rows 97 38 133 88 146 40 64 128 256), losses := [] }

theorem u6351 : Upper (D 9) (R 9) [96,36,129,80,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6351 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6352 : Route 9 := (fun mask => (mask,id))

def c6352 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6352 : Upper (D 9) (R 9) [96,36,129,80,130,256] 13 := by
  apply FastRouting.sound _ _ [96,36,129,80,130,256] 13 (by decide) (choices 1) [1,8,256] r6352 c6352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2709
  · exact u2710
  · exact u2711

def b6353 : PairBound 9 := { available := 258, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 38 133 88 152 33 322 386 258), lower := (rows 97 38 133 88 152 33 64 128 256), losses := [] }

theorem u6353 : Upper (D 9) (R 9) [96,36,129,80,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6353 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6354 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,5),(3,5),(4,5)], upper := (rows 97 38 133 88 152 34 321 385 257), lower := (rows 97 38 133 88 152 34 64 128 256), losses := [] }

theorem u6354 : Upper (D 9) (R 9) [96,36,129,80,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6354 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6355 : Route 9 := (fun mask => (mask,id))

def c6355 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6355 : Upper (D 9) (R 9) [96,36,129,80,136,256] 13 := by
  apply FastRouting.sound _ _ [96,36,129,80,136,256] 13 (by decide) (choices 1) [1,2,256] r6355 c6355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2712
  · exact u2713
  · exact u2714

def b6356 : PairBound 9 := { available := 392, camps := [{ cop := 2, region := 34, targets := 449 }], pairs := [(1,0),(1,6),(1,7),(1,8)], upper := (rows 97 38 133 88 273 34 456 392 392), lower := (rows 97 38 133 88 273 34 64 128 256), losses := [] }

theorem u6356 : Upper (D 9) (R 9) [96,36,129,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6356 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6357 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(4,6)], upper := (rows 97 38 133 88 273 40 450 386 386), lower := (rows 97 38 133 88 273 40 64 128 256), losses := [] }

theorem u6357 : Upper (D 9) (R 9) [96,36,129,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6357 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6358 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 345, targets := 128 },{ cop := 2, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(3,7),(4,7)], upper := (rows 97 38 133 88 273 160 330 394 266), lower := (rows 97 38 133 88 273 160 64 128 256), losses := [] }

theorem u6358 : Upper (D 9) (R 9) [96,36,129,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6358 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m6359_2 : Upper (D 9) (R 9) [96,36,129,80,257,256,2] 13 :=
  permutation_upper _ _ _ [96,36,129,80,257,8,128] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2716

theorem m6359_8 : Upper (D 9) (R 9) [96,36,129,80,257,256,8] 13 :=
  permutation_upper _ _ _ [96,36,129,80,257,2,128] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2715

def r6359 : Route 9 := (fun mask => (mask,id))

def c6359 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6359 : Upper (D 9) (R 9) [96,36,129,80,257,256] 13 := by
  apply FastRouting.sound _ _ [96,36,129,80,257,256] 13 (by decide) (choices 1) [2,8,128] r6359 c6359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m6359_2
  · exact m6359_8
  · exact u2717

#print axioms u6359
end Delivery.IrregularNine14.P09
