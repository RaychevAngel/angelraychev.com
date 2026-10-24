import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0048
import IrregularNine14P08C0049

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r10500 : Route 9 := (fun mask => (mask,id))

def c10500 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u10500 : Upper (D 8) (R 8) [66,33,40,132,288] 13 := by
  apply FastRouting.sound _ _ [66,33,40,132,288] 13 (by decide) (choices 1) [1,16,64,128] r10500 c10500
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2911
  · exact u2912
  · exact u2913
  · exact u2914

def r10501 : Route 9 := (fun mask => (mask,id))

def c10501 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10501 : Upper (D 8) (R 8) [66,33,40,132,320] 13 := by
  apply FastRouting.sound _ _ [66,33,40,132,320] 13 (by decide) (choices 1) [1,16,128] r10501 c10501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2915
  · exact u2916
  · exact u2917

def b10502 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 140 400 113 113 241 369), lower := (rows 67 35 44 140 400 32 64 128 256), losses := [] }

theorem u10502 : Upper (D 8) (R 8) [66,33,40,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10502 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10503 : PairBound 9 := { available := 420, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 44 152 81 420 484 420 420), lower := (rows 67 35 44 152 81 32 64 128 256), losses := [] }

theorem u10503 : Upper (D 8) (R 8) [66,33,40,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10503 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10504 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 44 152 84 417 481 417 417), lower := (rows 67 35 44 152 84 32 64 128 256), losses := [] }

theorem u10504 : Upper (D 8) (R 8) [66,33,40,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10504 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10505 : PairBound 9 := { available := 389, camps := [{ cop := 4, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 152 112 421 453 389 389), lower := (rows 67 35 44 152 112 32 64 128 256), losses := [] }

theorem u10505 : Upper (D 8) (R 8) [66,33,40,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10505 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10506 : PairBound 9 := { available := 356, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 152 145 356 356 484 356), lower := (rows 67 35 44 152 145 32 64 128 256), losses := [] }

theorem u10506 : Upper (D 8) (R 8) [66,33,40,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10506 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10507 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 152 148 353 353 481 353), lower := (rows 67 35 44 152 148 32 64 128 256), losses := [] }

theorem u10507 : Upper (D 8) (R 8) [66,33,40,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10507 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10508 : PairBound 9 := { available := 325, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 152 176 357 325 453 325), lower := (rows 67 35 44 152 176 32 64 128 256), losses := [] }

theorem u10508 : Upper (D 8) (R 8) [66,33,40,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10508 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10509 : PairBound 9 := { available := 293, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 152 208 293 357 421 293), lower := (rows 67 35 44 152 208 32 64 128 256), losses := [] }

theorem u10509 : Upper (D 8) (R 8) [66,33,40,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10509 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10510 : PairBound 9 := { available := 228, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 152 273 228 228 228 484), lower := (rows 67 35 44 152 273 32 64 128 256), losses := [] }

theorem u10510 : Upper (D 8) (R 8) [66,33,40,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10510 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10511 : Route 9 := (fun mask => (mask,id))

def c10511 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10511 : Upper (D 8) (R 8) [66,33,40,144,260] 13 := by
  apply FastRouting.sound _ _ [66,33,40,144,260] 13 (by decide) (choices 1) [1,64,128] r10511 c10511
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2918
  · exact u2919
  · exact u2920

def r10512 : Route 9 := (fun mask => (mask,id))

def c10512 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10512 : Upper (D 8) (R 8) [66,33,40,144,288] 13 := by
  apply FastRouting.sound _ _ [66,33,40,144,288] 13 (by decide) (choices 1) [1,4,64,128] r10512 c10512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2921
  · exact u2922
  · exact u2923
  · exact u2924

def r10513 : Route 9 := (fun mask => (mask,id))

def c10513 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10513 : Upper (D 8) (R 8) [66,33,40,144,320] 13 := by
  apply FastRouting.sound _ _ [66,33,40,144,320] 13 (by decide) (choices 1) [1,4,128] r10513 c10513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2925
  · exact u2926
  · exact u2927

def b10514 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 152 400 101 101 229 357), lower := (rows 67 35 44 152 400 32 64 128 256), losses := [] }

theorem u10514 : Upper (D 8) (R 8) [66,33,40,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10514 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10515 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 168 84 433 465 401 401), lower := (rows 67 35 44 168 84 32 64 128 256), losses := [] }

theorem u10515 : Upper (D 8) (R 8) [66,33,40,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10515 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10516 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 168 148 369 337 465 337), lower := (rows 67 35 44 168 148 32 64 128 256), losses := [] }

theorem u10516 : Upper (D 8) (R 8) [66,33,40,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10516 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10517 : PairBound 9 := { available := 277, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 168 208 309 341 405 277), lower := (rows 67 35 44 168 208 32 64 128 256), losses := [] }

theorem u10517 : Upper (D 8) (R 8) [66,33,40,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10517 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10518 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 168 276 241 209 209 465), lower := (rows 67 35 44 168 276 32 64 128 256), losses := [] }

theorem u10518 : Upper (D 8) (R 8) [66,33,40,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10518 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10519 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 168 336 181 213 149 405), lower := (rows 67 35 44 168 336 32 64 128 256), losses := [] }

theorem u10519 : Upper (D 8) (R 8) [66,33,40,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10519 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10520 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 168 400 117 85 213 341), lower := (rows 67 35 44 168 400 32 64 128 256), losses := [] }

theorem u10520 : Upper (D 8) (R 8) [66,33,40,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10520 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10521 : PairBound 9 := { available := 308, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 200 145 308 372 436 308), lower := (rows 67 35 44 200 145 32 64 128 256), losses := [] }

theorem u10521 : Upper (D 8) (R 8) [66,33,40,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10521 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10522 : PairBound 9 := { available := 305, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 200 148 305 369 433 305), lower := (rows 67 35 44 200 148 32 64 128 256), losses := [] }

theorem u10522 : Upper (D 8) (R 8) [66,33,40,192,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10522 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10523 : Route 9 := (fun mask => (mask,id))

def c10523 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u10523 : Upper (D 8) (R 8) [66,33,40,192,160] 13 := by
  apply FastRouting.sound _ _ [66,33,40,192,160] 13 (by decide) (choices 1) [1,4,16,256] r10523 c10523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2928
  · exact u2929
  · exact u2930
  · exact u2931

def b10524 : PairBound 9 := { available := 180, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 200 273 180 244 180 436), lower := (rows 67 35 44 200 273 32 64 128 256), losses := [] }

theorem u10524 : Upper (D 8) (R 8) [66,33,40,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10524 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10525 : Route 9 := (fun mask => (mask,id))

def c10525 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10525 : Upper (D 8) (R 8) [66,33,40,192,260] 13 := by
  apply FastRouting.sound _ _ [66,33,40,192,260] 13 (by decide) (choices 1) [1,16,128] r10525 c10525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2932
  · exact u2933
  · exact u2934

def r10526 : Route 9 := (fun mask => (mask,id))

def c10526 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10526 : Upper (D 8) (R 8) [66,33,40,192,288] 13 := by
  apply FastRouting.sound _ _ [66,33,40,192,288] 13 (by decide) (choices 1) [1,4,16,128] r10526 c10526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2935
  · exact u2936
  · exact u2937
  · exact u2938

def r10527 : Route 9 := (fun mask => (mask,id))

def c10527 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10527 : Upper (D 8) (R 8) [66,33,40,192,384] 13 := by
  apply FastRouting.sound _ _ [66,33,40,192,384] 13 (by decide) (choices 1) [1,4,16] r10527 c10527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2939
  · exact u2940
  · exact u2941

def b10528 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 265 84 176 240 176 432), lower := (rows 67 35 44 265 84 32 64 128 256), losses := [] }

theorem u10528 : Upper (D 8) (R 8) [66,33,40,257,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10528 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10529 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 265 148 240 240 240 496), lower := (rows 67 35 44 265 148 32 64 128 256), losses := [] }

theorem u10529 : Upper (D 8) (R 8) [66,33,40,257,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10529 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10530 : PairBound 9 := { available := 212, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 265 176 244 212 212 468), lower := (rows 67 35 44 265 176 32 64 128 256), losses := [] }

theorem u10530 : Upper (D 8) (R 8) [66,33,40,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10530 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10531 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 265 208 180 244 180 436), lower := (rows 67 35 44 265 208 32 64 128 256), losses := [] }

theorem u10531 : Upper (D 8) (R 8) [66,33,40,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10531 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10532 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 44 268 81 176 240 176 432), lower := (rows 67 35 44 268 81 32 64 128 256), losses := [] }

theorem u10532 : Upper (D 8) (R 8) [66,33,40,260,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10532 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10533 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 268 112 177 209 145 401), lower := (rows 67 35 44 268 112 32 64 128 256), losses := [] }

theorem u10533 : Upper (D 8) (R 8) [66,33,40,260,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10533 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10534 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 268 145 240 240 240 496), lower := (rows 67 35 44 268 145 32 64 128 256), losses := [] }

theorem u10534 : Upper (D 8) (R 8) [66,33,40,260,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10534 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10535 : Route 9 := (fun mask => (mask,id))

def c10535 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u10535 : Upper (D 8) (R 8) [66,33,40,260,160] 13 := by
  apply FastRouting.sound _ _ [66,33,40,260,160] 13 (by decide) (choices 1) [1,16,64,128] r10535 c10535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2942
  · exact u2943
  · exact u2944
  · exact u2945

def r10536 : Route 9 := (fun mask => (mask,id))

def c10536 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10536 : Upper (D 8) (R 8) [66,33,40,260,192] 13 := by
  apply FastRouting.sound _ _ [66,33,40,260,192] 13 (by decide) (choices 1) [1,16,128] r10536 c10536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2946
  · exact u2947
  · exact u2948

def b10537 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 44 280 81 164 228 164 420), lower := (rows 67 35 44 280 81 32 64 128 256), losses := [] }

theorem u10537 : Upper (D 8) (R 8) [66,33,40,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10537 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10538 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 44 280 84 161 225 161 417), lower := (rows 67 35 44 280 84 32 64 128 256), losses := [] }

theorem u10538 : Upper (D 8) (R 8) [66,33,40,272,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10538 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10539 : PairBound 9 := { available := 133, camps := [{ cop := 4, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 280 112 165 197 133 389), lower := (rows 67 35 44 280 112 32 64 128 256), losses := [] }

theorem u10539 : Upper (D 8) (R 8) [66,33,40,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10539 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10540 : PairBound 9 := { available := 228, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 280 145 228 228 228 484), lower := (rows 67 35 44 280 145 32 64 128 256), losses := [] }

theorem u10540 : Upper (D 8) (R 8) [66,33,40,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10540 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10541 : Route 9 := (fun mask => (mask,id))

def c10541 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10541 : Upper (D 8) (R 8) [66,33,40,272,132] 13 := by
  apply FastRouting.sound _ _ [66,33,40,272,132] 13 (by decide) (choices 1) [1,64,128] r10541 c10541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2949
  · exact u2950
  · exact u2951

def r10542 : Route 9 := (fun mask => (mask,id))

def c10542 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10542 : Upper (D 8) (R 8) [66,33,40,272,160] 13 := by
  apply FastRouting.sound _ _ [66,33,40,272,160] 13 (by decide) (choices 1) [1,4,64,128] r10542 c10542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2952
  · exact u2953
  · exact u2954
  · exact u2955

def r10543 : Route 9 := (fun mask => (mask,id))

def c10543 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10543 : Upper (D 8) (R 8) [66,33,40,272,192] 13 := by
  apply FastRouting.sound _ _ [66,33,40,272,192] 13 (by decide) (choices 1) [1,4,128] r10543 c10543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2956
  · exact u2957
  · exact u2958

def b10544 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 296 84 177 209 145 401), lower := (rows 67 35 44 296 84 32 64 128 256), losses := [] }

theorem u10544 : Upper (D 8) (R 8) [66,33,40,288,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10544 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10545 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 296 148 241 209 209 465), lower := (rows 67 35 44 296 148 32 64 128 256), losses := [] }

theorem u10545 : Upper (D 8) (R 8) [66,33,40,288,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10545 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10546 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 296 208 181 213 149 405), lower := (rows 67 35 44 296 208 32 64 128 256), losses := [] }

theorem u10546 : Upper (D 8) (R 8) [66,33,40,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10546 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10547 : PairBound 9 := { available := 180, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 328 145 180 244 180 436), lower := (rows 67 35 44 328 145 32 64 128 256), losses := [] }

theorem u10547 : Upper (D 8) (R 8) [66,33,40,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10547 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10548 : Route 9 := (fun mask => (mask,id))

def c10548 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10548 : Upper (D 8) (R 8) [66,33,40,320,132] 13 := by
  apply FastRouting.sound _ _ [66,33,40,320,132] 13 (by decide) (choices 1) [1,16,128] r10548 c10548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2959
  · exact u2960
  · exact u2961

def r10549 : Route 9 := (fun mask => (mask,id))

def c10549 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10549 : Upper (D 8) (R 8) [66,33,40,320,160] 13 := by
  apply FastRouting.sound _ _ [66,33,40,320,160] 13 (by decide) (choices 1) [1,4,16,128] r10549 c10549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2962
  · exact u2963
  · exact u2964
  · exact u2965

def b10550 : PairBound 9 := { available := 180, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 44 392 81 180 244 180 436), lower := (rows 67 35 44 392 81 32 64 128 256), losses := [] }

theorem u10550 : Upper (D 8) (R 8) [66,33,40,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10550 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10551 : Route 9 := (fun mask => (mask,id))

def c10551 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10551 : Upper (D 8) (R 8) [66,33,40,384,68] 13 := by
  apply FastRouting.sound _ _ [66,33,40,384,68] 13 (by decide) (choices 1) [1,16,128] r10551 c10551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2966
  · exact u2967
  · exact u2968

def b10552 : PairBound 9 := { available := 149, camps := [{ cop := 4, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 392 112 181 213 149 405), lower := (rows 67 35 44 392 112 32 64 128 256), losses := [] }

theorem u10552 : Upper (D 8) (R 8) [66,33,40,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10552 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10553 : PairBound 9 := { available := 116, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 392 145 116 116 244 372), lower := (rows 67 35 44 392 145 32 64 128 256), losses := [] }

theorem u10553 : Upper (D 8) (R 8) [66,33,40,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10553 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10554 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 392 148 113 113 241 369), lower := (rows 67 35 44 392 148 32 64 128 256), losses := [] }

theorem u10554 : Upper (D 8) (R 8) [66,33,40,384,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10554 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10555 : Route 9 := (fun mask => (mask,id))

def c10555 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10555 : Upper (D 8) (R 8) [66,33,40,384,160] 13 := by
  apply FastRouting.sound _ _ [66,33,40,384,160] 13 (by decide) (choices 1) [1,4,16,64] r10555 c10555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2969
  · exact u2970
  · exact u2971
  · exact u2972

def r10556 : Route 9 := (fun mask => (mask,id))

def c10556 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10556 : Upper (D 8) (R 8) [66,33,40,384,192] 13 := by
  apply FastRouting.sound _ _ [66,33,40,384,192] 13 (by decide) (choices 1) [1,4,16] r10556 c10556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2973
  · exact u2974
  · exact u2975

def b10557 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 69 140 176 312 376 440 312), lower := (rows 67 35 69 140 176 32 64 128 256), losses := [] }

theorem u10557 : Upper (D 8) (R 8) [66,33,65,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10557 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10558 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 69 140 280 176 240 176 432), lower := (rows 67 35 69 140 280 32 64 128 256), losses := [] }

theorem u10558 : Upper (D 8) (R 8) [66,33,65,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10558 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10559 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 69 140 304 184 248 184 440), lower := (rows 67 35 69 140 304 32 64 128 256), losses := [] }

theorem u10559 : Upper (D 8) (R 8) [66,33,65,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10559 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u10559
end Delivery.IrregularNine14.P08
