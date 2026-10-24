import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0049
import IrregularNine14P08C0050

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10560 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 69 140 400 56 120 184 312), lower := (rows 67 35 69 140 400 32 64 128 256), losses := [] }

theorem u10560 : Upper (D 8) (R 8) [66,33,65,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10560 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10561 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 69 152 276 168 232 168 424), lower := (rows 67 35 69 152 276 32 64 128 256), losses := [] }

theorem u10561 : Upper (D 8) (R 8) [66,33,65,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10561 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10562 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 69 152 280 164 228 164 420), lower := (rows 67 35 69 152 280 32 64 128 256), losses := [] }

theorem u10562 : Upper (D 8) (R 8) [66,33,65,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10562 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10563 : PairBound 9 := { available := 172, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 69 152 304 172 236 172 428), lower := (rows 67 35 69 152 304 32 64 128 256), losses := [] }

theorem u10563 : Upper (D 8) (R 8) [66,33,65,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10563 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10564 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 69 168 276 184 248 184 440), lower := (rows 67 35 69 168 276 32 64 128 256), losses := [] }

theorem u10564 : Upper (D 8) (R 8) [66,33,65,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10564 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10565 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 69 168 280 180 244 180 436), lower := (rows 67 35 69 168 280 32 64 128 256), losses := [] }

theorem u10565 : Upper (D 8) (R 8) [66,33,65,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10565 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10566 : PairBound 9 := { available := 156, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 69 168 304 188 220 156 412), lower := (rows 67 35 69 168 304 32 64 128 256), losses := [] }

theorem u10566 : Upper (D 8) (R 8) [66,33,65,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10566 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10567 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 69 168 400 60 124 188 316), lower := (rows 67 35 69 168 400 32 64 128 256), losses := [] }

theorem u10567 : Upper (D 8) (R 8) [66,33,65,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10567 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10568 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 76 137 148 304 368 432 304), lower := (rows 67 35 76 137 148 32 64 128 256), losses := [] }

theorem u10568 : Upper (D 8) (R 8) [66,33,72,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10568 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10569 : PairBound 9 := { available := 308, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 76 137 176 308 372 436 308), lower := (rows 67 35 76 137 176 32 64 128 256), losses := [] }

theorem u10569 : Upper (D 8) (R 8) [66,33,72,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10569 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10570 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 76 137 276 176 240 176 432), lower := (rows 67 35 76 137 276 32 64 128 256), losses := [] }

theorem u10570 : Upper (D 8) (R 8) [66,33,72,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10570 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10571 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 76 137 304 180 244 180 436), lower := (rows 67 35 76 137 304 32 64 128 256), losses := [] }

theorem u10571 : Upper (D 8) (R 8) [66,33,72,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10571 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10572 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 76 137 400 52 116 180 308), lower := (rows 67 35 76 137 400 32 64 128 256), losses := [] }

theorem u10572 : Upper (D 8) (R 8) [66,33,72,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10572 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10573 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 76 140 176 305 369 433 305), lower := (rows 67 35 76 140 176 32 64 128 256), losses := [] }

theorem u10573 : Upper (D 8) (R 8) [66,33,72,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10573 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10574 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 76 140 304 177 241 177 433), lower := (rows 67 35 76 140 304 32 64 128 256), losses := [] }

theorem u10574 : Upper (D 8) (R 8) [66,33,72,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10574 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10575 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 76 140 400 49 113 177 305), lower := (rows 67 35 76 140 400 32 64 128 256), losses := [] }

theorem u10575 : Upper (D 8) (R 8) [66,33,72,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10575 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10576 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 76 152 145 292 356 420 292), lower := (rows 67 35 76 152 145 32 64 128 256), losses := [] }

theorem u10576 : Upper (D 8) (R 8) [66,33,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10576 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10577 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 76 152 148 289 353 417 289), lower := (rows 67 35 76 152 148 32 64 128 256), losses := [] }

theorem u10577 : Upper (D 8) (R 8) [66,33,72,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10577 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10578 : PairBound 9 := { available := 293, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 76 152 176 293 357 421 293), lower := (rows 67 35 76 152 176 32 64 128 256), losses := [] }

theorem u10578 : Upper (D 8) (R 8) [66,33,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10578 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10579 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 76 152 273 164 228 164 420), lower := (rows 67 35 76 152 273 32 64 128 256), losses := [] }

theorem u10579 : Upper (D 8) (R 8) [66,33,72,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10579 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10580 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 76 152 276 161 225 161 417), lower := (rows 67 35 76 152 276 32 64 128 256), losses := [] }

theorem u10580 : Upper (D 8) (R 8) [66,33,72,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10580 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10581 : Route 9 := (fun mask => (mask,id))

def c10581 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10581 : Upper (D 8) (R 8) [66,33,72,144,288] 13 := by
  apply FastRouting.sound _ _ [66,33,72,144,288] 13 (by decide) (choices 1) [1,4,128] r10581 c10581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2976
  · exact u2977
  · exact u2978

def b10582 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 76 152 400 37 101 165 293), lower := (rows 67 35 76 152 400 32 64 128 256), losses := [] }

theorem u10582 : Upper (D 8) (R 8) [66,33,72,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10582 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10583 : PairBound 9 := { available := 308, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 76 168 145 308 372 436 308), lower := (rows 67 35 76 168 145 32 64 128 256), losses := [] }

theorem u10583 : Upper (D 8) (R 8) [66,33,72,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10583 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10584 : PairBound 9 := { available := 305, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 76 168 148 305 369 433 305), lower := (rows 67 35 76 168 148 32 64 128 256), losses := [] }

theorem u10584 : Upper (D 8) (R 8) [66,33,72,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10584 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10585 : PairBound 9 := { available := 277, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 35 76 168 176 309 341 405 277), lower := (rows 67 35 76 168 176 32 64 128 256), losses := [] }

theorem u10585 : Upper (D 8) (R 8) [66,33,72,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10585 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10586 : PairBound 9 := { available := 180, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 76 168 273 180 244 180 436), lower := (rows 67 35 76 168 273 32 64 128 256), losses := [] }

theorem u10586 : Upper (D 8) (R 8) [66,33,72,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10586 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10587 : Route 9 := (fun mask => (mask,id))

def c10587 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10587 : Upper (D 8) (R 8) [66,33,72,160,260] 13 := by
  apply FastRouting.sound _ _ [66,33,72,160,260] 13 (by decide) (choices 1) [1,16,128] r10587 c10587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2979
  · exact u2980
  · exact u2981

def r10588 : Route 9 := (fun mask => (mask,id))

def c10588 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10588 : Upper (D 8) (R 8) [66,33,72,160,288] 13 := by
  apply FastRouting.sound _ _ [66,33,72,160,288] 13 (by decide) (choices 1) [1,4,16,128] r10588 c10588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2982
  · exact u2983
  · exact u2984
  · exact u2985

def r10589 : Route 9 := (fun mask => (mask,id))

def c10589 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10589 : Upper (D 8) (R 8) [66,33,72,160,384] 13 := by
  apply FastRouting.sound _ _ [66,33,72,160,384] 13 (by decide) (choices 1) [1,4,16] r10589 c10589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2986
  · exact u2987
  · exact u2988

def b10590 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 76 265 148 176 240 176 432), lower := (rows 67 35 76 265 148 32 64 128 256), losses := [] }

theorem u10590 : Upper (D 8) (R 8) [66,33,72,257,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10590 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10591 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 76 265 176 180 244 180 436), lower := (rows 67 35 76 265 176 32 64 128 256), losses := [] }

theorem u10591 : Upper (D 8) (R 8) [66,33,72,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10591 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10592 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 76 268 176 177 241 177 433), lower := (rows 67 35 76 268 176 32 64 128 256), losses := [] }

theorem u10592 : Upper (D 8) (R 8) [66,33,72,260,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10592 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10593 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 76 280 145 164 228 164 420), lower := (rows 67 35 76 280 145 32 64 128 256), losses := [] }

theorem u10593 : Upper (D 8) (R 8) [66,33,72,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10593 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10594 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 76 280 148 161 225 161 417), lower := (rows 67 35 76 280 148 32 64 128 256), losses := [] }

theorem u10594 : Upper (D 8) (R 8) [66,33,72,272,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10594 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10595 : Route 9 := (fun mask => (mask,id))

def c10595 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10595 : Upper (D 8) (R 8) [66,33,72,272,160] 13 := by
  apply FastRouting.sound _ _ [66,33,72,272,160] 13 (by decide) (choices 1) [1,4,128] r10595 c10595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2989
  · exact u2990
  · exact u2991

def b10596 : PairBound 9 := { available := 180, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 76 296 145 180 244 180 436), lower := (rows 67 35 76 296 145 32 64 128 256), losses := [] }

theorem u10596 : Upper (D 8) (R 8) [66,33,72,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10596 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10597 : Route 9 := (fun mask => (mask,id))

def c10597 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10597 : Upper (D 8) (R 8) [66,33,72,288,132] 13 := by
  apply FastRouting.sound _ _ [66,33,72,288,132] 13 (by decide) (choices 1) [1,16,128] r10597 c10597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2992
  · exact u2993
  · exact u2994

def r10598 : Route 9 := (fun mask => (mask,id))

def c10598 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10598 : Upper (D 8) (R 8) [66,33,72,288,160] 13 := by
  apply FastRouting.sound _ _ [66,33,72,288,160] 13 (by decide) (choices 1) [1,4,16,128] r10598 c10598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2995
  · exact u2996
  · exact u2997
  · exact u2998

def b10599 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 76 392 145 52 116 180 308), lower := (rows 67 35 76 392 145 32 64 128 256), losses := [] }

theorem u10599 : Upper (D 8) (R 8) [66,33,72,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10599 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10600 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 76 392 148 49 113 177 305), lower := (rows 67 35 76 392 148 32 64 128 256), losses := [] }

theorem u10600 : Upper (D 8) (R 8) [66,33,72,384,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10600 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10601 : Route 9 := (fun mask => (mask,id))

def c10601 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10601 : Upper (D 8) (R 8) [66,33,72,384,160] 13 := by
  apply FastRouting.sound _ _ [66,33,72,384,160] 13 (by decide) (choices 1) [1,4,16] r10601 c10601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2999
  · exact u3000
  · exact u3001

def b10602 : PairBound 9 := { available := 281, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 100 140 176 313 345 409 281), lower := (rows 67 35 100 140 176 32 64 128 256), losses := [] }

theorem u10602 : Upper (D 8) (R 8) [66,33,96,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10602 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10603 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 100 140 280 177 241 177 433), lower := (rows 67 35 100 140 280 32 64 128 256), losses := [] }

theorem u10603 : Upper (D 8) (R 8) [66,33,96,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10603 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10604 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 100 140 304 185 217 153 409), lower := (rows 67 35 100 140 304 32 64 128 256), losses := [] }

theorem u10604 : Upper (D 8) (R 8) [66,33,96,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10604 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10605 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 100 140 400 57 121 185 313), lower := (rows 67 35 100 140 400 32 64 128 256), losses := [] }

theorem u10605 : Upper (D 8) (R 8) [66,33,96,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10605 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10606 : PairBound 9 := { available := 169, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 100 152 276 169 233 169 425), lower := (rows 67 35 100 152 276 32 64 128 256), losses := [] }

theorem u10606 : Upper (D 8) (R 8) [66,33,96,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10606 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10607 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 100 152 280 165 229 165 421), lower := (rows 67 35 100 152 280 32 64 128 256), losses := [] }

theorem u10607 : Upper (D 8) (R 8) [66,33,96,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10607 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10608 : PairBound 9 := { available := 141, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 100 152 304 173 205 141 397), lower := (rows 67 35 100 152 304 32 64 128 256), losses := [] }

theorem u10608 : Upper (D 8) (R 8) [66,33,96,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10608 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10609 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 100 168 276 185 217 153 409), lower := (rows 67 35 100 168 276 32 64 128 256), losses := [] }

theorem u10609 : Upper (D 8) (R 8) [66,33,96,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10609 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10610 : PairBound 9 := { available := 149, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 100 168 280 181 213 149 405), lower := (rows 67 35 100 168 280 32 64 128 256), losses := [] }

theorem u10610 : Upper (D 8) (R 8) [66,33,96,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10610 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10611 : PairBound 9 := { available := 29, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 100 168 400 61 93 157 285), lower := (rows 67 35 100 168 400 32 64 128 256), losses := [] }

theorem u10611 : Upper (D 8) (R 8) [66,33,96,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10611 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10612 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 133 140 280 112 112 240 368), lower := (rows 67 35 133 140 280 32 64 128 256), losses := [] }

theorem u10612 : Upper (D 8) (R 8) [66,33,129,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10612 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10613 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 133 140 304 120 120 248 376), lower := (rows 67 35 133 140 304 32 64 128 256), losses := [] }

theorem u10613 : Upper (D 8) (R 8) [66,33,129,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10613 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10614 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 133 140 336 56 120 184 312), lower := (rows 67 35 133 140 336 32 64 128 256), losses := [] }

theorem u10614 : Upper (D 8) (R 8) [66,33,129,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10614 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10615 : PairBound 9 := { available := 104, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 133 152 276 104 104 232 360), lower := (rows 67 35 133 152 276 32 64 128 256), losses := [] }

theorem u10615 : Upper (D 8) (R 8) [66,33,129,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10615 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10616 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 133 152 280 100 100 228 356), lower := (rows 67 35 133 152 280 32 64 128 256), losses := [] }

theorem u10616 : Upper (D 8) (R 8) [66,33,129,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10616 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10617 : PairBound 9 := { available := 108, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 133 152 304 108 108 236 364), lower := (rows 67 35 133 152 304 32 64 128 256), losses := [] }

theorem u10617 : Upper (D 8) (R 8) [66,33,129,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10617 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10618 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 133 152 336 44 108 172 300), lower := (rows 67 35 133 152 336 32 64 128 256), losses := [] }

theorem u10618 : Upper (D 8) (R 8) [66,33,129,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10618 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10619 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 133 168 276 120 120 248 376), lower := (rows 67 35 133 168 276 32 64 128 256), losses := [] }

theorem u10619 : Upper (D 8) (R 8) [66,33,129,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10619 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u10619
end Delivery.IrregularNine14.P08
