import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0045
import IrregularNine14P08C0046

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10020 : PairBound 9 := { available := 393, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 7 164 56 112 425 457 393 393), lower := (rows 67 7 164 56 112 32 64 128 256), losses := [] }

theorem u10020 : Upper (D 8) (R 8) [66,5,160,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10020 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10021 : PairBound 9 := { available := 360, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 56 145 360 360 488 360), lower := (rows 67 7 164 56 145 32 64 128 256), losses := [] }

theorem u10021 : Upper (D 8) (R 8) [66,5,160,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10021 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10022 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 7 164 56 152 353 353 481 353), lower := (rows 67 7 164 56 152 32 64 128 256), losses := [] }

theorem u10022 : Upper (D 8) (R 8) [66,5,160,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10022 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10023 : PairBound 9 := { available := 329, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 7 164 56 176 361 329 457 329), lower := (rows 67 7 164 56 176 32 64 128 256), losses := [] }

theorem u10023 : Upper (D 8) (R 8) [66,5,160,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10023 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10024 : Route 9 := (fun mask => (mask,id))

def c10024 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u10024 : Upper (D 8) (R 8) [66,5,160,48,192] 13 := by
  apply FastRouting.sound _ _ [66,5,160,48,192] 13 (by decide) (choices 1) [1,8,256] r10024 c10024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2721
  · exact u2722
  · exact u2723

def b10025 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 56 273 232 232 232 488), lower := (rows 67 7 164 56 273 32 64 128 256), losses := [] }

theorem u10025 : Upper (D 8) (R 8) [66,5,160,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10025 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10026 : Route 9 := (fun mask => (mask,id))

def c10026 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10026 : Upper (D 8) (R 8) [66,5,160,48,264] 13 := by
  apply FastRouting.sound _ _ [66,5,160,48,264] 13 (by decide) (choices 1) [1,64,128] r10026 c10026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2724
  · exact u2725
  · exact u2726

def b10027 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 7 164 56 304 233 201 201 457), lower := (rows 67 7 164 56 304 32 64 128 256), losses := [] }

theorem u10027 : Upper (D 8) (R 8) [66,5,160,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10027 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10028 : Route 9 := (fun mask => (mask,id))

def c10028 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10028 : Upper (D 8) (R 8) [66,5,160,48,320] 13 := by
  apply FastRouting.sound _ _ [66,5,160,48,320] 13 (by decide) (choices 1) [1,8,128] r10028 c10028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2727
  · exact u2728
  · exact u2729

def r10029 : Route 9 := (fun mask => (mask,id))

def c10029 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10029 : Upper (D 8) (R 8) [66,5,160,48,384] 13 := by
  apply FastRouting.sound _ _ [66,5,160,48,384] 13 (by decide) (choices 1) [1,8,64] r10029 c10029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2730
  · exact u2731
  · exact u2732

def b10030 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 164 73 152 304 368 432 304), lower := (rows 67 7 164 73 152 32 64 128 256), losses := [] }

theorem u10030 : Upper (D 8) (R 8) [66,5,160,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10030 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10031 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 164 73 280 176 240 176 432), lower := (rows 67 7 164 73 280 32 64 128 256), losses := [] }

theorem u10031 : Upper (D 8) (R 8) [66,5,160,65,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10031 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10032 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 164 73 304 184 248 184 440), lower := (rows 67 7 164 73 304 32 64 128 256), losses := [] }

theorem u10032 : Upper (D 8) (R 8) [66,5,160,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10032 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10033 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 164 73 400 56 120 184 312), lower := (rows 67 7 164 73 400 32 64 128 256), losses := [] }

theorem u10033 : Upper (D 8) (R 8) [66,5,160,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10033 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10034 : PairBound 9 := { available := 296, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 88 145 296 360 424 296), lower := (rows 67 7 164 88 145 32 64 128 256), losses := [] }

theorem u10034 : Upper (D 8) (R 8) [66,5,160,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10034 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10035 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 164 88 152 289 353 417 289), lower := (rows 67 7 164 88 152 32 64 128 256), losses := [] }

theorem u10035 : Upper (D 8) (R 8) [66,5,160,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10035 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10036 : PairBound 9 := { available := 297, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 7 164 88 176 297 361 425 297), lower := (rows 67 7 164 88 176 32 64 128 256), losses := [] }

theorem u10036 : Upper (D 8) (R 8) [66,5,160,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10036 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10037 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 88 273 168 232 168 424), lower := (rows 67 7 164 88 273 32 64 128 256), losses := [] }

theorem u10037 : Upper (D 8) (R 8) [66,5,160,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10037 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10038 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 164 88 280 161 225 161 417), lower := (rows 67 7 164 88 280 32 64 128 256), losses := [] }

theorem u10038 : Upper (D 8) (R 8) [66,5,160,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10038 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10039 : Route 9 := (fun mask => (mask,id))

def c10039 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10039 : Upper (D 8) (R 8) [66,5,160,80,288] 13 := by
  apply FastRouting.sound _ _ [66,5,160,80,288] 13 (by decide) (choices 1) [1,8,128] r10039 c10039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2733
  · exact u2734
  · exact u2735

def r10040 : Route 9 := (fun mask => (mask,id))

def c10040 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10040 : Upper (D 8) (R 8) [66,5,160,80,384] 13 := by
  apply FastRouting.sound _ _ [66,5,160,80,384] 13 (by decide) (choices 1) [1,8] r10040 c10040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2736
  · exact u2737

def b10041 : PairBound 9 := { available := 312, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 104 145 312 376 440 312), lower := (rows 67 7 164 104 145 32 64 128 256), losses := [] }

theorem u10041 : Upper (D 8) (R 8) [66,5,160,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10041 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10042 : Route 9 := (fun mask => (mask,id))

def c10042 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u10042 : Upper (D 8) (R 8) [66,5,160,96,136] 13 := by
  apply FastRouting.sound _ _ [66,5,160,96,136] 13 (by decide) (choices 1) [1,16,256] r10042 c10042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2738
  · exact u2739
  · exact u2740

def b10043 : PairBound 9 := { available := 281, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 7 164 104 176 313 345 409 281), lower := (rows 67 7 164 104 176 32 64 128 256), losses := [] }

theorem u10043 : Upper (D 8) (R 8) [66,5,160,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10043 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10044 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 104 273 184 248 184 440), lower := (rows 67 7 164 104 273 32 64 128 256), losses := [] }

theorem u10044 : Upper (D 8) (R 8) [66,5,160,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10044 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10045 : Route 9 := (fun mask => (mask,id))

def c10045 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10045 : Upper (D 8) (R 8) [66,5,160,96,264] 13 := by
  apply FastRouting.sound _ _ [66,5,160,96,264] 13 (by decide) (choices 1) [1,16,128] r10045 c10045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2741
  · exact u2742
  · exact u2743

def r10046 : Route 9 := (fun mask => (mask,id))

def c10046 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10046 : Upper (D 8) (R 8) [66,5,160,96,288] 13 := by
  apply FastRouting.sound _ _ [66,5,160,96,288] 13 (by decide) (choices 1) [1,8,16,128] r10046 c10046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2744
  · exact u2745
  · exact u2746
  · exact u2747

def r10047 : Route 9 := (fun mask => (mask,id))

def c10047 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10047 : Upper (D 8) (R 8) [66,5,160,96,384] 13 := by
  apply FastRouting.sound _ _ [66,5,160,96,384] 13 (by decide) (choices 1) [1,8,16] r10047 c10047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2748
  · exact u2749
  · exact u2750

def b10048 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 137 280 112 112 240 368), lower := (rows 67 7 164 137 280 32 64 128 256), losses := [] }

theorem u10048 : Upper (D 8) (R 8) [66,5,160,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10048 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10049 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 137 304 120 120 248 376), lower := (rows 67 7 164 137 304 32 64 128 256), losses := [] }

theorem u10049 : Upper (D 8) (R 8) [66,5,160,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10049 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10050 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 137 336 56 120 184 312), lower := (rows 67 7 164 137 336 32 64 128 256), losses := [] }

theorem u10050 : Upper (D 8) (R 8) [66,5,160,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10050 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10051 : PairBound 9 := { available := 104, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 152 273 104 104 232 360), lower := (rows 67 7 164 152 273 32 64 128 256), losses := [] }

theorem u10051 : Upper (D 8) (R 8) [66,5,160,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10051 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10052 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 164 152 280 97 97 225 353), lower := (rows 67 7 164 152 280 32 64 128 256), losses := [] }

theorem u10052 : Upper (D 8) (R 8) [66,5,160,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10052 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10053 : Route 9 := (fun mask => (mask,id))

def c10053 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10053 : Upper (D 8) (R 8) [66,5,160,144,288] 13 := by
  apply FastRouting.sound _ _ [66,5,160,144,288] 13 (by decide) (choices 1) [1,8,64] r10053 c10053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2751
  · exact u2752
  · exact u2753

def r10054 : Route 9 := (fun mask => (mask,id))

def c10054 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10054 : Upper (D 8) (R 8) [66,5,160,144,320] 13 := by
  apply FastRouting.sound _ _ [66,5,160,144,320] 13 (by decide) (choices 1) [1,8] r10054 c10054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2754
  · exact u2755

def b10055 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 7 164 168 280 113 113 241 369), lower := (rows 67 7 164 168 280 32 64 128 256), losses := [] }

theorem u10055 : Upper (D 8) (R 8) [66,5,160,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10055 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10056 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 7 164 168 304 121 89 217 345), lower := (rows 67 7 164 168 304 32 64 128 256), losses := [] }

theorem u10056 : Upper (D 8) (R 8) [66,5,160,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10056 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10057 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 7 164 168 336 57 121 185 313), lower := (rows 67 7 164 168 336 32 64 128 256), losses := [] }

theorem u10057 : Upper (D 8) (R 8) [66,5,160,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10057 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10058 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 200 273 56 120 184 312), lower := (rows 67 7 164 200 273 32 64 128 256), losses := [] }

theorem u10058 : Upper (D 8) (R 8) [66,5,160,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10058 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10059 : Route 9 := (fun mask => (mask,id))

def c10059 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10059 : Upper (D 8) (R 8) [66,5,160,192,264] 13 := by
  apply FastRouting.sound _ _ [66,5,160,192,264] 13 (by decide) (choices 1) [1,16] r10059 c10059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2756
  · exact u2757

def r10060 : Route 9 := (fun mask => (mask,id))

def c10060 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10060 : Upper (D 8) (R 8) [66,5,160,192,288] 13 := by
  apply FastRouting.sound _ _ [66,5,160,192,288] 13 (by decide) (choices 1) [1,8,16] r10060 c10060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2758
  · exact u2759
  · exact u2760

def b10061 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 268 56 49 224 224 224 480), lower := (rows 67 7 268 56 49 32 64 128 256), losses := [] }

theorem u10061 : Upper (D 8) (R 8) [66,5,264,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10061 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10062 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 268 56 81 160 224 160 416), lower := (rows 67 7 268 56 81 32 64 128 256), losses := [] }

theorem u10062 : Upper (D 8) (R 8) [66,5,264,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10062 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10063 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 7 268 56 112 161 225 161 417), lower := (rows 67 7 268 56 112 32 64 128 256), losses := [] }

theorem u10063 : Upper (D 8) (R 8) [66,5,264,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10063 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10064 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 268 56 145 224 224 224 480), lower := (rows 67 7 268 56 145 32 64 128 256), losses := [] }

theorem u10064 : Upper (D 8) (R 8) [66,5,264,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10064 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10065 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 7 268 56 176 225 225 225 481), lower := (rows 67 7 268 56 176 32 64 128 256), losses := [] }

theorem u10065 : Upper (D 8) (R 8) [66,5,264,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10065 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10066 : Route 9 := (fun mask => (mask,id))

def c10066 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10066 : Upper (D 8) (R 8) [66,5,264,48,192] 13 := by
  apply FastRouting.sound _ _ [66,5,264,48,192] 13 (by decide) (choices 1) [1,128] r10066 c10066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2761
  · exact u2762

def b10067 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 268 152 49 224 224 224 480), lower := (rows 67 7 268 152 49 32 64 128 256), losses := [] }

theorem u10067 : Upper (D 8) (R 8) [66,5,264,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10067 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10068 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 268 152 81 160 224 160 416), lower := (rows 67 7 268 152 81 32 64 128 256), losses := [] }

theorem u10068 : Upper (D 8) (R 8) [66,5,264,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10068 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10069 : Route 9 := (fun mask => (mask,id))

def c10069 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10069 : Upper (D 8) (R 8) [66,5,264,144,96] 13 := by
  apply FastRouting.sound _ _ [66,5,264,144,96] 13 (by decide) (choices 1) [1,128] r10069 c10069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2763
  · exact u2764

def b10070 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 268 152 145 96 96 224 352), lower := (rows 67 7 268 152 145 32 64 128 256), losses := [] }

theorem u10070 : Upper (D 8) (R 8) [66,5,264,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10070 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10071 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 268 152 176 97 97 225 353), lower := (rows 67 7 268 152 176 32 64 128 256), losses := [] }

theorem u10071 : Upper (D 8) (R 8) [66,5,264,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10071 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10072 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 268 152 208 33 97 161 289), lower := (rows 67 7 268 152 208 32 64 128 256), losses := [] }

theorem u10072 : Upper (D 8) (R 8) [66,5,264,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10072 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10073 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 268 168 49 240 240 240 496), lower := (rows 67 7 268 168 49 32 64 128 256), losses := [] }

theorem u10073 : Upper (D 8) (R 8) [66,5,264,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10073 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10074 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 268 168 81 176 240 176 432), lower := (rows 67 7 268 168 81 32 64 128 256), losses := [] }

theorem u10074 : Upper (D 8) (R 8) [66,5,264,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10074 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10075 : Route 9 := (fun mask => (mask,id))

def c10075 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10075 : Upper (D 8) (R 8) [66,5,264,160,96] 13 := by
  apply FastRouting.sound _ _ [66,5,264,160,96] 13 (by decide) (choices 1) [1,16,128] r10075 c10075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2765
  · exact u2766
  · exact u2767

def b10076 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 268 168 145 112 112 240 368), lower := (rows 67 7 268 168 145 32 64 128 256), losses := [] }

theorem u10076 : Upper (D 8) (R 8) [66,5,264,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10076 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10077 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 7 268 168 176 113 113 241 369), lower := (rows 67 7 268 168 176 32 64 128 256), losses := [] }

theorem u10077 : Upper (D 8) (R 8) [66,5,264,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10077 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10078 : Route 9 := (fun mask => (mask,id))

def c10078 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10078 : Upper (D 8) (R 8) [66,5,264,160,192] 13 := by
  apply FastRouting.sound _ _ [66,5,264,160,192] 13 (by decide) (choices 1) [1,16] r10078 c10078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2768
  · exact u2769

def b10079 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 25 56 224 224 224 480), lower := (rows 67 7 292 25 56 32 64 128 256), losses := [] }

theorem u10079 : Upper (D 8) (R 8) [66,5,288,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10079 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u10079
end Delivery.IrregularNine14.P08
