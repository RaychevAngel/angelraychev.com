import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0290
import IrregularNine14P06C0291
import IrregularNine14P06C0292

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r34020 : Route 9 := (fun mask => (mask,id))

def c34020 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34020 : Upper (D 6) (R 6) [10,160,66,48,260] 13 := by
  apply FastRouting.sound _ _ [10,160,66,48,260] 13 (by decide) (choices 1) [1,4,64] r34020 c34020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17417
  · exact u17418
  · exact u17419

def r34021 : Route 9 := (fun mask => (mask,id))

def c34021 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34021 : Upper (D 6) (R 6) [10,160,66,48,320] 13 := by
  apply FastRouting.sound _ _ [10,160,66,48,320] 13 (by decide) (choices 1) [1,4] r34021 c34021
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17420
  · exact u17421

def b34022 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 25, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 70 88 21 293 357 421 293), lower := (rows 11 162 70 88 21 32 64 128 256), losses := [] }

theorem u34022 : Upper (D 6) (R 6) [10,160,66,80,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34022 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34023 : Route 9 := (fun mask => (mask,id))

def c34023 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34023 : Upper (D 6) (R 6) [10,160,66,80,33] 13 := by
  apply FastRouting.sound _ _ [10,160,66,80,33] 13 (by decide) (choices 1) [1,4,256] r34023 c34023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17422
  · exact u17423
  · exact u17424

def r34024 : Route 9 := (fun mask => (mask,id))

def c34024 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34024 : Upper (D 6) (R 6) [10,160,66,80,36] 13 := by
  apply FastRouting.sound _ _ [10,160,66,80,36] 13 (by decide) (choices 1) [1,4,256] r34024 c34024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17425
  · exact u17426
  · exact u17427

def r34025 : Route 9 := (fun mask => (mask,id))

def c34025 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34025 : Upper (D 6) (R 6) [10,160,66,80,257] 13 := by
  apply FastRouting.sound _ _ [10,160,66,80,257] 13 (by decide) (choices 1) [1,4] r34025 c34025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17428
  · exact u17429

def r34026 : Route 9 := (fun mask => (mask,id))

def c34026 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34026 : Upper (D 6) (R 6) [10,160,66,80,260] 13 := by
  apply FastRouting.sound _ _ [10,160,66,80,260] 13 (by decide) (choices 1) [1,4] r34026 c34026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17430
  · exact u17431

def r34027 : Route 9 := (fun mask => (mask,id))

def c34027 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34027 : Upper (D 6) (R 6) [10,160,66,80,288] 13 := by
  apply FastRouting.sound _ _ [10,160,66,80,288] 13 (by decide) (choices 1) [1,4] r34027 c34027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17432
  · exact u17433

def b34028 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 360, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 70 104 21 309 341 405 277), lower := (rows 11 162 70 104 21 32 64 128 256), losses := [] }

theorem u34028 : Upper (D 6) (R 6) [10,160,66,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34028 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34029 : Route 9 := (fun mask => (mask,id))

def c34029 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34029 : Upper (D 6) (R 6) [10,160,66,96,257] 13 := by
  apply FastRouting.sound _ _ [10,160,66,96,257] 13 (by decide) (choices 1) [1,4,16] r34029 c34029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17434
  · exact u17435
  · exact u17436

def r34030 : Route 9 := (fun mask => (mask,id))

def c34030 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34030 : Upper (D 6) (R 6) [10,160,66,96,260] 13 := by
  apply FastRouting.sound _ _ [10,160,66,96,260] 13 (by decide) (choices 1) [1,4,16] r34030 c34030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17437
  · exact u17438
  · exact u17439

def b34031 : PairBound 9 := { available := 116, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 360, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 162 70 265 21 116 116 244 372), lower := (rows 11 162 70 265 21 32 64 128 256), losses := [] }

theorem u34031 : Upper (D 6) (R 6) [10,160,66,257,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34032 : Route 9 := (fun mask => (mask,id))

def c34032 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34032 : Upper (D 6) (R 6) [10,160,66,257,33] 13 := by
  apply FastRouting.sound _ _ [10,160,66,257,33] 13 (by decide) (choices 1) [4,16,64] r34032 c34032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17440
  · exact u17441
  · exact u17442

def r34033 : Route 9 := (fun mask => (mask,id))

def c34033 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34033 : Upper (D 6) (R 6) [10,160,66,257,36] 13 := by
  apply FastRouting.sound _ _ [10,160,66,257,36] 13 (by decide) (choices 1) [1,4,16,64] r34033 c34033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17443
  · exact u17444
  · exact u17445
  · exact u17446

def r34034 : Route 9 := (fun mask => (mask,id))

def c34034 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34034 : Upper (D 6) (R 6) [10,160,66,257,65] 13 := by
  apply FastRouting.sound _ _ [10,160,66,257,65] 13 (by decide) (choices 1) [4,16] r34034 c34034
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17447
  · exact u17448

def b34035 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 70 265 84 53 117 181 309), lower := (rows 11 162 70 265 84 32 64 128 256), losses := [] }

theorem u34035 : Upper (D 6) (R 6) [10,160,66,257,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34035 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34036 : Route 9 := (fun mask => (mask,id))

def c34036 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34036 : Upper (D 6) (R 6) [10,160,66,257,96] 13 := by
  apply FastRouting.sound _ _ [10,160,66,257,96] 13 (by decide) (choices 1) [1,4,16] r34036 c34036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17449
  · exact u17450
  · exact u17451

def r34037 : Route 9 := (fun mask => (mask,id))

def c34037 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34037 : Upper (D 6) (R 6) [10,160,66,260,5] 13 := by
  apply FastRouting.sound _ _ [10,160,66,260,5] 13 (by decide) (choices 1) [1,16,64] r34037 c34037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17452
  · exact u17453
  · exact u17454

def r34038 : Route 9 := (fun mask => (mask,id))

def c34038 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34038 : Upper (D 6) (R 6) [10,160,66,260,33] 13 := by
  apply FastRouting.sound _ _ [10,160,66,260,33] 13 (by decide) (choices 1) [1,4,16,64] r34038 c34038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17455
  · exact u17456
  · exact u17457
  · exact u17458

def r34039 : Route 9 := (fun mask => (mask,id))

def c34039 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34039 : Upper (D 6) (R 6) [10,160,66,260,36] 13 := by
  apply FastRouting.sound _ _ [10,160,66,260,36] 13 (by decide) (choices 1) [1,16,64] r34039 c34039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17459
  · exact u17460
  · exact u17461

def r34040 : Route 9 := (fun mask => (mask,id))

def c34040 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34040 : Upper (D 6) (R 6) [10,160,66,260,65] 13 := by
  apply FastRouting.sound _ _ [10,160,66,260,65] 13 (by decide) (choices 1) [1,4,16] r34040 c34040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17462
  · exact u17463
  · exact u17464

def b34041 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 70 268 84 49 113 177 305), lower := (rows 11 162 70 268 84 32 64 128 256), losses := [] }

theorem u34041 : Upper (D 6) (R 6) [10,160,66,260,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34041 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34042 : Route 9 := (fun mask => (mask,id))

def c34042 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34042 : Upper (D 6) (R 6) [10,160,66,260,96] 13 := by
  apply FastRouting.sound _ _ [10,160,66,260,96] 13 (by decide) (choices 1) [1,4,16] r34042 c34042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17465
  · exact u17466
  · exact u17467

def r34043 : Route 9 := (fun mask => (mask,id))

def c34043 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34043 : Upper (D 6) (R 6) [10,160,66,272,5] 13 := by
  apply FastRouting.sound _ _ [10,160,66,272,5] 13 (by decide) (choices 1) [1,4,64] r34043 c34043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17468
  · exact u17469
  · exact u17470

def r34044 : Route 9 := (fun mask => (mask,id))

def c34044 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34044 : Upper (D 6) (R 6) [10,160,66,272,33] 13 := by
  apply FastRouting.sound _ _ [10,160,66,272,33] 13 (by decide) (choices 1) [1,4,64] r34044 c34044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17471
  · exact u17472
  · exact u17473

def r34045 : Route 9 := (fun mask => (mask,id))

def c34045 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34045 : Upper (D 6) (R 6) [10,160,66,272,36] 13 := by
  apply FastRouting.sound _ _ [10,160,66,272,36] 13 (by decide) (choices 1) [1,4,64] r34045 c34045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17474
  · exact u17475
  · exact u17476

def r34046 : Route 9 := (fun mask => (mask,id))

def c34046 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34046 : Upper (D 6) (R 6) [10,160,66,272,65] 13 := by
  apply FastRouting.sound _ _ [10,160,66,272,65] 13 (by decide) (choices 1) [1,4] r34046 c34046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17477
  · exact u17478

def b34047 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 70 280 84 37 101 165 293), lower := (rows 11 162 70 280 84 32 64 128 256), losses := [] }

theorem u34047 : Upper (D 6) (R 6) [10,160,66,272,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34048 : Route 9 := (fun mask => (mask,id))

def c34048 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34048 : Upper (D 6) (R 6) [10,160,66,272,96] 13 := by
  apply FastRouting.sound _ _ [10,160,66,272,96] 13 (by decide) (choices 1) [1,4] r34048 c34048
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17479
  · exact u17480

def b34049 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 4, region := 360, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 70 296 21 117 85 213 341), lower := (rows 11 162 70 296 21 32 64 128 256), losses := [] }

theorem u34049 : Upper (D 6) (R 6) [10,160,66,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34049 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34050 : Route 9 := (fun mask => (mask,id))

def c34050 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34050 : Upper (D 6) (R 6) [10,160,66,288,65] 13 := by
  apply FastRouting.sound _ _ [10,160,66,288,65] 13 (by decide) (choices 1) [1,4,16] r34050 c34050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17481
  · exact u17482
  · exact u17483

def b34051 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 70 296 84 53 85 149 277), lower := (rows 11 162 70 296 84 32 64 128 256), losses := [] }

theorem u34051 : Upper (D 6) (R 6) [10,160,66,288,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34051 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34052 : Route 9 := (fun mask => (mask,id))

def c34052 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34052 : Upper (D 6) (R 6) [10,160,66,320,5] 13 := by
  apply FastRouting.sound _ _ [10,160,66,320,5] 13 (by decide) (choices 1) [1,4,16] r34052 c34052
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17484
  · exact u17485
  · exact u17486

def r34053 : Route 9 := (fun mask => (mask,id))

def c34053 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34053 : Upper (D 6) (R 6) [10,160,66,320,33] 13 := by
  apply FastRouting.sound _ _ [10,160,66,320,33] 13 (by decide) (choices 1) [1,4,16] r34053 c34053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17487
  · exact u17488
  · exact u17489

def r34054 : Route 9 := (fun mask => (mask,id))

def c34054 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34054 : Upper (D 6) (R 6) [10,160,66,320,36] 13 := by
  apply FastRouting.sound _ _ [10,160,66,320,36] 13 (by decide) (choices 1) [1,4,16] r34054 c34054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17490
  · exact u17491
  · exact u17492

def b34055 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 84 13 19 356 356 484 356), lower := (rows 11 162 84 13 19 32 64 128 256), losses := [] }

theorem u34055 : Upper (D 6) (R 6) [10,160,80,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34055 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34056 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 162 84 13 21 354 354 482 354), lower := (rows 11 162 84 13 21 32 64 128 256), losses := [] }

theorem u34056 : Upper (D 6) (R 6) [10,160,80,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34056 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34057 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 84 13 22 353 353 481 353), lower := (rows 11 162 84 13 22 32 64 128 256), losses := [] }

theorem u34057 : Upper (D 6) (R 6) [10,160,80,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34057 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34058 : Route 9 := (fun mask => (mask,id))

def c34058 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u34058 : Upper (D 6) (R 6) [10,160,80,5,33] 13 := by
  apply FastRouting.sound _ _ [10,160,80,5,33] 13 (by decide) (choices 1) [2,4,64,256] r34058 c34058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17493
  · exact u17494
  · exact u17495
  · exact u17496

def b34059 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 162 84 13 50 357 325 453 325), lower := (rows 11 162 84 13 50 32 64 128 256), losses := [] }

theorem u34059 : Upper (D 6) (R 6) [10,160,80,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34059 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34060 : Route 9 := (fun mask => (mask,id))

def c34060 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u34060 : Upper (D 6) (R 6) [10,160,80,5,36] 13 := by
  apply FastRouting.sound _ _ [10,160,80,5,36] 13 (by decide) (choices 1) [1,2,64,256] r34060 c34060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17497
  · exact u17498
  · exact u17499
  · exact u17500

def b34061 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 12, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 162 84 13 81 294 358 422 294), lower := (rows 11 162 84 13 81 32 64 128 256), losses := [] }

theorem u34061 : Upper (D 6) (R 6) [10,160,80,5,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34061 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34062 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 84 13 82 293 357 421 293), lower := (rows 11 162 84 13 82 32 64 128 256), losses := [] }

theorem u34062 : Upper (D 6) (R 6) [10,160,80,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34063 : PairBound 9 := { available := 291, camps := [{ cop := 6, region := 20, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 162 84 13 84 291 355 419 291), lower := (rows 11 162 84 13 84 32 64 128 256), losses := [] }

theorem u34063 : Upper (D 6) (R 6) [10,160,80,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34064 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 84 13 112 295 327 391 263), lower := (rows 11 162 84 13 112 32 64 128 256), losses := [] }

theorem u34064 : Upper (D 6) (R 6) [10,160,80,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34064 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34065 : Route 9 := (fun mask => (mask,id))

def c34065 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34065 : Upper (D 6) (R 6) [10,160,80,5,257] 13 := by
  apply FastRouting.sound _ _ [10,160,80,5,257] 13 (by decide) (choices 1) [2,4,64] r34065 c34065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17501
  · exact u17502
  · exact u17503

def r34066 : Route 9 := (fun mask => (mask,id))

def c34066 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34066 : Upper (D 6) (R 6) [10,160,80,5,258] 13 := by
  apply FastRouting.sound _ _ [10,160,80,5,258] 13 (by decide) (choices 1) [1,4,64] r34066 c34066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17504
  · exact u17505
  · exact u17506

def r34067 : Route 9 := (fun mask => (mask,id))

def c34067 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34067 : Upper (D 6) (R 6) [10,160,80,5,260] 13 := by
  apply FastRouting.sound _ _ [10,160,80,5,260] 13 (by decide) (choices 1) [1,2,64] r34067 c34067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17507
  · exact u17508
  · exact u17509

def r34068 : Route 9 := (fun mask => (mask,id))

def c34068 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34068 : Upper (D 6) (R 6) [10,160,80,5,288] 13 := by
  apply FastRouting.sound _ _ [10,160,80,5,288] 13 (by decide) (choices 1) [1,2,4,64] r34068 c34068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17510
  · exact u17511
  · exact u17512
  · exact u17513

def b34069 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 171, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 84 13 336 39 103 167 295), lower := (rows 11 162 84 13 336 32 64 128 256), losses := [] }

theorem u34069 : Upper (D 6) (R 6) [10,160,80,5,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34069 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34070 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 11 162 84 44 19 357 325 453 325), lower := (rows 11 162 84 44 19 32 64 128 256), losses := [] }

theorem u34070 : Upper (D 6) (R 6) [10,160,80,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34070 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34071 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 3, region := 451, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 162 84 44 21 355 323 451 323), lower := (rows 11 162 84 44 21 32 64 128 256), losses := [] }

theorem u34071 : Upper (D 6) (R 6) [10,160,80,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34071 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34072 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 3, region := 451, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 162 84 44 22 353 321 449 321), lower := (rows 11 162 84 44 22 32 64 128 256), losses := [] }

theorem u34072 : Upper (D 6) (R 6) [10,160,80,36,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34072 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34073 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 84 44 81 295 327 391 263), lower := (rows 11 162 84 44 81 32 64 128 256), losses := [] }

theorem u34073 : Upper (D 6) (R 6) [10,160,80,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34073 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34074 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 84 44 82 293 325 389 261), lower := (rows 11 162 84 44 82 32 64 128 256), losses := [] }

theorem u34074 : Upper (D 6) (R 6) [10,160,80,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34074 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34075 : PairBound 9 := { available := 259, camps := [{ cop := 6, region := 20, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 162 84 44 84 291 323 387 259), lower := (rows 11 162 84 44 84 32 64 128 256), losses := [] }

theorem u34075 : Upper (D 6) (R 6) [10,160,80,36,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34075 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34076 : Route 9 := (fun mask => (mask,id))

def c34076 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34076 : Upper (D 6) (R 6) [10,160,80,36,257] 13 := by
  apply FastRouting.sound _ _ [10,160,80,36,257] 13 (by decide) (choices 1) [1,2,4,64] r34076 c34076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17514
  · exact u17515
  · exact u17516
  · exact u17517

def r34077 : Route 9 := (fun mask => (mask,id))

def c34077 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34077 : Upper (D 6) (R 6) [10,160,80,36,258] 13 := by
  apply FastRouting.sound _ _ [10,160,80,36,258] 13 (by decide) (choices 1) [1,4,64] r34077 c34077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17518
  · exact u17519
  · exact u17520

def b34078 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 3, region := 195, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 162 84 44 276 99 67 195 323), lower := (rows 11 162 84 44 276 32 64 128 256), losses := [] }

theorem u34078 : Upper (D 6) (R 6) [10,160,80,36,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34078 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34079 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 171, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 84 44 336 39 71 135 263), lower := (rows 11 162 84 44 336 32 64 128 256), losses := [] }

theorem u34079 : Upper (D 6) (R 6) [10,160,80,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34079 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u34079
end Delivery.IrregularNine14.P06
