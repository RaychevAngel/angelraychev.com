import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0307
import IrregularNine14P07C0308
import IrregularNine14P07C0309

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r34080 : Route 9 := (fun mask => (mask,id))

def c34080 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34080 : Upper (D 7) (R 7) [34,65,40,260,129] 13 := by
  apply FastRouting.sound _ _ [34,65,40,260,129] 13 (by decide) (choices 1) [2,16,64,128] r34080 c34080
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18431
  · exact u18432
  · exact u18433
  · exact u18434

def r34081 : Route 9 := (fun mask => (mask,id))

def c34081 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34081 : Upper (D 7) (R 7) [34,65,40,260,130] 13 := by
  apply FastRouting.sound _ _ [34,65,40,260,130] 13 (by decide) (choices 1) [1,16,64,128] r34081 c34081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18435
  · exact u18436
  · exact u18437
  · exact u18438

def r34082 : Route 9 := (fun mask => (mask,id))

def c34082 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34082 : Upper (D 7) (R 7) [34,65,40,260,192] 13 := by
  apply FastRouting.sound _ _ [34,65,40,260,192] 13 (by decide) (choices 1) [1,2,16,128] r34082 c34082
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18439
  · exact u18440
  · exact u18441
  · exact u18442

def r34083 : Route 9 := (fun mask => (mask,id))

def c34083 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34083 : Upper (D 7) (R 7) [34,65,40,272,129] 13 := by
  apply FastRouting.sound _ _ [34,65,40,272,129] 13 (by decide) (choices 1) [2,4,64,128] r34083 c34083
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18443
  · exact u18444
  · exact u18445
  · exact u18446

def r34084 : Route 9 := (fun mask => (mask,id))

def c34084 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34084 : Upper (D 7) (R 7) [34,65,40,272,130] 13 := by
  apply FastRouting.sound _ _ [34,65,40,272,130] 13 (by decide) (choices 1) [1,4,64,128] r34084 c34084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18447
  · exact u18448
  · exact u18449
  · exact u18450

def r34085 : Route 9 := (fun mask => (mask,id))

def c34085 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34085 : Upper (D 7) (R 7) [34,65,40,272,132] 13 := by
  apply FastRouting.sound _ _ [34,65,40,272,132] 13 (by decide) (choices 1) [1,2,64,128] r34085 c34085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18451
  · exact u18452
  · exact u18453
  · exact u18454

def r34086 : Route 9 := (fun mask => (mask,id))

def c34086 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34086 : Upper (D 7) (R 7) [34,65,40,272,192] 13 := by
  apply FastRouting.sound _ _ [34,65,40,272,192] 13 (by decide) (choices 1) [1,2,4,128] r34086 c34086
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18455
  · exact u18456
  · exact u18457
  · exact u18458

def r34087 : Route 9 := (fun mask => (mask,id))

def c34087 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34087 : Upper (D 7) (R 7) [34,65,40,320,129] 13 := by
  apply FastRouting.sound _ _ [34,65,40,320,129] 13 (by decide) (choices 1) [2,4,16,128] r34087 c34087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18459
  · exact u18460
  · exact u18461
  · exact u18462

def r34088 : Route 9 := (fun mask => (mask,id))

def c34088 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34088 : Upper (D 7) (R 7) [34,65,40,320,130] 13 := by
  apply FastRouting.sound _ _ [34,65,40,320,130] 13 (by decide) (choices 1) [1,4,16,128] r34088 c34088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18463
  · exact u18464
  · exact u18465
  · exact u18466

def r34089 : Route 9 := (fun mask => (mask,id))

def c34089 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34089 : Upper (D 7) (R 7) [34,65,40,320,132] 13 := by
  apply FastRouting.sound _ _ [34,65,40,320,132] 13 (by decide) (choices 1) [1,2,16,128] r34089 c34089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18467
  · exact u18468
  · exact u18469
  · exact u18470

def r34090 : Route 9 := (fun mask => (mask,id))

def c34090 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34090 : Upper (D 7) (R 7) [34,65,40,384,129] 13 := by
  apply FastRouting.sound _ _ [34,65,40,384,129] 13 (by decide) (choices 1) [2,4,16,64] r34090 c34090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18471
  · exact u18472
  · exact u18473
  · exact u18474

def r34091 : Route 9 := (fun mask => (mask,id))

def c34091 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34091 : Upper (D 7) (R 7) [34,65,40,384,130] 13 := by
  apply FastRouting.sound _ _ [34,65,40,384,130] 13 (by decide) (choices 1) [1,4,16,64] r34091 c34091
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18475
  · exact u18476
  · exact u18477
  · exact u18478

def r34092 : Route 9 := (fun mask => (mask,id))

def c34092 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34092 : Upper (D 7) (R 7) [34,65,40,384,132] 13 := by
  apply FastRouting.sound _ _ [34,65,40,384,132] 13 (by decide) (choices 1) [1,2,16,64] r34092 c34092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18479
  · exact u18480
  · exact u18481
  · exact u18482

def r34093 : Route 9 := (fun mask => (mask,id))

def c34093 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34093 : Upper (D 7) (R 7) [34,65,40,384,192] 13 := by
  apply FastRouting.sound _ _ [34,65,40,384,192] 13 (by decide) (choices 1) [1,2,4,16] r34093 c34093
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18483
  · exact u18484
  · exact u18485
  · exact u18486

def r34094 : Route 9 := (fun mask => (mask,id))

def c34094 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34094 : Upper (D 7) (R 7) [34,65,96,129,130] 13 := by
  apply FastRouting.sound _ _ [34,65,96,129,130] 13 (by decide) (choices 1) [4,8,16,256] r34094 c34094
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18487
  · exact u18488
  · exact u18489
  · exact u18490

def r34095 : Route 9 := (fun mask => (mask,id))

def c34095 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34095 : Upper (D 7) (R 7) [34,65,96,129,132] 13 := by
  apply FastRouting.sound _ _ [34,65,96,129,132] 13 (by decide) (choices 1) [2,8,16,256] r34095 c34095
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18491
  · exact u18492
  · exact u18493
  · exact u18494

def b34096 : PairBound 9 := { available := 278, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 35 67 100 137 152 310 342 406 278), lower := (rows 35 67 100 137 152 32 64 128 256), losses := [] }

theorem u34096 : Upper (D 7) (R 7) [34,65,96,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34096 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34097 : Route 9 := (fun mask => (mask,id))

def c34097 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34097 : Upper (D 7) (R 7) [34,65,96,129,258] 13 := by
  apply FastRouting.sound _ _ [34,65,96,129,258] 13 (by decide) (choices 1) [4,8,16,128] r34097 c34097
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18495
  · exact u18496
  · exact u18497
  · exact u18498

def r34098 : Route 9 := (fun mask => (mask,id))

def c34098 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34098 : Upper (D 7) (R 7) [34,65,96,129,260] 13 := by
  apply FastRouting.sound _ _ [34,65,96,129,260] 13 (by decide) (choices 1) [2,8,16,128] r34098 c34098
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18499
  · exact u18500
  · exact u18501
  · exact u18502

def r34099 : Route 9 := (fun mask => (mask,id))

def c34099 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34099 : Upper (D 7) (R 7) [34,65,96,129,264] 13 := by
  apply FastRouting.sound _ _ [34,65,96,129,264] 13 (by decide) (choices 1) [2,4,16,128] r34099 c34099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18503
  · exact u18504
  · exact u18505
  · exact u18506

def r34100 : Route 9 := (fun mask => (mask,id))

def c34100 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34100 : Upper (D 7) (R 7) [34,65,96,129,384] 13 := by
  apply FastRouting.sound _ _ [34,65,96,129,384] 13 (by decide) (choices 1) [2,4,8,16] r34100 c34100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18507
  · exact u18508
  · exact u18509
  · exact u18510

def b34101 : PairBound 9 := { available := 275, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 35 67 100 140 152 307 339 403 275), lower := (rows 35 67 100 140 152 32 64 128 256), losses := [] }

theorem u34101 : Upper (D 7) (R 7) [34,65,96,132,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34101 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34102 : Route 9 := (fun mask => (mask,id))

def c34102 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34102 : Upper (D 7) (R 7) [34,65,96,132,257] 13 := by
  apply FastRouting.sound _ _ [34,65,96,132,257] 13 (by decide) (choices 1) [2,8,16,128] r34102 c34102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18511
  · exact u18512
  · exact u18513
  · exact u18514

def r34103 : Route 9 := (fun mask => (mask,id))

def c34103 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34103 : Upper (D 7) (R 7) [34,65,96,132,264] 13 := by
  apply FastRouting.sound _ _ [34,65,96,132,264] 13 (by decide) (choices 1) [1,2,16,128] r34103 c34103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18515
  · exact u18516
  · exact u18517
  · exact u18518

def r34104 : Route 9 := (fun mask => (mask,id))

def c34104 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34104 : Upper (D 7) (R 7) [34,65,96,132,384] 13 := by
  apply FastRouting.sound _ _ [34,65,96,132,384] 13 (by decide) (choices 1) [1,2,8,16] r34104 c34104
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18519
  · exact u18520
  · exact u18521
  · exact u18522

def b34105 : PairBound 9 := { available := 263, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 67 100 152 152 295 327 391 263), lower := (rows 35 67 100 152 152 32 64 128 256), losses := [] }

theorem u34105 : Upper (D 7) (R 7) [34,65,96,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34105 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34106 : Route 9 := (fun mask => (mask,id))

def c34106 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34106 : Upper (D 7) (R 7) [34,65,96,144,257] 13 := by
  apply FastRouting.sound _ _ [34,65,96,144,257] 13 (by decide) (choices 1) [2,4,8,128] r34106 c34106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18523
  · exact u18524
  · exact u18525
  · exact u18526

def r34107 : Route 9 := (fun mask => (mask,id))

def c34107 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34107 : Upper (D 7) (R 7) [34,65,96,144,260] 13 := by
  apply FastRouting.sound _ _ [34,65,96,144,260] 13 (by decide) (choices 1) [1,2,8,128] r34107 c34107
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18527
  · exact u18528
  · exact u18529
  · exact u18530

def r34108 : Route 9 := (fun mask => (mask,id))

def c34108 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34108 : Upper (D 7) (R 7) [34,65,96,144,264] 13 := by
  apply FastRouting.sound _ _ [34,65,96,144,264] 13 (by decide) (choices 1) [1,2,4,128] r34108 c34108
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18531
  · exact u18532
  · exact u18533
  · exact u18534

def b34109 : PairBound 9 := { available := 15, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 67 100 152 400 47 79 143 271), lower := (rows 35 67 100 152 400 32 64 128 256), losses := [] }

theorem u34109 : Upper (D 7) (R 7) [34,65,96,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34109 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34110 : Route 9 := (fun mask => (mask,id))

def c34110 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34110 : Upper (D 7) (R 7) [34,65,129,130,260] 13 := by
  apply FastRouting.sound _ _ [34,65,129,130,260] 13 (by decide) (choices 1) [8,16,64] r34110 c34110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18535
  · exact u18536
  · exact u18537

def r34111 : Route 9 := (fun mask => (mask,id))

def c34111 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34111 : Upper (D 7) (R 7) [34,65,129,130,288] 13 := by
  apply FastRouting.sound _ _ [34,65,129,130,288] 13 (by decide) (choices 1) [4,8,16,64] r34111 c34111
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18538
  · exact u18539
  · exact u18540
  · exact u18541

def b34112 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 67 133 140 274 120 120 248 376), lower := (rows 35 67 133 140 274 32 64 128 256), losses := [] }

theorem u34112 : Upper (D 7) (R 7) [34,65,129,132,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34112 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34113 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 67 133 140 280 114 114 242 370), lower := (rows 35 67 133 140 280 32 64 128 256), losses := [] }

theorem u34113 : Upper (D 7) (R 7) [34,65,129,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34113 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34114 : PairBound 9 := { available := 90, camps := [{ cop := 2, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 67 133 140 304 122 90 218 346), lower := (rows 35 67 133 140 304 32 64 128 256), losses := [] }

theorem u34114 : Upper (D 7) (R 7) [34,65,129,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34114 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34115 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 67 133 140 336 58 122 186 314), lower := (rows 35 67 133 140 336 32 64 128 256), losses := [] }

theorem u34115 : Upper (D 7) (R 7) [34,65,129,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34115 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34116 : Route 9 := (fun mask => (mask,id))

def c34116 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34116 : Upper (D 7) (R 7) [34,65,129,144,258] 13 := by
  apply FastRouting.sound _ _ [34,65,129,144,258] 13 (by decide) (choices 1) [4,8,64] r34116 c34116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18542
  · exact u18543
  · exact u18544

def r34117 : Route 9 := (fun mask => (mask,id))

def c34117 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34117 : Upper (D 7) (R 7) [34,65,129,144,260] 13 := by
  apply FastRouting.sound _ _ [34,65,129,144,260] 13 (by decide) (choices 1) [2,8,64] r34117 c34117
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18545
  · exact u18546
  · exact u18547

def r34118 : Route 9 := (fun mask => (mask,id))

def c34118 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34118 : Upper (D 7) (R 7) [34,65,129,144,264] 13 := by
  apply FastRouting.sound _ _ [34,65,129,144,264] 13 (by decide) (choices 1) [2,4,64] r34118 c34118
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18548
  · exact u18549
  · exact u18550

def r34119 : Route 9 := (fun mask => (mask,id))

def c34119 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34119 : Upper (D 7) (R 7) [34,65,129,144,288] 13 := by
  apply FastRouting.sound _ _ [34,65,129,144,288] 13 (by decide) (choices 1) [2,4,8,64] r34119 c34119
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18551
  · exact u18552
  · exact u18553
  · exact u18554

def r34120 : Route 9 := (fun mask => (mask,id))

def c34120 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34120 : Upper (D 7) (R 7) [34,65,129,144,320] 13 := by
  apply FastRouting.sound _ _ [34,65,129,144,320] 13 (by decide) (choices 1) [2,4,8] r34120 c34120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18555
  · exact u18556
  · exact u18557

def r34121 : Route 9 := (fun mask => (mask,id))

def c34121 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34121 : Upper (D 7) (R 7) [34,65,129,160,258] 13 := by
  apply FastRouting.sound _ _ [34,65,129,160,258] 13 (by decide) (choices 1) [4,8,16,64] r34121 c34121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18558
  · exact u18559
  · exact u18560
  · exact u18561

def r34122 : Route 9 := (fun mask => (mask,id))

def c34122 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34122 : Upper (D 7) (R 7) [34,65,129,160,260] 13 := by
  apply FastRouting.sound _ _ [34,65,129,160,260] 13 (by decide) (choices 1) [2,8,16,64] r34122 c34122
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18562
  · exact u18563
  · exact u18564
  · exact u18565

def r34123 : Route 9 := (fun mask => (mask,id))

def c34123 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34123 : Upper (D 7) (R 7) [34,65,129,160,264] 13 := by
  apply FastRouting.sound _ _ [34,65,129,160,264] 13 (by decide) (choices 1) [2,4,16,64] r34123 c34123
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18566
  · exact u18567
  · exact u18568
  · exact u18569

def r34124 : Route 9 := (fun mask => (mask,id))

def c34124 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34124 : Upper (D 7) (R 7) [34,65,129,160,320] 13 := by
  apply FastRouting.sound _ _ [34,65,129,160,320] 13 (by decide) (choices 1) [2,4,8,16] r34124 c34124
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18570
  · exact u18571
  · exact u18572
  · exact u18573

def r34125 : Route 9 := (fun mask => (mask,id))

def c34125 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34125 : Upper (D 7) (R 7) [34,65,129,192,258] 13 := by
  apply FastRouting.sound _ _ [34,65,129,192,258] 13 (by decide) (choices 1) [4,8,16] r34125 c34125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18574
  · exact u18575
  · exact u18576

def r34126 : Route 9 := (fun mask => (mask,id))

def c34126 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34126 : Upper (D 7) (R 7) [34,65,129,192,260] 13 := by
  apply FastRouting.sound _ _ [34,65,129,192,260] 13 (by decide) (choices 1) [2,8,16] r34126 c34126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18577
  · exact u18578
  · exact u18579

def r34127 : Route 9 := (fun mask => (mask,id))

def c34127 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34127 : Upper (D 7) (R 7) [34,65,129,192,264] 13 := by
  apply FastRouting.sound _ _ [34,65,129,192,264] 13 (by decide) (choices 1) [2,4,16] r34127 c34127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18580
  · exact u18581
  · exact u18582

def r34128 : Route 9 := (fun mask => (mask,id))

def c34128 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34128 : Upper (D 7) (R 7) [34,65,129,192,288] 13 := by
  apply FastRouting.sound _ _ [34,65,129,192,288] 13 (by decide) (choices 1) [2,4,8,16] r34128 c34128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18583
  · exact u18584
  · exact u18585
  · exact u18586

def b34129 : PairBound 9 := { available := 114, camps := [{ cop := 7, region := 12, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 35 67 140 140 273 114 114 242 370), lower := (rows 35 67 140 140 273 32 64 128 256), losses := [] }

theorem u34129 : Upper (D 7) (R 7) [34,65,136,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34129 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34130 : PairBound 9 := { available := 83, camps := [{ cop := 7, region := 12, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 35 67 140 140 304 115 83 211 339), lower := (rows 35 67 140 140 304 32 64 128 256), losses := [] }

theorem u34130 : Upper (D 7) (R 7) [34,65,136,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34130 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34131 : PairBound 9 := { available := 102, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 35 67 140 152 273 102 102 230 358), lower := (rows 35 67 140 152 273 32 64 128 256), losses := [] }

theorem u34131 : Upper (D 7) (R 7) [34,65,136,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34131 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34132 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 35 67 140 152 276 99 99 227 355), lower := (rows 35 67 140 152 276 32 64 128 256), losses := [] }

theorem u34132 : Upper (D 7) (R 7) [34,65,136,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34132 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34133 : PairBound 9 := { available := 71, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 35 67 140 152 304 103 71 199 327), lower := (rows 35 67 140 152 304 32 64 128 256), losses := [] }

theorem u34133 : Upper (D 7) (R 7) [34,65,136,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34133 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34134 : PairBound 9 := { available := 86, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 35 67 140 168 273 118 86 214 342), lower := (rows 35 67 140 168 273 32 64 128 256), losses := [] }

theorem u34134 : Upper (D 7) (R 7) [34,65,136,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34134 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34135 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 35 67 140 168 274 117 85 213 341), lower := (rows 35 67 140 168 274 32 64 128 256), losses := [] }

theorem u34135 : Upper (D 7) (R 7) [34,65,136,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34136 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 35 67 140 168 276 115 83 211 339), lower := (rows 35 67 140 168 276 32 64 128 256), losses := [] }

theorem u34136 : Upper (D 7) (R 7) [34,65,136,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34136 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34137 : PairBound 9 := { available := 23, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 35 67 140 168 336 55 87 151 279), lower := (rows 35 67 140 168 336 32 64 128 256), losses := [] }

theorem u34137 : Upper (D 7) (R 7) [34,65,136,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34137 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34138 : Route 9 := (fun mask => (mask,id))

def c34138 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34138 : Upper (D 7) (R 7) [34,65,136,257,160] 13 := by
  apply FastRouting.sound _ _ [34,65,136,257,160] 13 (by decide) (choices 1) [2,4,16,64] r34138 c34138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18587
  · exact u18588
  · exact u18589
  · exact u18590

def r34139 : Route 9 := (fun mask => (mask,id))

def c34139 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34139 : Upper (D 7) (R 7) [34,65,136,257,192] 13 := by
  apply FastRouting.sound _ _ [34,65,136,257,192] 13 (by decide) (choices 1) [2,4,16] r34139 c34139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18591
  · exact u18592
  · exact u18593

#print axioms u34139
end Delivery.IrregularNine14.P07
