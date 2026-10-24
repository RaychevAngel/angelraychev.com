import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0060
import IrregularNine14P09C0061
import IrregularNine14P09C0062

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r7020 : Route 9 := (fun mask => (mask,id))

def c7020 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7020 : Upper (D 9) (R 9) [34,5,72,160,192] 13 := by
  apply FastRouting.sound _ _ [34,5,72,160,192] 13 (by decide) (choices 1) [1,16,256] r7020 c7020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3612
  · exact u3613
  · exact u3614

def r7021 : Route 9 := (fun mask => (mask,id))

def c7021 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u7021 : Upper (D 9) (R 9) [34,5,72,160,257] 13 := by
  apply FastRouting.sound _ _ [34,5,72,160,257] 13 (by decide) (choices 1) [16,64,128,256] r7021 c7021
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3615
  · exact u3616
  · exact u3617
  · exact u3618

def r7022 : Route 9 := (fun mask => (mask,id))

def c7022 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7022 : Upper (D 9) (R 9) [34,5,72,160,320] 13 := by
  apply FastRouting.sound _ _ [34,5,72,160,320] 13 (by decide) (choices 1) [1,16,128,256] r7022 c7022
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3619
  · exact u3620
  · exact u3621
  · exact u3622

def r7023 : Route 9 := (fun mask => (mask,id))

def c7023 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7023 : Upper (D 9) (R 9) [34,5,72,160,384] 13 := by
  apply FastRouting.sound _ _ [34,5,72,160,384] 13 (by decide) (choices 1) [1,16,64,256] r7023 c7023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3623
  · exact u3624
  · exact u3625
  · exact u3626

def b7024 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 16, targets := 448 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(4,6),(4,7),(4,8)], upper := (rows 35 7 76 392 49 496 464 464 464), lower := (rows 35 7 76 392 49 32 64 128 256), losses := [] }

theorem u7024 : Upper (D 9) (R 9) [34,5,72,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7024 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7025 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7025 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7025 : Upper (D 9) (R 9) [34,5,72,384,65] 13 := by
  apply FastRouting.sound _ _ [34,5,72,384,65] 13 (by decide) (choices 1) [16,128] r7025 c7025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3627
  · exact u3628

def r7026 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7026 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7026 : Upper (D 9) (R 9) [34,5,72,384,96] 13 := by
  apply FastRouting.sound _ _ [34,5,72,384,96] 13 (by decide) (choices 1) [1,16,128] r7026 c7026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3629
  · exact u3630
  · exact u3631

def r7027 : Route 9 := (fun mask => (mask,id))

def c7027 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7027 : Upper (D 9) (R 9) [34,5,72,384,129] 13 := by
  apply FastRouting.sound _ _ [34,5,72,384,129] 13 (by decide) (choices 1) [16,64,256] r7027 c7027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3632
  · exact u3633
  · exact u3634

def r7028 : Route 9 := (fun mask => (mask,id))

def c7028 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7028 : Upper (D 9) (R 9) [34,5,72,384,160] 13 := by
  apply FastRouting.sound _ _ [34,5,72,384,160] 13 (by decide) (choices 1) [1,16,64,256] r7028 c7028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3635
  · exact u3636
  · exact u3637
  · exact u3638

def r7029 : Route 9 := (fun mask => (mask,id))

def c7029 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7029 : Upper (D 9) (R 9) [34,5,72,384,192] 13 := by
  apply FastRouting.sound _ _ [34,5,72,384,192] 13 (by decide) (choices 1) [1,16,256] r7029 c7029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3639
  · exact u3640
  · exact u3641

def b7030 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5),(4,6)], upper := (rows 35 7 76 392 400 113 113 241 369), lower := (rows 35 7 76 392 400 32 64 128 256), losses := [] }

theorem u7030 : Upper (D 9) (R 9) [34,5,72,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7030 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7031 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 24, targets := 448 }], pairs := [(3,6),(3,7),(3,8),(4,6),(4,7)], upper := (rows 35 7 196 25 56 480 448 448 448), lower := (rows 35 7 196 25 56 32 64 128 256), losses := [] }

theorem u7031 : Upper (D 9) (R 9) [34,5,192,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7031 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7032 : Route 9 := (fun mask => (mask,id))

def c7032 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7032 : Upper (D 9) (R 9) [34,5,192,17,72] 13 := by
  apply FastRouting.sound _ _ [34,5,192,17,72] 13 (by decide) (choices 1) [128,256] r7032 c7032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3642
  · exact u3643

def r7033 : Route 9 := (fun mask => (mask,id))

def c7033 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7033 : Upper (D 9) (R 9) [34,5,192,17,96] 13 := by
  apply FastRouting.sound _ _ [34,5,192,17,96] 13 (by decide) (choices 1) [8,128,256] r7033 c7033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3644
  · exact u3645
  · exact u3646

def b7034 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 16, targets := 289 },{ cop := 4, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5),(4,8)], upper := (rows 35 7 196 25 208 296 360 424 296), lower := (rows 35 7 196 25 208 32 64 128 256), losses := [] }

theorem u7034 : Upper (D 9) (R 9) [34,5,192,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7034 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7035 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7035 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7035 : Upper (D 9) (R 9) [34,5,192,17,264] 13 := by
  apply FastRouting.sound _ _ [34,5,192,17,264] 13 (by decide) (choices 1) [64,256] r7035 c7035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3647
  · exact u3648

def r7036 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7036 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | _ => 0)

theorem u7036 : Upper (D 9) (R 9) [34,5,192,17,288] 13 := by
  apply FastRouting.sound _ _ [34,5,192,17,288] 13 (by decide) (choices 1) [8,64,256] r7036 c7036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3649
  · exact u3650
  · exact u3651

def r7037 : Route 9 := (fun mask => (mask,id))

def c7037 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7037 : Upper (D 9) (R 9) [34,5,192,17,320] 13 := by
  apply FastRouting.sound _ _ [34,5,192,17,320] 13 (by decide) (choices 1) [8,128,256] r7037 c7037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3652
  · exact u3653
  · exact u3654

def b7038 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 7 196 41 88 432 464 400 400), lower := (rows 35 7 196 41 88 32 64 128 256), losses := [] }

theorem u7038 : Upper (D 9) (R 9) [34,5,192,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7038 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7039 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 7 196 41 280 496 464 464 464), lower := (rows 35 7 196 41 280 32 64 128 256), losses := [] }

theorem u7039 : Upper (D 9) (R 9) [34,5,192,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7039 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7040 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 7 196 41 336 440 472 408 408), lower := (rows 35 7 196 41 336 32 64 128 256), losses := [] }

theorem u7040 : Upper (D 9) (R 9) [34,5,192,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7040 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7041 : Route 9 := (fun mask => (mask,id))

def c7041 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7041 : Upper (D 9) (R 9) [34,5,192,48,65] 13 := by
  apply FastRouting.sound _ _ [34,5,192,48,65] 13 (by decide) (choices 1) [8,128,256] r7041 c7041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3655
  · exact u3656
  · exact u3657

def r7042 : Route 9 := (fun mask => (mask,id))

def c7042 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7042 : Upper (D 9) (R 9) [34,5,192,48,72] 13 := by
  apply FastRouting.sound _ _ [34,5,192,48,72] 13 (by decide) (choices 1) [1,128,256] r7042 c7042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3658
  · exact u3659
  · exact u3660

def b7043 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 16, targets := 289 },{ cop := 4, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5),(4,8)], upper := (rows 35 7 196 56 208 297 329 393 265), lower := (rows 35 7 196 56 208 32 64 128 256), losses := [] }

theorem u7043 : Upper (D 9) (R 9) [34,5,192,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7043 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7044 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7044 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | _ => 0)

theorem u7044 : Upper (D 9) (R 9) [34,5,192,48,257] 13 := by
  apply FastRouting.sound _ _ [34,5,192,48,257] 13 (by decide) (choices 1) [8,64,256] r7044 c7044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3661
  · exact u3662
  · exact u3663

def r7045 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7045 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7045 : Upper (D 9) (R 9) [34,5,192,48,264] 13 := by
  apply FastRouting.sound _ _ [34,5,192,48,264] 13 (by decide) (choices 1) [1,64,256] r7045 c7045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3664
  · exact u3665
  · exact u3666

def r7046 : Route 9 := (fun mask => (mask,id))

def c7046 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7046 : Upper (D 9) (R 9) [34,5,192,48,320] 13 := by
  apply FastRouting.sound _ _ [34,5,192,48,320] 13 (by decide) (choices 1) [1,8,128,256] r7046 c7046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3667
  · exact u3668
  · exact u3669
  · exact u3670

def r7047 : Route 9 := (fun mask => (mask,id))

def c7047 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7047 : Upper (D 9) (R 9) [34,5,192,65,136] 13 := by
  apply FastRouting.sound _ _ [34,5,192,65,136] 13 (by decide) (choices 1) [16,256] r7047 c7047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3671
  · exact u3672

def r7048 : Route 9 := (fun mask => (mask,id))

def c7048 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7048 : Upper (D 9) (R 9) [34,5,192,65,160] 13 := by
  apply FastRouting.sound _ _ [34,5,192,65,160] 13 (by decide) (choices 1) [8,16,256] r7048 c7048
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3673
  · exact u3674
  · exact u3675

def r7049 : Route 9 := (fun mask => (mask,id))

def c7049 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7049 : Upper (D 9) (R 9) [34,5,192,65,264] 13 := by
  apply FastRouting.sound _ _ [34,5,192,65,264] 13 (by decide) (choices 1) [16,128,256] r7049 c7049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3676
  · exact u3677
  · exact u3678

def r7050 : Route 9 := (fun mask => (mask,id))

def c7050 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u7050 : Upper (D 9) (R 9) [34,5,192,65,288] 13 := by
  apply FastRouting.sound _ _ [34,5,192,65,288] 13 (by decide) (choices 1) [8,16,128,256] r7050 c7050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3679
  · exact u3680
  · exact u3681
  · exact u3682

def r7051 : Route 9 := (fun mask => (mask,id))

def c7051 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7051 : Upper (D 9) (R 9) [34,5,192,65,384] 13 := by
  apply FastRouting.sound _ _ [34,5,192,65,384] 13 (by decide) (choices 1) [8,16,256] r7051 c7051
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3683
  · exact u3684
  · exact u3685

def b7052 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 24, targets := 289 }], pairs := [(3,0),(3,5),(3,8),(4,0),(4,5)], upper := (rows 35 7 196 88 152 289 353 417 289), lower := (rows 35 7 196 88 152 32 64 128 256), losses := [] }

theorem u7052 : Upper (D 9) (R 9) [34,5,192,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7052 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7053 : Route 9 := (fun mask => (mask,id))

def c7053 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7053 : Upper (D 9) (R 9) [34,5,192,80,160] 13 := by
  apply FastRouting.sound _ _ [34,5,192,80,160] 13 (by decide) (choices 1) [1,8,256] r7053 c7053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3686
  · exact u3687
  · exact u3688

def r7054 : Route 9 := (fun mask => (mask,id))

def c7054 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7054 : Upper (D 9) (R 9) [34,5,192,80,257] 13 := by
  apply FastRouting.sound _ _ [34,5,192,80,257] 13 (by decide) (choices 1) [8,128,256] r7054 c7054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3689
  · exact u3690
  · exact u3691

def r7055 : Route 9 := (fun mask => (mask,id))

def c7055 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7055 : Upper (D 9) (R 9) [34,5,192,80,264] 13 := by
  apply FastRouting.sound _ _ [34,5,192,80,264] 13 (by decide) (choices 1) [1,128,256] r7055 c7055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3692
  · exact u3693
  · exact u3694

def r7056 : Route 9 := (fun mask => (mask,id))

def c7056 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7056 : Upper (D 9) (R 9) [34,5,192,80,288] 13 := by
  apply FastRouting.sound _ _ [34,5,192,80,288] 13 (by decide) (choices 1) [1,8,128,256] r7056 c7056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3695
  · exact u3696
  · exact u3697
  · exact u3698

def r7057 : Route 9 := (fun mask => (mask,id))

def c7057 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7057 : Upper (D 9) (R 9) [34,5,192,80,384] 13 := by
  apply FastRouting.sound _ _ [34,5,192,80,384] 13 (by decide) (choices 1) [1,8,256] r7057 c7057
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3699
  · exact u3700
  · exact u3701

def r7058 : Route 9 := (fun mask => (mask,id))

def c7058 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u7058 : Upper (D 9) (R 9) [34,5,192,96,257] 13 := by
  apply FastRouting.sound _ _ [34,5,192,96,257] 13 (by decide) (choices 1) [8,16,128,256] r7058 c7058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3702
  · exact u3703
  · exact u3704
  · exact u3705

def r7059 : Route 9 := (fun mask => (mask,id))

def c7059 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7059 : Upper (D 9) (R 9) [34,5,192,96,264] 13 := by
  apply FastRouting.sound _ _ [34,5,192,96,264] 13 (by decide) (choices 1) [1,16,128,256] r7059 c7059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3706
  · exact u3707
  · exact u3708
  · exact u3709

def r7060 : Route 9 := (fun mask => (mask,id))

def c7060 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7060 : Upper (D 9) (R 9) [34,5,192,96,384] 13 := by
  apply FastRouting.sound _ _ [34,5,192,96,384] 13 (by decide) (choices 1) [1,8,16,256] r7060 c7060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3710
  · exact u3711
  · exact u3712
  · exact u3713

def b7061 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 8, targets := 289 },{ cop := 3, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5),(3,8)], upper := (rows 35 7 196 200 273 312 376 440 312), lower := (rows 35 7 196 200 273 32 64 128 256), losses := [] }

theorem u7061 : Upper (D 9) (R 9) [34,5,192,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7061 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7062 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 8, targets := 289 },{ cop := 3, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5),(3,8)], upper := (rows 35 7 196 200 280 305 369 433 305), lower := (rows 35 7 196 200 280 32 64 128 256), losses := [] }

theorem u7062 : Upper (D 9) (R 9) [34,5,192,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7062 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7063 : PairBound 9 := { available := 281, camps := [{ cop := 2, region := 8, targets := 289 },{ cop := 3, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5),(3,8)], upper := (rows 35 7 196 200 304 313 345 409 281), lower := (rows 35 7 196 200 304 32 64 128 256), losses := [] }

theorem u7063 : Upper (D 9) (R 9) [34,5,192,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7063 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7064 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 224 },{ cop := 4, region := 231, targets := 256 }], pairs := [(0,8),(1,8),(4,5),(4,6),(4,7)], upper := (rows 35 7 196 265 280 240 240 240 496), lower := (rows 35 7 196 265 280 32 64 128 256), losses := [] }

theorem u7064 : Upper (D 9) (R 9) [34,5,192,257,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7064 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7065 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7065 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u7065 : Upper (D 9) (R 9) [34,5,192,257,288] 13 := by
  apply FastRouting.sound _ _ [34,5,192,257,288] 13 (by decide) (choices 1) [8,16,64] r7065 c7065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3714
  · exact u3715
  · exact u3716

def r7066 : Route 9 := (fun mask => (mask,id))

def c7066 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7066 : Upper (D 9) (R 9) [34,5,192,257,320] 13 := by
  apply FastRouting.sound _ _ [34,5,192,257,320] 13 (by decide) (choices 1) [8,16,128] r7066 c7066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3717
  · exact u3718
  · exact u3719

def b7067 : PairBound 9 := { available := 225, camps := [{ cop := 8, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7),(4,0)], upper := (rows 35 7 196 280 280 225 225 225 481), lower := (rows 35 7 196 280 280 32 64 128 256), losses := [] }

theorem u7067 : Upper (D 9) (R 9) [34,5,192,272,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7067 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7068 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 7 196 280 304 233 201 201 457), lower := (rows 35 7 196 280 304 32 64 128 256), losses := [] }

theorem u7068 : Upper (D 9) (R 9) [34,5,192,272,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7068 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7069 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 7 196 280 336 169 233 169 425), lower := (rows 35 7 196 280 336 32 64 128 256), losses := [] }

theorem u7069 : Upper (D 9) (R 9) [34,5,192,272,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7069 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7070 : Route 9 := (fun mask => (mask,id))

def c7070 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7070 : Upper (D 9) (R 9) [34,5,192,288,320] 13 := by
  apply FastRouting.sound _ _ [34,5,192,288,320] 13 (by decide) (choices 1) [1,8,16,128] r7070 c7070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3720
  · exact u3721
  · exact u3722
  · exact u3723

theorem m7071_16 : Upper (D 9) (R 9) [34,5,192,320,384,16] 13 :=
  permutation_upper _ _ _ [34,5,192,320,384,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3725

def r7071 : Route 9 := (fun mask => (mask,id))

def c7071 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7071 : Upper (D 9) (R 9) [34,5,192,320,384] 13 := by
  apply FastRouting.sound _ _ [34,5,192,320,384] 13 (by decide) (choices 1) [1,8,16] r7071 c7071
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3724
  · exact u3725
  · exact m7071_16

def b7072 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 15, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 14 21 73 112 416 448 384 384), lower := (rows 35 14 21 73 112 32 64 128 256), losses := [] }

theorem u7072 : Upper (D 9) (R 9) [34,12,17,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7072 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7073 : Route 9 := (fun mask => (mask,id))

def c7073 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7073 : Upper (D 9) (R 9) [34,12,17,65,160] 13 := by
  apply FastRouting.sound _ _ [34,12,17,65,160] 13 (by decide) (choices 1) [64,128,256] r7073 c7073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3726
  · exact u3727
  · exact u3728

def r7074 : Route 9 := (fun mask => (mask,id))

def c7074 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7074 : Upper (D 9) (R 9) [34,12,17,65,192] 13 := by
  apply FastRouting.sound _ _ [34,12,17,65,192] 13 (by decide) (choices 1) [128,256] r7074 c7074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3729
  · exact u3730

def r7075 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7075 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7075 : Upper (D 9) (R 9) [34,12,17,65,384] 13 := by
  apply FastRouting.sound _ _ [34,12,17,65,384] 13 (by decide) (choices 1) [64,128] r7075 c7075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3731
  · exact u3732

def b7076 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 23, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 14 21 104 81 416 448 384 384), lower := (rows 35 14 21 104 81 32 64 128 256), losses := [] }

theorem u7076 : Upper (D 9) (R 9) [34,12,17,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7076 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7077 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 4, targets := 448 },{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(2,6),(2,7),(2,8),(4,5)], upper := (rows 35 14 21 104 145 480 448 448 448), lower := (rows 35 14 21 104 145 32 64 128 256), losses := [] }

theorem u7077 : Upper (D 9) (R 9) [34,12,17,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7077 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7078 : Route 9 := (fun mask => (mask,id))

def c7078 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7078 : Upper (D 9) (R 9) [34,12,17,96,192] 13 := by
  apply FastRouting.sound _ _ [34,12,17,96,192] 13 (by decide) (choices 1) [1,128,256] r7078 c7078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3733
  · exact u3734
  · exact u3735

def r7079 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7079 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7079 : Upper (D 9) (R 9) [34,12,17,96,384] 13 := by
  apply FastRouting.sound _ _ [34,12,17,96,384] 13 (by decide) (choices 1) [1,64,128] r7079 c7079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3736
  · exact u3737
  · exact u3738

#print axioms u7079
end Delivery.IrregularNine14.P09
