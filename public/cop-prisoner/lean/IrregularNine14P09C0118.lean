import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0062
import IrregularNine14P09C0063
import IrregularNine14P09C0064

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7080 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 20, targets := 448 }], pairs := [(2,6),(2,7),(2,8),(4,6),(4,7)], upper := (rows 35 14 21 200 49 480 448 448 448), lower := (rows 35 14 21 200 49 32 64 128 256), losses := [] }

theorem u7080 : Upper (D 9) (R 9) [34,12,17,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7080 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7081 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 4, targets := 416 },{ cop := 2, region := 490, targets := 1 }], pairs := [(1,0),(2,5),(2,7),(2,8),(3,0)], upper := (rows 35 14 21 200 81 416 480 416 416), lower := (rows 35 14 21 200 81 32 64 128 256), losses := [] }

theorem u7081 : Upper (D 9) (R 9) [34,12,17,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7081 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7082 : Route 9 := (fun mask => (mask,id))

def c7082 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7082 : Upper (D 9) (R 9) [34,12,17,192,96] 13 := by
  apply FastRouting.sound _ _ [34,12,17,192,96] 13 (by decide) (choices 1) [1,128,256] r7082 c7082
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3739
  · exact u3740
  · exact u3741

def b7083 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 16, targets := 289 },{ cop := 4, region := 8, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5),(4,8)], upper := (rows 35 14 21 200 208 289 353 417 289), lower := (rows 35 14 21 200 208 32 64 128 256), losses := [] }

theorem u7083 : Upper (D 9) (R 9) [34,12,17,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7083 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7084 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 4, targets := 480 },{ cop := 2, region := 490, targets := 1 }], pairs := [(1,0),(2,5),(2,6),(2,7),(2,8)], upper := (rows 35 14 21 200 273 480 480 480 480), lower := (rows 35 14 21 200 273 32 64 128 256), losses := [] }

theorem u7084 : Upper (D 9) (R 9) [34,12,17,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7084 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7085 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7085 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7085 : Upper (D 9) (R 9) [34,12,17,192,288] 13 := by
  apply FastRouting.sound _ _ [34,12,17,192,288] 13 (by decide) (choices 1) [1,64,256] r7085 c7085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3742
  · exact u3743
  · exact u3744

def r7086 : Route 9 := (fun mask => (mask,id))

def c7086 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7086 : Upper (D 9) (R 9) [34,12,17,192,320] 13 := by
  apply FastRouting.sound _ _ [34,12,17,192,320] 13 (by decide) (choices 1) [1,128,256] r7086 c7086
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3745
  · exact u3746
  · exact u3747

def b7087 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 16, targets := 384 },{ cop := 4, region := 8, targets := 128 }], pairs := [(3,5),(3,7),(4,5),(4,7),(4,8)], upper := (rows 35 14 52 73 81 416 448 384 384), lower := (rows 35 14 52 73 81 32 64 128 256), losses := [] }

theorem u7087 : Upper (D 9) (R 9) [34,12,48,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7087 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7088 : Route 9 := (fun mask => (mask,id))

def c7088 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7088 : Upper (D 9) (R 9) [34,12,48,65,129] 13 := by
  apply FastRouting.sound _ _ [34,12,48,65,129] 13 (by decide) (choices 1) [64,128,256] r7088 c7088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3748
  · exact u3749
  · exact u3750

def r7089 : Route 9 := (fun mask => (mask,id))

def c7089 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7089 : Upper (D 9) (R 9) [34,12,48,65,192] 13 := by
  apply FastRouting.sound _ _ [34,12,48,65,192] 13 (by decide) (choices 1) [1,128,256] r7089 c7089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3751
  · exact u3752
  · exact u3753

def r7090 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7090 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7090 : Upper (D 9) (R 9) [34,12,48,65,384] 13 := by
  apply FastRouting.sound _ _ [34,12,48,65,384] 13 (by decide) (choices 1) [1,64,128] r7090 c7090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3754
  · exact u3755
  · exact u3756

def b7091 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 417, targets := 64 },{ cop := 4, region := 420, targets := 64 }], pairs := [(0,6),(1,5),(2,6),(3,5),(4,5)], upper := (rows 35 14 52 200 81 417 449 385 385), lower := (rows 35 14 52 200 81 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 29 17 0 81 145 273), good := (rows 475 14 478 200 473 0 64 128 256) }] }

theorem u7091 : Upper (D 9) (R 9) [34,12,48,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7091 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7092 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 16, targets := 289 },{ cop := 4, region := 8, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5),(4,8)], upper := (rows 35 14 52 200 208 289 321 385 257), lower := (rows 35 14 52 200 208 32 64 128 256), losses := [] }

theorem u7092 : Upper (D 9) (R 9) [34,12,48,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7092 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7093 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7093 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7093 : Upper (D 9) (R 9) [34,12,48,192,257] 13 := by
  apply FastRouting.sound _ _ [34,12,48,192,257] 13 (by decide) (choices 1) [1,64,256] r7093 c7093
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3757
  · exact u3758
  · exact u3759

def r7094 : Route 9 := (fun mask => (mask,id))

def c7094 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7094 : Upper (D 9) (R 9) [34,12,48,192,320] 13 := by
  apply FastRouting.sound _ _ [34,12,48,192,320] 13 (by decide) (choices 1) [1,128,256] r7094 c7094
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3760
  · exact u3761
  · exact u3762

def b7095 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 384 }], pairs := [(1,5),(2,5),(3,5),(4,7),(4,8)], upper := (rows 35 14 69 88 49 416 448 384 384), lower := (rows 35 14 69 88 49 32 64 128 256), losses := [] }

theorem u7095 : Upper (D 9) (R 9) [34,12,65,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7095 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7096 : Route 9 := (fun mask => (mask,id))

def c7096 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7096 : Upper (D 9) (R 9) [34,12,65,80,129] 13 := by
  apply FastRouting.sound _ _ [34,12,65,80,129] 13 (by decide) (choices 1) [128,256] r7096 c7096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3763
  · exact u3764

def r7097 : Route 9 := (fun mask => (mask,id))

def c7097 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7097 : Upper (D 9) (R 9) [34,12,65,80,160] 13 := by
  apply FastRouting.sound _ _ [34,12,65,80,160] 13 (by decide) (choices 1) [1,128,256] r7097 c7097
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3765
  · exact u3766
  · exact u3767

def r7098 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7098 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7098 : Upper (D 9) (R 9) [34,12,65,80,384] 13 := by
  apply FastRouting.sound _ _ [34,12,65,80,384] 13 (by decide) (choices 1) [1,128] r7098 c7098
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3768
  · exact u3769

def r7099 : Route 9 := (fun mask => (mask,id))

def c7099 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7099 : Upper (D 9) (R 9) [34,12,65,129,96] 13 := by
  apply FastRouting.sound _ _ [34,12,65,129,96] 13 (by decide) (choices 1) [16,128,256] r7099 c7099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3770
  · exact u3771
  · exact u3772

def r7100 : Route 9 := (fun mask => (mask,id))

def c7100 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7100 : Upper (D 9) (R 9) [34,12,65,129,192] 13 := by
  apply FastRouting.sound _ _ [34,12,65,129,192] 13 (by decide) (choices 1) [16,256] r7100 c7100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3773
  · exact u3774

theorem m7101_128 : Upper (D 9) (R 9) [34,12,65,129,288,128] 13 :=
  permutation_upper _ _ _ [34,12,65,129,288,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3776

def r7101 : Route 9 := (fun mask => (mask,id))

def c7101 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u7101 : Upper (D 9) (R 9) [34,12,65,129,288] 13 := by
  apply FastRouting.sound _ _ [34,12,65,129,288] 13 (by decide) (choices 1) [16,64,128,256] r7101 c7101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3775
  · exact u3776
  · exact m7101_128
  · exact u3777

def r7102 : Route 9 := (fun mask => (mask,id))

def c7102 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7102 : Upper (D 9) (R 9) [34,12,65,129,320] 13 := by
  apply FastRouting.sound _ _ [34,12,65,129,320] 13 (by decide) (choices 1) [16,128,256] r7102 c7102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3778
  · exact u3779
  · exact u3780

def b7103 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 16, targets := 448 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(4,6),(4,7),(4,8)], upper := (rows 35 14 69 152 49 480 448 448 448), lower := (rows 35 14 69 152 49 32 64 128 256), losses := [] }

theorem u7103 : Upper (D 9) (R 9) [34,12,65,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7103 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7104 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 16, targets := 416 },{ cop := 4, region := 4, targets := 160 }], pairs := [(2,5),(2,7),(4,5),(4,7),(4,8)], upper := (rows 35 14 69 152 81 416 480 416 416), lower := (rows 35 14 69 152 81 32 64 128 256), losses := [] }

theorem u7104 : Upper (D 9) (R 9) [34,12,65,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7104 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7105 : Route 9 := (fun mask => (mask,id))

def c7105 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7105 : Upper (D 9) (R 9) [34,12,65,144,96] 13 := by
  apply FastRouting.sound _ _ [34,12,65,144,96] 13 (by decide) (choices 1) [1,128,256] r7105 c7105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3781
  · exact u3782
  · exact u3783

def b7106 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 359, targets := 128 },{ cop := 4, region := 8, targets := 96 }], pairs := [(0,7),(1,7),(2,7),(3,5),(3,6)], upper := (rows 35 14 69 152 145 352 352 480 352), lower := (rows 35 14 69 152 145 32 64 128 256), losses := [] }

theorem u7106 : Upper (D 9) (R 9) [34,12,65,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7106 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7107 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 35 14 69 152 176 353 321 449 321), lower := (rows 35 14 69 152 176 32 64 128 256), losses := [] }

theorem u7107 : Upper (D 9) (R 9) [34,12,65,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7107 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7108 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 35 14 69 152 208 289 353 417 289), lower := (rows 35 14 69 152 208 32 64 128 256), losses := [] }

theorem u7108 : Upper (D 9) (R 9) [34,12,65,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7108 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7109 : Route 9 := (fun mask => (mask,id))

def c7109 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7109 : Upper (D 9) (R 9) [34,12,65,144,257] 13 := by
  apply FastRouting.sound _ _ [34,12,65,144,257] 13 (by decide) (choices 1) [64,128,256] r7109 c7109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3784
  · exact u3785
  · exact u3786

def r7110 : Route 9 := (fun mask => (mask,id))

def c7110 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7110 : Upper (D 9) (R 9) [34,12,65,144,288] 13 := by
  apply FastRouting.sound _ _ [34,12,65,144,288] 13 (by decide) (choices 1) [1,64,128,256] r7110 c7110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3787
  · exact u3788
  · exact u3789
  · exact u3790

def r7111 : Route 9 := (fun mask => (mask,id))

def c7111 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7111 : Upper (D 9) (R 9) [34,12,65,144,320] 13 := by
  apply FastRouting.sound _ _ [34,12,65,144,320] 13 (by decide) (choices 1) [1,128,256] r7111 c7111
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3791
  · exact u3792
  · exact u3793

def b7112 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 35 14 69 152 400 353 353 481 353), lower := (rows 35 14 69 152 400 32 64 128 256), losses := [] }

theorem u7112 : Upper (D 9) (R 9) [34,12,65,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7112 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7113 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 16, targets := 384 },{ cop := 4, region := 4, targets := 128 }], pairs := [(2,5),(2,7),(4,5),(4,7),(4,8)], upper := (rows 35 14 69 168 81 432 464 400 400), lower := (rows 35 14 69 168 81 32 64 128 256), losses := [] }

theorem u7113 : Upper (D 9) (R 9) [34,12,65,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7113 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7114 : Route 9 := (fun mask => (mask,id))

def c7114 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7114 : Upper (D 9) (R 9) [34,12,65,160,129] 13 := by
  apply FastRouting.sound _ _ [34,12,65,160,129] 13 (by decide) (choices 1) [16,64,256] r7114 c7114
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3794
  · exact u3795
  · exact u3796

def r7115 : Route 9 := (fun mask => (mask,id))

def c7115 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7115 : Upper (D 9) (R 9) [34,12,65,160,192] 13 := by
  apply FastRouting.sound _ _ [34,12,65,160,192] 13 (by decide) (choices 1) [1,16,256] r7115 c7115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3797
  · exact u3798
  · exact u3799

def r7116 : Route 9 := (fun mask => (mask,id))

def c7116 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u7116 : Upper (D 9) (R 9) [34,12,65,160,257] 13 := by
  apply FastRouting.sound _ _ [34,12,65,160,257] 13 (by decide) (choices 1) [16,64,128,256] r7116 c7116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3800
  · exact u3801
  · exact u3802
  · exact u3803

def r7117 : Route 9 := (fun mask => (mask,id))

def c7117 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7117 : Upper (D 9) (R 9) [34,12,65,160,320] 13 := by
  apply FastRouting.sound _ _ [34,12,65,160,320] 13 (by decide) (choices 1) [1,16,128,256] r7117 c7117
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3804
  · exact u3805
  · exact u3806
  · exact u3807

def r7118 : Route 9 := (fun mask => (mask,id))

def c7118 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7118 : Upper (D 9) (R 9) [34,12,65,160,384] 13 := by
  apply FastRouting.sound _ _ [34,12,65,160,384] 13 (by decide) (choices 1) [1,16,64,256] r7118 c7118
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3808
  · exact u3809
  · exact u3810
  · exact u3811

def b7119 : PairBound 9 := { available := 400, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 384 }], pairs := [(1,5),(2,5),(3,5),(4,7),(4,8)], upper := (rows 35 14 69 200 49 432 464 400 400), lower := (rows 35 14 69 200 49 32 64 128 256), losses := [] }

theorem u7119 : Upper (D 9) (R 9) [34,12,65,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7119 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7120 : Route 9 := (fun mask => (mask,id))

def c7120 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7120 : Upper (D 9) (R 9) [34,12,65,192,129] 13 := by
  apply FastRouting.sound _ _ [34,12,65,192,129] 13 (by decide) (choices 1) [16,256] r7120 c7120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3812
  · exact u3813

def r7121 : Route 9 := (fun mask => (mask,id))

def c7121 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7121 : Upper (D 9) (R 9) [34,12,65,192,160] 13 := by
  apply FastRouting.sound _ _ [34,12,65,192,160] 13 (by decide) (choices 1) [1,16,256] r7121 c7121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3814
  · exact u3815
  · exact u3816

def r7122 : Route 9 := (fun mask => (mask,id))

def c7122 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7122 : Upper (D 9) (R 9) [34,12,65,192,257] 13 := by
  apply FastRouting.sound _ _ [34,12,65,192,257] 13 (by decide) (choices 1) [16,128,256] r7122 c7122
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3817
  · exact u3818
  · exact u3819

def r7123 : Route 9 := (fun mask => (mask,id))

def c7123 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7123 : Upper (D 9) (R 9) [34,12,65,192,288] 13 := by
  apply FastRouting.sound _ _ [34,12,65,192,288] 13 (by decide) (choices 1) [1,16,128,256] r7123 c7123
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3820
  · exact u3821
  · exact u3822
  · exact u3823

def r7124 : Route 9 := (fun mask => (mask,id))

def c7124 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7124 : Upper (D 9) (R 9) [34,12,65,192,384] 13 := by
  apply FastRouting.sound _ _ [34,12,65,192,384] 13 (by decide) (choices 1) [1,16,256] r7124 c7124
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3824
  · exact u3825
  · exact u3826

def b7125 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 16, targets := 448 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(4,6),(4,7),(4,8)], upper := (rows 35 14 69 392 49 496 464 464 464), lower := (rows 35 14 69 392 49 32 64 128 256), losses := [] }

theorem u7125 : Upper (D 9) (R 9) [34,12,65,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7125 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7126 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 16, targets := 416 },{ cop := 4, region := 4, targets := 160 }], pairs := [(2,5),(2,7),(4,5),(4,7),(4,8)], upper := (rows 35 14 69 392 81 432 496 432 432), lower := (rows 35 14 69 392 81 32 64 128 256), losses := [] }

theorem u7126 : Upper (D 9) (R 9) [34,12,65,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7126 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7127 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7127 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7127 : Upper (D 9) (R 9) [34,12,65,384,96] 13 := by
  apply FastRouting.sound _ _ [34,12,65,384,96] 13 (by decide) (choices 1) [1,16,128] r7127 c7127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3827
  · exact u3828
  · exact u3829

def r7128 : Route 9 := (fun mask => (mask,id))

def c7128 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7128 : Upper (D 9) (R 9) [34,12,65,384,129] 13 := by
  apply FastRouting.sound _ _ [34,12,65,384,129] 13 (by decide) (choices 1) [16,64,256] r7128 c7128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3830
  · exact u3831
  · exact u3832

def r7129 : Route 9 := (fun mask => (mask,id))

def c7129 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7129 : Upper (D 9) (R 9) [34,12,65,384,160] 13 := by
  apply FastRouting.sound _ _ [34,12,65,384,160] 13 (by decide) (choices 1) [1,16,64,256] r7129 c7129
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3833
  · exact u3834
  · exact u3835
  · exact u3836

def r7130 : Route 9 := (fun mask => (mask,id))

def c7130 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7130 : Upper (D 9) (R 9) [34,12,65,384,192] 13 := by
  apply FastRouting.sound _ _ [34,12,65,384,192] 13 (by decide) (choices 1) [1,16,256] r7130 c7130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3837
  · exact u3838
  · exact u3839

def b7131 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5),(4,6)], upper := (rows 35 14 69 392 400 113 113 241 369), lower := (rows 35 14 69 392 400 32 64 128 256), losses := [] }

theorem u7131 : Upper (D 9) (R 9) [34,12,65,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7131 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7132 : Route 9 := (fun mask => (mask,id))

def c7132 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7132 : Upper (D 9) (R 9) [34,12,80,96,129] 13 := by
  apply FastRouting.sound _ _ [34,12,80,96,129] 13 (by decide) (choices 1) [1,128,256] r7132 c7132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3840
  · exact u3841
  · exact u3842

def r7133 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7133 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7133 : Upper (D 9) (R 9) [34,12,80,96,384] 13 := by
  apply FastRouting.sound _ _ [34,12,80,96,384] 13 (by decide) (choices 1) [1,128] r7133 c7133
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3843
  · exact u3844

def b7134 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 427, targets := 64 },{ cop := 4, region := 4, targets := 129 }], pairs := [(0,6),(1,6),(2,0),(2,7),(3,6)], upper := (rows 35 14 84 168 81 417 449 385 385), lower := (rows 35 14 84 168 81 32 64 128 256), losses := [] }

theorem u7134 : Upper (D 9) (R 9) [34,12,80,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7134 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7135 : Route 9 := (fun mask => (mask,id))

def c7135 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7135 : Upper (D 9) (R 9) [34,12,80,160,129] 13 := by
  apply FastRouting.sound _ _ [34,12,80,160,129] 13 (by decide) (choices 1) [1,64,256] r7135 c7135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3845
  · exact u3846
  · exact u3847

def b7136 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 4, targets := 417 },{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7),(2,8)], upper := (rows 35 14 84 168 208 289 321 385 257), lower := (rows 35 14 84 168 208 32 64 128 256), losses := [] }

theorem u7136 : Upper (D 9) (R 9) [34,12,80,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7136 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7137 : Route 9 := (fun mask => (mask,id))

def c7137 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7137 : Upper (D 9) (R 9) [34,12,80,160,257] 13 := by
  apply FastRouting.sound _ _ [34,12,80,160,257] 13 (by decide) (choices 1) [1,64,128,256] r7137 c7137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3848
  · exact u3849
  · exact u3850
  · exact u3851

def b7138 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 4, targets := 417 },{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7),(2,8)], upper := (rows 35 14 84 168 336 417 449 385 385), lower := (rows 35 14 84 168 336 32 64 128 256), losses := [] }

theorem u7138 : Upper (D 9) (R 9) [34,12,80,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7138 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7139 : Route 9 := (fun mask => (mask,id))

def c7139 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7139 : Upper (D 9) (R 9) [34,12,80,160,384] 13 := by
  apply FastRouting.sound _ _ [34,12,80,160,384] 13 (by decide) (choices 1) [1,64,256] r7139 c7139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3852
  · exact u3853
  · exact u3854

#print axioms u7139
end Delivery.IrregularNine14.P09
