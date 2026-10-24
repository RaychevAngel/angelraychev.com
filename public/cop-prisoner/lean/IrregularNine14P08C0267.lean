import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0095
import IrregularNine14P08C0096

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r16020 : Route 9 := (fun mask => (mask,id))

def c16020 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16020 : Upper (D 8) (R 8) [192,36,72,257,160] 13 := by
  apply FastRouting.sound _ _ [192,36,72,257,160] 13 (by decide) (choices 1) [1,2,16] r16020 c16020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5741
  · exact u5742
  · exact u5743

def b16021 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 38 76 266 176 49 113 177 305), lower := (rows 193 38 76 266 176 32 64 128 256), losses := [] }

theorem u16021 : Upper (D 8) (R 8) [192,36,72,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16021 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16022 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 366, targets := 128 }], pairs := [(1,7)], upper := (rows 193 38 76 280 145 35 99 163 291), lower := (rows 193 38 76 280 145 32 64 128 256), losses := [] }

theorem u16022 : Upper (D 8) (R 8) [192,36,72,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16022 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16023 : Route 9 := (fun mask => (mask,id))

def c16023 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16023 : Upper (D 8) (R 8) [192,36,72,272,130] 13 := by
  apply FastRouting.sound _ _ [192,36,72,272,130] 13 (by decide) (choices 1) [1] r16023 c16023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u5744

def r16024 : Route 9 := (fun mask => (mask,id))

def c16024 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16024 : Upper (D 8) (R 8) [192,36,72,272,160] 13 := by
  apply FastRouting.sound _ _ [192,36,72,272,160] 13 (by decide) (choices 1) [1,2] r16024 c16024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5745
  · exact u5746

def b16025 : PairBound 9 := { available := 51, camps := [{ cop := 4, region := 366, targets := 128 }], pairs := [(1,7)], upper := (rows 193 38 76 296 145 51 115 179 307), lower := (rows 193 38 76 296 145 32 64 128 256), losses := [] }

theorem u16025 : Upper (D 8) (R 8) [192,36,72,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16025 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16026 : Route 9 := (fun mask => (mask,id))

def c16026 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16026 : Upper (D 8) (R 8) [192,36,72,288,130] 13 := by
  apply FastRouting.sound _ _ [192,36,72,288,130] 13 (by decide) (choices 1) [1,16] r16026 c16026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5747
  · exact u5748

def r16027 : Route 9 := (fun mask => (mask,id))

def c16027 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16027 : Upper (D 8) (R 8) [192,36,72,288,160] 13 := by
  apply FastRouting.sound _ _ [192,36,72,288,160] 13 (by decide) (choices 1) [1,2,16] r16027 c16027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5749
  · exact u5750
  · exact u5751

def b16028 : PairBound 9 := { available := 139, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 100 56 273 171 203 139 395), lower := (rows 193 38 100 56 273 32 64 128 256), losses := [] }

theorem u16028 : Upper (D 8) (R 8) [192,36,96,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16028 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16029 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 100 56 274 169 201 137 393), lower := (rows 193 38 100 56 274 32 64 128 256), losses := [] }

theorem u16029 : Upper (D 8) (R 8) [192,36,96,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16029 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16030 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 100 56 280 163 195 131 387), lower := (rows 193 38 100 56 280 32 64 128 256), losses := [] }

theorem u16030 : Upper (D 8) (R 8) [192,36,96,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16030 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16031 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 100 56 400 43 75 139 267), lower := (rows 193 38 100 56 400 32 64 128 256), losses := [] }

theorem u16031 : Upper (D 8) (R 8) [192,36,96,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16031 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16032 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 100 138 273 57 121 185 313), lower := (rows 193 38 100 138 273 32 64 128 256), losses := [] }

theorem u16032 : Upper (D 8) (R 8) [192,36,96,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16032 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16033 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 100 138 280 49 113 177 305), lower := (rows 193 38 100 138 280 32 64 128 256), losses := [] }

theorem u16033 : Upper (D 8) (R 8) [192,36,96,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16033 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16034 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 100 138 304 57 89 153 281), lower := (rows 193 38 100 138 304 32 64 128 256), losses := [] }

theorem u16034 : Upper (D 8) (R 8) [192,36,96,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16034 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16035 : PairBound 9 := { available := 43, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 100 152 273 43 107 171 299), lower := (rows 193 38 100 152 273 32 64 128 256), losses := [] }

theorem u16035 : Upper (D 8) (R 8) [192,36,96,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16035 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16036 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 100 152 274 41 105 169 297), lower := (rows 193 38 100 152 274 32 64 128 256), losses := [] }

theorem u16036 : Upper (D 8) (R 8) [192,36,96,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16036 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16037 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 100 152 304 43 75 139 267), lower := (rows 193 38 100 152 304 32 64 128 256), losses := [] }

theorem u16037 : Upper (D 8) (R 8) [192,36,96,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16037 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16038 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 100 168 273 59 91 155 283), lower := (rows 193 38 100 168 273 32 64 128 256), losses := [] }

theorem u16038 : Upper (D 8) (R 8) [192,36,96,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16038 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16039 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 100 168 274 57 89 153 281), lower := (rows 193 38 100 168 274 32 64 128 256), losses := [] }

theorem u16039 : Upper (D 8) (R 8) [192,36,96,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16039 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16040 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 100 168 280 51 83 147 275), lower := (rows 193 38 100 168 280 32 64 128 256), losses := [] }

theorem u16040 : Upper (D 8) (R 8) [192,36,96,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16040 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16041 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 38 196 56 273 43 107 171 299), lower := (rows 193 38 196 56 273 32 64 128 256), losses := [] }

theorem u16041 : Upper (D 8) (R 8) [192,36,192,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16041 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16042 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 38 196 56 274 41 105 169 297), lower := (rows 193 38 196 56 274 32 64 128 256), losses := [] }

theorem u16042 : Upper (D 8) (R 8) [192,36,192,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16042 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16043 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 38 196 56 280 35 99 163 291), lower := (rows 193 38 196 56 280 32 64 128 256), losses := [] }

theorem u16043 : Upper (D 8) (R 8) [192,36,192,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16043 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16044 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 261 73 146 56 120 184 312), lower := (rows 193 38 261 73 146 32 64 128 256), losses := [] }

theorem u16044 : Upper (D 8) (R 8) [192,36,257,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16044 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16045 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 261 73 152 50 114 178 306), lower := (rows 193 38 261 73 152 32 64 128 256), losses := [] }

theorem u16045 : Upper (D 8) (R 8) [192,36,257,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16045 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16046 : PairBound 9 := { available := 58, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 261 73 176 58 122 186 314), lower := (rows 193 38 261 73 176 32 64 128 256), losses := [] }

theorem u16046 : Upper (D 8) (R 8) [192,36,257,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16046 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16047 : Route 9 := (fun mask => (mask,id))

def c16047 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16047 : Upper (D 8) (R 8) [192,36,257,66,136] 13 := by
  apply FastRouting.sound _ _ [192,36,257,66,136] 13 (by decide) (choices 1) [1,16] r16047 c16047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5752
  · exact u5753

def r16048 : Route 9 := (fun mask => (mask,id))

def c16048 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16048 : Upper (D 8) (R 8) [192,36,257,66,160] 13 := by
  apply FastRouting.sound _ _ [192,36,257,66,160] 13 (by decide) (choices 1) [1,8,16] r16048 c16048
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5754
  · exact u5755
  · exact u5756

def b16049 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 193 38 261 88 152 35 99 163 291), lower := (rows 193 38 261 88 152 32 64 128 256), losses := [] }

theorem u16049 : Upper (D 8) (R 8) [192,36,257,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16049 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16050 : Route 9 := (fun mask => (mask,id))

def c16050 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16050 : Upper (D 8) (R 8) [192,36,257,80,160] 13 := by
  apply FastRouting.sound _ _ [192,36,257,80,160] 13 (by decide) (choices 1) [1,2,8] r16050 c16050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5757
  · exact u5758
  · exact u5759

theorem m16051_16 : Upper (D 8) (R 8) [192,36,257,96,160,16] 13 :=
  permutation_upper _ _ _ [192,36,257,96,160,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5762

def r16051 : Route 9 := (fun mask => (mask,id))

def c16051 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16051 : Upper (D 8) (R 8) [192,36,257,96,160] 13 := by
  apply FastRouting.sound _ _ [192,36,257,96,160] 13 (by decide) (choices 1) [1,2,8,16] r16051 c16051
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5760
  · exact u5761
  · exact u5762
  · exact m16051_16

def b16052 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 262 73 152 49 113 177 305), lower := (rows 193 38 262 73 152 32 64 128 256), losses := [] }

theorem u16052 : Upper (D 8) (R 8) [192,36,258,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16052 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16053 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 262 73 176 57 121 185 313), lower := (rows 193 38 262 73 176 32 64 128 256), losses := [] }

theorem u16053 : Upper (D 8) (R 8) [192,36,258,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16053 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16054 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 193 38 262 88 152 33 97 161 289), lower := (rows 193 38 262 88 152 32 64 128 256), losses := [] }

theorem u16054 : Upper (D 8) (R 8) [192,36,258,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16054 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16055 : Route 9 := (fun mask => (mask,id))

def c16055 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16055 : Upper (D 8) (R 8) [192,36,258,80,160] 13 := by
  apply FastRouting.sound _ _ [192,36,258,80,160] 13 (by decide) (choices 1) [1,8] r16055 c16055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5763
  · exact u5764

theorem m16056_16 : Upper (D 8) (R 8) [192,36,258,96,160,16] 13 :=
  permutation_upper _ _ _ [192,36,258,96,160,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5766

def r16056 : Route 9 := (fun mask => (mask,id))

def c16056 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16056 : Upper (D 8) (R 8) [192,36,258,96,160] 13 := by
  apply FastRouting.sound _ _ [192,36,258,96,160] 13 (by decide) (choices 1) [1,8,16] r16056 c16056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5765
  · exact u5766
  · exact m16056_16

def b16057 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 268 73 146 49 113 177 305), lower := (rows 193 38 268 73 146 32 64 128 256), losses := [] }

theorem u16057 : Upper (D 8) (R 8) [192,36,264,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16057 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16058 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 268 73 176 51 115 179 307), lower := (rows 193 38 268 73 176 32 64 128 256), losses := [] }

theorem u16058 : Upper (D 8) (R 8) [192,36,264,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16058 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16059 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 38 268 74 176 49 113 177 305), lower := (rows 193 38 268 74 176 32 64 128 256), losses := [] }

theorem u16059 : Upper (D 8) (R 8) [192,36,264,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16059 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16060 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 366, targets := 128 }], pairs := [(1,7)], upper := (rows 193 38 268 88 145 35 99 163 291), lower := (rows 193 38 268 88 145 32 64 128 256), losses := [] }

theorem u16060 : Upper (D 8) (R 8) [192,36,264,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16060 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16061 : Route 9 := (fun mask => (mask,id))

def c16061 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16061 : Upper (D 8) (R 8) [192,36,264,80,130] 13 := by
  apply FastRouting.sound _ _ [192,36,264,80,130] 13 (by decide) (choices 1) [1] r16061 c16061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u5767

def r16062 : Route 9 := (fun mask => (mask,id))

def c16062 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16062 : Upper (D 8) (R 8) [192,36,264,80,160] 13 := by
  apply FastRouting.sound _ _ [192,36,264,80,160] 13 (by decide) (choices 1) [1,2] r16062 c16062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5768
  · exact u5769

def b16063 : PairBound 9 := { available := 51, camps := [{ cop := 4, region := 366, targets := 128 }], pairs := [(1,7)], upper := (rows 193 38 268 104 145 51 115 179 307), lower := (rows 193 38 268 104 145 32 64 128 256), losses := [] }

theorem u16063 : Upper (D 8) (R 8) [192,36,264,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16063 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16064 : Route 9 := (fun mask => (mask,id))

def c16064 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16064 : Upper (D 8) (R 8) [192,36,264,96,130] 13 := by
  apply FastRouting.sound _ _ [192,36,264,96,130] 13 (by decide) (choices 1) [1,16] r16064 c16064
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5770
  · exact u5771

def r16065 : Route 9 := (fun mask => (mask,id))

def c16065 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16065 : Upper (D 8) (R 8) [192,36,264,96,160] 13 := by
  apply FastRouting.sound _ _ [192,36,264,96,160] 13 (by decide) (choices 1) [1,2,16] r16065 c16065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5772
  · exact u5773
  · exact u5774

def b16066 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 292 74 152 49 113 177 305), lower := (rows 193 38 292 74 152 32 64 128 256), losses := [] }

theorem u16066 : Upper (D 8) (R 8) [192,36,288,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16066 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16067 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 292 74 176 57 89 153 281), lower := (rows 193 38 292 74 176 32 64 128 256), losses := [] }

theorem u16067 : Upper (D 8) (R 8) [192,36,288,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16067 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16068 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 292 88 176 43 75 139 267), lower := (rows 193 38 292 88 176 32 64 128 256), losses := [] }

theorem u16068 : Upper (D 8) (R 8) [192,36,288,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16068 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16069 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 28 41 112 224 224 224 480), lower := (rows 259 7 28 41 112 32 64 128 256), losses := [] }

theorem u16069 : Upper (D 8) (R 8) [258,5,24,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16069 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16070 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 28 41 208 224 224 224 480), lower := (rows 259 7 28 41 208 32 64 128 256), losses := [] }

theorem u16070 : Upper (D 8) (R 8) [258,5,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16070 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16071 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 28 73 112 160 224 160 416), lower := (rows 259 7 28 73 112 32 64 128 256), losses := [] }

theorem u16071 : Upper (D 8) (R 8) [258,5,24,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16071 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16072 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 28 73 176 224 224 224 480), lower := (rows 259 7 28 73 176 32 64 128 256), losses := [] }

theorem u16072 : Upper (D 8) (R 8) [258,5,24,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16072 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16073 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 28 73 208 160 224 160 416), lower := (rows 259 7 28 73 208 32 64 128 256), losses := [] }

theorem u16073 : Upper (D 8) (R 8) [258,5,24,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16073 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16074 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 28 104 112 161 225 161 417), lower := (rows 259 7 28 104 112 32 64 128 256), losses := [] }

theorem u16074 : Upper (D 8) (R 8) [258,5,24,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16074 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m16075_128 : Upper (D 8) (R 8) [258,5,24,96,160,128] 13 :=
  permutation_upper _ _ _ [258,5,24,96,160,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5776

def r16075 : Route 9 := (fun mask => (mask,id))

def c16075 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16075 : Upper (D 8) (R 8) [258,5,24,96,160] 13 := by
  apply FastRouting.sound _ _ [258,5,24,96,160] 13 (by decide) (choices 1) [1,64,128] r16075 c16075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5775
  · exact u5776
  · exact m16075_128

def b16076 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 28 104 208 161 225 161 417), lower := (rows 259 7 28 104 208 32 64 128 256), losses := [] }

theorem u16076 : Upper (D 8) (R 8) [258,5,24,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16076 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16077 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 28 200 208 33 97 161 289), lower := (rows 259 7 28 200 208 32 64 128 256), losses := [] }

theorem u16077 : Upper (D 8) (R 8) [258,5,24,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16077 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16078 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 204, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 44 88 49 224 224 224 480), lower := (rows 259 7 44 88 49 32 64 128 256), losses := [] }

theorem u16078 : Upper (D 8) (R 8) [258,5,40,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16078 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16079 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 44 88 81 160 224 160 416), lower := (rows 259 7 44 88 81 32 64 128 256), losses := [] }

theorem u16079 : Upper (D 8) (R 8) [258,5,40,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16079 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u16079
end Delivery.IrregularNine14.P08
