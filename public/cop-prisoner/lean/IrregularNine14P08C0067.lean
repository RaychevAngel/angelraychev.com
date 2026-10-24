import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0009

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r4020 : Route 9 := (fun mask => (mask,id))

def c4020 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4020 : Upper (D 8) (R 8) [66,288,33,96,132,128] 13 := by
  apply FastRouting.sound _ _ [66,288,33,96,132,128] 13 (by decide) (choices 1) [1,8,16] r4020 c4020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u563
  · exact u564
  · exact u565

def b4021 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 37 104 152 33 212 148 404), lower := (rows 67 290 37 104 152 33 64 128 256), losses := [] }

theorem u4021 : Upper (D 8) (R 8) [66,288,33,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4021 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4022 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 290 37 104 152 36 209 145 401), lower := (rows 67 290 37 104 152 36 64 128 256), losses := [] }

theorem u4022 : Upper (D 8) (R 8) [66,288,33,96,136,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4022 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4023 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 67 290 37 104 152 48 197 133 389), lower := (rows 67 290 37 104 152 48 64 128 256), losses := [] }

theorem u4023 : Upper (D 8) (R 8) [66,288,33,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4023 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4024 : Route 9 := (fun mask => (mask,id))

def c4024 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4024 : Upper (D 8) (R 8) [66,288,33,96,136,128] 13 := by
  apply FastRouting.sound _ _ [66,288,33,96,136,128] 13 (by decide) (choices 1) [1,4,16] r4024 c4024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u566
  · exact u567
  · exact u568

def b4025 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 67 290 37 137 148 40 112 240 368), lower := (rows 67 290 37 137 148 40 64 128 256), losses := [] }

theorem u4025 : Upper (D 8) (R 8) [66,288,33,129,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4025 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4026 : PairBound 9 := { available := 104, camps := [], pairs := [], upper := (rows 67 290 37 137 148 48 104 232 360), lower := (rows 67 290 37 137 148 48 64 128 256), losses := [] }

theorem u4026 : Upper (D 8) (R 8) [66,288,33,129,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4026 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4027 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 37 137 148 96 120 184 312), lower := (rows 67 290 37 137 148 96 64 128 256), losses := [] }

theorem u4027 : Upper (D 8) (R 8) [66,288,33,129,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4027 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4028 : PairBound 9 := { available := 88, camps := [], pairs := [], upper := (rows 67 290 37 137 176 36 88 216 344), lower := (rows 67 290 37 137 176 36 64 128 256), losses := [] }

theorem u4028 : Upper (D 8) (R 8) [66,288,33,129,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4028 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4029 : PairBound 9 := { available := 84, camps := [], pairs := [], upper := (rows 67 290 37 137 176 40 84 212 340), lower := (rows 67 290 37 137 176 40 64 128 256), losses := [] }

theorem u4029 : Upper (D 8) (R 8) [66,288,33,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4029 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4030 : PairBound 9 := { available := 76, camps := [], pairs := [], upper := (rows 67 290 37 137 176 48 76 204 332), lower := (rows 67 290 37 137 176 48 64 128 256), losses := [] }

theorem u4030 : Upper (D 8) (R 8) [66,288,33,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4030 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4031 : PairBound 9 := { available := 28, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 37 137 176 96 92 156 284), lower := (rows 67 290 37 137 176 96 64 128 256), losses := [] }

theorem u4031 : Upper (D 8) (R 8) [66,288,33,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4031 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4032 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 67 290 37 137 208 36 120 184 312), lower := (rows 67 290 37 137 208 36 64 128 256), losses := [] }

theorem u4032 : Upper (D 8) (R 8) [66,288,33,129,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4032 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4033 : PairBound 9 := { available := 52, camps := [], pairs := [], upper := (rows 67 290 37 137 208 40 116 180 308), lower := (rows 67 290 37 137 208 40 64 128 256), losses := [] }

theorem u4033 : Upper (D 8) (R 8) [66,288,33,129,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4033 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4034 : PairBound 9 := { available := 44, camps := [], pairs := [], upper := (rows 67 290 37 137 208 48 108 172 300), lower := (rows 67 290 37 137 208 48 64 128 256), losses := [] }

theorem u4034 : Upper (D 8) (R 8) [66,288,33,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4034 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4035 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 37 140 176 33 88 216 344), lower := (rows 67 290 37 140 176 33 64 128 256), losses := [] }

theorem u4035 : Upper (D 8) (R 8) [66,288,33,132,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4035 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4036 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 67 290 37 140 176 40 81 209 337), lower := (rows 67 290 37 140 176 40 64 128 256), losses := [] }

theorem u4036 : Upper (D 8) (R 8) [66,288,33,132,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4036 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4037 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 67 290 37 140 176 48 73 201 329), lower := (rows 67 290 37 140 176 48 64 128 256), losses := [] }

theorem u4037 : Upper (D 8) (R 8) [66,288,33,132,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4037 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4038 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 37 140 176 96 89 153 281), lower := (rows 67 290 37 140 176 96 64 128 256), losses := [] }

theorem u4038 : Upper (D 8) (R 8) [66,288,33,132,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4038 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4039 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 37 140 208 33 120 184 312), lower := (rows 67 290 37 140 208 33 64 128 256), losses := [] }

theorem u4039 : Upper (D 8) (R 8) [66,288,33,132,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4039 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4040 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 290 37 140 208 40 113 177 305), lower := (rows 67 290 37 140 208 40 64 128 256), losses := [] }

theorem u4040 : Upper (D 8) (R 8) [66,288,33,132,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4040 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4041 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 290 37 140 208 48 105 169 297), lower := (rows 67 290 37 140 208 48 64 128 256), losses := [] }

theorem u4041 : Upper (D 8) (R 8) [66,288,33,132,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4041 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4042 : PairBound 9 := { available := 28, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 37 168 208 33 92 156 284), lower := (rows 67 290 37 168 208 33 64 128 256), losses := [] }

theorem u4042 : Upper (D 8) (R 8) [66,288,33,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4042 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4043 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 67 290 37 168 208 36 89 153 281), lower := (rows 67 290 37 168 208 36 64 128 256), losses := [] }

theorem u4043 : Upper (D 8) (R 8) [66,288,33,160,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4043 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4044 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 67 290 37 168 208 40 85 149 277), lower := (rows 67 290 37 168 208 40 64 128 256), losses := [] }

theorem u4044 : Upper (D 8) (R 8) [66,288,33,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4044 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4045 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 67 290 37 168 208 48 77 141 269), lower := (rows 67 290 37 168 208 48 64 128 256), losses := [] }

theorem u4045 : Upper (D 8) (R 8) [66,288,33,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4045 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4046 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 386, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 44 88 145 33 228 164 420), lower := (rows 67 290 44 88 145 33 64 128 256), losses := [] }

theorem u4046 : Upper (D 8) (R 8) [66,288,40,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4046 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4047 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 290 44 88 145 36 225 161 417), lower := (rows 67 290 44 88 145 36 64 128 256), losses := [] }

theorem u4047 : Upper (D 8) (R 8) [66,288,40,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4047 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4048 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 44 88 145 160 101 165 293), lower := (rows 67 290 44 88 145 160 64 128 256), losses := [] }

theorem u4048 : Upper (D 8) (R 8) [66,288,40,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4048 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4049 : Route 9 := (fun mask => (mask,id))

def c4049 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4049 : Upper (D 8) (R 8) [66,288,40,80,160,1] 13 := by
  apply FastRouting.sound _ _ [66,288,40,80,160,1] 13 (by decide) (choices 1) [1,4,128] r4049 c4049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u569
  · exact u570
  · exact u571

def b4050 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 290 44 88 176 36 193 129 385), lower := (rows 67 290 44 88 176 36 64 128 256), losses := [] }

theorem u4050 : Upper (D 8) (R 8) [66,288,40,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4050 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4051 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 44 88 176 160 69 133 261), lower := (rows 67 290 44 88 176 160 64 128 256), losses := [] }

theorem u4051 : Upper (D 8) (R 8) [66,288,40,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4051 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4052 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 44 137 84 33 240 176 432), lower := (rows 67 290 44 137 84 33 64 128 256), losses := [] }

theorem u4052 : Upper (D 8) (R 8) [66,288,40,129,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4052 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4053 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 290 44 137 84 48 225 161 417), lower := (rows 67 290 44 137 84 48 64 128 256), losses := [] }

theorem u4053 : Upper (D 8) (R 8) [66,288,40,129,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4053 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4054 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 44 137 84 160 113 177 305), lower := (rows 67 290 44 137 84 160 64 128 256), losses := [] }

theorem u4054 : Upper (D 8) (R 8) [66,288,40,129,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4054 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4055 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 44 137 112 33 212 148 404), lower := (rows 67 290 44 137 112 33 64 128 256), losses := [] }

theorem u4055 : Upper (D 8) (R 8) [66,288,40,129,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4055 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4056 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 290 44 137 112 36 209 145 401), lower := (rows 67 290 44 137 112 36 64 128 256), losses := [] }

theorem u4056 : Upper (D 8) (R 8) [66,288,40,129,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4056 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4057 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 67 290 44 137 112 48 197 133 389), lower := (rows 67 290 44 137 112 48 64 128 256), losses := [] }

theorem u4057 : Upper (D 8) (R 8) [66,288,40,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4057 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4058 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 44 137 112 160 85 149 277), lower := (rows 67 290 44 137 112 160 64 128 256), losses := [] }

theorem u4058 : Upper (D 8) (R 8) [66,288,40,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4058 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4059 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 44 137 176 33 84 212 340), lower := (rows 67 290 44 137 176 33 64 128 256), losses := [] }

theorem u4059 : Upper (D 8) (R 8) [66,288,40,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4059 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4060 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 67 290 44 137 176 36 81 209 337), lower := (rows 67 290 44 137 176 36 64 128 256), losses := [] }

theorem u4060 : Upper (D 8) (R 8) [66,288,40,129,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4060 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4061 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 67 290 44 137 176 48 69 197 325), lower := (rows 67 290 44 137 176 48 64 128 256), losses := [] }

theorem u4061 : Upper (D 8) (R 8) [66,288,40,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4061 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4062 : PairBound 9 := { available := 21, camps := [], pairs := [(2,0)], upper := (rows 67 290 44 137 176 96 85 149 277), lower := (rows 67 290 44 137 176 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 97 64 128 256), good := (rows 98 290 60 188 176 96 96 128 256) }] }

theorem u4062 : Upper (D 8) (R 8) [66,288,40,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4062 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4063 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 44 137 208 33 116 180 308), lower := (rows 67 290 44 137 208 33 64 128 256), losses := [] }

theorem u4063 : Upper (D 8) (R 8) [66,288,40,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4063 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4064 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 290 44 137 208 36 113 177 305), lower := (rows 67 290 44 137 208 36 64 128 256), losses := [] }

theorem u4064 : Upper (D 8) (R 8) [66,288,40,129,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4064 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4065 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 290 44 137 208 48 101 165 293), lower := (rows 67 290 44 137 208 48 64 128 256), losses := [] }

theorem u4065 : Upper (D 8) (R 8) [66,288,40,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4065 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4066 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 67 290 44 140 112 33 209 145 401), lower := (rows 67 290 44 140 112 33 64 128 256), losses := [] }

theorem u4066 : Upper (D 8) (R 8) [66,288,40,132,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4066 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4067 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 290 44 140 112 48 193 129 385), lower := (rows 67 290 44 140 112 48 64 128 256), losses := [] }

theorem u4067 : Upper (D 8) (R 8) [66,288,40,132,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4067 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4068 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 290 44 140 112 160 81 145 273), lower := (rows 67 290 44 140 112 160 64 128 256), losses := [] }

theorem u4068 : Upper (D 8) (R 8) [66,288,40,132,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4068 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4069 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 67 290 44 152 112 33 197 133 389), lower := (rows 67 290 44 152 112 33 64 128 256), losses := [] }

theorem u4069 : Upper (D 8) (R 8) [66,288,40,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4069 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4070 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 290 44 152 112 36 193 129 385), lower := (rows 67 290 44 152 112 36 64 128 256), losses := [] }

theorem u4070 : Upper (D 8) (R 8) [66,288,40,144,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4070 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4071 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 44 152 112 160 69 133 261), lower := (rows 67 290 44 152 112 160 64 128 256), losses := [] }

theorem u4071 : Upper (D 8) (R 8) [66,288,40,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4071 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4072 : Route 9 := (fun mask => (mask,id))

def c4072 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4072 : Upper (D 8) (R 8) [66,288,40,192,129,1] 13 := by
  apply FastRouting.sound _ _ [66,288,40,192,129,1] 13 (by decide) (choices 1) [4,16,32] r4072 c4072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u572
  · exact u573
  · exact u574

def b4073 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 290 44 200 145 36 113 177 305), lower := (rows 67 290 44 200 145 36 64 128 256), losses := [] }

theorem u4073 : Upper (D 8) (R 8) [66,288,40,192,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4073 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4074 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 290 44 200 145 48 101 165 293), lower := (rows 67 290 44 200 145 48 64 128 256), losses := [] }

theorem u4074 : Upper (D 8) (R 8) [66,288,40,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4074 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4075 : Route 9 := (fun mask => (mask,id))

def c4075 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4075 : Upper (D 8) (R 8) [66,288,40,192,160,1] 13 := by
  apply FastRouting.sound _ _ [66,288,40,192,160,1] 13 (by decide) (choices 1) [1,4,16] r4075 c4075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u575
  · exact u576
  · exact u577

def b4076 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 67 290 44 200 176 36 81 145 273), lower := (rows 67 290 44 200 176 36 64 128 256), losses := [] }

theorem u4076 : Upper (D 8) (R 8) [66,288,40,192,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4076 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4077 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 67 290 44 200 176 48 69 133 261), lower := (rows 67 290 44 200 176 48 64 128 256), losses := [] }

theorem u4077 : Upper (D 8) (R 8) [66,288,40,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4077 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4078 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 67 290 76 137 176 33 116 180 308), lower := (rows 67 290 76 137 176 33 64 128 256), losses := [] }

theorem u4078 : Upper (D 8) (R 8) [66,288,72,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4078 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4079 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 290 76 137 176 36 113 177 305), lower := (rows 67 290 76 137 176 36 64 128 256), losses := [] }

theorem u4079 : Upper (D 8) (R 8) [66,288,72,129,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4079 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u4079
end Delivery.IrregularNine14.P08
