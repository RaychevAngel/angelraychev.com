import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0011
import IrregularNine14P01C0012

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3120 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 26 324 74 17 162 226 162 418), lower := (rows 53 26 324 74 17 32 64 128 256), losses := [] }

theorem u3120 : Upper (D 1) (R 1) [52,24,320,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3120
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3121 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 26, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 324 74 18 161 225 161 417), lower := (rows 53 26 324 74 18 32 64 128 256), losses := [] }

theorem u3121 : Upper (D 1) (R 1) [52,24,320,66,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3121
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3122 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 324 74 48 163 195 131 387), lower := (rows 53 26 324 74 48 32 64 128 256), losses := [] }

theorem u3122 : Upper (D 1) (R 1) [52,24,320,66,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3122
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3123 : Route 9 := (fun mask => (mask,id))

def c3123 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3123 : Upper (D 1) (R 1) [52,24,320,66,128] 13 := by
  apply FastRouting.sound _ _ [52,24,320,66,128] 13 (by decide) (choices 1) [1,2,128] r3123 c3123
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u710
  · exact u711
  · exact u712

def b3124 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 53 26 324 104 17 162 194 130 386), lower := (rows 53 26 324 104 17 32 64 128 256), losses := [] }

theorem u3124 : Upper (D 1) (R 1) [52,24,320,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3124
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3125 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 324 104 18 163 195 131 387), lower := (rows 53 26 324 104 18 32 64 128 256), losses := [] }

theorem u3125 : Upper (D 1) (R 1) [52,24,320,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3125
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3126 : Route 9 := (fun mask => (mask,id))

def c3126 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3126 : Upper (D 1) (R 1) [52,24,320,96,128] 13 := by
  apply FastRouting.sound _ _ [52,24,320,96,128] 13 (by decide) (choices 1) [1,2,128] r3126 c3126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u713
  · exact u714
  · exact u715

def b3127 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 53 26 324 138 17 226 226 226 482), lower := (rows 53 26 324 138 17 32 64 128 256), losses := [] }

theorem u3127 : Upper (D 1) (R 1) [52,24,320,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3127
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3128 : PairBound 9 := { available := 225, camps := [{ cop := 7, region := 26, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 324 138 18 225 225 225 481), lower := (rows 53 26 324 138 18 32 64 128 256), losses := [] }

theorem u3128 : Upper (D 1) (R 1) [52,24,320,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3128
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3129 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 324 138 48 227 195 195 451), lower := (rows 53 26 324 138 48 32 64 128 256), losses := [] }

theorem u3129 : Upper (D 1) (R 1) [52,24,320,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3129
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3130 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 138, targets := 64 }], pairs := [(1,6)], upper := (rows 53 26 324 138 80 163 227 163 419), lower := (rows 53 26 324 138 80 32 64 128 256), losses := [] }

theorem u3130 : Upper (D 1) (R 1) [52,24,320,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3130
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3131 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 324 138 144 99 99 227 355), lower := (rows 53 26 324 138 144 32 64 128 256), losses := [] }

theorem u3131 : Upper (D 1) (R 1) [52,24,320,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3131
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3132 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 53 26 324 168 17 226 194 194 450), lower := (rows 53 26 324 168 17 32 64 128 256), losses := [] }

theorem u3132 : Upper (D 1) (R 1) [52,24,320,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3132
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3133 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 324 168 18 227 195 195 451), lower := (rows 53 26 324 168 18 32 64 128 256), losses := [] }

theorem u3133 : Upper (D 1) (R 1) [52,24,320,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3133
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3134 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 138, targets := 64 }], pairs := [(1,6)], upper := (rows 53 26 324 168 80 163 195 131 387), lower := (rows 53 26 324 168 80 32 64 128 256), losses := [] }

theorem u3134 : Upper (D 1) (R 1) [52,24,320,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3134
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3135 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7)], upper := (rows 53 26 324 168 144 99 67 195 323), lower := (rows 53 26 324 168 144 32 64 128 256), losses := [] }

theorem u3135 : Upper (D 1) (R 1) [52,24,320,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3135
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3136 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 26 324 200 17 162 226 162 418), lower := (rows 53 26 324 200 17 32 64 128 256), losses := [] }

theorem u3136 : Upper (D 1) (R 1) [52,24,320,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3136
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3137 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 324 200 18 163 227 163 419), lower := (rows 53 26 324 200 18 32 64 128 256), losses := [] }

theorem u3137 : Upper (D 1) (R 1) [52,24,320,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3137
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3138 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 324 200 48 163 195 131 387), lower := (rows 53 26 324 200 48 32 64 128 256), losses := [] }

theorem u3138 : Upper (D 1) (R 1) [52,24,320,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3138
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3139 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7)], upper := (rows 53 26 324 200 144 35 99 163 291), lower := (rows 53 26 324 200 144 32 64 128 256), losses := [] }

theorem u3139 : Upper (D 1) (R 1) [52,24,320,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3139
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3140 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 53 67 14 392 18 240 240 240 496), lower := (rows 53 67 14 392 18 32 64 128 256), losses := [] }

theorem u3140 : Upper (D 1) (R 1) [52,65,10,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3140
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3141 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 14 392 48 242 210 210 466), lower := (rows 53 67 14 392 48 32 64 128 256), losses := [] }

theorem u3141 : Upper (D 1) (R 1) [52,65,10,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3141
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3142_2 : Upper (D 1) (R 1) [52,65,10,384,64,2] 13 :=
  permutation_upper _ _ _ [52,65,10,384,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u716

theorem m3142_16 : Upper (D 1) (R 1) [52,65,10,384,64,16] 13 :=
  permutation_upper _ _ _ [52,65,10,384,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u717

def r3142 : Route 9 := (fun mask => (mask,id))

def c3142 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3142 : Upper (D 1) (R 1) [52,65,10,384,64] 13 := by
  apply FastRouting.sound _ _ [52,65,10,384,64] 13 (by decide) (choices 1) [2,16,128] r3142 c3142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3142_2
  · exact m3142_16
  · exact u718

def b3143 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 67 14 392 144 114 114 242 370), lower := (rows 53 67 14 392 144 32 64 128 256), losses := [] }

theorem u3143 : Upper (D 1) (R 1) [52,65,10,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3143
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3144 : PairBound 9 := { available := 424, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 53 67 134 88 18 424 488 424 424), lower := (rows 53 67 134 88 18 32 64 128 256), losses := [] }

theorem u3144 : Upper (D 1) (R 1) [52,65,130,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3144
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3145 : PairBound 9 := { available := 418, camps := [], pairs := [], upper := (rows 53 67 134 88 24 418 482 418 418), lower := (rows 53 67 134 88 24 32 64 128 256), losses := [] }

theorem u3145 : Upper (D 1) (R 1) [52,65,130,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3145
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3146 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 134 88 48 426 458 394 394), lower := (rows 53 67 134 88 48 32 64 128 256), losses := [] }

theorem u3146 : Upper (D 1) (R 1) [52,65,130,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3146
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3147 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 67 134 88 144 298 362 426 298), lower := (rows 53 67 134 88 144 32 64 128 256), losses := [] }

theorem u3147 : Upper (D 1) (R 1) [52,65,130,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3147
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3148 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 53 67 134 88 272 170 234 170 426), lower := (rows 53 67 134 88 272 32 64 128 256), losses := [] }

theorem u3148 : Upper (D 1) (R 1) [52,65,130,80,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3148
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3149 : PairBound 9 := { available := 360, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 53 67 134 152 18 360 360 488 360), lower := (rows 53 67 134 152 18 32 64 128 256), losses := [] }

theorem u3149 : Upper (D 1) (R 1) [52,65,130,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3149
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3150 : PairBound 9 := { available := 354, camps := [], pairs := [], upper := (rows 53 67 134 152 24 354 354 482 354), lower := (rows 53 67 134 152 24 32 64 128 256), losses := [] }

theorem u3150 : Upper (D 1) (R 1) [52,65,130,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3150
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3151 : PairBound 9 := { available := 330, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 134 152 48 362 330 458 330), lower := (rows 53 67 134 152 48 32 64 128 256), losses := [] }

theorem u3151 : Upper (D 1) (R 1) [52,65,130,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3151
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3152 : PairBound 9 := { available := 298, camps := [], pairs := [(3,1)], upper := (rows 53 67 134 152 80 298 362 426 298), lower := (rows 53 67 134 152 80 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 82 32 64 128 256), good := (rows 61 81 156 152 80 32 80 128 256) }] }

theorem u3152 : Upper (D 1) (R 1) [52,65,130,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3152
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3153 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 53 67 134 152 272 106 106 234 362), lower := (rows 53 67 134 152 272 32 64 128 256), losses := [] }

theorem u3153 : Upper (D 1) (R 1) [52,65,130,144,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3153
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3154 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 53 67 134 200 18 312 376 440 312), lower := (rows 53 67 134 200 18 32 64 128 256), losses := [] }

theorem u3154 : Upper (D 1) (R 1) [52,65,130,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3154
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3155 : PairBound 9 := { available := 306, camps := [], pairs := [], upper := (rows 53 67 134 200 24 306 370 434 306), lower := (rows 53 67 134 200 24 32 64 128 256), losses := [] }

theorem u3155 : Upper (D 1) (R 1) [52,65,130,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3155
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3156 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 134 200 48 314 346 410 282), lower := (rows 53 67 134 200 48 32 64 128 256), losses := [] }

theorem u3156 : Upper (D 1) (R 1) [52,65,130,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3156
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3157 : PairBound 9 := { available := 58, camps := [], pairs := [], upper := (rows 53 67 134 200 272 58 122 186 314), lower := (rows 53 67 134 200 272 32 64 128 256), losses := [] }

theorem u3157 : Upper (D 1) (R 1) [52,65,130,192,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3157
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3158 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 53 67 134 266 24 240 240 240 496), lower := (rows 53 67 134 266 24 32 64 128 256), losses := [] }

theorem u3158 : Upper (D 1) (R 1) [52,65,130,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3158
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3159 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 134 266 48 248 216 216 472), lower := (rows 53 67 134 266 48 32 64 128 256), losses := [] }

theorem u3159 : Upper (D 1) (R 1) [52,65,130,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3159
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3160_8 : Upper (D 1) (R 1) [52,65,130,258,64,8] 13 :=
  permutation_upper _ _ _ [52,65,130,258,8,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u719

theorem m3160_16 : Upper (D 1) (R 1) [52,65,130,258,64,16] 13 :=
  permutation_upper _ _ _ [52,65,130,258,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u720

def r3160 : Route 9 := (fun mask => (mask,id))

def c3160 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3160 : Upper (D 1) (R 1) [52,65,130,258,64] 13 := by
  apply FastRouting.sound _ _ [52,65,130,258,64] 13 (by decide) (choices 1) [8,16,128] r3160 c3160
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3160_8
  · exact m3160_16
  · exact u721

def b3161 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 67 134 266 144 120 120 248 376), lower := (rows 53 67 134 266 144 32 64 128 256), losses := [] }

theorem u3161 : Upper (D 1) (R 1) [52,65,130,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3161
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3162 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 53 67 134 280 18 232 232 232 488), lower := (rows 53 67 134 280 18 32 64 128 256), losses := [] }

theorem u3162 : Upper (D 1) (R 1) [52,65,130,272,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3162
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3163 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 53 67 134 280 24 226 226 226 482), lower := (rows 53 67 134 280 24 32 64 128 256), losses := [] }

theorem u3163 : Upper (D 1) (R 1) [52,65,130,272,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3163
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3164 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 134 280 48 234 202 202 458), lower := (rows 53 67 134 280 48 32 64 128 256), losses := [] }

theorem u3164 : Upper (D 1) (R 1) [52,65,130,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3164
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3165 : Route 9 := (fun mask => (mask,id))

def c3165 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3165 : Upper (D 1) (R 1) [52,65,130,272,64] 13 := by
  apply FastRouting.sound _ _ [52,65,130,272,64] 13 (by decide) (choices 1) [2,8,128] r3165 c3165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u722
  · exact u723
  · exact u724

def b3166 : PairBound 9 := { available := 106, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 67 134 280 144 106 106 234 362), lower := (rows 53 67 134 280 144 32 64 128 256), losses := [] }

theorem u3166 : Upper (D 1) (R 1) [52,65,130,272,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3166
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3167 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 53 67 134 328 18 184 248 184 440), lower := (rows 53 67 134 328 18 32 64 128 256), losses := [] }

theorem u3167 : Upper (D 1) (R 1) [52,65,130,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3167
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3168 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 53 67 134 328 24 178 242 178 434), lower := (rows 53 67 134 328 24 32 64 128 256), losses := [] }

theorem u3168 : Upper (D 1) (R 1) [52,65,130,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3168
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3169 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 134 328 48 186 218 154 410), lower := (rows 53 67 134 328 48 32 64 128 256), losses := [] }

theorem u3169 : Upper (D 1) (R 1) [52,65,130,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3169
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3170 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 67 134 328 144 58 122 186 314), lower := (rows 53 67 134 328 144 32 64 128 256), losses := [] }

theorem u3170 : Upper (D 1) (R 1) [52,65,130,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3170
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3171 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 53 67 134 392 18 120 120 248 376), lower := (rows 53 67 134 392 18 32 64 128 256), losses := [] }

theorem u3171 : Upper (D 1) (R 1) [52,65,130,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3171
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3172 : PairBound 9 := { available := 114, camps := [], pairs := [], upper := (rows 53 67 134 392 24 114 114 242 370), lower := (rows 53 67 134 392 24 32 64 128 256), losses := [] }

theorem u3172 : Upper (D 1) (R 1) [52,65,130,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3172
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3173 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 134 392 48 122 90 218 346), lower := (rows 53 67 134 392 48 32 64 128 256), losses := [] }

theorem u3173 : Upper (D 1) (R 1) [52,65,130,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3173
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3174_2 : Upper (D 1) (R 1) [52,65,130,384,64,2] 13 :=
  permutation_upper _ _ _ [52,65,130,384,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u725

theorem m3174_8 : Upper (D 1) (R 1) [52,65,130,384,64,8] 13 :=
  permutation_upper _ _ _ [52,65,130,384,8,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u726

theorem m3174_16 : Upper (D 1) (R 1) [52,65,130,384,64,16] 13 :=
  permutation_upper _ _ _ [52,65,130,384,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u727

def r3174 : Route 9 := (fun mask => (mask,id))

def c3174 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3174 : Upper (D 1) (R 1) [52,65,130,384,64] 13 := by
  apply FastRouting.sound _ _ [52,65,130,384,64] 13 (by decide) (choices 1) [2,8,16] r3174 c3174
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3174_2
  · exact m3174_8
  · exact m3174_16

def r3175 : Route 9 := (fun mask => (mask,id))

def c3175 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3175 : Upper (D 1) (R 1) [52,65,136,258,2] 13 := by
  apply FastRouting.sound _ _ [52,65,136,258,2] 13 (by decide) (choices 1) [16,64,128] r3175 c3175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u728
  · exact u729
  · exact u730

def b3176 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 140 266 48 242 210 210 466), lower := (rows 53 67 140 266 48 32 64 128 256), losses := [] }

theorem u3176 : Upper (D 1) (R 1) [52,65,136,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3176
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3177_2 : Upper (D 1) (R 1) [52,65,136,258,64,2] 13 :=
  permutation_upper _ _ _ [52,65,136,258,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u729

theorem m3177_16 : Upper (D 1) (R 1) [52,65,136,258,64,16] 13 :=
  permutation_upper _ _ _ [52,65,136,258,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u731

def r3177 : Route 9 := (fun mask => (mask,id))

def c3177 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3177 : Upper (D 1) (R 1) [52,65,136,258,64] 13 := by
  apply FastRouting.sound _ _ [52,65,136,258,64] 13 (by decide) (choices 1) [2,16,128] r3177 c3177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3177_2
  · exact m3177_16
  · exact u732

def b3178 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 67 140 266 144 114 114 242 370), lower := (rows 53 67 140 266 144 32 64 128 256), losses := [] }

theorem u3178 : Upper (D 1) (R 1) [52,65,136,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3178
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3179 : Route 9 := (fun mask => (mask,id))

def c3179 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3179 : Upper (D 1) (R 1) [52,65,136,320,2] 13 := by
  apply FastRouting.sound _ _ [52,65,136,320,2] 13 (by decide) (choices 1) [2,16,128] r3179 c3179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u733
  · exact u734
  · exact u735

#print axioms u3179
end Delivery.IrregularNine14.P01
