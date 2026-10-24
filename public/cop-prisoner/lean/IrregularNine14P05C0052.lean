import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0013
import IrregularNine14P05C0014

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3120 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 56, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 67 388 44 50 40 89 153 281), lower := (rows 7 67 388 44 50 40 64 128 256), losses := [] }

theorem u3120 : Upper (D 5) (R 5) [6,65,384,36,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3120
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3121 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 67 388 44 50 48 73 137 265), lower := (rows 7 67 388 44 50 48 64 128 256), losses := [] }

theorem u3121 : Upper (D 5) (R 5) [6,65,384,36,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3121
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3122 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 67 388 56 25 34 108 172 300), lower := (rows 7 67 388 56 25 34 64 128 256), losses := [] }

theorem u3122 : Upper (D 5) (R 5) [6,65,384,48,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3122
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3123 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 67 388 56 25 36 106 170 298), lower := (rows 7 67 388 56 25 36 64 128 256), losses := [] }

theorem u3123 : Upper (D 5) (R 5) [6,65,384,48,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3123
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3124 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 56, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 67 388 56 25 40 102 166 294), lower := (rows 7 67 388 56 25 40 64 128 256), losses := [] }

theorem u3124 : Upper (D 5) (R 5) [6,65,384,48,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3124
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3125 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 67 388 56 26 33 108 172 300), lower := (rows 7 67 388 56 26 33 64 128 256), losses := [] }

theorem u3125 : Upper (D 5) (R 5) [6,65,384,48,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3125
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3126 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 56, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 67 388 56 26 36 105 169 297), lower := (rows 7 67 388 56 26 36 64 128 256), losses := [] }

theorem u3126 : Upper (D 5) (R 5) [6,65,384,48,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3126
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3127 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 56, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 67 388 56 26 40 101 165 293), lower := (rows 7 67 388 56 26 40 64 128 256), losses := [] }

theorem u3127 : Upper (D 5) (R 5) [6,65,384,48,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3127
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3128 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 67 388 56 28 33 106 170 298), lower := (rows 7 67 388 56 28 33 64 128 256), losses := [] }

theorem u3128 : Upper (D 5) (R 5) [6,65,384,48,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3128
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3129 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 56, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 67 388 56 28 34 105 169 297), lower := (rows 7 67 388 56 28 34 64 128 256), losses := [] }

theorem u3129 : Upper (D 5) (R 5) [6,65,384,48,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3129
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3130 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 67 388 56 28 40 99 163 291), lower := (rows 7 67 388 56 28 40 64 128 256), losses := [] }

theorem u3130 : Upper (D 5) (R 5) [6,65,384,48,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3130
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3131 : Route 9 := (fun mask => (mask,id))

def c3131 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3131 : Upper (D 5) (R 5) [6,72,136,17,288,1] 13 := by
  apply FastRouting.sound _ _ [6,72,136,17,288,1] 13 (by decide) (choices 1) [2,4,32] r3131 c3131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u835
  · exact u836
  · exact u837

def r3132 : Route 9 := (fun mask => (mask,id))

def c3132 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3132 : Upper (D 5) (R 5) [6,72,136,17,288,2] 13 := by
  apply FastRouting.sound _ _ [6,72,136,17,288,2] 13 (by decide) (choices 1) [1,4,32] r3132 c3132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u838
  · exact u839
  · exact u840

def b3133 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 74 140 41 50 33 340 404 276), lower := (rows 7 74 140 41 50 33 64 128 256), losses := [] }

theorem u3133 : Upper (D 5) (R 5) [6,72,136,33,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3133
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3134 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 338, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 74 140 41 50 36 337 401 273), lower := (rows 7 74 140 41 50 36 64 128 256), losses := [] }

theorem u3134 : Upper (D 5) (R 5) [6,72,136,33,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3134
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3135 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 74 140 41 50 48 325 389 261), lower := (rows 7 74 140 41 50 48 64 128 256), losses := [] }

theorem u3135 : Upper (D 5) (R 5) [6,72,136,33,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3135
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3136 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 304, targets := 8 }], pairs := [(4,3)], upper := (rows 7 74 140 41 50 288 85 149 277), lower := (rows 7 74 140 41 50 288 64 128 256), losses := [] }

theorem u3136 : Upper (D 5) (R 5) [6,72,136,33,34,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3136
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3137 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 404, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 74 140 41 273 34 116 180 308), lower := (rows 7 74 140 41 273 34 64 128 256), losses := [] }

theorem u3137 : Upper (D 5) (R 5) [6,72,136,33,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3137
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3138 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 198, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 140 41 273 48 102 166 294), lower := (rows 7 74 140 41 273 48 64 128 256), losses := [] }

theorem u3138 : Upper (D 5) (R 5) [6,72,136,33,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3138
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3139 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 74 140 41 274 33 116 180 308), lower := (rows 7 74 140 41 274 33 64 128 256), losses := [] }

theorem u3139 : Upper (D 5) (R 5) [6,72,136,33,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3139
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3140 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 338, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 74 140 41 274 36 113 177 305), lower := (rows 7 74 140 41 274 36 64 128 256), losses := [] }

theorem u3140 : Upper (D 5) (R 5) [6,72,136,33,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3140
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3141 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 304, targets := 8 }], pairs := [(4,3)], upper := (rows 7 74 140 41 274 48 101 165 293), lower := (rows 7 74 140 41 274 48 64 128 256), losses := [] }

theorem u3141 : Upper (D 5) (R 5) [6,72,136,33,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3141
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3142 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 74 140 41 304 33 86 150 278), lower := (rows 7 74 140 41 304 33 64 128 256), losses := [] }

theorem u3142 : Upper (D 5) (R 5) [6,72,136,33,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3142
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3143 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 404, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 74 140 41 304 34 85 149 277), lower := (rows 7 74 140 41 304 34 64 128 256), losses := [] }

theorem u3143 : Upper (D 5) (R 5) [6,72,136,33,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3143
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3144 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 74 140 41 304 48 71 135 263), lower := (rows 7 74 140 41 304 48 64 128 256), losses := [] }

theorem u3144 : Upper (D 5) (R 5) [6,72,136,33,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3144
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3145 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 198, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 74 140 56 273 33 102 166 294), lower := (rows 7 74 140 56 273 33 64 128 256), losses := [] }

theorem u3145 : Upper (D 5) (R 5) [6,72,136,48,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3145
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3146 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 304, targets := 8 }], pairs := [(3,0),(4,3)], upper := (rows 7 74 140 56 273 34 101 165 293), lower := (rows 7 74 140 56 273 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 35 64 128 256), good := (rows 38 106 140 56 312 34 64 128 256) }] }

theorem u3146 : Upper (D 5) (R 5) [6,72,136,48,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3146
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3147 : Route 9 := (fun mask => (mask,id))

def c3147 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3147 : Upper (D 5) (R 5) [6,72,136,48,258,1] 13 := by
  apply FastRouting.sound _ _ [6,72,136,48,258,1] 13 (by decide) (choices 1) [1,4,32] r3147 c3147
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u841
  · exact u842
  · exact u843

def r3148 : Route 9 := (fun mask => (mask,id))

def c3148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3148 : Upper (D 5) (R 5) [6,72,136,48,258,4] 13 := by
  apply FastRouting.sound _ _ [6,72,136,48,258,4] 13 (by decide) (choices 1) [1,32] r3148 c3148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u844
  · exact u845

def b3149 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 74 140 265 49 34 116 180 308), lower := (rows 7 74 140 265 49 34 64 128 256), losses := [] }

theorem u3149 : Upper (D 5) (R 5) [6,72,136,257,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3149
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3150 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 48, targets := 2 }], pairs := [(4,1)], upper := (rows 7 74 140 265 49 48 102 166 294), lower := (rows 7 74 140 265 49 48 64 128 256), losses := [] }

theorem u3150 : Upper (D 5) (R 5) [6,72,136,257,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3150
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3151 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 48, targets := 4 },{ cop := 0, region := 48, targets := 8 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 140 265 50 33 116 180 308), lower := (rows 7 74 140 265 50 33 64 128 256), losses := [] }

theorem u3151 : Upper (D 5) (R 5) [6,72,136,257,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3151
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3152 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 48, targets := 1 },{ cop := 0, region := 48, targets := 8 }], pairs := [(4,0),(4,3)], upper := (rows 7 74 140 265 50 36 113 177 305), lower := (rows 7 74 140 265 50 36 64 128 256), losses := [] }

theorem u3152 : Upper (D 5) (R 5) [6,72,136,257,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3152
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3153 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 74 140 265 50 48 101 165 293), lower := (rows 7 74 140 265 50 48 64 128 256), losses := [] }

theorem u3153 : Upper (D 5) (R 5) [6,72,136,257,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3153
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3154 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 74 140 280 49 33 102 166 294), lower := (rows 7 74 140 280 49 33 64 128 256), losses := [] }

theorem u3154 : Upper (D 5) (R 5) [6,72,136,272,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3154
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3155 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 74 140 280 49 34 101 165 293), lower := (rows 7 74 140 280 49 34 64 128 256), losses := [] }

theorem u3155 : Upper (D 5) (R 5) [6,72,136,272,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3155
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3156 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 48, targets := 4 },{ cop := 0, region := 48, targets := 8 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 140 280 50 33 101 165 293), lower := (rows 7 74 140 280 50 33 64 128 256), losses := [] }

theorem u3156 : Upper (D 5) (R 5) [6,72,136,272,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3156
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3157 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 48, targets := 1 },{ cop := 0, region := 48, targets := 8 }], pairs := [(4,0),(4,3)], upper := (rows 7 74 140 280 50 36 97 161 289), lower := (rows 7 74 140 280 50 36 64 128 256), losses := [] }

theorem u3157 : Upper (D 5) (R 5) [6,72,136,272,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3157
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3158 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 74 140 296 49 33 86 150 278), lower := (rows 7 74 140 296 49 33 64 128 256), losses := [] }

theorem u3158 : Upper (D 5) (R 5) [6,72,136,288,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3158
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3159 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 74 140 296 49 34 85 149 277), lower := (rows 7 74 140 296 49 34 64 128 256), losses := [] }

theorem u3159 : Upper (D 5) (R 5) [6,72,136,288,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3159
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3160 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 199, targets := 32 }], pairs := [(0,5)], upper := (rows 7 74 140 296 49 48 71 135 263), lower := (rows 7 74 140 296 49 48 64 128 256), losses := [] }

theorem u3160 : Upper (D 5) (R 5) [6,72,136,288,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3160
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3161 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 48, targets := 4 },{ cop := 0, region := 48, targets := 8 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 140 296 50 33 85 149 277), lower := (rows 7 74 140 296 50 33 64 128 256), losses := [] }

theorem u3161 : Upper (D 5) (R 5) [6,72,136,288,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3161
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3162 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 48, targets := 1 },{ cop := 0, region := 48, targets := 8 }], pairs := [(4,0),(4,3)], upper := (rows 7 74 140 296 50 36 81 145 273), lower := (rows 7 74 140 296 50 36 64 128 256), losses := [] }

theorem u3162 : Upper (D 5) (R 5) [6,72,136,288,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3162
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3163 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 74 140 296 50 48 69 133 261), lower := (rows 7 74 140 296 50 48 64 128 256), losses := [] }

theorem u3163 : Upper (D 5) (R 5) [6,72,136,288,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3163
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3164 : PairBound 9 := { available := 268, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 74 148 41 50 33 332 396 268), lower := (rows 7 74 148 41 50 33 64 128 256), losses := [] }

theorem u3164 : Upper (D 5) (R 5) [6,72,144,33,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3164
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3165 : PairBound 9 := { available := 265, camps := [{ cop := 3, region := 338, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 74 148 41 50 36 329 393 265), lower := (rows 7 74 148 41 50 36 64 128 256), losses := [] }

theorem u3165 : Upper (D 5) (R 5) [6,72,144,33,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3165
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3166 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 389, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 74 148 41 50 40 325 389 261), lower := (rows 7 74 148 41 50 40 64 128 256), losses := [] }

theorem u3166 : Upper (D 5) (R 5) [6,72,144,33,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3166
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3167 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 296, targets := 2 }], pairs := [(3,1)], upper := (rows 7 74 148 41 50 288 77 141 269), lower := (rows 7 74 148 41 50 288 64 128 256), losses := [] }

theorem u3167 : Upper (D 5) (R 5) [6,72,144,33,34,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3167
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3168 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 404, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 74 148 41 273 34 108 172 300), lower := (rows 7 74 148 41 273 34 64 128 256), losses := [] }

theorem u3168 : Upper (D 5) (R 5) [6,72,144,33,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3168
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3169 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 338, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 74 148 41 273 36 106 170 298), lower := (rows 7 74 148 41 273 36 64 128 256), losses := [] }

theorem u3169 : Upper (D 5) (R 5) [6,72,144,33,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3169
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3170 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 74 148 41 273 40 102 166 294), lower := (rows 7 74 148 41 273 40 64 128 256), losses := [] }

theorem u3170 : Upper (D 5) (R 5) [6,72,144,33,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3170
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3171 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 74 148 41 274 33 108 172 300), lower := (rows 7 74 148 41 274 33 64 128 256), losses := [] }

theorem u3171 : Upper (D 5) (R 5) [6,72,144,33,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3171
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3172 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 338, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 74 148 41 274 36 105 169 297), lower := (rows 7 74 148 41 274 36 64 128 256), losses := [] }

theorem u3172 : Upper (D 5) (R 5) [6,72,144,33,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3172
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3173 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 40, targets := 2 },{ cop := 0, region := 40, targets := 4 }], pairs := [(3,1),(3,2)], upper := (rows 7 74 148 41 274 40 101 165 293), lower := (rows 7 74 148 41 274 40 64 128 256), losses := [] }

theorem u3173 : Upper (D 5) (R 5) [6,72,144,33,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3173
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3174 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 74 148 41 280 33 102 166 294), lower := (rows 7 74 148 41 280 33 64 128 256), losses := [] }

theorem u3174 : Upper (D 5) (R 5) [6,72,144,33,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3174
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3175 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 404, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 74 148 41 280 34 101 165 293), lower := (rows 7 74 148 41 280 34 64 128 256), losses := [] }

theorem u3175 : Upper (D 5) (R 5) [6,72,144,33,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3175
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3176 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 338, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 74 148 41 280 36 99 163 291), lower := (rows 7 74 148 41 280 36 64 128 256), losses := [] }

theorem u3176 : Upper (D 5) (R 5) [6,72,144,33,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3176
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3177 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 74 148 41 304 33 78 142 270), lower := (rows 7 74 148 41 304 33 64 128 256), losses := [] }

theorem u3177 : Upper (D 5) (R 5) [6,72,144,33,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3177
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3178 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 404, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 74 148 41 304 34 77 141 269), lower := (rows 7 74 148 41 304 34 64 128 256), losses := [] }

theorem u3178 : Upper (D 5) (R 5) [6,72,144,33,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3178
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3179 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 338, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 74 148 41 304 36 75 139 267), lower := (rows 7 74 148 41 304 36 64 128 256), losses := [] }

theorem u3179 : Upper (D 5) (R 5) [6,72,144,33,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3179
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u3179
end Delivery.IrregularNine14.P05
