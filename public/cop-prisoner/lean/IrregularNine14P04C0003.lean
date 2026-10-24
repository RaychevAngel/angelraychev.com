import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P04C0000

namespace Delivery.IrregularNine14.P04
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b180 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 42 84 137 273 36 90 154 282), lower := (rows 7 42 84 137 273 36 64 128 256), losses := [] }

theorem u180 : Upper (D 4) (R 4) [6,40,80,129,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b180
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b181 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 341, targets := 8 }], pairs := [(0,3)], upper := (rows 7 42 84 137 273 40 86 150 278), lower := (rows 7 42 84 137 273 40 64 128 256), losses := [] }

theorem u181 : Upper (D 4) (R 4) [6,40,80,129,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b181
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b182 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 136, targets := 16 }], pairs := [(3,4)], upper := (rows 7 42 84 137 273 48 78 142 270), lower := (rows 7 42 84 137 273 48 64 128 256), losses := [] }

theorem u182 : Upper (D 4) (R 4) [6,40,80,129,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b182
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b183 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 340, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 84 137 274 33 92 156 284), lower := (rows 7 42 84 137 274 33 64 128 256), losses := [] }

theorem u183 : Upper (D 4) (R 4) [6,40,80,129,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b183
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b184 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 42 84 137 274 36 89 153 281), lower := (rows 7 42 84 137 274 36 64 128 256), losses := [] }

theorem u184 : Upper (D 4) (R 4) [6,40,80,129,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b184
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b185 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 341, targets := 8 }], pairs := [(0,3)], upper := (rows 7 42 84 137 274 40 85 149 277), lower := (rows 7 42 84 137 274 40 64 128 256), losses := [] }

theorem u185 : Upper (D 4) (R 4) [6,40,80,129,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b185
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b186 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 136, targets := 2 }], pairs := [(3,1)], upper := (rows 7 42 84 137 274 48 77 141 269), lower := (rows 7 42 84 137 274 48 64 128 256), losses := [] }

theorem u186 : Upper (D 4) (R 4) [6,40,80,129,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b186
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b187 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 340, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 84 137 276 33 90 154 282), lower := (rows 7 42 84 137 276 33 64 128 256), losses := [] }

theorem u187 : Upper (D 4) (R 4) [6,40,80,129,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b187
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b188 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1)], upper := (rows 7 42 84 137 276 34 89 153 281), lower := (rows 7 42 84 137 276 34 64 128 256), losses := [] }

theorem u188 : Upper (D 4) (R 4) [6,40,80,129,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b188
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b189 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 341, targets := 8 }], pairs := [(0,3)], upper := (rows 7 42 84 137 276 40 83 147 275), lower := (rows 7 42 84 137 276 40 64 128 256), losses := [] }

theorem u189 : Upper (D 4) (R 4) [6,40,80,129,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b189
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b190 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 136, targets := 4 }], pairs := [(3,2)], upper := (rows 7 42 84 137 276 48 75 139 267), lower := (rows 7 42 84 137 276 48 64 128 256), losses := [] }

theorem u190 : Upper (D 4) (R 4) [6,40,80,129,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b190
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b191 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 340, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 84 137 280 33 86 150 278), lower := (rows 7 42 84 137 280 33 64 128 256), losses := [] }

theorem u191 : Upper (D 4) (R 4) [6,40,80,129,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b191
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b192 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1)], upper := (rows 7 42 84 137 280 34 85 149 277), lower := (rows 7 42 84 137 280 34 64 128 256), losses := [] }

theorem u192 : Upper (D 4) (R 4) [6,40,80,129,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b192
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b193 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 42 84 137 280 36 83 147 275), lower := (rows 7 42 84 137 280 36 64 128 256), losses := [] }

theorem u193 : Upper (D 4) (R 4) [6,40,80,129,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b193
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b194 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 84 137 280 48 71 135 263), lower := (rows 7 42 84 137 280 48 64 128 256), losses := [] }

theorem u194 : Upper (D 4) (R 4) [6,40,80,129,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b194
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r195 : Route 9 := (fun mask => (mask,id))

def c195 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u195 : Upper (D 4) (R 4) [6,40,80,130,260,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130,260,1] 13 (by decide) (choices 1) [1,8,16] r195 c195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29
  · exact u30
  · exact u31

def b196 : PairBound 9 := { available := 17, camps := [{ cop := 7, region := 42, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 84 138 276 40 81 145 273), lower := (rows 7 42 84 138 276 40 64 128 256), losses := [] }

theorem u196 : Upper (D 4) (R 4) [6,40,80,130,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b196
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b197 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 4 }], pairs := [(3,2)], upper := (rows 7 42 84 138 276 48 73 137 265), lower := (rows 7 42 84 138 276 48 64 128 256), losses := [] }

theorem u197 : Upper (D 4) (R 4) [6,40,80,130,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b197
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r198 : Route 9 := (fun mask => (mask,id))

def c198 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u198 : Upper (D 4) (R 4) [6,40,80,130,264,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130,264,1] 13 (by decide) (choices 1) [1,4,16] r198 c198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u32
  · exact u33
  · exact u34

def b199 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 42 84 138 280 36 81 145 273), lower := (rows 7 42 84 138 280 36 64 128 256), losses := [] }

theorem u199 : Upper (D 4) (R 4) [6,40,80,130,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b199
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b200 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 84 138 280 48 69 133 261), lower := (rows 7 42 84 138 280 48 64 128 256), losses := [] }

theorem u200 : Upper (D 4) (R 4) [6,40,80,130,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b200
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b201 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 35, targets := 16 }], pairs := [(0,4)], upper := (rows 7 42 84 140 274 33 89 153 281), lower := (rows 7 42 84 140 274 33 64 128 256), losses := [] }

theorem u201 : Upper (D 4) (R 4) [6,40,80,132,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b201
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b202 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 341, targets := 8 }], pairs := [(0,3)], upper := (rows 7 42 84 140 274 40 81 145 273), lower := (rows 7 42 84 140 274 40 64 128 256), losses := [] }

theorem u202 : Upper (D 4) (R 4) [6,40,80,132,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b202
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b203 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 2 }], pairs := [(3,1)], upper := (rows 7 42 84 140 274 48 73 137 265), lower := (rows 7 42 84 140 274 48 64 128 256), losses := [] }

theorem u203 : Upper (D 4) (R 4) [6,40,80,132,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b203
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b204 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 35, targets := 16 }], pairs := [(0,4)], upper := (rows 7 42 84 140 280 33 83 147 275), lower := (rows 7 42 84 140 280 33 64 128 256), losses := [] }

theorem u204 : Upper (D 4) (R 4) [6,40,80,132,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b204
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b205 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1)], upper := (rows 7 42 84 140 280 34 81 145 273), lower := (rows 7 42 84 140 280 34 64 128 256), losses := [] }

theorem u205 : Upper (D 4) (R 4) [6,40,80,132,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b205
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b206 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 84 140 280 48 67 131 259), lower := (rows 7 42 84 140 280 48 64 128 256), losses := [] }

theorem u206 : Upper (D 4) (R 4) [6,40,80,132,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b206
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r207 : Route 9 := (fun mask => (mask,id))

def c207 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u207 : Upper (D 4) (R 4) [6,40,80,144,264,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,144,264,1] 13 (by decide) (choices 1) [1,2,4] r207 c207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u35
  · exact u36
  · exact u37

def b208 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1)], upper := (rows 7 42 84 152 280 34 69 133 261), lower := (rows 7 42 84 152 280 34 64 128 256), losses := [] }

theorem u208 : Upper (D 4) (R 4) [6,40,80,144,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b208
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b209 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 42 84 152 280 36 67 131 259), lower := (rows 7 42 84 152 280 36 64 128 256), losses := [] }

theorem u209 : Upper (D 4) (R 4) [6,40,80,144,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b209
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b210 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 35, targets := 16 }], pairs := [(0,4)], upper := (rows 7 42 196 28 273 33 90 154 282), lower := (rows 7 42 196 28 273 33 64 128 256), losses := [] }

theorem u210 : Upper (D 4) (R 4) [6,40,192,20,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b210
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b211 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1)], upper := (rows 7 42 196 28 273 34 89 153 281), lower := (rows 7 42 196 28 273 34 64 128 256), losses := [] }

theorem u211 : Upper (D 4) (R 4) [6,40,192,20,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b211
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b212 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 469, targets := 8 }], pairs := [(0,3)], upper := (rows 7 42 196 28 273 40 83 147 275), lower := (rows 7 42 196 28 273 40 64 128 256), losses := [] }

theorem u212 : Upper (D 4) (R 4) [6,40,192,20,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b212
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b213 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 197, targets := 16 }], pairs := [(0,4)], upper := (rows 7 42 196 28 273 48 75 139 267), lower := (rows 7 42 196 28 273 48 64 128 256), losses := [] }

theorem u213 : Upper (D 4) (R 4) [6,40,192,20,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b213
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b214 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 35, targets := 16 }], pairs := [(0,4)], upper := (rows 7 42 196 28 274 33 89 153 281), lower := (rows 7 42 196 28 274 33 64 128 256), losses := [] }

theorem u214 : Upper (D 4) (R 4) [6,40,192,20,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b214
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b215 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 469, targets := 8 }], pairs := [(0,3)], upper := (rows 7 42 196 28 274 40 81 145 273), lower := (rows 7 42 196 28 274 40 64 128 256), losses := [] }

theorem u215 : Upper (D 4) (R 4) [6,40,192,20,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b215
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b216 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 197, targets := 16 }], pairs := [(0,4)], upper := (rows 7 42 196 28 274 48 73 137 265), lower := (rows 7 42 196 28 274 48 64 128 256), losses := [] }

theorem u216 : Upper (D 4) (R 4) [6,40,192,20,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b216
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b217 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 35, targets := 16 }], pairs := [(0,4)], upper := (rows 7 42 196 266 28 33 81 145 273), lower := (rows 7 42 196 266 28 33 64 128 256), losses := [] }

theorem u217 : Upper (D 4) (R 4) [6,40,192,258,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b217
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b218 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 196 266 28 48 81 145 273), lower := (rows 7 42 196 266 28 48 64 128 256), losses := [] }

theorem u218 : Upper (D 4) (R 4) [6,40,192,258,12,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b218
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b219 : PairBound 9 := { available := 402, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 7 7 13 56 88 434 466 402 402), lower := (rows 7 7 13 56 88 32 64 128 256), losses := [] }

theorem u219 : Upper (D 4) (R 4) [6,5,9,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b219
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b220 : PairBound 9 := { available := 282, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 7 7 13 56 208 314 346 410 282), lower := (rows 7 7 13 56 208 32 64 128 256), losses := [] }

theorem u220 : Upper (D 4) (R 4) [6,5,9,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b220
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b221 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 7 7 13 104 152 306 338 402 274), lower := (rows 7 7 13 104 152 32 64 128 256), losses := [] }

theorem u221 : Upper (D 4) (R 4) [6,5,9,96,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b221
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b222 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 7 7 13 104 400 58 90 154 282), lower := (rows 7 7 13 104 400 32 64 128 256), losses := [] }

theorem u222 : Upper (D 4) (R 4) [6,5,9,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b222
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b223 : PairBound 9 := { available := 408, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 28 41 82 440 472 408 408), lower := (rows 7 7 28 41 82 32 64 128 256), losses := [] }

theorem u223 : Upper (D 4) (R 4) [6,5,24,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b223
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b224 : PairBound 9 := { available := 282, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 28 41 208 314 346 410 282), lower := (rows 7 7 28 41 208 32 64 128 256), losses := [] }

theorem u224 : Upper (D 4) (R 4) [6,5,24,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b224
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b225 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 28 104 400 59 91 155 283), lower := (rows 7 7 28 104 400 32 64 128 256), losses := [] }

theorem u225 : Upper (D 4) (R 4) [6,5,24,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b225
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b226 : PairBound 9 := { available := 282, camps := [{ cop := 5, region := 7, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 37 88 152 314 346 410 282), lower := (rows 7 7 37 88 152 32 64 128 256), losses := [] }

theorem u226 : Upper (D 4) (R 4) [6,5,33,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b226
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b227 : PairBound 9 := { available := 26, camps := [{ cop := 5, region := 7, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 37 88 400 58 90 154 282), lower := (rows 7 7 37 88 400 32 64 128 256), losses := [] }

theorem u227 : Upper (D 4) (R 4) [6,5,33,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b227
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b228 : PairBound 9 := { available := 402, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 44 25 88 434 466 402 402), lower := (rows 7 7 44 25 88 32 64 128 256), losses := [] }

theorem u228 : Upper (D 4) (R 4) [6,5,40,17,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b228
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b229 : PairBound 9 := { available := 282, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 44 25 208 314 346 410 282), lower := (rows 7 7 44 25 208 32 64 128 256), losses := [] }

theorem u229 : Upper (D 4) (R 4) [6,5,40,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b229
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b230 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 44 73 152 306 338 402 274), lower := (rows 7 7 44 73 152 32 64 128 256), losses := [] }

theorem u230 : Upper (D 4) (R 4) [6,5,40,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b230
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b231 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 44 73 400 58 90 154 282), lower := (rows 7 7 44 73 400 32 64 128 256), losses := [] }

theorem u231 : Upper (D 4) (R 4) [6,5,40,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b231
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b232 : PairBound 9 := { available := 402, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 44 88 25 434 466 402 402), lower := (rows 7 7 44 88 25 32 64 128 256), losses := [] }

theorem u232 : Upper (D 4) (R 4) [6,5,40,80,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b232
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b233 : PairBound 9 := { available := 282, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 44 88 145 314 346 410 282), lower := (rows 7 7 44 88 145 32 64 128 256), losses := [] }

theorem u233 : Upper (D 4) (R 4) [6,5,40,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b233
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b234 : PairBound 9 := { available := 275, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 44 88 152 307 339 403 275), lower := (rows 7 7 44 88 152 32 64 128 256), losses := [] }

theorem u234 : Upper (D 4) (R 4) [6,5,40,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b234
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b235 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 44 88 400 59 91 155 283), lower := (rows 7 7 44 88 400 32 64 128 256), losses := [] }

theorem u235 : Upper (D 4) (R 4) [6,5,40,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b235
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b236 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 44 200 25 306 338 402 274), lower := (rows 7 7 44 200 25 32 64 128 256), losses := [] }

theorem u236 : Upper (D 4) (R 4) [6,5,40,192,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b236
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b237 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 44 200 273 58 90 154 282), lower := (rows 7 7 44 200 273 32 64 128 256), losses := [] }

theorem u237 : Upper (D 4) (R 4) [6,5,40,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b237
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b238 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 44 200 280 51 83 147 275), lower := (rows 7 7 44 200 280 32 64 128 256), losses := [] }

theorem u238 : Upper (D 4) (R 4) [6,5,40,192,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b238
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b239 : PairBound 9 := { available := 282, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 100 25 152 314 346 410 282), lower := (rows 7 7 100 25 152 32 64 128 256), losses := [] }

theorem u239 : Upper (D 4) (R 4) [6,5,96,17,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b239
    (constants 4).1 (constants 4).2 (by decide +kernel)

#print axioms u239
end Delivery.IrregularNine14.P04
