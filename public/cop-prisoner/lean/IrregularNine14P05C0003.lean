import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0000

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b180 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 68, targets := 1 }], pairs := [(2,0)], upper := (rows 7 19 76 140 56 288 96 131 259), lower := (rows 7 19 76 140 56 288 96 128 256), losses := [] }

theorem u180 : Upper (D 5) (R 5) [6,17,72,132,40,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b180
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b181 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 71, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 140 280 33 66 160 288), lower := (rows 7 19 76 140 280 33 66 128 256), losses := [] }

theorem u181 : Upper (D 5) (R 5) [6,17,72,132,264,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b181
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r182 : Route 9 := (fun mask => (mask,id))

def c182 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u182 : Upper (D 5) (R 5) [6,17,72,132,264,1,32] 13 := by
  apply FastRouting.sound _ _ [6,17,72,132,264,1,32] 13 (by decide) (choices 1) [2,32] r182 c182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14
  · exact u15

def b183 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 71, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 140 280 34 65 160 288), lower := (rows 7 19 76 140 280 34 65 128 256), losses := [] }

theorem u183 : Upper (D 5) (R 5) [6,17,72,132,264,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b183
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r184 : Route 9 := (fun mask => (mask,id))

def c184 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u184 : Upper (D 5) (R 5) [6,17,72,132,264,2,32] 13 := by
  apply FastRouting.sound _ _ [6,17,72,132,264,2,32] 13 (by decide) (choices 1) [1,32] r184 c184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16
  · exact u17

def b185 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 19 76 140 304 33 66 168 296), lower := (rows 7 19 76 140 304 33 66 128 256), losses := [] }

theorem u185 : Upper (D 5) (R 5) [6,17,72,132,288,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b185
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b186 : PairBound 9 := { available := 34, camps := [{ cop := 7, region := 76, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 76 140 304 33 72 162 290), lower := (rows 7 19 76 140 304 33 72 128 256), losses := [] }

theorem u186 : Upper (D 5) (R 5) [6,17,72,132,288,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b186
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b187 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 136, targets := 1 },{ cop := 0, region := 136, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 19 76 140 304 33 96 138 266), lower := (rows 7 19 76 140 304 33 96 128 256), losses := [] }

theorem u187 : Upper (D 5) (R 5) [6,17,72,132,288,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b187
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b188 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 19 76 140 304 34 65 168 296), lower := (rows 7 19 76 140 304 34 65 128 256), losses := [] }

theorem u188 : Upper (D 5) (R 5) [6,17,72,132,288,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b188
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b189 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 76, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 76 140 304 34 72 161 289), lower := (rows 7 19 76 140 304 34 72 128 256), losses := [] }

theorem u189 : Upper (D 5) (R 5) [6,17,72,132,288,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b189
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b190 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 19 76 140 304 34 96 137 265), lower := (rows 7 19 76 140 304 34 96 128 256), losses := [] }

theorem u190 : Upper (D 5) (R 5) [6,17,72,132,288,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b190
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b191 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 71, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 168 280 33 66 164 292), lower := (rows 7 19 76 168 280 33 66 128 256), losses := [] }

theorem u191 : Upper (D 5) (R 5) [6,17,72,160,264,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b191
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b192 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 19 76 168 280 33 68 162 290), lower := (rows 7 19 76 168 280 33 68 128 256), losses := [] }

theorem u192 : Upper (D 5) (R 5) [6,17,72,160,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b192
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b193 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 275, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 168 280 33 96 134 262), lower := (rows 7 19 76 168 280 33 96 128 256), losses := [] }

theorem u193 : Upper (D 5) (R 5) [6,17,72,160,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b193
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b194 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 71, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 168 280 34 65 164 292), lower := (rows 7 19 76 168 280 34 65 128 256), losses := [] }

theorem u194 : Upper (D 5) (R 5) [6,17,72,160,264,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b194
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b195 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 19 76 168 280 34 68 161 289), lower := (rows 7 19 76 168 280 34 68 128 256), losses := [] }

theorem u195 : Upper (D 5) (R 5) [6,17,72,160,264,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b195
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b196 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 275, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 168 280 34 96 133 261), lower := (rows 7 19 76 168 280 34 96 128 256), losses := [] }

theorem u196 : Upper (D 5) (R 5) [6,17,72,160,264,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b196
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b197 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 71, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 168 280 36 65 162 290), lower := (rows 7 19 76 168 280 36 65 128 256), losses := [] }

theorem u197 : Upper (D 5) (R 5) [6,17,72,160,264,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b197
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b198 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 71, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 168 280 36 66 161 289), lower := (rows 7 19 76 168 280 36 66 128 256), losses := [] }

theorem u198 : Upper (D 5) (R 5) [6,17,72,160,264,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b198
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b199 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 108, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 76 168 280 36 96 131 259), lower := (rows 7 19 76 168 280 36 96 128 256), losses := [] }

theorem u199 : Upper (D 5) (R 5) [6,17,72,160,264,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b199
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b200 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 19 76 168 304 33 66 140 268), lower := (rows 7 19 76 168 304 33 66 128 256), losses := [] }

theorem u200 : Upper (D 5) (R 5) [6,17,72,160,288,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b200
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b201 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 19 76 168 304 33 68 138 266), lower := (rows 7 19 76 168 304 33 68 128 256), losses := [] }

theorem u201 : Upper (D 5) (R 5) [6,17,72,160,288,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b201
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b202 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 307, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 76 168 304 33 72 134 262), lower := (rows 7 19 76 168 304 33 72 128 256), losses := [] }

theorem u202 : Upper (D 5) (R 5) [6,17,72,160,288,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b202
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b203 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 19 76 168 304 34 65 140 268), lower := (rows 7 19 76 168 304 34 65 128 256), losses := [] }

theorem u203 : Upper (D 5) (R 5) [6,17,72,160,288,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b203
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b204 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 19 76 168 304 34 68 137 265), lower := (rows 7 19 76 168 304 34 68 128 256), losses := [] }

theorem u204 : Upper (D 5) (R 5) [6,17,72,160,288,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b204
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b205 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 307, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 76 168 304 34 72 133 261), lower := (rows 7 19 76 168 304 34 72 128 256), losses := [] }

theorem u205 : Upper (D 5) (R 5) [6,17,72,160,288,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b205
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b206 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 19 76 168 304 36 65 138 266), lower := (rows 7 19 76 168 304 36 65 128 256), losses := [] }

theorem u206 : Upper (D 5) (R 5) [6,17,72,160,288,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b206
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b207 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 19 76 168 304 36 66 137 265), lower := (rows 7 19 76 168 304 36 66 128 256), losses := [] }

theorem u207 : Upper (D 5) (R 5) [6,17,72,160,288,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b207
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b208 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 108, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 76 168 304 36 72 131 259), lower := (rows 7 19 76 168 304 36 72 128 256), losses := [] }

theorem u208 : Upper (D 5) (R 5) [6,17,72,160,288,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b208
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b209 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 71, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 392 56 33 66 164 292), lower := (rows 7 19 76 392 56 33 66 128 256), losses := [] }

theorem u209 : Upper (D 5) (R 5) [6,17,72,384,40,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b209
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b210 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 19 76 392 56 33 68 162 290), lower := (rows 7 19 76 392 56 33 68 128 256), losses := [] }

theorem u210 : Upper (D 5) (R 5) [6,17,72,384,40,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b210
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b211 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 76 392 56 33 96 134 262), lower := (rows 7 19 76 392 56 33 96 128 256), losses := [] }

theorem u211 : Upper (D 5) (R 5) [6,17,72,384,40,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b211
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b212 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 71, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 392 56 34 65 164 292), lower := (rows 7 19 76 392 56 34 65 128 256), losses := [] }

theorem u212 : Upper (D 5) (R 5) [6,17,72,384,40,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b212
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b213 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 19 76 392 56 34 68 161 289), lower := (rows 7 19 76 392 56 34 68 128 256), losses := [] }

theorem u213 : Upper (D 5) (R 5) [6,17,72,384,40,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b213
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b214 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 392, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 19 76 392 56 34 96 133 261), lower := (rows 7 19 76 392 56 34 96 128 256), losses := [] }

theorem u214 : Upper (D 5) (R 5) [6,17,72,384,40,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b214
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b215 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 296, targets := 2 }], pairs := [(3,1)], upper := (rows 7 19 100 41 152 288 66 140 268), lower := (rows 7 19 100 41 152 288 66 128 256), losses := [] }

theorem u215 : Upper (D 5) (R 5) [6,17,96,33,136,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b215
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b216 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2)], upper := (rows 7 19 100 41 152 288 68 138 266), lower := (rows 7 19 100 41 152 288 68 128 256), losses := [] }

theorem u216 : Upper (D 5) (R 5) [6,17,96,33,136,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b216
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b217 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 68, targets := 1 }], pairs := [(2,0)], upper := (rows 7 19 100 41 152 288 72 134 262), lower := (rows 7 19 100 41 152 288 72 128 256), losses := [] }

theorem u217 : Upper (D 5) (R 5) [6,17,96,33,136,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b217
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b218 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 296, targets := 1 }], pairs := [(3,0)], upper := (rows 7 19 100 42 152 288 65 140 268), lower := (rows 7 19 100 42 152 288 65 128 256), losses := [] }

theorem u218 : Upper (D 5) (R 5) [6,17,96,34,136,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b218
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b219 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2)], upper := (rows 7 19 100 42 152 288 68 137 265), lower := (rows 7 19 100 42 152 288 68 128 256), losses := [] }

theorem u219 : Upper (D 5) (R 5) [6,17,96,34,136,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b219
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b220 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 68, targets := 1 }], pairs := [(2,0)], upper := (rows 7 19 100 42 152 288 72 133 261), lower := (rows 7 19 100 42 152 288 72 128 256), losses := [] }

theorem u220 : Upper (D 5) (R 5) [6,17,96,34,136,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b220
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b221 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 19 100 137 280 40 66 164 292), lower := (rows 7 19 100 137 280 40 66 128 256), losses := [] }

theorem u221 : Upper (D 5) (R 5) [6,17,96,129,264,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b221
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b222 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 19 100 137 280 40 68 162 290), lower := (rows 7 19 100 137 280 40 68 128 256), losses := [] }

theorem u222 : Upper (D 5) (R 5) [6,17,96,129,264,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b222
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b223 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 100 137 280 40 96 134 262), lower := (rows 7 19 100 137 280 40 96 128 256), losses := [] }

theorem u223 : Upper (D 5) (R 5) [6,17,96,129,264,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b223
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b224 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 71, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 100 137 304 40 66 140 268), lower := (rows 7 19 100 137 304 40 66 128 256), losses := [] }

theorem u224 : Upper (D 5) (R 5) [6,17,96,129,288,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b224
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b225 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 19 100 137 304 40 68 138 266), lower := (rows 7 19 100 137 304 40 68 128 256), losses := [] }

theorem u225 : Upper (D 5) (R 5) [6,17,96,129,288,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b225
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b226 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 275, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 100 137 304 40 72 134 262), lower := (rows 7 19 100 137 304 40 72 128 256), losses := [] }

theorem u226 : Upper (D 5) (R 5) [6,17,96,129,288,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b226
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b227 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 71, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 100 138 304 40 65 140 268), lower := (rows 7 19 100 138 304 40 65 128 256), losses := [] }

theorem u227 : Upper (D 5) (R 5) [6,17,96,130,288,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b227
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b228 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 19 100 138 304 40 68 137 265), lower := (rows 7 19 100 138 304 40 68 128 256), losses := [] }

theorem u228 : Upper (D 5) (R 5) [6,17,96,130,288,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b228
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b229 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 275, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 100 138 304 40 72 133 261), lower := (rows 7 19 100 138 304 40 72 128 256), losses := [] }

theorem u229 : Upper (D 5) (R 5) [6,17,96,130,288,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b229
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b230 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 136, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 19 100 140 280 33 66 168 296), lower := (rows 7 19 100 140 280 33 66 128 256), losses := [] }

theorem u230 : Upper (D 5) (R 5) [6,17,96,132,264,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b230
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r231 : Route 9 := (fun mask => (mask,id))

def c231 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u231 : Upper (D 5) (R 5) [6,17,96,132,264,1,8] 13 := by
  apply FastRouting.sound _ _ [6,17,96,132,264,1,8] 13 (by decide) (choices 1) [2,32] r231 c231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18
  · exact u19

def b232 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 100 140 280 33 96 138 266), lower := (rows 7 19 100 140 280 33 96 128 256), losses := [] }

theorem u232 : Upper (D 5) (R 5) [6,17,96,132,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b232
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b233 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 136, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 19 100 140 280 34 65 168 296), lower := (rows 7 19 100 140 280 34 65 128 256), losses := [] }

theorem u233 : Upper (D 5) (R 5) [6,17,96,132,264,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b233
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r234 : Route 9 := (fun mask => (mask,id))

def c234 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u234 : Upper (D 5) (R 5) [6,17,96,132,264,2,8] 13 := by
  apply FastRouting.sound _ _ [6,17,96,132,264,2,8] 13 (by decide) (choices 1) [1,32] r234 c234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20
  · exact u21

def b235 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 100 140 280 34 96 137 265), lower := (rows 7 19 100 140 280 34 96 128 256), losses := [] }

theorem u235 : Upper (D 5) (R 5) [6,17,96,132,264,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b235
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b236 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 19 100 140 280 40 65 162 290), lower := (rows 7 19 100 140 280 40 65 128 256), losses := [] }

theorem u236 : Upper (D 5) (R 5) [6,17,96,132,264,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b236
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b237 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 19 100 140 280 40 66 161 289), lower := (rows 7 19 100 140 280 40 66 128 256), losses := [] }

theorem u237 : Upper (D 5) (R 5) [6,17,96,132,264,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b237
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b238 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 100 140 280 40 96 131 259), lower := (rows 7 19 100 140 280 40 96 128 256), losses := [] }

theorem u238 : Upper (D 5) (R 5) [6,17,96,132,264,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b238
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b239 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 71, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 100 140 304 40 65 138 266), lower := (rows 7 19 100 140 304 40 65 128 256), losses := [] }

theorem u239 : Upper (D 5) (R 5) [6,17,96,132,288,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b239
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u239
end Delivery.IrregularNine14.P05
