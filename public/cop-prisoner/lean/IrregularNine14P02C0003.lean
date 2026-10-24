import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0000

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b180 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 7 76 392 48 160 336 464 336), lower := (rows 51 7 76 392 48 160 64 128 256), losses := [] }

theorem u180 : Upper (D 2) (R 2) [50,5,72,384,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b180
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b181 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(0,8),(3,6)], upper := (rows 51 7 76 392 80 160 368 432 304), lower := (rows 51 7 76 392 80 160 64 128 256), losses := [{ target := 8, region := (rows 5 6 4 8 84 168 64 128 0), good := (rows 51 23 127 168 80 160 80 160 0) }] }

theorem u181 : Upper (D 2) (R 2) [50,5,72,384,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b181
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b182 : PairBound 9 := { available := 112, camps := [], pairs := [(0,6),(1,6)], upper := (rows 51 7 76 392 144 288 112 240 368), lower := (rows 51 7 76 392 144 288 64 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 152 296 0 128 256), good := (rows 51 7 63 440 144 288 0 144 288) }] }

theorem u182 : Upper (D 2) (R 2) [50,5,72,384,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b182
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b183 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 51 7 84 200 272 40 480 416 416), lower := (rows 51 7 84 200 272 40 64 128 256), losses := [] }

theorem u183 : Upper (D 2) (R 2) [50,5,80,192,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b183
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r184 : Route 9 := (fun mask => (mask,id))

def c184 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u184 : Upper (D 2) (R 2) [50,5,80,192,256,128] 13 := by
  apply FastRouting.sound _ _ [50,5,80,192,256,128] 13 (by decide) (choices 1) [8,32,256] r184 c184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u30
  · exact u31
  · exact u32

def b185 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 206, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 51 7 84 200 272 288 232 168 424), lower := (rows 51 7 84 200 272 288 64 128 256), losses := [] }

theorem u185 : Upper (D 2) (R 2) [50,5,80,192,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b185
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b186 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 326, targets := 128 }], pairs := [(1,7)], upper := (rows 51 7 84 392 144 40 352 480 352), lower := (rows 51 7 84 392 144 40 64 128 256), losses := [] }

theorem u186 : Upper (D 2) (R 2) [50,5,80,384,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b186
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b187 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 51 7 84 392 144 96 360 424 296), lower := (rows 51 7 84 392 144 96 64 128 256), losses := [] }

theorem u187 : Upper (D 2) (R 2) [50,5,80,384,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b187
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r188 : Route 9 := (fun mask => (mask,id))

def c188 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u188 : Upper (D 2) (R 2) [50,5,80,384,128,256] 13 := by
  apply FastRouting.sound _ _ [50,5,80,384,128,256] 13 (by decide) (choices 1) [8,32] r188 c188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u33
  · exact u34

def b189 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 454, targets := 16 }], pairs := [(1,4)], upper := (rows 51 7 196 88 272 40 480 416 416), lower := (rows 51 7 196 88 272 40 64 128 256), losses := [] }

theorem u189 : Upper (D 2) (R 2) [50,5,192,80,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b189
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b190 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 328, targets := 128 },{ cop := 3, region := 420, targets := 16 }], pairs := [(2,4),(3,7)], upper := (rows 51 7 196 88 272 160 360 424 296), lower := (rows 51 7 196 88 272 160 64 128 256), losses := [] }

theorem u190 : Upper (D 2) (R 2) [50,5,192,80,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b190
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b191 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 206, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 51 7 196 88 272 288 232 168 424), lower := (rows 51 7 196 88 272 288 64 128 256), losses := [] }

theorem u191 : Upper (D 2) (R 2) [50,5,192,80,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b191
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b192 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 454, targets := 16 }], pairs := [(1,4)], upper := (rows 51 7 196 328 24 48 480 416 416), lower := (rows 51 7 196 328 24 48 64 128 256), losses := [] }

theorem u192 : Upper (D 2) (R 2) [50,5,192,320,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b192
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b193 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(3,7)], upper := (rows 51 7 196 328 24 160 368 432 304), lower := (rows 51 7 196 328 24 160 64 128 256), losses := [] }

theorem u193 : Upper (D 2) (R 2) [50,5,192,320,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b193
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b194 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 198, targets := 256 }], pairs := [(1,8)], upper := (rows 51 7 196 328 24 288 240 176 432), lower := (rows 51 7 196 328 24 288 64 128 256), losses := [] }

theorem u194 : Upper (D 2) (R 2) [50,5,192,320,8,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b194
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b195 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 51, targets := 320 }], pairs := [(0,6),(0,8)], upper := (rows 51 7 196 328 48 160 344 408 280), lower := (rows 51 7 196 328 48 160 64 128 256), losses := [] }

theorem u195 : Upper (D 2) (R 2) [50,5,192,320,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b195
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b196 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 7 196 328 48 288 216 152 408), lower := (rows 51 7 196 328 48 288 64 128 256), losses := [] }

theorem u196 : Upper (D 2) (R 2) [50,5,192,320,32,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b196
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r197 : Route 9 := (fun mask => (mask,id))

def c197 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u197 : Upper (D 2) (R 2) [50,5,192,320,128,256] 13 := by
  apply FastRouting.sound _ _ [50,5,192,320,128,256] 13 (by decide) (choices 1) [8,16,32] r197 c197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u35
  · exact u36
  · exact u37

def b198 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 452, targets := 16 },{ cop := 0, region := 392, targets := 64 }], pairs := [(2,4),(3,6)], upper := (rows 51 14 69 152 272 96 480 416 416), lower := (rows 51 14 69 152 272 96 64 128 256), losses := [] }

theorem u198 : Upper (D 2) (R 2) [50,12,65,144,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b198
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b199 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 324, targets := 16 },{ cop := 0, region := 324, targets := 128 }], pairs := [(2,4),(2,7)], upper := (rows 51 14 69 152 272 160 352 480 352), lower := (rows 51 14 69 152 272 160 64 128 256), losses := [] }

theorem u199 : Upper (D 2) (R 2) [50,12,65,144,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b199
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b200 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 206, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 51 14 69 152 272 288 224 224 480), lower := (rows 51 14 69 152 272 288 64 128 256), losses := [] }

theorem u200 : Upper (D 2) (R 2) [50,12,65,144,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b200
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b201 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 14 69 200 48 288 464 400 400), lower := (rows 51 14 69 200 48 288 64 128 256), losses := [] }

theorem u201 : Upper (D 2) (R 2) [50,12,65,192,32,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b201
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b202 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 324, targets := 128 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(2,7)], upper := (rows 51 14 69 200 144 288 368 432 304), lower := (rows 51 14 69 200 144 288 64 128 256), losses := [] }

theorem u202 : Upper (D 2) (R 2) [50,12,65,192,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b202
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b203 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 206, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 51 14 69 200 272 288 240 176 432), lower := (rows 51 14 69 200 272 288 64 128 256), losses := [] }

theorem u203 : Upper (D 2) (R 2) [50,12,65,192,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b203
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b204 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 14 69 392 48 160 336 464 336), lower := (rows 51 14 69 392 48 160 64 128 256), losses := [] }

theorem u204 : Upper (D 2) (R 2) [50,12,65,384,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b204
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b205 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 392, targets := 64 },{ cop := 0, region := 324, targets := 128 }], pairs := [(2,7),(3,6)], upper := (rows 51 14 69 392 80 160 368 432 304), lower := (rows 51 14 69 392 80 160 64 128 256), losses := [] }

theorem u205 : Upper (D 2) (R 2) [50,12,65,384,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b205
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b206 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 68, targets := 128 },{ cop := 0, region := 68, targets := 256 }], pairs := [(2,7),(2,8)], upper := (rows 51 14 69 392 144 288 112 240 368), lower := (rows 51 14 69 392 144 288 64 128 256), losses := [] }

theorem u206 : Upper (D 2) (R 2) [50,12,65,384,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b206
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b207 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 67 76 392 20 160 368 432 304), lower := (rows 51 67 76 392 20 160 64 128 256), losses := [] }

theorem u207 : Upper (D 2) (R 2) [50,65,72,384,4,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b207
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b208 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 67 76 392 48 160 340 404 276), lower := (rows 51 67 76 392 48 160 64 128 256), losses := [] }

theorem u208 : Upper (D 2) (R 2) [50,65,72,384,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b208
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m209_32 : Upper (D 2) (R 2) [50,65,72,384,128,256,32] 13 :=
  permutation_upper _ _ _ [50,65,72,384,128,256,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39

def r209 : Route 9 := (fun mask => (mask,id))

def c209 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u209 : Upper (D 2) (R 2) [50,65,72,384,128,256] 13 := by
  apply FastRouting.sound _ _ [50,65,72,384,128,256] 13 (by decide) (choices 1) [4,16,32] r209 c209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u38
  · exact u39
  · exact m209_32

def b210 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(1,7)], upper := (rows 51 67 140 280 144 36 352 480 352), lower := (rows 51 67 140 280 144 36 64 128 256), losses := [] }

theorem u210 : Upper (D 2) (R 2) [50,65,136,272,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b210
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b211 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 67 140 280 144 96 356 420 292), lower := (rows 51 67 140 280 144 96 64 128 256), losses := [] }

theorem u211 : Upper (D 2) (R 2) [50,65,136,272,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b211
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r212 : Route 9 := (fun mask => (mask,id))

def c212 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u212 : Upper (D 2) (R 2) [50,65,136,272,128,256] 13 := by
  apply FastRouting.sound _ _ [50,65,136,272,128,256] 13 (by decide) (choices 1) [4,32] r212 c212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u40
  · exact u41

def b213 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(1,7)], upper := (rows 51 67 140 328 20 160 368 432 304), lower := (rows 51 67 140 328 20 160 64 128 256), losses := [] }

theorem u213 : Upper (D 2) (R 2) [50,65,136,320,4,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b213
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b214 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 194, targets := 256 }], pairs := [(1,8)], upper := (rows 51 67 140 328 20 288 240 176 432), lower := (rows 51 67 140 328 20 288 64 128 256), losses := [] }

theorem u214 : Upper (D 2) (R 2) [50,65,136,320,4,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b214
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b215 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 67 140 328 48 160 340 404 276), lower := (rows 51 67 140 328 48 160 64 128 256), losses := [] }

theorem u215 : Upper (D 2) (R 2) [50,65,136,320,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b215
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b216 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 67 140 328 48 288 212 148 404), lower := (rows 51 67 140 328 48 288 64 128 256), losses := [] }

theorem u216 : Upper (D 2) (R 2) [50,65,136,320,32,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b216
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r217 : Route 9 := (fun mask => (mask,id))

def c217 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u217 : Upper (D 2) (R 2) [50,65,136,320,128,256] 13 := by
  apply FastRouting.sound _ _ [50,65,136,320,128,256] 13 (by decide) (choices 1) [4,16,32] r217 c217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u42
  · exact u43
  · exact u44

def b218 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 67 196 392 20 288 120 184 312), lower := (rows 51 67 196 392 20 288 64 128 256), losses := [] }

theorem u218 : Upper (D 2) (R 2) [50,65,192,384,4,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b218
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b219 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 198, targets := 256 }], pairs := [(1,8)], upper := (rows 51 67 196 392 24 288 116 180 308), lower := (rows 51 67 196 392 24 288 64 128 256), losses := [] }

theorem u219 : Upper (D 2) (R 2) [50,65,192,384,8,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b219
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b220 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 67 196 392 48 288 92 156 284), lower := (rows 51 67 196 392 48 288 64 128 256), losses := [] }

theorem u220 : Upper (D 2) (R 2) [50,65,192,384,32,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b220
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b221 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 13 152 272 96 480 416 416), lower := (rows 51 70 13 152 272 96 64 128 256), losses := [] }

theorem u221 : Upper (D 2) (R 2) [50,68,9,144,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b221
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b222 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4),(1,7)], upper := (rows 51 70 13 152 272 160 352 480 352), lower := (rows 51 70 13 152 272 160 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 8 309 32 97 0 289), good := (rows 371 86 351 24 272 368 64 0 272) }] }

theorem u222 : Upper (D 2) (R 2) [50,68,9,144,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b222
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b223 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 206, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 51 70 13 152 272 288 224 224 480), lower := (rows 51 70 13 152 272 288 64 128 256), losses := [] }

theorem u223 : Upper (D 2) (R 2) [50,68,9,144,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b223
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b224 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 13 200 48 288 464 400 400), lower := (rows 51 70 13 200 48 288 64 128 256), losses := [] }

theorem u224 : Upper (D 2) (R 2) [50,68,9,192,32,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b224
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b225 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(1,7)], upper := (rows 51 70 13 200 144 288 368 432 304), lower := (rows 51 70 13 200 144 288 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 8 16 309 81 0 273), good := (rows 371 102 367 72 368 288 64 0 288) }] }

theorem u225 : Upper (D 2) (R 2) [50,68,9,192,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b225
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b226 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 206, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 51 70 13 200 272 288 240 176 432), lower := (rows 51 70 13 200 272 288 64 128 256), losses := [] }

theorem u226 : Upper (D 2) (R 2) [50,68,9,192,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b226
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b227 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 13 392 48 160 336 464 336), lower := (rows 51 70 13 392 48 160 64 128 256), losses := [] }

theorem u227 : Upper (D 2) (R 2) [50,68,9,384,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b227
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b228 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 13 392 80 160 368 432 304), lower := (rows 51 70 13 392 80 160 64 128 256), losses := [] }

theorem u228 : Upper (D 2) (R 2) [50,68,9,384,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b228
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b229 : PairBound 9 := { available := 112, camps := [], pairs := [(1,7),(1,8)], upper := (rows 51 70 13 392 144 288 112 240 368), lower := (rows 51 70 13 392 144 288 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 8 16 317 81 0 273), good := (rows 371 102 367 296 368 288 64 0 288) },{ target := 8, region := (rows 1 6 4 8 189 32 97 161 0), good := (rows 243 86 223 152 144 240 64 144 0) }] }

theorem u229 : Upper (D 2) (R 2) [50,68,9,384,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b229
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b230 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 342, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 28 168 272 33 448 448 448), lower := (rows 51 70 28 168 272 33 64 128 256), losses := [] }

theorem u230 : Upper (D 2) (R 2) [50,68,24,160,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b230
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b231 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 28 168 272 96 449 385 385), lower := (rows 51 70 28 168 272 96 64 128 256), losses := [] }

theorem u231 : Upper (D 2) (R 2) [50,68,24,160,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b231
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b232 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 51 70 28 168 272 160 321 449 321), lower := (rows 51 70 28 168 272 160 64 128 256), losses := [] }

theorem u232 : Upper (D 2) (R 2) [50,68,24,160,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b232
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b233 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 206, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 51 70 28 168 272 288 193 193 449), lower := (rows 51 70 28 168 272 288 64 128 256), losses := [] }

theorem u233 : Upper (D 2) (R 2) [50,68,24,160,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b233
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b234 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 454, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 133 88 272 40 480 416 416), lower := (rows 51 70 133 88 272 40 64 128 256), losses := [] }

theorem u234 : Upper (D 2) (R 2) [50,68,129,80,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b234
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b235 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 51 70 133 88 272 160 360 424 296), lower := (rows 51 70 133 88 272 160 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 47 309 32 97 0 289), good := (rows 379 94 351 88 272 376 64 0 272) }] }

theorem u235 : Upper (D 2) (R 2) [50,68,129,80,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b235
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b236 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 206, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 51 70 133 88 272 288 232 168 424), lower := (rows 51 70 133 88 272 288 64 128 256), losses := [] }

theorem u236 : Upper (D 2) (R 2) [50,68,129,80,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b236
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b237 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 454, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 133 152 272 40 352 480 352), lower := (rows 51 70 133 152 272 40 64 128 256), losses := [] }

theorem u237 : Upper (D 2) (R 2) [50,68,129,144,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b237
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b238 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 133 152 272 96 360 424 296), lower := (rows 51 70 133 152 272 96 64 128 256), losses := [] }

theorem u238 : Upper (D 2) (R 2) [50,68,129,144,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b238
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b239 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 206, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 51 70 133 152 272 288 104 232 360), lower := (rows 51 70 133 152 272 288 64 128 256), losses := [] }

theorem u239 : Upper (D 2) (R 2) [50,68,129,144,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b239
    (constants 2).1 (constants 2).2 (by decide +kernel)

#print axioms u239
end Delivery.IrregularNine14.P02
