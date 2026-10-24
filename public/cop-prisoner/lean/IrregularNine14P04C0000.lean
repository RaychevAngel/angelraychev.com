import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P04
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b0 : PairBound 9 := { available := 8, camps := [{ cop := 0, region := 280, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 196 26 276 40 65 144 264), lower := (rows 7 35 196 26 276 40 65 144 256), losses := [] }

theorem u0 : Upper (D 4) (R 4) [6,33,192,18,260,8,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b0
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b1 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 272, targets := 2 }], pairs := [(4,1)], upper := (rows 7 35 196 26 276 40 72 144 257), lower := (rows 7 35 196 26 276 40 72 144 256), losses := [] }

theorem u1 : Upper (D 4) (R 4) [6,33,192,18,260,8,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b1
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b2 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 101, targets := 8 }], pairs := [(0,3)], upper := (rows 7 26 100 138 276 33 65 152 280), lower := (rows 7 26 100 138 276 33 65 128 256), losses := [] }

theorem u2 : Upper (D 4) (R 4) [6,24,96,130,260,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b2
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b3 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 272, targets := 2 }], pairs := [(4,1)], upper := (rows 7 26 100 138 276 33 72 145 273), lower := (rows 7 26 100 138 276 33 72 128 256), losses := [] }

theorem u3 : Upper (D 4) (R 4) [6,24,96,130,260,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b3
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b4 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 4 }], pairs := [(3,2)], upper := (rows 7 26 100 138 276 33 80 137 265), lower := (rows 7 26 100 138 276 33 80 128 256), losses := [] }

theorem u4 : Upper (D 4) (R 4) [6,24,96,130,260,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b4
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b5 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2)], upper := (rows 7 35 76 137 274 48 68 152 280), lower := (rows 7 35 76 137 274 48 68 128 256), losses := [] }

theorem u5 : Upper (D 4) (R 4) [6,33,72,129,258,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b5
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b6 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 307, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 137 274 48 72 148 276), lower := (rows 7 35 76 137 274 48 72 128 256), losses := [] }

theorem u6 : Upper (D 4) (R 4) [6,33,72,129,258,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b6
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b7 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 136, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 76 137 274 48 80 140 268), lower := (rows 7 35 76 137 274 48 80 128 256), losses := [] }

theorem u7 : Upper (D 4) (R 4) [6,33,72,129,258,16,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b7
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b8 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 408, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 76 137 280 48 66 148 276), lower := (rows 7 35 76 137 280 48 66 128 256), losses := [] }

theorem u8 : Upper (D 4) (R 4) [6,33,72,129,264,16,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b8
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b9 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2)], upper := (rows 7 35 76 137 280 48 68 146 274), lower := (rows 7 35 76 137 280 48 68 128 256), losses := [] }

theorem u9 : Upper (D 4) (R 4) [6,33,72,129,264,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b9
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b10 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 68, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 137 280 48 80 134 262), lower := (rows 7 35 76 137 280 48 80 128 256), losses := [] }

theorem u10 : Upper (D 4) (R 4) [6,33,72,129,264,16,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b10
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b11 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 76 138 280 48 65 148 276), lower := (rows 7 35 76 138 280 48 65 128 256), losses := [] }

theorem u11 : Upper (D 4) (R 4) [6,33,72,130,264,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b11
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b12 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2)], upper := (rows 7 35 76 138 280 48 68 145 273), lower := (rows 7 35 76 138 280 48 68 128 256), losses := [] }

theorem u12 : Upper (D 4) (R 4) [6,33,72,130,264,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b12
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b13 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 68, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 138 280 48 80 133 261), lower := (rows 7 35 76 138 280 48 80 128 256), losses := [] }

theorem u13 : Upper (D 4) (R 4) [6,33,72,130,264,16,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b13
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b14 : PairBound 9 := { available := 272, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 76 140 26 48 65 400 272), lower := (rows 7 35 76 140 26 48 65 128 256), losses := [] }

theorem u14 : Upper (D 4) (R 4) [6,33,72,132,10,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b14
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b15 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 392, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 76 140 26 48 80 385 257), lower := (rows 7 35 76 140 26 48 80 128 256), losses := [] }

theorem u15 : Upper (D 4) (R 4) [6,33,72,132,10,16,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b15
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b16 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 7 35 76 140 26 48 320 145 273), lower := (rows 7 35 76 140 26 48 320 128 256), losses := [] }

theorem u16 : Upper (D 4) (R 4) [6,33,72,132,10,16,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b16
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b17 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 76 140 274 48 65 152 280), lower := (rows 7 35 76 140 274 48 65 128 256), losses := [] }

theorem u17 : Upper (D 4) (R 4) [6,33,72,132,258,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b17
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b18 : PairBound 9 := { available := 17, camps := [{ cop := 7, region := 76, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 140 274 48 72 145 273), lower := (rows 7 35 76 140 274 48 72 128 256), losses := [] }

theorem u18 : Upper (D 4) (R 4) [6,33,72,132,258,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b18
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b19 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 76 140 274 48 80 137 265), lower := (rows 7 35 76 140 274 48 80 128 256), losses := [] }

theorem u19 : Upper (D 4) (R 4) [6,33,72,132,258,16,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b19
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b20 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 76 140 280 48 65 146 274), lower := (rows 7 35 76 140 280 48 65 128 256), losses := [] }

theorem u20 : Upper (D 4) (R 4) [6,33,72,132,264,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b20
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b21 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 76 140 280 48 66 145 273), lower := (rows 7 35 76 140 280 48 66 128 256), losses := [] }

theorem u21 : Upper (D 4) (R 4) [6,33,72,132,264,16,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b21
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b22 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 68, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 140 280 48 80 131 259), lower := (rows 7 35 76 140 280 48 80 128 256), losses := [] }

theorem u22 : Upper (D 4) (R 4) [6,33,72,132,264,16,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b22
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b23 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 76 392 26 48 65 148 276), lower := (rows 7 35 76 392 26 48 65 128 256), losses := [] }

theorem u23 : Upper (D 4) (R 4) [6,33,72,384,10,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b23
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b24 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2)], upper := (rows 7 35 76 392 26 48 68 145 273), lower := (rows 7 35 76 392 26 48 68 128 256), losses := [] }

theorem u24 : Upper (D 4) (R 4) [6,33,72,384,10,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b24
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b25 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 392, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 76 392 26 48 80 133 261), lower := (rows 7 35 76 392 26 48 80 128 256), losses := [] }

theorem u25 : Upper (D 4) (R 4) [6,33,72,384,10,16,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b25
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b26 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 280, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 196 26 276 40 65 152 280), lower := (rows 7 35 196 26 276 40 65 128 256), losses := [] }

theorem u26 : Upper (D 4) (R 4) [6,33,192,18,260,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b26
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b27 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 272, targets := 2 }], pairs := [(4,1)], upper := (rows 7 35 196 26 276 40 72 145 273), lower := (rows 7 35 196 26 276 40 72 128 256), losses := [] }

theorem u27 : Upper (D 4) (R 4) [6,33,192,18,260,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b27
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m28_1 : Upper (D 4) (R 4) [6,33,192,18,260,8,16,1] 13 :=
  permutation_upper _ _ _ [6,33,192,18,260,8,1,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u0

theorem m28_8 : Upper (D 4) (R 4) [6,33,192,18,260,8,16,8] 13 :=
  permutation_upper _ _ _ [6,33,192,18,260,8,8,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1

def r28 : Route 9 := (fun mask => (mask,id))

def c28 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u28 : Upper (D 4) (R 4) [6,33,192,18,260,8,16] 13 := by
  apply FastRouting.sound _ _ [6,33,192,18,260,8,16] 13 (by decide) (choices 1) [1,8] r28 c28
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m28_1
  · exact m28_8

def b29 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 7 42 84 138 276 33 65 152 280), lower := (rows 7 42 84 138 276 33 65 128 256), losses := [] }

theorem u29 : Upper (D 4) (R 4) [6,40,80,130,260,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b29
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b30 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 272, targets := 2 }], pairs := [(4,1)], upper := (rows 7 42 84 138 276 33 72 145 273), lower := (rows 7 42 84 138 276 33 72 128 256), losses := [] }

theorem u30 : Upper (D 4) (R 4) [6,40,80,130,260,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b30
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b31 : PairBound 9 := { available := 9, camps := [{ cop := 8, region := 84, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 84 138 276 33 80 137 265), lower := (rows 7 42 84 138 276 33 80 128 256), losses := [] }

theorem u31 : Upper (D 4) (R 4) [6,40,80,130,260,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b31
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b32 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 7 42 84 138 280 33 65 148 276), lower := (rows 7 42 84 138 280 33 65 128 256), losses := [] }

theorem u32 : Upper (D 4) (R 4) [6,40,80,130,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b32
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b33 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2)], upper := (rows 7 42 84 138 280 33 68 145 273), lower := (rows 7 42 84 138 280 33 68 128 256), losses := [] }

theorem u33 : Upper (D 4) (R 4) [6,40,80,130,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b33
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b34 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 171, targets := 16 }], pairs := [(0,4)], upper := (rows 7 42 84 138 280 33 80 133 261), lower := (rows 7 42 84 138 280 33 80 128 256), losses := [] }

theorem u34 : Upper (D 4) (R 4) [6,40,80,130,264,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b34
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b35 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 7 42 84 152 280 33 65 134 262), lower := (rows 7 42 84 152 280 33 65 128 256), losses := [] }

theorem u35 : Upper (D 4) (R 4) [6,40,80,144,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b35
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b36 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 408, targets := 2 }], pairs := [(3,1)], upper := (rows 7 42 84 152 280 33 66 133 261), lower := (rows 7 42 84 152 280 33 66 128 256), losses := [] }

theorem u36 : Upper (D 4) (R 4) [6,40,80,144,264,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b36
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b37 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2)], upper := (rows 7 42 84 152 280 33 68 131 259), lower := (rows 7 42 84 152 280 33 68 128 256), losses := [] }

theorem u37 : Upper (D 4) (R 4) [6,40,80,144,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b37
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b38 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 52 88 145 34 332 396 268), lower := (rows 7 11 52 88 145 34 64 128 256), losses := [] }

theorem u38 : Upper (D 4) (R 4) [6,9,48,80,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b38
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b39 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 474, targets := 4 }], pairs := [(1,2)], upper := (rows 7 11 52 88 145 36 330 394 266), lower := (rows 7 11 52 88 145 36 64 128 256), losses := [] }

theorem u39 : Upper (D 4) (R 4) [6,9,48,80,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b39
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b40 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 88 145 40 326 390 262), lower := (rows 7 11 52 88 145 40 64 128 256), losses := [] }

theorem u40 : Upper (D 4) (R 4) [6,9,48,80,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b40
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b41 : PairBound 9 := { available := 14, camps := [], pairs := [], upper := (rows 7 11 52 88 145 288 78 142 270), lower := (rows 7 11 52 88 145 288 64 128 256), losses := [] }

theorem u41 : Upper (D 4) (R 4) [6,9,48,80,129,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b41
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b42 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 52 88 148 33 330 394 266), lower := (rows 7 11 52 88 148 33 64 128 256), losses := [] }

theorem u42 : Upper (D 4) (R 4) [6,9,48,80,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b42
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b43 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 52 88 148 34 329 393 265), lower := (rows 7 11 52 88 148 34 64 128 256), losses := [] }

theorem u43 : Upper (D 4) (R 4) [6,9,48,80,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b43
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b44 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 88 148 40 323 387 259), lower := (rows 7 11 52 88 148 40 64 128 256), losses := [] }

theorem u44 : Upper (D 4) (R 4) [6,9,48,80,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b44
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b45 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 7 11 52 88 148 288 75 139 267), lower := (rows 7 11 52 88 148 288 64 128 256), losses := [] }

theorem u45 : Upper (D 4) (R 4) [6,9,48,80,132,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b45
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b46 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 52 88 400 33 78 142 270), lower := (rows 7 11 52 88 400 33 64 128 256), losses := [] }

theorem u46 : Upper (D 4) (R 4) [6,9,48,80,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b46
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b47 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 52 88 400 34 77 141 269), lower := (rows 7 11 52 88 400 34 64 128 256), losses := [] }

theorem u47 : Upper (D 4) (R 4) [6,9,48,80,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b47
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b48 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 474, targets := 4 }], pairs := [(1,2)], upper := (rows 7 11 52 88 400 36 75 139 267), lower := (rows 7 11 52 88 400 36 64 128 256), losses := [] }

theorem u48 : Upper (D 4) (R 4) [6,9,48,80,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b48
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b49 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 88 400 40 71 135 263), lower := (rows 7 11 52 88 400 40 64 128 256), losses := [] }

theorem u49 : Upper (D 4) (R 4) [6,9,48,80,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b49
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b50 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 52 200 273 34 92 156 284), lower := (rows 7 11 52 200 273 34 64 128 256), losses := [] }

theorem u50 : Upper (D 4) (R 4) [6,9,48,192,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b50
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b51 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 474, targets := 4 }], pairs := [(1,2)], upper := (rows 7 11 52 200 273 36 90 154 282), lower := (rows 7 11 52 200 273 36 64 128 256), losses := [] }

theorem u51 : Upper (D 4) (R 4) [6,9,48,192,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b51
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b52 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 272, targets := 8 }], pairs := [(4,3)], upper := (rows 7 11 52 200 273 40 86 150 278), lower := (rows 7 11 52 200 273 40 64 128 256), losses := [] }

theorem u52 : Upper (D 4) (R 4) [6,9,48,192,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b52
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b53 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 203, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 52 200 273 48 78 142 270), lower := (rows 7 11 52 200 273 48 64 128 256), losses := [] }

theorem u53 : Upper (D 4) (R 4) [6,9,48,192,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b53
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b54 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 52 200 274 33 92 156 284), lower := (rows 7 11 52 200 274 33 64 128 256), losses := [] }

theorem u54 : Upper (D 4) (R 4) [6,9,48,192,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b54
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b55 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 474, targets := 4 }], pairs := [(1,2)], upper := (rows 7 11 52 200 274 36 89 153 281), lower := (rows 7 11 52 200 274 36 64 128 256), losses := [] }

theorem u55 : Upper (D 4) (R 4) [6,9,48,192,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b55
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b56 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 272, targets := 8 }], pairs := [(4,3)], upper := (rows 7 11 52 200 274 40 85 149 277), lower := (rows 7 11 52 200 274 40 64 128 256), losses := [] }

theorem u56 : Upper (D 4) (R 4) [6,9,48,192,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b56
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b57 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 203, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 52 200 274 48 77 141 269), lower := (rows 7 11 52 200 274 48 64 128 256), losses := [] }

theorem u57 : Upper (D 4) (R 4) [6,9,48,192,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b57
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b58 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 52 200 276 33 90 154 282), lower := (rows 7 11 52 200 276 33 64 128 256), losses := [] }

theorem u58 : Upper (D 4) (R 4) [6,9,48,192,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b58
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b59 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 52 200 276 34 89 153 281), lower := (rows 7 11 52 200 276 34 64 128 256), losses := [] }

theorem u59 : Upper (D 4) (R 4) [6,9,48,192,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b59
    (constants 4).1 (constants 4).2 (by decide +kernel)

#print axioms u59
end Delivery.IrregularNine14.P04
