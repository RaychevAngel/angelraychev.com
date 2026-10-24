import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0061
import IrregularNine14P01C0062

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7200 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 274 76 41 210 226 194 194 450), lower := (rows 53 274 76 41 16 32 64 128 256), losses := [] }

theorem u7200 : Upper (D 1) (R 1) [52,272,72,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7200
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7201 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 274 76 42 211 227 195 195 451), lower := (rows 53 274 76 42 16 32 64 128 256), losses := [] }

theorem u7201 : Upper (D 1) (R 1) [52,272,72,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7201
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7202 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 274 76 73 178 162 226 162 418), lower := (rows 53 274 76 73 16 32 64 128 256), losses := [] }

theorem u7202 : Upper (D 1) (R 1) [52,272,72,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7202
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7203 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 274 76 74 179 163 227 163 419), lower := (rows 53 274 76 74 16 32 64 128 256), losses := [] }

theorem u7203 : Upper (D 1) (R 1) [52,272,72,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7203
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7204 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 274 76 104 147 163 195 131 387), lower := (rows 53 274 76 104 16 32 64 128 256), losses := [] }

theorem u7204 : Upper (D 1) (R 1) [52,272,72,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7204
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7205 : Route 9 := (fun mask => (mask,id))

def c7205 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7205 : Upper (D 1) (R 1) [52,272,72,129] 13 := by
  apply FastRouting.sound _ _ [52,272,72,129] 13 (by decide) (choices 1) [2,32,64,128] r7205 c7205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3689
  · exact u3690
  · exact u3691
  · exact u3692

def r7206 : Route 9 := (fun mask => (mask,id))

def c7206 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7206 : Upper (D 1) (R 1) [52,272,72,130] 13 := by
  apply FastRouting.sound _ _ [52,272,72,130] 13 (by decide) (choices 1) [1,2,32,64,128] r7206 c7206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3693
  · exact u3694
  · exact u3695
  · exact u3696
  · exact u3697

def b7207 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 274 76 168 211 227 195 195 451), lower := (rows 53 274 76 168 16 32 64 128 256), losses := [] }

theorem u7207 : Upper (D 1) (R 1) [52,272,72,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7207
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7208 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 274 76 200 179 163 227 163 419), lower := (rows 53 274 76 200 16 32 64 128 256), losses := [] }

theorem u7208 : Upper (D 1) (R 1) [52,272,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7208
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7209 : PairBound 9 := { available := 234, camps := [{ cop := 3, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 53 274 196 11 250 234 234 234 490), lower := (rows 53 274 196 11 16 32 64 128 256), losses := [] }

theorem u7209 : Upper (D 1) (R 1) [52,272,192,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7209
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7210 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 274 196 41 218 234 202 202 458), lower := (rows 53 274 196 41 16 32 64 128 256), losses := [] }

theorem u7210 : Upper (D 1) (R 1) [52,272,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7210
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7211 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7211 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7211 : Upper (D 1) (R 1) [52,272,192,34] 13 := by
  apply FastRouting.sound _ _ [52,272,192,34] 13 (by decide) (choices 1) [1,2,8,64] r7211 c7211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3698
  · exact u3699
  · exact u3700
  · exact u3701

def b7212 : PairBound 9 := { available := 170, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 53 274 196 73 186 170 234 170 426), lower := (rows 53 274 196 73 16 32 64 128 256), losses := [] }

theorem u7212 : Upper (D 1) (R 1) [52,272,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7212
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7213 : Route 9 := (fun mask => (mask,id))

def c7213 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7213 : Upper (D 1) (R 1) [52,272,192,66] 13 := by
  apply FastRouting.sound _ _ [52,272,192,66] 13 (by decide) (choices 1) [1,2,8,32,128] r7213 c7213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3702
  · exact u3703
  · exact u3704
  · exact u3705
  · exact u3706

def r7214 : Route 9 := (fun mask => (mask,id))

def c7214 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7214 : Upper (D 1) (R 1) [52,272,192,96] 13 := by
  apply FastRouting.sound _ _ [52,272,192,96] 13 (by decide) (choices 1) [1,2,8,128] r7214 c7214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3707
  · exact u3708
  · exact u3709
  · exact u3710

def b7215 : PairBound 9 := { available := 43, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 274 196 200 59 43 107 171 299), lower := (rows 53 274 196 200 16 32 64 128 256), losses := [] }

theorem u7215 : Upper (D 1) (R 1) [52,272,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7215
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7216 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 53 322 7 26 248 232 232 232 488), lower := (rows 53 322 7 26 16 32 64 128 256), losses := [] }

theorem u7216 : Upper (D 1) (R 1) [52,320,3,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7216
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7217 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 322 7 56 218 234 202 202 458), lower := (rows 53 322 7 56 16 32 64 128 256), losses := [] }

theorem u7217 : Upper (D 1) (R 1) [52,320,3,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7217
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7218 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 322 7 74 184 184 248 184 440), lower := (rows 53 322 7 74 16 32 64 128 256), losses := [] }

theorem u7218 : Upper (D 1) (R 1) [52,320,3,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7218
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7219 : PairBound 9 := { available := 170, camps := [{ cop := 3, region := 418, targets := 16 }], pairs := [(1,4)], upper := (rows 53 322 7 88 186 170 234 170 426), lower := (rows 53 322 7 88 16 32 64 128 256), losses := [] }

theorem u7219 : Upper (D 1) (R 1) [52,320,3,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7219
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7220 : Route 9 := (fun mask => (mask,id))

def c7220 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u7220 : Upper (D 1) (R 1) [52,320,3,130] 13 := by
  apply FastRouting.sound _ _ [52,320,3,130] 13 (by decide) (choices 1) [8,32,64,128] r7220 c7220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3711
  · exact u3712
  · exact u3713
  · exact u3714

def b7221 : PairBound 9 := { available := 234, camps := [{ cop := 3, region := 354, targets := 16 }], pairs := [(1,4)], upper := (rows 53 322 7 152 250 234 234 234 490), lower := (rows 53 322 7 152 16 32 64 128 256), losses := [] }

theorem u7221 : Upper (D 1) (R 1) [52,320,3,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7221
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7222 : Route 9 := (fun mask => (mask,id))

def c7222 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7222 : Upper (D 1) (R 1) [52,320,3,192] 13 := by
  apply FastRouting.sound _ _ [52,320,3,192] 13 (by decide) (choices 1) [2,8,32,128] r7222 c7222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3715
  · exact u3716
  · exact u3717
  · exact u3718

def b7223 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 322 13 26 242 226 226 226 482), lower := (rows 53 322 13 26 16 32 64 128 256), losses := [] }

theorem u7223 : Upper (D 1) (R 1) [52,320,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7223
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7224 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 53 322 13 56 210 226 194 194 450), lower := (rows 53 322 13 56 16 32 64 128 256), losses := [] }

theorem u7224 : Upper (D 1) (R 1) [52,320,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7224
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7225 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 322 13 74 178 178 242 178 434), lower := (rows 53 322 13 74 16 32 64 128 256), losses := [] }

theorem u7225 : Upper (D 1) (R 1) [52,320,9,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7225
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7226 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 322 13 88 178 162 226 162 418), lower := (rows 53 322 13 88 16 32 64 128 256), losses := [] }

theorem u7226 : Upper (D 1) (R 1) [52,320,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7226
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7227 : Route 9 := (fun mask => (mask,id))

def c7227 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7227 : Upper (D 1) (R 1) [52,320,9,130] 13 := by
  apply FastRouting.sound _ _ [52,320,9,130] 13 (by decide) (choices 1) [2,32,64,128] r7227 c7227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3719
  · exact u3720
  · exact u3721
  · exact u3722

def b7228 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 322 13 152 242 226 226 226 482), lower := (rows 53 322 13 152 16 32 64 128 256), losses := [] }

theorem u7228 : Upper (D 1) (R 1) [52,320,9,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7228
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7229 : Route 9 := (fun mask => (mask,id))

def c7229 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7229 : Upper (D 1) (R 1) [52,320,9,192] 13 := by
  apply FastRouting.sound _ _ [52,320,9,192] 13 (by decide) (choices 1) [2,32,128] r7229 c7229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3723
  · exact u3724
  · exact u3725

def b7230 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 53 322 14 11 240 240 240 240 496), lower := (rows 53 322 14 11 16 32 64 128 256), losses := [] }

theorem u7230 : Upper (D 1) (R 1) [52,320,10,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7230
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7231 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 322 14 25 242 226 226 226 482), lower := (rows 53 322 14 25 16 32 64 128 256), losses := [] }

theorem u7231 : Upper (D 1) (R 1) [52,320,10,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7231
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7232 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 53 322 14 26 241 225 225 225 481), lower := (rows 53 322 14 26 16 32 64 128 256), losses := [] }

theorem u7232 : Upper (D 1) (R 1) [52,320,10,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7232
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7233 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 322 14 56 211 227 195 195 451), lower := (rows 53 322 14 56 16 32 64 128 256), losses := [] }

theorem u7233 : Upper (D 1) (R 1) [52,320,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7233
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7234 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 53 322 14 73 178 178 242 178 434), lower := (rows 53 322 14 73 16 32 64 128 256), losses := [] }

theorem u7234 : Upper (D 1) (R 1) [52,320,10,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7234
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7235 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 53 322 14 74 177 177 241 177 433), lower := (rows 53 322 14 74 16 32 64 128 256), losses := [] }

theorem u7235 : Upper (D 1) (R 1) [52,320,10,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7235
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7236 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 322 14 88 179 163 227 163 419), lower := (rows 53 322 14 88 16 32 64 128 256), losses := [] }

theorem u7236 : Upper (D 1) (R 1) [52,320,10,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7236
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7237 : Route 9 := (fun mask => (mask,id))

def c7237 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7237 : Upper (D 1) (R 1) [52,320,10,129] 13 := by
  apply FastRouting.sound _ _ [52,320,10,129] 13 (by decide) (choices 1) [2,32,64,128] r7237 c7237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3726
  · exact u3727
  · exact u3728
  · exact u3729

def b7238 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 53 322 14 138 241 241 241 241 497), lower := (rows 53 322 14 138 16 32 64 128 256), losses := [] }

theorem u7238 : Upper (D 1) (R 1) [52,320,10,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7238
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7239 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 322 14 152 243 227 227 227 483), lower := (rows 53 322 14 152 16 32 64 128 256), losses := [] }

theorem u7239 : Upper (D 1) (R 1) [52,320,10,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7239
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7240 : PairBound 9 := { available := 179, camps := [{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 53 322 14 200 179 179 243 179 435), lower := (rows 53 322 14 200 16 32 64 128 256), losses := [] }

theorem u7240 : Upper (D 1) (R 1) [52,320,10,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7240
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7241 : PairBound 9 := { available := 178, camps := [], pairs := [(0,6)], upper := (rows 53 322 76 11 178 178 242 178 434), lower := (rows 53 322 76 11 16 32 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 26 42 0 138 266), good := (rows 53 434 445 443 16 32 0 128 256) }] }

theorem u7241 : Upper (D 1) (R 1) [52,320,72,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7241
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7242 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 322 76 25 178 162 226 162 418), lower := (rows 53 322 76 25 16 32 64 128 256), losses := [] }

theorem u7242 : Upper (D 1) (R 1) [52,320,72,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7242
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7243 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 322 76 26 179 163 227 163 419), lower := (rows 53 322 76 26 16 32 64 128 256), losses := [] }

theorem u7243 : Upper (D 1) (R 1) [52,320,72,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7243
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7244 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 322 76 56 147 163 195 131 387), lower := (rows 53 322 76 56 16 32 64 128 256), losses := [] }

theorem u7244 : Upper (D 1) (R 1) [52,320,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7244
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7245 : Route 9 := (fun mask => (mask,id))

def c7245 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7245 : Upper (D 1) (R 1) [52,320,72,129] 13 := by
  apply FastRouting.sound _ _ [52,320,72,129] 13 (by decide) (choices 1) [2,32,128] r7245 c7245
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3730
  · exact u3731
  · exact u3732

def r7246 : Route 9 := (fun mask => (mask,id))

def c7246 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7246 : Upper (D 1) (R 1) [52,320,72,130] 13 := by
  apply FastRouting.sound _ _ [52,320,72,130] 13 (by decide) (choices 1) [1,2,32,128] r7246 c7246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3733
  · exact u3734
  · exact u3735
  · exact u3736

def b7247 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 322 76 152 179 163 227 163 419), lower := (rows 53 322 76 152 16 32 64 128 256), losses := [] }

theorem u7247 : Upper (D 1) (R 1) [52,320,72,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7247
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7248 : PairBound 9 := { available := 234, camps := [{ cop := 3, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 53 322 133 26 250 234 234 234 490), lower := (rows 53 322 133 26 16 32 64 128 256), losses := [] }

theorem u7248 : Upper (D 1) (R 1) [52,320,129,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7248
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7249 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 322 133 56 218 234 202 202 458), lower := (rows 53 322 133 56 16 32 64 128 256), losses := [] }

theorem u7249 : Upper (D 1) (R 1) [52,320,129,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7249
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7250 : PairBound 9 := { available := 186, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 322 133 74 186 186 250 186 442), lower := (rows 53 322 133 74 16 32 64 128 256), losses := [] }

theorem u7250 : Upper (D 1) (R 1) [52,320,129,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7250
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7251 : PairBound 9 := { available := 170, camps := [{ cop := 3, region := 418, targets := 16 }], pairs := [(1,4)], upper := (rows 53 322 133 88 186 170 234 170 426), lower := (rows 53 322 133 88 16 32 64 128 256), losses := [] }

theorem u7251 : Upper (D 1) (R 1) [52,320,129,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7251
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7252 : PairBound 9 := { available := 122, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7)], upper := (rows 53 322 133 138 122 122 122 250 378), lower := (rows 53 322 133 138 16 32 64 128 256), losses := [] }

theorem u7252 : Upper (D 1) (R 1) [52,320,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7252
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7253 : PairBound 9 := { available := 106, camps := [{ cop := 3, region := 354, targets := 16 }], pairs := [(1,4)], upper := (rows 53 322 133 152 122 106 106 234 362), lower := (rows 53 322 133 152 16 32 64 128 256), losses := [] }

theorem u7253 : Upper (D 1) (R 1) [52,320,129,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7253
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7254 : PairBound 9 := { available := 58, camps := [{ cop := 3, region := 306, targets := 128 }], pairs := [(1,7)], upper := (rows 53 322 133 200 58 58 122 186 314), lower := (rows 53 322 133 200 16 32 64 128 256), losses := [] }

theorem u7254 : Upper (D 1) (R 1) [52,320,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7254
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7255 : Route 9 := (fun mask => (mask,id))

def c7255 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u7255 : Upper (D 1) (R 1) [52,320,130,3] 13 := by
  apply FastRouting.sound _ _ [52,320,130,3] 13 (by decide) (choices 1) [8,32,64,128] r7255 c7255
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3737
  · exact u3738
  · exact u3739
  · exact u3740

def b7256 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 322 134 25 250 234 234 234 490), lower := (rows 53 322 134 25 16 32 64 128 256), losses := [] }

theorem u7256 : Upper (D 1) (R 1) [52,320,130,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7256
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7257 : Route 9 := (fun mask => (mask,id))

def c7257 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u7257 : Upper (D 1) (R 1) [52,320,130,18] 13 := by
  apply FastRouting.sound _ _ [52,320,130,18] 13 (by decide) (choices 1) [1,8,32,64,128] r7257 c7257
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3741
  · exact u3742
  · exact u3743
  · exact u3744
  · exact u3745

def b7258 : PairBound 9 := { available := 203, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 322 134 56 219 235 203 203 459), lower := (rows 53 322 134 56 16 32 64 128 256), losses := [] }

theorem u7258 : Upper (D 1) (R 1) [52,320,130,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7258
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7259 : Route 9 := (fun mask => (mask,id))

def c7259 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7259 : Upper (D 1) (R 1) [52,320,130,65] 13 := by
  apply FastRouting.sound _ _ [52,320,130,65] 13 (by decide) (choices 1) [2,8,32,128] r7259 c7259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3746
  · exact u3747
  · exact u3748
  · exact u3749

#print axioms u7259
end Delivery.IrregularNine14.P01
