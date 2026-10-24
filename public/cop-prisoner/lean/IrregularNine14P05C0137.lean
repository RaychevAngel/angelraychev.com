import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0078
import IrregularNine14P05C0079

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r8220 : Route 9 := (fun mask => (mask,id))

def c8220 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8220 : Upper (D 5) (R 5) [34,68,130,257,40] 13 := by
  apply FastRouting.sound _ _ [34,68,130,257,40] 13 (by decide) (choices 1) [1,4,8,16] r8220 c8220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4716
  · exact u4717
  · exact u4718
  · exact u4719

def r8221 : Route 9 := (fun mask => (mask,id))

def c8221 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8221 : Upper (D 5) (R 5) [34,68,130,260,9] 13 := by
  apply FastRouting.sound _ _ [34,68,130,260,9] 13 (by decide) (choices 1) [1,8,16] r8221 c8221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4720
  · exact u4721
  · exact u4722

def b8222 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 134 268 49 57 89 153 281), lower := (rows 35 70 134 268 49 32 64 128 256), losses := [] }

theorem u8222 : Upper (D 5) (R 5) [34,68,130,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8222
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8223 : Route 9 := (fun mask => (mask,id))

def c8223 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8223 : Upper (D 5) (R 5) [34,68,130,260,40] 13 := by
  apply FastRouting.sound _ _ [34,68,130,260,40] 13 (by decide) (choices 1) [1,8,16] r8223 c8223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4723
  · exact u4724
  · exact u4725

def b8224 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 296, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 70 134 280 21 41 105 169 297), lower := (rows 35 70 134 280 21 32 64 128 256), losses := [] }

theorem u8224 : Upper (D 5) (R 5) [34,68,130,272,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8224
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8225 : Route 9 := (fun mask => (mask,id))

def c8225 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8225 : Upper (D 5) (R 5) [34,68,130,272,9] 13 := by
  apply FastRouting.sound _ _ [34,68,130,272,9] 13 (by decide) (choices 1) [1,4,8] r8225 c8225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4726
  · exact u4727
  · exact u4728

def r8226 : Route 9 := (fun mask => (mask,id))

def c8226 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8226 : Upper (D 5) (R 5) [34,68,130,272,12] 13 := by
  apply FastRouting.sound _ _ [34,68,130,272,12] 13 (by decide) (choices 1) [1,8] r8226 c8226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4729
  · exact u4730

def b8227 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 134 280 49 45 77 141 269), lower := (rows 35 70 134 280 49 32 64 128 256), losses := [] }

theorem u8227 : Upper (D 5) (R 5) [34,68,130,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8227
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8228 : Route 9 := (fun mask => (mask,id))

def c8228 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8228 : Upper (D 5) (R 5) [34,68,130,272,36] 13 := by
  apply FastRouting.sound _ _ [34,68,130,272,36] 13 (by decide) (choices 1) [1,8] r8228 c8228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4731
  · exact u4732

def r8229 : Route 9 := (fun mask => (mask,id))

def c8229 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8229 : Upper (D 5) (R 5) [34,68,130,272,40] 13 := by
  apply FastRouting.sound _ _ [34,68,130,272,40] 13 (by decide) (choices 1) [1,4,8] r8229 c8229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4733
  · exact u4734
  · exact u4735

def b8230 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 296, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 70 134 296 21 57 89 153 281), lower := (rows 35 70 134 296 21 32 64 128 256), losses := [] }

theorem u8230 : Upper (D 5) (R 5) [34,68,130,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8230
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8231 : PairBound 9 := { available := 29, camps := [{ cop := 4, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 134 296 25 61 93 157 285), lower := (rows 35 70 134 296 25 32 64 128 256), losses := [] }

theorem u8231 : Upper (D 5) (R 5) [34,68,130,288,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8231
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8232 : Route 9 := (fun mask => (mask,id))

def c8232 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8232 : Upper (D 5) (R 5) [34,68,130,288,12] 13 := by
  apply FastRouting.sound _ _ [34,68,130,288,12] 13 (by decide) (choices 1) [1,8,16] r8232 c8232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4736
  · exact u4737
  · exact u4738

def b8233 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 24, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 70 140 56 19 301 333 397 269), lower := (rows 35 70 140 56 19 32 64 128 256), losses := [] }

theorem u8233 : Upper (D 5) (R 5) [34,68,136,48,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8233
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8234 : Route 9 := (fun mask => (mask,id))

def c8234 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8234 : Upper (D 5) (R 5) [34,68,136,48,5] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48,5] 13 (by decide) (choices 1) [1,2,8,256] r8234 c8234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4739
  · exact u4740
  · exact u4741
  · exact u4742

def b8235 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 16, targets := 9 }], pairs := [(4,0),(4,3)], upper := (rows 35 70 140 56 22 297 329 393 265), lower := (rows 35 70 140 56 22 32 64 128 256), losses := [] }

theorem u8235 : Upper (D 5) (R 5) [34,68,136,48,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8235
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8236 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 24, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 70 140 56 25 295 327 391 263), lower := (rows 35 70 140 56 25 32 64 128 256), losses := [] }

theorem u8236 : Upper (D 5) (R 5) [34,68,136,48,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8236
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8237 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 70 140 56 26 293 325 389 261), lower := (rows 35 70 140 56 26 32 64 128 256), losses := [] }

theorem u8237 : Upper (D 5) (R 5) [34,68,136,48,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8237
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8238 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 70 140 56 28 291 323 387 259), lower := (rows 35 70 140 56 28 32 64 128 256), losses := [] }

theorem u8238 : Upper (D 5) (R 5) [34,68,136,48,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8238
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8239 : Route 9 := (fun mask => (mask,id))

def c8239 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8239 : Upper (D 5) (R 5) [34,68,136,48,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48,257] 13 (by decide) (choices 1) [1,2,4,8] r8239 c8239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4743
  · exact u4744
  · exact u4745
  · exact u4746

def r8240 : Route 9 := (fun mask => (mask,id))

def c8240 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8240 : Upper (D 5) (R 5) [34,68,136,48,258] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48,258] 13 (by decide) (choices 1) [1,4,8] r8240 c8240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4747
  · exact u4748
  · exact u4749

def r8241 : Route 9 := (fun mask => (mask,id))

def c8241 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8241 : Upper (D 5) (R 5) [34,68,136,48,260] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48,260] 13 (by decide) (choices 1) [1,2,8] r8241 c8241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4750
  · exact u4751
  · exact u4752

def b8242 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 99, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 140 56 280 39 71 135 263), lower := (rows 35 70 140 56 280 32 64 128 256), losses := [] }

theorem u8242 : Upper (D 5) (R 5) [34,68,136,48,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8242
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8243 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 70 140 265 19 60 124 188 316), lower := (rows 35 70 140 265 19 32 64 128 256), losses := [] }

theorem u8243 : Upper (D 5) (R 5) [34,68,136,257,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8243
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8244 : Route 9 := (fun mask => (mask,id))

def c8244 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8244 : Upper (D 5) (R 5) [34,68,136,257,5] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,5] 13 (by decide) (choices 1) [2,8,16] r8244 c8244
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4753
  · exact u4754
  · exact u4755

def b8245 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 16, targets := 9 }], pairs := [(4,0),(4,3)], upper := (rows 35 70 140 265 22 57 121 185 313), lower := (rows 35 70 140 265 22 32 64 128 256), losses := [] }

theorem u8245 : Upper (D 5) (R 5) [34,68,136,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8245
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8246 : PairBound 9 := { available := 54, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 140 265 25 54 118 182 310), lower := (rows 35 70 140 265 25 32 64 128 256), losses := [] }

theorem u8246 : Upper (D 5) (R 5) [34,68,136,257,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8246
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8247 : Route 9 := (fun mask => (mask,id))

def c8247 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8247 : Upper (D 5) (R 5) [34,68,136,257,10] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,10] 13 (by decide) (choices 1) [1,4,16] r8247 c8247
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4756
  · exact u4757
  · exact u4758

def b8248 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 70 140 265 28 51 115 179 307), lower := (rows 35 70 140 265 28 32 64 128 256), losses := [] }

theorem u8248 : Upper (D 5) (R 5) [34,68,136,257,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8248
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8249 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 140 265 49 62 94 158 286), lower := (rows 35 70 140 265 49 32 64 128 256), losses := [] }

theorem u8249 : Upper (D 5) (R 5) [34,68,136,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8249
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8250 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 70 140 265 50 61 93 157 285), lower := (rows 35 70 140 265 50 32 64 128 256), losses := [] }

theorem u8250 : Upper (D 5) (R 5) [34,68,136,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8250
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8251 : Route 9 := (fun mask => (mask,id))

def c8251 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8251 : Upper (D 5) (R 5) [34,68,136,257,36] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,36] 13 (by decide) (choices 1) [1,2,8,16] r8251 c8251
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4759
  · exact u4760
  · exact u4761
  · exact u4762

def r8252 : Route 9 := (fun mask => (mask,id))

def c8252 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8252 : Upper (D 5) (R 5) [34,68,136,257,40] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,40] 13 (by decide) (choices 1) [1,2,4,16] r8252 c8252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4763
  · exact u4764
  · exact u4765
  · exact u4766

def r8253 : Route 9 := (fun mask => (mask,id))

def c8253 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8253 : Upper (D 5) (R 5) [34,68,136,258,5] 13 := by
  apply FastRouting.sound _ _ [34,68,136,258,5] 13 (by decide) (choices 1) [1,8,16] r8253 c8253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4767
  · exact u4768
  · exact u4769

def r8254 : Route 9 := (fun mask => (mask,id))

def c8254 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8254 : Upper (D 5) (R 5) [34,68,136,258,9] 13 := by
  apply FastRouting.sound _ _ [34,68,136,258,9] 13 (by decide) (choices 1) [1,4,16] r8254 c8254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4770
  · exact u4771
  · exact u4772

def b8255 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 70 140 266 28 49 113 177 305), lower := (rows 35 70 140 266 28 32 64 128 256), losses := [] }

theorem u8255 : Upper (D 5) (R 5) [34,68,136,258,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8255
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8256 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 140 266 49 61 93 157 285), lower := (rows 35 70 140 266 49 32 64 128 256), losses := [] }

theorem u8256 : Upper (D 5) (R 5) [34,68,136,258,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8256
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8257 : Route 9 := (fun mask => (mask,id))

def c8257 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8257 : Upper (D 5) (R 5) [34,68,136,258,36] 13 := by
  apply FastRouting.sound _ _ [34,68,136,258,36] 13 (by decide) (choices 1) [1,8,16] r8257 c8257
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4773
  · exact u4774
  · exact u4775

def r8258 : Route 9 := (fun mask => (mask,id))

def c8258 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8258 : Upper (D 5) (R 5) [34,68,136,258,40] 13 := by
  apply FastRouting.sound _ _ [34,68,136,258,40] 13 (by decide) (choices 1) [1,4,16] r8258 c8258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4776
  · exact u4777
  · exact u4778

def b8259 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 70 140 268 19 57 121 185 313), lower := (rows 35 70 140 268 19 32 64 128 256), losses := [] }

theorem u8259 : Upper (D 5) (R 5) [34,68,136,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8259
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8260 : Route 9 := (fun mask => (mask,id))

def c8260 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8260 : Upper (D 5) (R 5) [34,68,136,260,9] 13 := by
  apply FastRouting.sound _ _ [34,68,136,260,9] 13 (by decide) (choices 1) [1,2,16] r8260 c8260
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4779
  · exact u4780
  · exact u4781

def b8261 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 140 268 26 49 113 177 305), lower := (rows 35 70 140 268 26 32 64 128 256), losses := [] }

theorem u8261 : Upper (D 5) (R 5) [34,68,136,260,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8261
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8262 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 140 268 49 59 91 155 283), lower := (rows 35 70 140 268 49 32 64 128 256), losses := [] }

theorem u8262 : Upper (D 5) (R 5) [34,68,136,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8262
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8263 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 70 140 268 50 57 89 153 281), lower := (rows 35 70 140 268 50 32 64 128 256), losses := [] }

theorem u8263 : Upper (D 5) (R 5) [34,68,136,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8263
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8264 : Route 9 := (fun mask => (mask,id))

def c8264 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8264 : Upper (D 5) (R 5) [34,68,136,260,40] 13 := by
  apply FastRouting.sound _ _ [34,68,136,260,40] 13 (by decide) (choices 1) [1,2,16] r8264 c8264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4782
  · exact u4783
  · exact u4784

def b8265 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 70 140 280 19 45 109 173 301), lower := (rows 35 70 140 280 19 32 64 128 256), losses := [] }

theorem u8265 : Upper (D 5) (R 5) [34,68,136,272,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8265
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8266 : Route 9 := (fun mask => (mask,id))

def c8266 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8266 : Upper (D 5) (R 5) [34,68,136,272,5] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,5] 13 (by decide) (choices 1) [1,2,8] r8266 c8266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4785
  · exact u4786
  · exact u4787

def b8267 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 16, targets := 9 }], pairs := [(4,0),(4,3)], upper := (rows 35 70 140 280 22 41 105 169 297), lower := (rows 35 70 140 280 22 32 64 128 256), losses := [] }

theorem u8267 : Upper (D 5) (R 5) [34,68,136,272,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8267
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8268 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 99, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 140 280 25 39 103 167 295), lower := (rows 35 70 140 280 25 32 64 128 256), losses := [] }

theorem u8268 : Upper (D 5) (R 5) [34,68,136,272,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8268
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8269 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 99, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 140 280 26 37 101 165 293), lower := (rows 35 70 140 280 26 32 64 128 256), losses := [] }

theorem u8269 : Upper (D 5) (R 5) [34,68,136,272,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8269
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8270 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 70 140 280 28 35 99 163 291), lower := (rows 35 70 140 280 28 32 64 128 256), losses := [] }

theorem u8270 : Upper (D 5) (R 5) [34,68,136,272,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8270
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8271 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 140 280 49 47 79 143 271), lower := (rows 35 70 140 280 49 32 64 128 256), losses := [] }

theorem u8271 : Upper (D 5) (R 5) [34,68,136,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8271
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8272 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 70 140 280 50 45 77 141 269), lower := (rows 35 70 140 280 50 32 64 128 256), losses := [] }

theorem u8272 : Upper (D 5) (R 5) [34,68,136,272,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8272
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8273 : Route 9 := (fun mask => (mask,id))

def c8273 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8273 : Upper (D 5) (R 5) [34,68,136,272,36] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,36] 13 (by decide) (choices 1) [1,2,8] r8273 c8273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4788
  · exact u4789
  · exact u4790

def b8274 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 99, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 140 280 56 39 71 135 263), lower := (rows 35 70 140 280 56 32 64 128 256), losses := [] }

theorem u8274 : Upper (D 5) (R 5) [34,68,136,272,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8274
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8275 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 70 140 296 19 61 93 157 285), lower := (rows 35 70 140 296 19 32 64 128 256), losses := [] }

theorem u8275 : Upper (D 5) (R 5) [34,68,136,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8275
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8276 : Route 9 := (fun mask => (mask,id))

def c8276 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8276 : Upper (D 5) (R 5) [34,68,136,288,5] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,5] 13 (by decide) (choices 1) [1,2,8,16] r8276 c8276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4791
  · exact u4792
  · exact u4793
  · exact u4794

def b8277 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 16, targets := 9 }], pairs := [(4,0),(4,3)], upper := (rows 35 70 140 296 22 57 89 153 281), lower := (rows 35 70 140 296 22 32 64 128 256), losses := [] }

theorem u8277 : Upper (D 5) (R 5) [34,68,136,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8277
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8278 : PairBound 9 := { available := 23, camps := [{ cop := 4, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 140 296 25 55 87 151 279), lower := (rows 35 70 140 296 25 32 64 128 256), losses := [] }

theorem u8278 : Upper (D 5) (R 5) [34,68,136,288,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8278
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8279 : Route 9 := (fun mask => (mask,id))

def c8279 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8279 : Upper (D 5) (R 5) [34,68,136,288,10] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,10] 13 (by decide) (choices 1) [1,4,16] r8279 c8279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4795
  · exact u4796
  · exact u4797

#print axioms u8279
end Delivery.IrregularNine14.P05
