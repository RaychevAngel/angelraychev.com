import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0027
import IrregularNine14P08C0028

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8220 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 76 392 49 240 240 240 496), lower := (rows 35 7 76 392 49 32 64 128 256), losses := [] }

theorem u8220 : Upper (D 8) (R 8) [34,5,72,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8220 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8221 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 428, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 76 392 81 176 240 176 432), lower := (rows 35 7 76 392 81 32 64 128 256), losses := [] }

theorem u8221 : Upper (D 8) (R 8) [34,5,72,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8221 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8222 : Route 9 := (fun mask => (mask,id))

def c8222 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8222 : Upper (D 8) (R 8) [34,5,72,384,96] 13 := by
  apply FastRouting.sound _ _ [34,5,72,384,96] 13 (by decide) (choices 1) [1,16,128] r8222 c8222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1665
  · exact u1666
  · exact u1667

def b8223 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 76 392 145 112 112 240 368), lower := (rows 35 7 76 392 145 32 64 128 256), losses := [] }

theorem u8223 : Upper (D 8) (R 8) [34,5,72,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8223 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8224 : Route 9 := (fun mask => (mask,id))

def c8224 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8224 : Upper (D 8) (R 8) [34,5,72,384,160] 13 := by
  apply FastRouting.sound _ _ [34,5,72,384,160] 13 (by decide) (choices 1) [1,16,64] r8224 c8224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1668
  · exact u1669
  · exact u1670

def r8225 : Route 9 := (fun mask => (mask,id))

def c8225 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8225 : Upper (D 8) (R 8) [34,5,72,384,192] 13 := by
  apply FastRouting.sound _ _ [34,5,72,384,192] 13 (by decide) (choices 1) [1,16] r8225 c8225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1671
  · exact u1672

def b8226 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 196 25 56 480 480 480 480), lower := (rows 35 7 196 25 56 32 64 128 256), losses := [] }

theorem u8226 : Upper (D 8) (R 8) [34,5,192,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8226 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8227 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 196 25 88 416 480 416 416), lower := (rows 35 7 196 25 88 32 64 128 256), losses := [] }

theorem u8227 : Upper (D 8) (R 8) [34,5,192,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8227 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8228 : PairBound 9 := { available := 424, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 196 25 112 424 488 424 424), lower := (rows 35 7 196 25 112 32 64 128 256), losses := [] }

theorem u8228 : Upper (D 8) (R 8) [34,5,192,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8228 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8229 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 196 25 280 224 224 224 480), lower := (rows 35 7 196 25 280 32 64 128 256), losses := [] }

theorem u8229 : Upper (D 8) (R 8) [34,5,192,17,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8229 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8230 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 196 25 304 232 232 232 488), lower := (rows 35 7 196 25 304 32 64 128 256), losses := [] }

theorem u8230 : Upper (D 8) (R 8) [34,5,192,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8230 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8231 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 196 25 336 168 232 168 424), lower := (rows 35 7 196 25 336 32 64 128 256), losses := [] }

theorem u8231 : Upper (D 8) (R 8) [34,5,192,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8231 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8232 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 196 41 56 496 464 464 464), lower := (rows 35 7 196 41 56 32 64 128 256), losses := [] }

theorem u8232 : Upper (D 8) (R 8) [34,5,192,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8232 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8233 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 196 41 88 432 496 432 432), lower := (rows 35 7 196 41 88 32 64 128 256), losses := [] }

theorem u8233 : Upper (D 8) (R 8) [34,5,192,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8233 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8234 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 196 41 112 440 472 408 408), lower := (rows 35 7 196 41 112 32 64 128 256), losses := [] }

theorem u8234 : Upper (D 8) (R 8) [34,5,192,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8234 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8235 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 196 41 280 240 240 240 496), lower := (rows 35 7 196 41 280 32 64 128 256), losses := [] }

theorem u8235 : Upper (D 8) (R 8) [34,5,192,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8235 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8236 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 196 41 304 248 216 216 472), lower := (rows 35 7 196 41 304 32 64 128 256), losses := [] }

theorem u8236 : Upper (D 8) (R 8) [34,5,192,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8236 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8237 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 196 41 336 184 248 184 440), lower := (rows 35 7 196 41 336 32 64 128 256), losses := [] }

theorem u8237 : Upper (D 8) (R 8) [34,5,192,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8237 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8238 : PairBound 9 := { available := 449, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 7 196 56 56 481 449 449 449), lower := (rows 35 7 196 56 56 32 64 128 256), losses := [] }

theorem u8238 : Upper (D 8) (R 8) [34,5,192,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8238 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8239 : PairBound 9 := { available := 424, camps := [{ cop := 4, region := 428, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 196 56 81 424 488 424 424), lower := (rows 35 7 196 56 81 32 64 128 256), losses := [] }

theorem u8239 : Upper (D 8) (R 8) [34,5,192,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8239 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8240 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 196 56 88 417 481 417 417), lower := (rows 35 7 196 56 88 32 64 128 256), losses := [] }

theorem u8240 : Upper (D 8) (R 8) [34,5,192,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8240 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8241 : PairBound 9 := { available := 393, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 7 196 56 112 425 457 393 393), lower := (rows 35 7 196 56 112 32 64 128 256), losses := [] }

theorem u8241 : Upper (D 8) (R 8) [34,5,192,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8241 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8242 : PairBound 9 := { available := 297, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 7 196 56 208 297 361 425 297), lower := (rows 35 7 196 56 208 32 64 128 256), losses := [] }

theorem u8242 : Upper (D 8) (R 8) [34,5,192,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8242 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8243 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 196 56 273 232 232 232 488), lower := (rows 35 7 196 56 273 32 64 128 256), losses := [] }

theorem u8243 : Upper (D 8) (R 8) [34,5,192,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8243 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8244 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8244 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8244 : Upper (D 8) (R 8) [34,5,192,48,264] 13 := by
  apply FastRouting.sound _ _ [34,5,192,48,264] 13 (by decide) (choices 1) [1,64] r8244 c8244
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1673
  · exact u1674

def b8245 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 7 196 56 304 233 201 201 457), lower := (rows 35 7 196 56 304 32 64 128 256), losses := [] }

theorem u8245 : Upper (D 8) (R 8) [34,5,192,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8245 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8246 : Route 9 := (fun mask => (mask,id))

def c8246 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8246 : Upper (D 8) (R 8) [34,5,192,48,320] 13 := by
  apply FastRouting.sound _ _ [34,5,192,48,320] 13 (by decide) (choices 1) [1,8,128] r8246 c8246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1675
  · exact u1676
  · exact u1677

def b8247 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 196 73 152 304 368 432 304), lower := (rows 35 7 196 73 152 32 64 128 256), losses := [] }

theorem u8247 : Upper (D 8) (R 8) [34,5,192,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8247 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8248 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 196 73 176 312 376 440 312), lower := (rows 35 7 196 73 176 32 64 128 256), losses := [] }

theorem u8248 : Upper (D 8) (R 8) [34,5,192,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8248 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8249 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 196 73 280 176 240 176 432), lower := (rows 35 7 196 73 280 32 64 128 256), losses := [] }

theorem u8249 : Upper (D 8) (R 8) [34,5,192,65,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8249 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8250 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 196 73 304 184 248 184 440), lower := (rows 35 7 196 73 304 32 64 128 256), losses := [] }

theorem u8250 : Upper (D 8) (R 8) [34,5,192,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8250 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8251 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 196 73 400 56 120 184 312), lower := (rows 35 7 196 73 400 32 64 128 256), losses := [] }

theorem u8251 : Upper (D 8) (R 8) [34,5,192,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8251 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8252 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 7 196 88 152 289 353 417 289), lower := (rows 35 7 196 88 152 32 64 128 256), losses := [] }

theorem u8252 : Upper (D 8) (R 8) [34,5,192,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8252 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8253 : Route 9 := (fun mask => (mask,id))

def c8253 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8253 : Upper (D 8) (R 8) [34,5,192,80,160] 13 := by
  apply FastRouting.sound _ _ [34,5,192,80,160] 13 (by decide) (choices 1) [1,8,256] r8253 c8253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1678
  · exact u1679
  · exact u1680

def b8254 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 196 88 273 168 232 168 424), lower := (rows 35 7 196 88 273 32 64 128 256), losses := [] }

theorem u8254 : Upper (D 8) (R 8) [34,5,192,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8254 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8255 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 196 88 280 161 225 161 417), lower := (rows 35 7 196 88 280 32 64 128 256), losses := [] }

theorem u8255 : Upper (D 8) (R 8) [34,5,192,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8255 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8256 : Route 9 := (fun mask => (mask,id))

def c8256 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8256 : Upper (D 8) (R 8) [34,5,192,80,288] 13 := by
  apply FastRouting.sound _ _ [34,5,192,80,288] 13 (by decide) (choices 1) [1,8,128] r8256 c8256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1681
  · exact u1682
  · exact u1683

def r8257 : Route 9 := (fun mask => (mask,id))

def c8257 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8257 : Upper (D 8) (R 8) [34,5,192,80,384] 13 := by
  apply FastRouting.sound _ _ [34,5,192,80,384] 13 (by decide) (choices 1) [1,8] r8257 c8257
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1684
  · exact u1685

theorem m8258_16 : Upper (D 8) (R 8) [34,5,192,96,160,16] 13 :=
  permutation_upper _ _ _ [34,5,192,96,160,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1687

def r8258 : Route 9 := (fun mask => (mask,id))

def c8258 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8258 : Upper (D 8) (R 8) [34,5,192,96,160] 13 := by
  apply FastRouting.sound _ _ [34,5,192,96,160] 13 (by decide) (choices 1) [1,8,16,256] r8258 c8258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1686
  · exact u1687
  · exact m8258_16
  · exact u1688

def b8259 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 196 104 273 184 248 184 440), lower := (rows 35 7 196 104 273 32 64 128 256), losses := [] }

theorem u8259 : Upper (D 8) (R 8) [34,5,192,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8259 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8260 : Route 9 := (fun mask => (mask,id))

def c8260 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8260 : Upper (D 8) (R 8) [34,5,192,96,264] 13 := by
  apply FastRouting.sound _ _ [34,5,192,96,264] 13 (by decide) (choices 1) [1,16,128] r8260 c8260
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1689
  · exact u1690
  · exact u1691

def r8261 : Route 9 := (fun mask => (mask,id))

def c8261 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8261 : Upper (D 8) (R 8) [34,5,192,96,288] 13 := by
  apply FastRouting.sound _ _ [34,5,192,96,288] 13 (by decide) (choices 1) [1,8,16,128] r8261 c8261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1692
  · exact u1693
  · exact u1694
  · exact u1695

def r8262 : Route 9 := (fun mask => (mask,id))

def c8262 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8262 : Upper (D 8) (R 8) [34,5,192,96,384] 13 := by
  apply FastRouting.sound _ _ [34,5,192,96,384] 13 (by decide) (choices 1) [1,8,16] r8262 c8262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1696
  · exact u1697
  · exact u1698

def b8263 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 7 196 200 280 49 113 177 305), lower := (rows 35 7 196 200 280 32 64 128 256), losses := [] }

theorem u8263 : Upper (D 8) (R 8) [34,5,192,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8263 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8264 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 7 196 200 304 57 121 185 313), lower := (rows 35 7 196 200 304 32 64 128 256), losses := [] }

theorem u8264 : Upper (D 8) (R 8) [34,5,192,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8264 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8265 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 268 56 49 224 192 192 448), lower := (rows 35 7 268 56 49 32 64 128 256), losses := [] }

theorem u8265 : Upper (D 8) (R 8) [34,5,264,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8265 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8266 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 428, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 268 56 81 224 224 224 480), lower := (rows 35 7 268 56 81 32 64 128 256), losses := [] }

theorem u8266 : Upper (D 8) (R 8) [34,5,264,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8266 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8267 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 7 268 56 112 225 193 193 449), lower := (rows 35 7 268 56 112 32 64 128 256), losses := [] }

theorem u8267 : Upper (D 8) (R 8) [34,5,264,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8267 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8268 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8268 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8268 : Upper (D 8) (R 8) [34,5,264,48,192] 13 := by
  apply FastRouting.sound _ _ [34,5,264,48,192] 13 (by decide) (choices 1) [1,64] r8268 c8268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1699
  · exact u1700

def b8269 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 268 88 49 224 224 224 480), lower := (rows 35 7 268 88 49 32 64 128 256), losses := [] }

theorem u8269 : Upper (D 8) (R 8) [34,5,264,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8269 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8270 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 268 88 81 160 224 160 416), lower := (rows 35 7 268 88 81 32 64 128 256), losses := [] }

theorem u8270 : Upper (D 8) (R 8) [34,5,264,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8270 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8271 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 268 88 112 161 225 161 417), lower := (rows 35 7 268 88 112 32 64 128 256), losses := [] }

theorem u8271 : Upper (D 8) (R 8) [34,5,264,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8271 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8272 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 268 88 145 224 224 224 480), lower := (rows 35 7 268 88 145 32 64 128 256), losses := [] }

theorem u8272 : Upper (D 8) (R 8) [34,5,264,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8272 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8273 : Route 9 := (fun mask => (mask,id))

def c8273 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8273 : Upper (D 8) (R 8) [34,5,264,80,160] 13 := by
  apply FastRouting.sound _ _ [34,5,264,80,160] 13 (by decide) (choices 1) [1,64,128] r8273 c8273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1701
  · exact u1702
  · exact u1703

def b8274 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 268 88 208 161 225 161 417), lower := (rows 35 7 268 88 208 32 64 128 256), losses := [] }

theorem u8274 : Upper (D 8) (R 8) [34,5,264,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8274 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8275 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 268 104 49 240 208 208 464), lower := (rows 35 7 268 104 49 32 64 128 256), losses := [] }

theorem u8275 : Upper (D 8) (R 8) [34,5,264,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8275 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8276 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 428, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 268 104 81 176 240 176 432), lower := (rows 35 7 268 104 81 32 64 128 256), losses := [] }

theorem u8276 : Upper (D 8) (R 8) [34,5,264,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8276 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8277 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 7 268 104 112 177 209 145 401), lower := (rows 35 7 268 104 112 32 64 128 256), losses := [] }

theorem u8277 : Upper (D 8) (R 8) [34,5,264,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8277 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8278 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 268 104 145 240 240 240 496), lower := (rows 35 7 268 104 145 32 64 128 256), losses := [] }

theorem u8278 : Upper (D 8) (R 8) [34,5,264,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8278 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8279 : Route 9 := (fun mask => (mask,id))

def c8279 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8279 : Upper (D 8) (R 8) [34,5,264,96,160] 13 := by
  apply FastRouting.sound _ _ [34,5,264,96,160] 13 (by decide) (choices 1) [1,16,64,128] r8279 c8279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1704
  · exact u1705
  · exact u1706
  · exact u1707

#print axioms u8279
end Delivery.IrregularNine14.P08
