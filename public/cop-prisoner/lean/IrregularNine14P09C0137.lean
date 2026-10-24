import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0094
import IrregularNine14P09C0095
import IrregularNine14P09C0096

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8220 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 7 140 168 274 369 337 465 337), lower := (rows 97 7 140 168 274 32 64 128 256), losses := [] }

theorem u8220 : Upper (D 9) (R 9) [96,5,136,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8220 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8221 : PairBound 9 := { available := 275, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 7 140 168 336 307 339 403 275), lower := (rows 97 7 140 168 336 32 64 128 256), losses := [] }

theorem u8221 : Upper (D 9) (R 9) [96,5,136,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8221 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8222 : Route 9 := (fun mask => (mask,id))

def c8222 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u8222 : Upper (D 9) (R 9) [96,5,136,257,34] 13 := by
  apply FastRouting.sound _ _ [96,5,136,257,34] 13 (by decide) (choices 1) [16,64,128,256] r8222 c8222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5683
  · exact u5684
  · exact u5685
  · exact u5686

def b8223 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 16, targets := 384 },{ cop := 4, region := 1, targets := 384 },{ cop := 0, region := 16, targets := 1 }], pairs := [(0,7),(0,8),(4,0),(4,7),(4,8)], upper := (rows 97 7 140 265 112 434 466 402 402), lower := (rows 97 7 140 265 112 32 64 128 256), losses := [] }

theorem u8223 : Upper (D 9) (R 9) [96,5,136,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8223 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8224 : Route 9 := (fun mask => (mask,id))

def c8224 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8224 : Upper (D 9) (R 9) [96,5,136,257,130] 13 := by
  apply FastRouting.sound _ _ [96,5,136,257,130] 13 (by decide) (choices 1) [16,64,256] r8224 c8224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5687
  · exact u5688
  · exact u5689

def r8225 : Route 9 := (fun mask => (mask,id))

def c8225 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8225 : Upper (D 9) (R 9) [96,5,136,257,160] 13 := by
  apply FastRouting.sound _ _ [96,5,136,257,160] 13 (by decide) (choices 1) [2,16,64,256] r8225 c8225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5690
  · exact u5691
  · exact u5692
  · exact u5693

def r8226 : Route 9 := (fun mask => (mask,id))

def c8226 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8226 : Upper (D 9) (R 9) [96,5,136,257,258] 13 := by
  apply FastRouting.sound _ _ [96,5,136,257,258] 13 (by decide) (choices 1) [16,64,128] r8226 c8226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5694
  · exact u5695
  · exact u5696

def r8227 : Route 9 := (fun mask => (mask,id))

def c8227 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8227 : Upper (D 9) (R 9) [96,5,136,257,288] 13 := by
  apply FastRouting.sound _ _ [96,5,136,257,288] 13 (by decide) (choices 1) [2,16,64,128] r8227 c8227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5697
  · exact u5698
  · exact u5699
  · exact u5700

def r8228 : Route 9 := (fun mask => (mask,id))

def c8228 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8228 : Upper (D 9) (R 9) [96,5,136,257,384] 13 := by
  apply FastRouting.sound _ _ [96,5,136,257,384] 13 (by decide) (choices 1) [2,16,64] r8228 c8228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5701
  · exact u5702
  · exact u5703

def b8229 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 16, targets := 448 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(4,6),(4,7),(4,8)], upper := (rows 97 7 140 266 49 496 464 464 464), lower := (rows 97 7 140 266 49 32 64 128 256), losses := [] }

theorem u8229 : Upper (D 9) (R 9) [96,5,136,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8229 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8230 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 16, targets := 384 },{ cop := 4, region := 1, targets := 384 },{ cop := 0, region := 16, targets := 1 }], pairs := [(0,7),(0,8),(4,0),(4,7),(4,8)], upper := (rows 97 7 140 266 112 433 465 401 401), lower := (rows 97 7 140 266 112 32 64 128 256), losses := [] }

theorem u8230 : Upper (D 9) (R 9) [96,5,136,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8230 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8231 : Route 9 := (fun mask => (mask,id))

def c8231 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8231 : Upper (D 9) (R 9) [96,5,136,258,129] 13 := by
  apply FastRouting.sound _ _ [96,5,136,258,129] 13 (by decide) (choices 1) [16,64,256] r8231 c8231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5704
  · exact u5705
  · exact u5706

def r8232 : Route 9 := (fun mask => (mask,id))

def c8232 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8232 : Upper (D 9) (R 9) [96,5,136,258,160] 13 := by
  apply FastRouting.sound _ _ [96,5,136,258,160] 13 (by decide) (choices 1) [1,16,64,256] r8232 c8232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5707
  · exact u5708
  · exact u5709
  · exact u5710

def r8233 : Route 9 := (fun mask => (mask,id))

def c8233 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8233 : Upper (D 9) (R 9) [96,5,136,258,257] 13 := by
  apply FastRouting.sound _ _ [96,5,136,258,257] 13 (by decide) (choices 1) [16,64,128] r8233 c8233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5711
  · exact u5712
  · exact u5713

def r8234 : Route 9 := (fun mask => (mask,id))

def c8234 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8234 : Upper (D 9) (R 9) [96,5,136,258,288] 13 := by
  apply FastRouting.sound _ _ [96,5,136,258,288] 13 (by decide) (choices 1) [1,16,64,128] r8234 c8234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5714
  · exact u5715
  · exact u5716
  · exact u5717

def r8235 : Route 9 := (fun mask => (mask,id))

def c8235 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8235 : Upper (D 9) (R 9) [96,5,136,258,384] 13 := by
  apply FastRouting.sound _ _ [96,5,136,258,384] 13 (by decide) (choices 1) [1,16,64] r8235 c8235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5718
  · exact u5719
  · exact u5720

def b8236 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 16, targets := 448 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(4,6),(4,7),(4,8)], upper := (rows 97 7 140 280 49 482 450 450 450), lower := (rows 97 7 140 280 49 32 64 128 256), losses := [] }

theorem u8236 : Upper (D 9) (R 9) [96,5,136,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8236 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8237 : Route 9 := (fun mask => (mask,id))

def c8237 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8237 : Upper (D 9) (R 9) [96,5,136,272,34] 13 := by
  apply FastRouting.sound _ _ [96,5,136,272,34] 13 (by decide) (choices 1) [1,64,128,256] r8237 c8237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5721
  · exact u5722
  · exact u5723
  · exact u5724

def b8238 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 16, targets := 384 },{ cop := 4, region := 1, targets := 384 },{ cop := 0, region := 16, targets := 1 }], pairs := [(0,7),(0,8),(4,0),(4,7),(4,8)], upper := (rows 97 7 140 280 112 419 451 387 387), lower := (rows 97 7 140 280 112 32 64 128 256), losses := [] }

theorem u8238 : Upper (D 9) (R 9) [96,5,136,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8238 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8239 : Route 9 := (fun mask => (mask,id))

def c8239 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8239 : Upper (D 9) (R 9) [96,5,136,272,129] 13 := by
  apply FastRouting.sound _ _ [96,5,136,272,129] 13 (by decide) (choices 1) [2,64,256] r8239 c8239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5725
  · exact u5726
  · exact u5727

def r8240 : Route 9 := (fun mask => (mask,id))

def c8240 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8240 : Upper (D 9) (R 9) [96,5,136,272,130] 13 := by
  apply FastRouting.sound _ _ [96,5,136,272,130] 13 (by decide) (choices 1) [1,64,256] r8240 c8240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5728
  · exact u5729
  · exact u5730

def r8241 : Route 9 := (fun mask => (mask,id))

def c8241 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8241 : Upper (D 9) (R 9) [96,5,136,272,160] 13 := by
  apply FastRouting.sound _ _ [96,5,136,272,160] 13 (by decide) (choices 1) [1,2,64,256] r8241 c8241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5731
  · exact u5732
  · exact u5733
  · exact u5734

def b8242 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 7 140 280 273 226 226 226 482), lower := (rows 97 7 140 280 273 32 64 128 256), losses := [] }

theorem u8242 : Upper (D 9) (R 9) [96,5,136,272,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8242 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8243 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 225, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 7 140 280 274 225 225 225 481), lower := (rows 97 7 140 280 274 32 64 128 256), losses := [] }

theorem u8243 : Upper (D 9) (R 9) [96,5,136,272,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8243 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8244 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 7 140 280 304 227 195 195 451), lower := (rows 97 7 140 280 304 32 64 128 256), losses := [] }

theorem u8244 : Upper (D 9) (R 9) [96,5,136,272,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8244 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8245 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 12, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(3,0),(3,5)], upper := (rows 97 7 140 280 400 99 99 227 355), lower := (rows 97 7 140 280 400 32 64 128 256), losses := [] }

theorem u8245 : Upper (D 9) (R 9) [96,5,136,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8245 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8246 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 16, targets := 416 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(2,6),(4,5),(4,7),(4,8)], upper := (rows 97 7 140 296 81 434 466 402 402), lower := (rows 97 7 140 296 81 32 64 128 256), losses := [] }

theorem u8246 : Upper (D 9) (R 9) [96,5,136,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8246 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8247 : Route 9 := (fun mask => (mask,id))

def c8247 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u8247 : Upper (D 9) (R 9) [96,5,136,288,66] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,66] 13 (by decide) (choices 1) [1,16,128,256] r8247 c8247
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5735
  · exact u5736
  · exact u5737
  · exact u5738

def r8248 : Route 9 := (fun mask => (mask,id))

def c8248 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8248 : Upper (D 9) (R 9) [96,5,136,288,129] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,129] 13 (by decide) (choices 1) [2,16,64,256] r8248 c8248
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5739
  · exact u5740
  · exact u5741
  · exact u5742

def r8249 : Route 9 := (fun mask => (mask,id))

def c8249 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8249 : Upper (D 9) (R 9) [96,5,136,288,130] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,130] 13 (by decide) (choices 1) [1,16,64,256] r8249 c8249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5743
  · exact u5744
  · exact u5745
  · exact u5746

def r8250 : Route 9 := (fun mask => (mask,id))

def c8250 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8250 : Upper (D 9) (R 9) [96,5,136,288,192] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,192] 13 (by decide) (choices 1) [1,2,16,256] r8250 c8250
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5747
  · exact u5748
  · exact u5749
  · exact u5750

def r8251 : Route 9 := (fun mask => (mask,id))

def c8251 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8251 : Upper (D 9) (R 9) [96,5,136,288,257] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,257] 13 (by decide) (choices 1) [2,16,64,128] r8251 c8251
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5751
  · exact u5752
  · exact u5753
  · exact u5754

def r8252 : Route 9 := (fun mask => (mask,id))

def c8252 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8252 : Upper (D 9) (R 9) [96,5,136,288,258] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,258] 13 (by decide) (choices 1) [1,16,64,128] r8252 c8252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5755
  · exact u5756
  · exact u5757
  · exact u5758

def r8253 : Route 9 := (fun mask => (mask,id))

def c8253 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8253 : Upper (D 9) (R 9) [96,5,136,288,320] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,320] 13 (by decide) (choices 1) [1,2,16,128] r8253 c8253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5759
  · exact u5760
  · exact u5761
  · exact u5762

def r8254 : Route 9 := (fun mask => (mask,id))

def c8254 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8254 : Upper (D 9) (R 9) [96,5,136,288,384] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,384] 13 (by decide) (choices 1) [1,2,16,64] r8254 c8254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5763
  · exact u5764
  · exact u5765
  · exact u5766

def b8255 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 7 140 392 50 369 337 465 337), lower := (rows 97 7 140 392 50 32 64 128 256), losses := [] }

theorem u8255 : Upper (D 9) (R 9) [96,5,136,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8255 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8256 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 7 140 392 273 114 114 242 370), lower := (rows 97 7 140 392 273 32 64 128 256), losses := [] }

theorem u8256 : Upper (D 9) (R 9) [96,5,136,384,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8256 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8257 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 7 140 392 274 113 113 241 369), lower := (rows 97 7 140 392 274 32 64 128 256), losses := [] }

theorem u8257 : Upper (D 9) (R 9) [96,5,136,384,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8257 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8258 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 7 140 392 304 115 83 211 339), lower := (rows 97 7 140 392 304 32 64 128 256), losses := [] }

theorem u8258 : Upper (D 9) (R 9) [96,5,136,384,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8258 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8259 : Route 9 := (fun mask => (mask,id))

def c8259 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8259 : Upper (D 9) (R 9) [96,5,160,17,192] 13 := by
  apply FastRouting.sound _ _ [96,5,160,17,192] 13 (by decide) (choices 1) [2,8,256] r8259 c8259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5767
  · exact u5768
  · exact u5769

def r8260 : Route 9 := (fun mask => (mask,id))

def c8260 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8260 : Upper (D 9) (R 9) [96,5,160,17,320] 13 := by
  apply FastRouting.sound _ _ [96,5,160,17,320] 13 (by decide) (choices 1) [2,8,128,256] r8260 c8260
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5770
  · exact u5771
  · exact u5772
  · exact u5773

def r8261 : Route 9 := (fun mask => (mask,id))

def c8261 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8261 : Upper (D 9) (R 9) [96,5,160,17,384] 13 := by
  apply FastRouting.sound _ _ [96,5,160,17,384] 13 (by decide) (choices 1) [2,8,64,256] r8261 c8261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5774
  · exact u5775
  · exact u5776
  · exact u5777

def b8262 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 16, targets := 416 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(2,6),(4,5),(4,7),(4,8)], upper := (rows 97 7 164 26 81 424 456 392 392), lower := (rows 97 7 164 26 81 32 64 128 256), losses := [] }

theorem u8262 : Upper (D 9) (R 9) [96,5,160,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8262 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8263 : Route 9 := (fun mask => (mask,id))

def c8263 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8263 : Upper (D 9) (R 9) [96,5,160,18,72] 13 := by
  apply FastRouting.sound _ _ [96,5,160,18,72] 13 (by decide) (choices 1) [1,128,256] r8263 c8263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5778
  · exact u5779
  · exact u5780

def r8264 : Route 9 := (fun mask => (mask,id))

def c8264 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8264 : Upper (D 9) (R 9) [96,5,160,18,129] 13 := by
  apply FastRouting.sound _ _ [96,5,160,18,129] 13 (by decide) (choices 1) [8,64,256] r8264 c8264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5781
  · exact u5782
  · exact u5783

def r8265 : Route 9 := (fun mask => (mask,id))

def c8265 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8265 : Upper (D 9) (R 9) [96,5,160,18,136] 13 := by
  apply FastRouting.sound _ _ [96,5,160,18,136] 13 (by decide) (choices 1) [1,64,256] r8265 c8265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5784
  · exact u5785
  · exact u5786

def r8266 : Route 9 := (fun mask => (mask,id))

def c8266 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8266 : Upper (D 9) (R 9) [96,5,160,18,192] 13 := by
  apply FastRouting.sound _ _ [96,5,160,18,192] 13 (by decide) (choices 1) [1,8,256] r8266 c8266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5787
  · exact u5788
  · exact u5789

def r8267 : Route 9 := (fun mask => (mask,id))

def c8267 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | _ => 0)

theorem u8267 : Upper (D 9) (R 9) [96,5,160,18,257] 13 := by
  apply FastRouting.sound _ _ [96,5,160,18,257] 13 (by decide) (choices 1) [8,64,128,256] r8267 c8267
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5790
  · exact u5791
  · exact u5792
  · exact u5793

def r8268 : Route 9 := (fun mask => (mask,id))

def c8268 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8268 : Upper (D 9) (R 9) [96,5,160,18,264] 13 := by
  apply FastRouting.sound _ _ [96,5,160,18,264] 13 (by decide) (choices 1) [1,64,128,256] r8268 c8268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5794
  · exact u5795
  · exact u5796
  · exact u5797

def r8269 : Route 9 := (fun mask => (mask,id))

def c8269 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8269 : Upper (D 9) (R 9) [96,5,160,18,320] 13 := by
  apply FastRouting.sound _ _ [96,5,160,18,320] 13 (by decide) (choices 1) [1,8,128,256] r8269 c8269
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5798
  · exact u5799
  · exact u5800
  · exact u5801

def r8270 : Route 9 := (fun mask => (mask,id))

def c8270 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8270 : Upper (D 9) (R 9) [96,5,160,18,384] 13 := by
  apply FastRouting.sound _ _ [96,5,160,18,384] 13 (by decide) (choices 1) [1,8,64,256] r8270 c8270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5802
  · exact u5803
  · exact u5804
  · exact u5805

def b8271 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 8, targets := 416 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(2,6),(3,5),(3,7),(3,8)], upper := (rows 97 7 164 73 146 312 344 408 280), lower := (rows 97 7 164 73 146 32 64 128 256), losses := [] }

theorem u8271 : Upper (D 9) (R 9) [96,5,160,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8271 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8272 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 8, targets := 416 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(2,6),(3,5),(3,7),(3,8)], upper := (rows 97 7 164 73 152 306 338 402 274), lower := (rows 97 7 164 73 152 32 64 128 256), losses := [] }

theorem u8272 : Upper (D 9) (R 9) [96,5,160,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8272 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8273 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 8, targets := 416 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(2,6),(3,5),(3,7),(3,8)], upper := (rows 97 7 164 73 274 440 472 408 408), lower := (rows 97 7 164 73 274 32 64 128 256), losses := [] }

theorem u8273 : Upper (D 9) (R 9) [96,5,160,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8273 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8274 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 8, targets := 416 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(2,6),(3,5),(3,7),(3,8)], upper := (rows 97 7 164 73 280 434 466 402 402), lower := (rows 97 7 164 73 280 32 64 128 256), losses := [] }

theorem u8274 : Upper (D 9) (R 9) [96,5,160,65,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8274 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8275 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 8, targets := 416 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(2,6),(3,5),(3,7),(3,8)], upper := (rows 97 7 164 73 400 314 346 410 282), lower := (rows 97 7 164 73 400 32 64 128 256), losses := [] }

theorem u8275 : Upper (D 9) (R 9) [96,5,160,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8275 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8276 : Route 9 := (fun mask => (mask,id))

def c8276 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8276 : Upper (D 9) (R 9) [96,5,160,66,129] 13 := by
  apply FastRouting.sound _ _ [96,5,160,66,129] 13 (by decide) (choices 1) [8,16,256] r8276 c8276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5806
  · exact u5807
  · exact u5808

def r8277 : Route 9 := (fun mask => (mask,id))

def c8277 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8277 : Upper (D 9) (R 9) [96,5,160,66,136] 13 := by
  apply FastRouting.sound _ _ [96,5,160,66,136] 13 (by decide) (choices 1) [1,16,256] r8277 c8277
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5809
  · exact u5810
  · exact u5811

def r8278 : Route 9 := (fun mask => (mask,id))

def c8278 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u8278 : Upper (D 9) (R 9) [96,5,160,66,257] 13 := by
  apply FastRouting.sound _ _ [96,5,160,66,257] 13 (by decide) (choices 1) [8,16,128,256] r8278 c8278
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5812
  · exact u5813
  · exact u5814
  · exact u5815

def r8279 : Route 9 := (fun mask => (mask,id))

def c8279 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u8279 : Upper (D 9) (R 9) [96,5,160,66,264] 13 := by
  apply FastRouting.sound _ _ [96,5,160,66,264] 13 (by decide) (choices 1) [1,16,128,256] r8279 c8279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5816
  · exact u5817
  · exact u5818
  · exact u5819

#print axioms u8279
end Delivery.IrregularNine14.P09
