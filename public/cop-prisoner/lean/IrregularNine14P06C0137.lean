import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0010

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8220 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 80, targets := 6 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(4,1),(4,2)], upper := (rows 41 131 262 26 112 36 65 196 324), lower := (rows 41 131 262 26 112 36 65 128 256), losses := [] }

theorem u8220 : Upper (D 6) (R 6) [40,129,258,18,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8221 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 131 262 26 112 36 68 193 321), lower := (rows 41 131 262 26 112 36 68 128 256), losses := [] }

theorem u8221 : Upper (D 6) (R 6) [40,129,258,18,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8221 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8222 : Route 9 := (fun mask => (mask,id))

def c8222 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8222 : Upper (D 6) (R 6) [40,129,258,66,5,4,16] 13 := by
  apply FastRouting.sound _ _ [40,129,258,66,5,4,16] 13 (by decide) (choices 1) [32,64] r8222 c8222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u643
  · exact u644

def b8223 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 104, targets := 1 }], pairs := [(1,2),(3,0),(3,2)], upper := (rows 41 131 262 74 21 36 96 208 336), lower := (rows 41 131 262 74 21 36 96 128 256), losses := [{ target := 2, region := (rows 1 18 0 26 16 32 97 144 272), good := (rows 105 203 266 74 475 96 96 128 256) }] }

theorem u8223 : Upper (D 6) (R 6) [40,129,258,66,5,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8224 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 72, targets := 33 }], pairs := [(3,0),(3,5)], upper := (rows 41 131 262 74 21 48 68 224 352), lower := (rows 41 131 262 74 21 48 68 128 256), losses := [] }

theorem u8224 : Upper (D 6) (R 6) [40,129,258,66,5,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8224 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8225 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 260, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 41 131 262 74 21 48 96 196 324), lower := (rows 41 131 262 74 21 48 96 128 256), losses := [] }

theorem u8225 : Upper (D 6) (R 6) [40,129,258,66,5,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8225 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8226 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 422, targets := 64 },{ cop := 2, region := 72, targets := 1 }], pairs := [(1,6),(2,6),(3,0)], upper := (rows 41 131 262 74 81 36 68 176 304), lower := (rows 41 131 262 74 81 36 68 128 256), losses := [] }

theorem u8226 : Upper (D 6) (R 6) [40,129,258,66,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8226 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8227 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 88, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 41 131 262 74 81 36 80 164 292), lower := (rows 41 131 262 74 81 36 80 128 256), losses := [] }

theorem u8227 : Upper (D 6) (R 6) [40,129,258,66,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8227 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8228 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 41 131 262 74 81 36 96 148 276), lower := (rows 41 131 262 74 81 36 96 128 256), losses := [] }

theorem u8228 : Upper (D 6) (R 6) [40,129,258,66,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8228 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8229 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 72, targets := 36 },{ cop := 3, region := 308, targets := 1 }], pairs := [(2,0),(3,2),(3,5)], upper := (rows 41 131 262 74 84 36 65 176 304), lower := (rows 41 131 262 74 84 36 65 128 256), losses := [] }

theorem u8229 : Upper (D 6) (R 6) [40,129,258,66,68,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8229 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8230 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 41 131 262 74 84 36 80 161 289), lower := (rows 41 131 262 74 84 36 80 128 256), losses := [] }

theorem u8230 : Upper (D 6) (R 6) [40,129,258,66,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8230 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8231 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 120, targets := 1 },{ cop := 2, region := 112, targets := 2 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 41 131 262 74 84 36 96 145 273), lower := (rows 41 131 262 74 84 36 96 128 256), losses := [] }

theorem u8231 : Upper (D 6) (R 6) [40,129,258,66,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8231 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8232 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 80, targets := 6 },{ cop := 1, region := 72, targets := 4 }], pairs := [(3,2),(4,1),(4,2)], upper := (rows 41 131 262 74 112 36 65 148 276), lower := (rows 41 131 262 74 112 36 65 128 256), losses := [] }

theorem u8232 : Upper (D 6) (R 6) [40,129,258,66,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8233 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 131 262 74 112 36 68 145 273), lower := (rows 41 131 262 74 112 36 68 128 256), losses := [] }

theorem u8233 : Upper (D 6) (R 6) [40,129,258,66,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8233 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8234 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 41 131 262 74 112 36 80 133 261), lower := (rows 41 131 262 74 112 36 80 128 256), losses := [] }

theorem u8234 : Upper (D 6) (R 6) [40,129,258,66,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8234 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8235 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 131 262 88 21 34 68 224 352), lower := (rows 41 131 262 88 21 34 68 128 256), losses := [] }

theorem u8235 : Upper (D 6) (R 6) [40,129,258,80,5,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8235 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8236 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 356, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 41 131 262 88 21 34 96 196 324), lower := (rows 41 131 262 88 21 34 96 128 256), losses := [{ target := 0, region := (rows 0 2 38 24 16 38 119 247 375), good := (rows 492 486 486 472 508 486 484 128 256) },{ target := 1, region := (rows 1 0 4 24 16 32 97 144 272), good := (rows 105 193 260 472 477 96 96 128 256) }] }

theorem u8236 : Upper (D 6) (R 6) [40,129,258,80,5,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8236 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8237 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 41 131 276 14 21 96 66 224 352), lower := (rows 41 131 276 14 21 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 107 74 235 363), good := (rows 488 482 276 494 436 480 482 128 256) }] }

theorem u8237 : Upper (D 6) (R 6) [40,129,272,6,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8237 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8238 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 113, targets := 2 },{ cop := 3, region := 97, targets := 4 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 41 131 276 14 21 96 96 194 322), lower := (rows 41 131 276 14 21 96 96 128 256), losses := [] }

theorem u8238 : Upper (D 6) (R 6) [40,129,272,6,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8238 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8239 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 113, targets := 4 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(0,2),(4,2)], upper := (rows 41 131 276 14 50 96 65 196 324), lower := (rows 41 131 276 14 50 96 65 128 256), losses := [] }

theorem u8239 : Upper (D 6) (R 6) [40,129,272,6,34,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8239 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8240 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 112, targets := 1 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(1,5),(4,0)], upper := (rows 41 131 276 14 50 96 68 193 321), lower := (rows 41 131 276 14 50 96 68 128 256), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 76 129 257), good := (rows 459 387 340 78 18 64 68 128 256) }] }

theorem u8240 : Upper (D 6) (R 6) [40,129,272,6,34,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8240 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8241 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 113, targets := 4 },{ cop := 4, region := 292, targets := 1 }], pairs := [(0,2),(2,0),(4,2)], upper := (rows 41 131 276 14 81 96 66 164 292), lower := (rows 41 131 276 14 81 96 66 128 256), losses := [] }

theorem u8241 : Upper (D 6) (R 6) [40,129,272,6,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8241 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8242 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 130, targets := 68 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(1,2),(1,6)], upper := (rows 41 131 276 14 81 96 68 162 290), lower := (rows 41 131 276 14 81 96 68 128 256), losses := [] }

theorem u8242 : Upper (D 6) (R 6) [40,129,272,6,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8243 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 390, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 41 131 276 14 81 96 96 134 262), lower := (rows 41 131 276 14 81 96 96 128 256), losses := [] }

theorem u8243 : Upper (D 6) (R 6) [40,129,272,6,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8243 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8244 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 113, targets := 4 },{ cop := 4, region := 292, targets := 1 }], pairs := [(0,2),(2,0),(4,2)], upper := (rows 41 131 276 14 82 96 65 164 292), lower := (rows 41 131 276 14 82 96 65 128 256), losses := [] }

theorem u8244 : Upper (D 6) (R 6) [40,129,272,6,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8244 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8245 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 130, targets := 68 },{ cop := 3, region := 80, targets := 1 }], pairs := [(1,2),(1,6),(4,0)], upper := (rows 41 131 276 14 82 96 68 161 289), lower := (rows 41 131 276 14 82 96 68 128 256), losses := [] }

theorem u8245 : Upper (D 6) (R 6) [40,129,272,6,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8246 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 112, targets := 5 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(4,0),(4,2)], upper := (rows 41 131 276 14 82 96 96 133 261), lower := (rows 41 131 276 14 82 96 96 128 256), losses := [] }

theorem u8246 : Upper (D 6) (R 6) [40,129,272,6,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8246 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8247 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 171, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 131 276 73 22 34 68 224 352), lower := (rows 41 131 276 73 22 34 68 128 256), losses := [] }

theorem u8247 : Upper (D 6) (R 6) [40,129,272,65,6,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8248 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 73, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 131 276 73 22 34 96 196 324), lower := (rows 41 131 276 73 22 34 96 128 256), losses := [] }

theorem u8248 : Upper (D 6) (R 6) [40,129,272,65,6,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8248 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8249 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 107, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 131 276 73 52 34 66 196 324), lower := (rows 41 131 276 73 52 34 66 128 256), losses := [] }

theorem u8249 : Upper (D 6) (R 6) [40,129,272,65,36,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8249 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8250 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 171, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 131 276 73 52 34 68 194 322), lower := (rows 41 131 276 73 52 34 68 128 256), losses := [] }

theorem u8250 : Upper (D 6) (R 6) [40,129,272,65,36,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8251 : PairBound 9 := { available := 36, camps := [{ cop := 7, region := 107, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 131 276 73 84 34 66 164 292), lower := (rows 41 131 276 73 84 34 66 128 256), losses := [] }

theorem u8251 : Upper (D 6) (R 6) [40,129,272,65,68,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8252 : PairBound 9 := { available := 34, camps := [{ cop := 8, region := 84, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 41 131 276 73 84 34 68 162 290), lower := (rows 41 131 276 73 84 34 68 128 256), losses := [] }

theorem u8252 : Upper (D 6) (R 6) [40,129,272,65,68,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8253 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 73, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 131 276 73 84 34 96 134 262), lower := (rows 41 131 276 73 84 34 96 128 256), losses := [] }

theorem u8253 : Upper (D 6) (R 6) [40,129,272,65,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8253 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8254 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 72, targets := 36 },{ cop := 3, region := 308, targets := 1 }], pairs := [(2,0),(3,2),(3,5)], upper := (rows 41 131 276 74 50 36 65 196 324), lower := (rows 41 131 276 74 50 36 65 128 256), losses := [] }

theorem u8254 : Upper (D 6) (R 6) [40,129,272,66,34,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8254 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8255 : PairBound 9 := { available := 65, camps := [], pairs := [(0,1),(3,0),(4,0)], upper := (rows 41 131 276 74 50 36 68 193 321), lower := (rows 41 131 276 74 50 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 24 100 100 128 256), good := (rows 120 130 380 122 122 100 100 128 256) },{ target := 1, region := (rows 9 0 4 8 16 100 100 137 265), good := (rows 489 385 372 489 112 100 100 128 256) }] }

theorem u8255 : Upper (D 6) (R 6) [40,129,272,66,34,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8256 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 88, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 41 131 276 74 81 36 66 164 292), lower := (rows 41 131 276 74 81 36 66 128 256), losses := [] }

theorem u8256 : Upper (D 6) (R 6) [40,129,272,66,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8256 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8257 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 130, targets := 68 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,2),(1,6),(2,6)], upper := (rows 41 131 276 74 81 36 68 162 290), lower := (rows 41 131 276 74 81 36 68 128 256), losses := [] }

theorem u8257 : Upper (D 6) (R 6) [40,129,272,66,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8258 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 41 131 276 74 81 36 96 134 262), lower := (rows 41 131 276 74 81 36 96 128 256), losses := [] }

theorem u8258 : Upper (D 6) (R 6) [40,129,272,66,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8258 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8259 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 80, targets := 6 },{ cop := 1, region := 72, targets := 4 }], pairs := [(3,2),(4,1),(4,2)], upper := (rows 41 131 276 74 112 36 65 134 262), lower := (rows 41 131 276 74 112 36 65 128 256), losses := [] }

theorem u8259 : Upper (D 6) (R 6) [40,129,272,66,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8259 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8260 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 72, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 131 276 74 112 36 66 133 261), lower := (rows 41 131 276 74 112 36 66 128 256), losses := [] }

theorem u8260 : Upper (D 6) (R 6) [40,129,272,66,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8261 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 41 131 276 74 112 36 68 131 259), lower := (rows 41 131 276 74 112 36 68 128 256), losses := [] }

theorem u8261 : Upper (D 6) (R 6) [40,129,272,66,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8261 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8262 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 41 131 276 76 21 34 66 224 352), lower := (rows 41 131 276 76 21 34 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 98 98 235 363), good := (rows 488 482 276 492 404 482 482 128 256) }] }

theorem u8262 : Upper (D 6) (R 6) [40,129,272,68,5,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8262 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8263 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(1,2),(3,0)], upper := (rows 41 131 276 76 21 34 96 194 322), lower := (rows 41 131 276 76 21 34 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 34 99 162 290), good := (rows 488 482 284 76 92 482 480 128 256) }] }

theorem u8263 : Upper (D 6) (R 6) [40,129,272,68,5,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8263 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8264 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(1,2),(3,1)], upper := (rows 41 131 276 76 22 34 65 224 352), lower := (rows 41 131 276 76 22 34 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 32 67 161 289), good := (rows 489 449 284 76 92 480 449 128 256) }] }

theorem u8264 : Upper (D 6) (R 6) [40,129,272,68,6,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8264 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8265 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 163, targets := 4 },{ cop := 4, region := 104, targets := 1 }], pairs := [(0,2),(1,2),(3,0)], upper := (rows 41 131 276 76 22 34 96 193 321), lower := (rows 41 131 276 76 22 34 96 128 256), losses := [] }

theorem u8265 : Upper (D 6) (R 6) [40,129,272,68,6,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8265 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8266 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 163, targets := 64 },{ cop := 4, region := 292, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 41 131 276 76 82 34 65 164 292), lower := (rows 41 131 276 76 82 34 65 128 256), losses := [] }

theorem u8266 : Upper (D 6) (R 6) [40,129,272,68,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8266 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8267 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 131 276 76 82 34 68 161 289), lower := (rows 41 131 276 76 82 34 68 128 256), losses := [] }

theorem u8267 : Upper (D 6) (R 6) [40,129,272,68,66,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8268 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 112, targets := 5 },{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 41 131 276 76 82 34 96 133 261), lower := (rows 41 131 276 76 82 34 96 128 256), losses := [] }

theorem u8268 : Upper (D 6) (R 6) [40,129,272,68,66,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8268 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8269 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 80, targets := 6 },{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 41 131 276 76 112 34 65 134 262), lower := (rows 41 131 276 76 112 34 65 128 256), losses := [] }

theorem u8269 : Upper (D 6) (R 6) [40,129,272,68,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8270 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 269, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 131 276 76 112 34 66 133 261), lower := (rows 41 131 276 76 112 34 66 128 256), losses := [] }

theorem u8270 : Upper (D 6) (R 6) [40,129,272,68,96,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8270 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8271 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 131 276 76 112 34 68 131 259), lower := (rows 41 131 276 76 112 34 68 128 256), losses := [] }

theorem u8271 : Upper (D 6) (R 6) [40,129,272,68,96,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8271 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8272 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 113, targets := 4 },{ cop := 4, region := 292, targets := 1 }], pairs := [(0,2),(2,0),(4,2)], upper := (rows 41 131 292 14 81 96 66 148 276), lower := (rows 41 131 292 14 81 96 66 128 256), losses := [] }

theorem u8272 : Upper (D 6) (R 6) [40,129,288,6,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8272 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8273 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 113, targets := 2 },{ cop := 4, region := 130, targets := 32 }], pairs := [(0,1),(1,5),(4,1)], upper := (rows 41 131 292 14 81 96 68 146 274), lower := (rows 41 131 292 14 81 96 68 128 256), losses := [] }

theorem u8273 : Upper (D 6) (R 6) [40,129,288,6,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8273 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8274 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 113, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 41 131 292 14 81 96 80 134 262), lower := (rows 41 131 292 14 81 96 80 128 256), losses := [] }

theorem u8274 : Upper (D 6) (R 6) [40,129,288,6,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8274 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8275 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 113, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 41 131 292 14 82 48 65 196 324), lower := (rows 41 131 292 14 82 48 65 128 256), losses := [] }

theorem u8275 : Upper (D 6) (R 6) [40,129,288,6,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8275 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8276 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 324, targets := 2 },{ cop := 3, region := 80, targets := 1 }], pairs := [(2,1),(4,0)], upper := (rows 41 131 292 14 82 48 68 193 321), lower := (rows 41 131 292 14 82 48 68 128 256), losses := [] }

theorem u8276 : Upper (D 6) (R 6) [40,129,288,6,66,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8276 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8277 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 113, targets := 4 },{ cop := 4, region := 292, targets := 1 }], pairs := [(0,2),(2,0),(4,2)], upper := (rows 41 131 292 14 82 96 65 148 276), lower := (rows 41 131 292 14 82 96 65 128 256), losses := [] }

theorem u8277 : Upper (D 6) (R 6) [40,129,288,6,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8278 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 100, targets := 3 },{ cop := 3, region := 80, targets := 1 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 41 131 292 14 82 96 68 145 273), lower := (rows 41 131 292 14 82 96 68 128 256), losses := [] }

theorem u8278 : Upper (D 6) (R 6) [40,129,288,6,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8278 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8279 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 41 131 292 14 82 96 80 133 261), lower := (rows 41 131 292 14 82 96 80 128 256), losses := [] }

theorem u8279 : Upper (D 6) (R 6) [40,129,288,6,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8279 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u8279
end Delivery.IrregularNine14.P06
