import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0341
import IrregularNine14P07C0342

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b35400 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 194 37 73 148 314 346 410 282), lower := (rows 35 194 37 73 148 32 64 128 256), losses := [] }

theorem u35400 : Upper (D 7) (R 7) [34,192,33,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35400 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35401 : PairBound 9 := { available := 278, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 194 37 73 152 310 342 406 278), lower := (rows 35 194 37 73 152 32 64 128 256), losses := [] }

theorem u35401 : Upper (D 7) (R 7) [34,192,33,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35401 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35402 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 194 37 73 274 188 220 156 412), lower := (rows 35 194 37 73 274 32 64 128 256), losses := [] }

theorem u35402 : Upper (D 7) (R 7) [34,192,33,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35402 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35403 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 194 37 73 276 186 218 154 410), lower := (rows 35 194 37 73 276 32 64 128 256), losses := [] }

theorem u35403 : Upper (D 7) (R 7) [34,192,33,65,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35403 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35404 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 194 37 73 280 182 214 150 406), lower := (rows 35 194 37 73 280 32 64 128 256), losses := [] }

theorem u35404 : Upper (D 7) (R 7) [34,192,33,65,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35404 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35405 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 194 37 73 400 62 94 158 286), lower := (rows 35 194 37 73 400 32 64 128 256), losses := [] }

theorem u35405 : Upper (D 7) (R 7) [34,192,33,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35405 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35406 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 194 37 76 152 307 339 403 275), lower := (rows 35 194 37 76 152 32 64 128 256), losses := [] }

theorem u35406 : Upper (D 7) (R 7) [34,192,33,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35406 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35407 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 194 37 76 273 186 218 154 410), lower := (rows 35 194 37 76 273 32 64 128 256), losses := [] }

theorem u35407 : Upper (D 7) (R 7) [34,192,33,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35407 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35408 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 194 37 76 274 185 217 153 409), lower := (rows 35 194 37 76 274 32 64 128 256), losses := [] }

theorem u35408 : Upper (D 7) (R 7) [34,192,33,68,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35408 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35409 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 194 37 76 280 179 211 147 403), lower := (rows 35 194 37 76 280 32 64 128 256), losses := [] }

theorem u35409 : Upper (D 7) (R 7) [34,192,33,68,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35409 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35410 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 194 37 76 400 59 91 155 283), lower := (rows 35 194 37 76 400 32 64 128 256), losses := [] }

theorem u35410 : Upper (D 7) (R 7) [34,192,33,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35410 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35411 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 194 37 88 273 174 206 142 398), lower := (rows 35 194 37 88 273 32 64 128 256), losses := [] }

theorem u35411 : Upper (D 7) (R 7) [34,192,33,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35411 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35412 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 194 37 88 274 173 205 141 397), lower := (rows 35 194 37 88 274 32 64 128 256), losses := [] }

theorem u35412 : Upper (D 7) (R 7) [34,192,33,80,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35412 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35413 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 194 37 88 276 171 203 139 395), lower := (rows 35 194 37 88 276 32 64 128 256), losses := [] }

theorem u35413 : Upper (D 7) (R 7) [34,192,33,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35414 : PairBound 9 := { available := 135, camps := [{ cop := 2, region := 474, targets := 32 },{ cop := 0, region := 4, targets := 2 }], pairs := [(1,5),(2,1),(3,5),(4,5)], upper := (rows 35 194 37 88 280 167 199 135 391), lower := (rows 35 194 37 88 280 32 64 128 256), losses := [] }

theorem u35414 : Upper (D 7) (R 7) [34,192,33,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35414 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35415 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 194 37 88 400 47 79 143 271), lower := (rows 35 194 37 88 400 32 64 128 256), losses := [] }

theorem u35415 : Upper (D 7) (R 7) [34,192,33,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35415 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35416 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 194 38 73 145 316 348 412 284), lower := (rows 35 194 38 73 145 32 64 128 256), losses := [] }

theorem u35416 : Upper (D 7) (R 7) [34,192,34,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35416 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35417 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 194 38 73 148 313 345 409 281), lower := (rows 35 194 38 73 148 32 64 128 256), losses := [] }

theorem u35417 : Upper (D 7) (R 7) [34,192,34,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35417 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35418 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 194 38 73 152 309 341 405 277), lower := (rows 35 194 38 73 152 32 64 128 256), losses := [] }

theorem u35418 : Upper (D 7) (R 7) [34,192,34,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35418 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35419 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 194 38 73 273 188 220 156 412), lower := (rows 35 194 38 73 273 32 64 128 256), losses := [] }

theorem u35419 : Upper (D 7) (R 7) [34,192,34,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35419 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35420 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 194 38 73 276 185 217 153 409), lower := (rows 35 194 38 73 276 32 64 128 256), losses := [] }

theorem u35420 : Upper (D 7) (R 7) [34,192,34,65,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35420 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35421 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 194 38 73 280 181 213 149 405), lower := (rows 35 194 38 73 280 32 64 128 256), losses := [] }

theorem u35421 : Upper (D 7) (R 7) [34,192,34,65,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35421 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35422 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 194 38 73 400 61 93 157 285), lower := (rows 35 194 38 73 400 32 64 128 256), losses := [] }

theorem u35422 : Upper (D 7) (R 7) [34,192,34,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35422 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35423 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 194 38 76 152 305 337 401 273), lower := (rows 35 194 38 76 152 32 64 128 256), losses := [] }

theorem u35423 : Upper (D 7) (R 7) [34,192,34,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35423 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35424 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 194 38 76 273 185 217 153 409), lower := (rows 35 194 38 76 273 32 64 128 256), losses := [] }

theorem u35424 : Upper (D 7) (R 7) [34,192,34,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35424 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35425 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 194 38 76 280 177 209 145 401), lower := (rows 35 194 38 76 280 32 64 128 256), losses := [] }

theorem u35425 : Upper (D 7) (R 7) [34,192,34,68,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35425 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35426 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 194 38 76 400 57 89 153 281), lower := (rows 35 194 38 76 400 32 64 128 256), losses := [] }

theorem u35426 : Upper (D 7) (R 7) [34,192,34,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35426 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35427 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 194 38 88 273 173 205 141 397), lower := (rows 35 194 38 88 273 32 64 128 256), losses := [] }

theorem u35427 : Upper (D 7) (R 7) [34,192,34,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35428 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 194 38 88 276 169 201 137 393), lower := (rows 35 194 38 88 276 32 64 128 256), losses := [] }

theorem u35428 : Upper (D 7) (R 7) [34,192,34,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35428 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35429 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 37, targets := 64 },{ cop := 0, region := 4, targets := 1 },{ cop := 0, region := 4, targets := 128 }], pairs := [(0,6),(2,0),(2,6),(2,7)], upper := (rows 35 194 38 88 280 165 197 133 389), lower := (rows 35 194 38 88 280 32 64 128 256), losses := [] }

theorem u35429 : Upper (D 7) (R 7) [34,192,34,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35429 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35430 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 194 38 88 400 45 77 141 269), lower := (rows 35 194 38 88 400 32 64 128 256), losses := [] }

theorem u35430 : Upper (D 7) (R 7) [34,192,34,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35430 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35431 : Route 9 := (fun mask => (mask,id))

def c35431 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35431 : Upper (D 7) (R 7) [34,192,40,65,129] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65,129] 13 (by decide) (choices 1) [2,4,16,256] r35431 c35431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20508
  · exact u20509
  · exact u20510
  · exact u20511

def b35432 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 35 194 44 73 146 309 341 405 277), lower := (rows 35 194 44 73 146 32 64 128 256), losses := [] }

theorem u35432 : Upper (D 7) (R 7) [34,192,40,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35432 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35433 : Route 9 := (fun mask => (mask,id))

def c35433 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35433 : Upper (D 7) (R 7) [34,192,40,65,132] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65,132] 13 (by decide) (choices 1) [1,2,16,256] r35433 c35433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20512
  · exact u20513
  · exact u20514
  · exact u20515

def r35434 : Route 9 := (fun mask => (mask,id))

def c35434 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35434 : Upper (D 7) (R 7) [34,192,40,65,257] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65,257] 13 (by decide) (choices 1) [2,4,16,128] r35434 c35434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20516
  · exact u20517
  · exact u20518
  · exact u20519

def r35435 : Route 9 := (fun mask => (mask,id))

def c35435 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35435 : Upper (D 7) (R 7) [34,192,40,65,258] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65,258] 13 (by decide) (choices 1) [1,4,16,128] r35435 c35435
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20520
  · exact u20521
  · exact u20522
  · exact u20523

def r35436 : Route 9 := (fun mask => (mask,id))

def c35436 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35436 : Upper (D 7) (R 7) [34,192,40,65,260] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65,260] 13 (by decide) (choices 1) [1,2,16,128] r35436 c35436
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20524
  · exact u20525
  · exact u20526
  · exact u20527

def r35437 : Route 9 := (fun mask => (mask,id))

def c35437 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35437 : Upper (D 7) (R 7) [34,192,40,65,384] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65,384] 13 (by decide) (choices 1) [1,2,4,16] r35437 c35437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20528
  · exact u20529
  · exact u20530
  · exact u20531

def b35438 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 194 44 74 145 309 341 405 277), lower := (rows 35 194 44 74 145 32 64 128 256), losses := [] }

theorem u35438 : Upper (D 7) (R 7) [34,192,40,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35438 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35439 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 194 44 74 148 305 337 401 273), lower := (rows 35 194 44 74 148 32 64 128 256), losses := [] }

theorem u35439 : Upper (D 7) (R 7) [34,192,40,66,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35440 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 194 44 74 273 181 213 149 405), lower := (rows 35 194 44 74 273 32 64 128 256), losses := [] }

theorem u35440 : Upper (D 7) (R 7) [34,192,40,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35440 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35441 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 194 44 74 276 177 209 145 401), lower := (rows 35 194 44 74 276 32 64 128 256), losses := [] }

theorem u35441 : Upper (D 7) (R 7) [34,192,40,66,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35441 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35442 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 194 44 74 400 53 85 149 277), lower := (rows 35 194 44 74 400 32 64 128 256), losses := [] }

theorem u35442 : Upper (D 7) (R 7) [34,192,40,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35442 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35443 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(1,5),(4,5),(4,6)], upper := (rows 35 194 44 76 145 307 339 403 275), lower := (rows 35 194 44 76 145 32 64 128 256), losses := [] }

theorem u35443 : Upper (D 7) (R 7) [34,192,40,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35443 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35444 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(1,5),(4,5),(4,6)], upper := (rows 35 194 44 76 273 179 211 147 403), lower := (rows 35 194 44 76 273 32 64 128 256), losses := [] }

theorem u35444 : Upper (D 7) (R 7) [34,192,40,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35444 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35445 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(1,5),(4,5),(4,6)], upper := (rows 35 194 44 76 274 177 209 145 401), lower := (rows 35 194 44 76 274 32 64 128 256), losses := [] }

theorem u35445 : Upper (D 7) (R 7) [34,192,40,68,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35445 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35446 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(1,5),(4,5),(4,6)], upper := (rows 35 194 44 76 400 51 83 147 275), lower := (rows 35 194 44 76 400 32 64 128 256), losses := [] }

theorem u35446 : Upper (D 7) (R 7) [34,192,40,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35446 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35447 : Route 9 := (fun mask => (mask,id))

def c35447 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35447 : Upper (D 7) (R 7) [34,192,40,80,129] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,129] 13 (by decide) (choices 1) [1,2,4,256] r35447 c35447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20532
  · exact u20533
  · exact u20534
  · exact u20535

def b35448 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 35 194 44 88 146 293 325 389 261), lower := (rows 35 194 44 88 146 32 64 128 256), losses := [] }

theorem u35448 : Upper (D 7) (R 7) [34,192,40,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35448 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35449 : Route 9 := (fun mask => (mask,id))

def c35449 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35449 : Upper (D 7) (R 7) [34,192,40,80,132] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,132] 13 (by decide) (choices 1) [1,2,256] r35449 c35449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20536
  · exact u20537
  · exact u20538

def r35450 : Route 9 := (fun mask => (mask,id))

def c35450 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35450 : Upper (D 7) (R 7) [34,192,40,80,257] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,257] 13 (by decide) (choices 1) [1,2,4,128] r35450 c35450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20539
  · exact u20540
  · exact u20541
  · exact u20542

def r35451 : Route 9 := (fun mask => (mask,id))

def c35451 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35451 : Upper (D 7) (R 7) [34,192,40,80,258] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,258] 13 (by decide) (choices 1) [1,4,128] r35451 c35451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20543
  · exact u20544
  · exact u20545

def r35452 : Route 9 := (fun mask => (mask,id))

def c35452 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35452 : Upper (D 7) (R 7) [34,192,40,80,260] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,260] 13 (by decide) (choices 1) [1,2,128] r35452 c35452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20546
  · exact u20547
  · exact u20548

def r35453 : Route 9 := (fun mask => (mask,id))

def c35453 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35453 : Upper (D 7) (R 7) [34,192,40,80,384] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,384] 13 (by decide) (choices 1) [1,2,4] r35453 c35453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20549
  · exact u20550
  · exact u20551

def b35454 : PairBound 9 := { available := 23, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 44 200 273 55 87 151 279), lower := (rows 35 194 44 200 273 32 64 128 256), losses := [] }

theorem u35454 : Upper (D 7) (R 7) [34,192,40,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35454 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35455 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 44 200 274 53 85 149 277), lower := (rows 35 194 44 200 274 32 64 128 256), losses := [] }

theorem u35455 : Upper (D 7) (R 7) [34,192,40,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35456 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 44 200 276 51 83 147 275), lower := (rows 35 194 44 200 276 32 64 128 256), losses := [] }

theorem u35456 : Upper (D 7) (R 7) [34,192,40,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35456 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35457 : Route 9 := (fun mask => (mask,id))

def c35457 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35457 : Upper (D 7) (R 7) [34,192,40,257,65] 13 := by
  apply FastRouting.sound _ _ [34,192,40,257,65] 13 (by decide) (choices 1) [2,4,16,128] r35457 c35457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20552
  · exact u20553
  · exact u20554
  · exact u20555

def b35458 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 194 44 265 82 181 213 149 405), lower := (rows 35 194 44 265 82 32 64 128 256), losses := [] }

theorem u35458 : Upper (D 7) (R 7) [34,192,40,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35458 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35459 : Route 9 := (fun mask => (mask,id))

def c35459 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35459 : Upper (D 7) (R 7) [34,192,40,257,68] 13 := by
  apply FastRouting.sound _ _ [34,192,40,257,68] 13 (by decide) (choices 1) [1,2,16,128] r35459 c35459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20556
  · exact u20557
  · exact u20558
  · exact u20559

#print axioms u35459
end Delivery.IrregularNine14.P07
