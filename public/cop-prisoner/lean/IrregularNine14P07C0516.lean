import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0220
import IrregularNine14P07C0221

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r30960 : Route 9 := (fun mask => (mask,id))

def c30960 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30960 : Upper (D 7) (R 7) [6,40,80,320,129] 13 := by
  apply FastRouting.sound _ _ [6,40,80,320,129] 13 (by decide) (choices 1) [1,2,128] r30960 c30960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13202
  · exact u13203
  · exact u13204

def r30961 : Route 9 := (fun mask => (mask,id))

def c30961 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30961 : Upper (D 7) (R 7) [6,40,80,320,130] 13 := by
  apply FastRouting.sound _ _ [6,40,80,320,130] 13 (by decide) (choices 1) [1,128] r30961 c30961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13205
  · exact u13206

def r30962 : Route 9 := (fun mask => (mask,id))

def c30962 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30962 : Upper (D 7) (R 7) [6,40,80,320,160] 13 := by
  apply FastRouting.sound _ _ [6,40,80,320,160] 13 (by decide) (choices 1) [1,2,128] r30962 c30962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13207
  · exact u13208
  · exact u13209

def b30963 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 228, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 7 42 84 392 19 225 225 225 481), lower := (rows 7 42 84 392 19 32 64 128 256), losses := [] }

theorem u30963 : Upper (D 7) (R 7) [6,40,80,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30963 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30964 : Route 9 := (fun mask => (mask,id))

def c30964 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30964 : Upper (D 7) (R 7) [6,40,80,384,33] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384,33] 13 (by decide) (choices 1) [1,2,64,128] r30964 c30964
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13210
  · exact u13211
  · exact u13212
  · exact u13213

def b30965 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 197, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 84 392 50 225 193 193 449), lower := (rows 7 42 84 392 50 32 64 128 256), losses := [] }

theorem u30965 : Upper (D 7) (R 7) [6,40,80,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30965 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30966 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 7 42 84 392 81 163 227 163 419), lower := (rows 7 42 84 392 81 32 64 128 256), losses := [] }

theorem u30966 : Upper (D 7) (R 7) [6,40,80,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30966 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30967 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 84 392 82 161 225 161 417), lower := (rows 7 42 84 392 82 32 64 128 256), losses := [] }

theorem u30967 : Upper (D 7) (R 7) [6,40,80,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30967 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30968 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 7 42 84 392 112 163 195 131 387), lower := (rows 7 42 84 392 112 32 64 128 256), losses := [] }

theorem u30968 : Upper (D 7) (R 7) [6,40,80,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30968 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30969 : Route 9 := (fun mask => (mask,id))

def c30969 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30969 : Upper (D 7) (R 7) [6,40,80,384,129] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384,129] 13 (by decide) (choices 1) [1,2,64] r30969 c30969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13214
  · exact u13215
  · exact u13216

def r30970 : Route 9 := (fun mask => (mask,id))

def c30970 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30970 : Upper (D 7) (R 7) [6,40,80,384,130] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384,130] 13 (by decide) (choices 1) [1,64] r30970 c30970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13217
  · exact u13218

def r30971 : Route 9 := (fun mask => (mask,id))

def c30971 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30971 : Upper (D 7) (R 7) [6,40,80,384,160] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384,160] 13 (by decide) (choices 1) [1,2,64] r30971 c30971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13219
  · exact u13220
  · exact u13221

def b30972 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 7 42 84 392 208 35 99 163 291), lower := (rows 7 42 84 392 208 32 64 128 256), losses := [] }

theorem u30972 : Upper (D 7) (R 7) [6,40,80,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30972 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30973 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 27, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 42 100 25 19 480 448 448 448), lower := (rows 7 42 100 25 19 32 64 128 256), losses := [] }

theorem u30973 : Upper (D 7) (R 7) [6,40,96,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30974 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 27, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 100 25 81 418 450 386 386), lower := (rows 7 42 100 25 81 32 64 128 256), losses := [] }

theorem u30974 : Upper (D 7) (R 7) [6,40,96,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30974 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30975 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 27, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 100 25 82 417 449 385 385), lower := (rows 7 42 100 25 82 32 64 128 256), losses := [] }

theorem u30975 : Upper (D 7) (R 7) [6,40,96,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30976 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 7 42 100 25 145 482 450 450 450), lower := (rows 7 42 100 25 145 32 64 128 256), losses := [] }

theorem u30976 : Upper (D 7) (R 7) [6,40,96,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30976 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30977 : Route 9 := (fun mask => (mask,id))

def c30977 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u30977 : Upper (D 7) (R 7) [6,40,96,17,130] 13 := by
  apply FastRouting.sound _ _ [6,40,96,17,130] 13 (by decide) (choices 1) [1,64,128,256] r30977 c30977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13222
  · exact u13223
  · exact u13224
  · exact u13225

def r30978 : Route 9 := (fun mask => (mask,id))

def c30978 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30978 : Upper (D 7) (R 7) [6,40,96,17,192] 13 := by
  apply FastRouting.sound _ _ [6,40,96,17,192] 13 (by decide) (choices 1) [1,2,128,256] r30978 c30978
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13226
  · exact u13227
  · exact u13228
  · exact u13229

def b30979 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 7 42 100 25 273 226 194 194 450), lower := (rows 7 42 100 25 273 32 64 128 256), losses := [] }

theorem u30979 : Upper (D 7) (R 7) [6,40,96,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30980 : Route 9 := (fun mask => (mask,id))

def c30980 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30980 : Upper (D 7) (R 7) [6,40,96,17,258] 13 := by
  apply FastRouting.sound _ _ [6,40,96,17,258] 13 (by decide) (choices 1) [1,64,128] r30980 c30980
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13230
  · exact u13231
  · exact u13232

def r30981 : Route 9 := (fun mask => (mask,id))

def c30981 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30981 : Upper (D 7) (R 7) [6,40,96,17,320] 13 := by
  apply FastRouting.sound _ _ [6,40,96,17,320] 13 (by decide) (choices 1) [1,2,128] r30981 c30981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13233
  · exact u13234
  · exact u13235

def r30982 : Route 9 := (fun mask => (mask,id))

def c30982 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30982 : Upper (D 7) (R 7) [6,40,96,17,384] 13 := by
  apply FastRouting.sound _ _ [6,40,96,17,384] 13 (by decide) (choices 1) [1,2,64,128] r30982 c30982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13236
  · exact u13237
  · exact u13238
  · exact u13239

def b30983 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 27, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 100 88 19 417 449 385 385), lower := (rows 7 42 100 88 19 32 64 128 256), losses := [] }

theorem u30983 : Upper (D 7) (R 7) [6,40,96,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30983 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30984 : Route 9 := (fun mask => (mask,id))

def c30984 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30984 : Upper (D 7) (R 7) [6,40,96,80,129] 13 := by
  apply FastRouting.sound _ _ [6,40,96,80,129] 13 (by decide) (choices 1) [1,2,128,256] r30984 c30984
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13240
  · exact u13241
  · exact u13242
  · exact u13243

def b30985 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 484, targets := 2 },{ cop := 0, region := 400, targets := 64 }], pairs := [(2,1),(3,5),(4,5),(4,6)], upper := (rows 7 42 100 88 146 417 449 385 385), lower := (rows 7 42 100 88 146 32 64 128 256), losses := [] }

theorem u30985 : Upper (D 7) (R 7) [6,40,96,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30985 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30986 : Route 9 := (fun mask => (mask,id))

def c30986 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30986 : Upper (D 7) (R 7) [6,40,96,80,257] 13 := by
  apply FastRouting.sound _ _ [6,40,96,80,257] 13 (by decide) (choices 1) [1,2,128] r30986 c30986
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13244
  · exact u13245
  · exact u13246

def b30987 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 228, targets := 2 },{ cop := 0, region := 400, targets := 64 }], pairs := [(2,1),(3,5),(4,5),(4,6)], upper := (rows 7 42 100 88 274 161 193 129 385), lower := (rows 7 42 100 88 274 32 64 128 256), losses := [] }

theorem u30987 : Upper (D 7) (R 7) [6,40,96,80,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30988 : Route 9 := (fun mask => (mask,id))

def c30988 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30988 : Upper (D 7) (R 7) [6,40,96,80,384] 13 := by
  apply FastRouting.sound _ _ [6,40,96,80,384] 13 (by decide) (choices 1) [1,2,128] r30988 c30988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13247
  · exact u13248
  · exact u13249

def b30989 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 7 42 100 137 19 496 464 464 464), lower := (rows 7 42 100 137 19 32 64 128 256), losses := [] }

theorem u30989 : Upper (D 7) (R 7) [6,40,96,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30990 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(3,5),(3,6),(4,5)], upper := (rows 7 42 100 137 81 434 466 402 402), lower := (rows 7 42 100 137 81 32 64 128 256), losses := [] }

theorem u30990 : Upper (D 7) (R 7) [6,40,96,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30990 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30991 : Route 9 := (fun mask => (mask,id))

def c30991 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u30991 : Upper (D 7) (R 7) [6,40,96,129,66] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,66] 13 (by decide) (choices 1) [1,16,128,256] r30991 c30991
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13250
  · exact u13251
  · exact u13252
  · exact u13253

def b30992 : PairBound 9 := { available := 338, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 7 42 100 137 145 370 338 466 338), lower := (rows 7 42 100 137 145 32 64 128 256), losses := [] }

theorem u30992 : Upper (D 7) (R 7) [6,40,96,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30993 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 357, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 137 146 369 337 465 337), lower := (rows 7 42 100 137 146 32 64 128 256), losses := [] }

theorem u30993 : Upper (D 7) (R 7) [6,40,96,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30994 : Route 9 := (fun mask => (mask,id))

def c30994 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30994 : Upper (D 7) (R 7) [6,40,96,129,192] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,192] 13 (by decide) (choices 1) [1,2,16,256] r30994 c30994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13254
  · exact u13255
  · exact u13256
  · exact u13257

def r30995 : Route 9 := (fun mask => (mask,id))

def c30995 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30995 : Upper (D 7) (R 7) [6,40,96,129,257] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,257] 13 (by decide) (choices 1) [2,16,64,128] r30995 c30995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13258
  · exact u13259
  · exact u13260
  · exact u13261

def r30996 : Route 9 := (fun mask => (mask,id))

def c30996 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30996 : Upper (D 7) (R 7) [6,40,96,129,258] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,258] 13 (by decide) (choices 1) [1,16,64,128] r30996 c30996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13262
  · exact u13263
  · exact u13264
  · exact u13265

def r30997 : Route 9 := (fun mask => (mask,id))

def c30997 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30997 : Upper (D 7) (R 7) [6,40,96,129,320] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,320] 13 (by decide) (choices 1) [1,2,16,128] r30997 c30997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13266
  · exact u13267
  · exact u13268
  · exact u13269

def r30998 : Route 9 := (fun mask => (mask,id))

def c30998 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30998 : Upper (D 7) (R 7) [6,40,96,129,384] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,384] 13 (by decide) (choices 1) [1,2,16,64] r30998 c30998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13270
  · exact u13271
  · exact u13272
  · exact u13273

def b30999 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 7 42 100 152 19 481 449 449 449), lower := (rows 7 42 100 152 19 32 64 128 256), losses := [] }

theorem u30999 : Upper (D 7) (R 7) [6,40,96,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30999 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31000 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(3,5),(3,6),(4,5)], upper := (rows 7 42 100 152 81 419 451 387 387), lower := (rows 7 42 100 152 81 32 64 128 256), losses := [] }

theorem u31000 : Upper (D 7) (R 7) [6,40,96,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31000 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31001 : Route 9 := (fun mask => (mask,id))

def c31001 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u31001 : Upper (D 7) (R 7) [6,40,96,144,66] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144,66] 13 (by decide) (choices 1) [1,128,256] r31001 c31001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13274
  · exact u13275
  · exact u13276

def b31002 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 42 100 152 145 355 323 451 323), lower := (rows 7 42 100 152 145 32 64 128 256), losses := [] }

theorem u31002 : Upper (D 7) (R 7) [6,40,96,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31002 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31003 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 42 100 152 146 353 321 449 321), lower := (rows 7 42 100 152 146 32 64 128 256), losses := [] }

theorem u31003 : Upper (D 7) (R 7) [6,40,96,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31003 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31004 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 42 100 152 208 291 323 387 259), lower := (rows 7 42 100 152 208 32 64 128 256), losses := [] }

theorem u31004 : Upper (D 7) (R 7) [6,40,96,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31004 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31005 : Route 9 := (fun mask => (mask,id))

def c31005 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31005 : Upper (D 7) (R 7) [6,40,96,144,257] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144,257] 13 (by decide) (choices 1) [1,2,64,128] r31005 c31005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13277
  · exact u13278
  · exact u13279
  · exact u13280

def r31006 : Route 9 := (fun mask => (mask,id))

def c31006 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31006 : Upper (D 7) (R 7) [6,40,96,144,258] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144,258] 13 (by decide) (choices 1) [1,64,128] r31006 c31006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13281
  · exact u13282
  · exact u13283

def r31007 : Route 9 := (fun mask => (mask,id))

def c31007 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31007 : Upper (D 7) (R 7) [6,40,96,144,320] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144,320] 13 (by decide) (choices 1) [1,2,128] r31007 c31007
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13284
  · exact u13285
  · exact u13286

def b31008 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 42 100 152 400 99 67 195 323), lower := (rows 7 42 100 152 400 32 64 128 256), losses := [] }

theorem u31008 : Upper (D 7) (R 7) [6,40,96,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31008 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31009 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(4,5)], upper := (rows 7 42 100 200 19 433 465 401 401), lower := (rows 7 42 100 200 19 32 64 128 256), losses := [] }

theorem u31009 : Upper (D 7) (R 7) [6,40,96,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31009 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31010 : Route 9 := (fun mask => (mask,id))

def c31010 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31010 : Upper (D 7) (R 7) [6,40,96,192,129] 13 := by
  apply FastRouting.sound _ _ [6,40,96,192,129] 13 (by decide) (choices 1) [1,2,16,256] r31010 c31010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13287
  · exact u13288
  · exact u13289
  · exact u13290

def b31011 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 357, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 200 146 305 337 401 273), lower := (rows 7 42 100 200 146 32 64 128 256), losses := [] }

theorem u31011 : Upper (D 7) (R 7) [6,40,96,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31011 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31012 : Route 9 := (fun mask => (mask,id))

def c31012 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31012 : Upper (D 7) (R 7) [6,40,96,192,257] 13 := by
  apply FastRouting.sound _ _ [6,40,96,192,257] 13 (by decide) (choices 1) [1,2,16,128] r31012 c31012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13291
  · exact u13292
  · exact u13293
  · exact u13294

def r31013 : Route 9 := (fun mask => (mask,id))

def c31013 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31013 : Upper (D 7) (R 7) [6,40,96,192,258] 13 := by
  apply FastRouting.sound _ _ [6,40,96,192,258] 13 (by decide) (choices 1) [1,16,128] r31013 c31013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13295
  · exact u13296
  · exact u13297

def r31014 : Route 9 := (fun mask => (mask,id))

def c31014 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31014 : Upper (D 7) (R 7) [6,40,96,192,384] 13 := by
  apply FastRouting.sound _ _ [6,40,96,192,384] 13 (by decide) (choices 1) [1,2,16] r31014 c31014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13298
  · exact u13299
  · exact u13300

def b31015 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 7 42 100 265 19 240 208 208 464), lower := (rows 7 42 100 265 19 32 64 128 256), losses := [] }

theorem u31015 : Upper (D 7) (R 7) [6,40,96,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31016 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(3,5),(3,6),(4,5)], upper := (rows 7 42 100 265 81 178 210 146 402), lower := (rows 7 42 100 265 81 32 64 128 256), losses := [] }

theorem u31016 : Upper (D 7) (R 7) [6,40,96,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31017 : Route 9 := (fun mask => (mask,id))

def c31017 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31017 : Upper (D 7) (R 7) [6,40,96,257,66] 13 := by
  apply FastRouting.sound _ _ [6,40,96,257,66] 13 (by decide) (choices 1) [1,16,128] r31017 c31017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13301
  · exact u13302
  · exact u13303

def r31018 : Route 9 := (fun mask => (mask,id))

def c31018 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31018 : Upper (D 7) (R 7) [6,40,96,257,129] 13 := by
  apply FastRouting.sound _ _ [6,40,96,257,129] 13 (by decide) (choices 1) [2,16,64,128] r31018 c31018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13304
  · exact u13305
  · exact u13306
  · exact u13307

def r31019 : Route 9 := (fun mask => (mask,id))

def c31019 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31019 : Upper (D 7) (R 7) [6,40,96,257,130] 13 := by
  apply FastRouting.sound _ _ [6,40,96,257,130] 13 (by decide) (choices 1) [1,16,64,128] r31019 c31019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13308
  · exact u13309
  · exact u13310
  · exact u13311

#print axioms u31019
end Delivery.IrregularNine14.P07
