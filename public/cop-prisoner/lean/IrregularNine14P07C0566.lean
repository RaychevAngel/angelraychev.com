import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0304

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r33960 : Route 9 := (fun mask => (mask,id))

def c33960 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33960 : Upper (D 7) (R 7) [34,65,24,160,257] 13 := by
  apply FastRouting.sound _ _ [34,65,24,160,257] 13 (by decide) (choices 1) [2,4,64,128] r33960 c33960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18250
  · exact u18251
  · exact u18252
  · exact u18253

def r33961 : Route 9 := (fun mask => (mask,id))

def c33961 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33961 : Upper (D 7) (R 7) [34,65,24,160,258] 13 := by
  apply FastRouting.sound _ _ [34,65,24,160,258] 13 (by decide) (choices 1) [1,4,64,128] r33961 c33961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18254
  · exact u18255
  · exact u18256
  · exact u18257

def r33962 : Route 9 := (fun mask => (mask,id))

def c33962 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33962 : Upper (D 7) (R 7) [34,65,24,160,260] 13 := by
  apply FastRouting.sound _ _ [34,65,24,160,260] 13 (by decide) (choices 1) [1,2,64,128] r33962 c33962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18258
  · exact u18259
  · exact u18260
  · exact u18261

def r33963 : Route 9 := (fun mask => (mask,id))

def c33963 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33963 : Upper (D 7) (R 7) [34,65,24,160,320] 13 := by
  apply FastRouting.sound _ _ [34,65,24,160,320] 13 (by decide) (choices 1) [1,2,4,128] r33963 c33963
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18262
  · exact u18263
  · exact u18264
  · exact u18265

def r33964 : Route 9 := (fun mask => (mask,id))

def c33964 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33964 : Upper (D 7) (R 7) [34,65,24,160,384] 13 := by
  apply FastRouting.sound _ _ [34,65,24,160,384] 13 (by decide) (choices 1) [1,2,4,64] r33964 c33964
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18266
  · exact u18267
  · exact u18268
  · exact u18269

def b33965 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 76 146 440 472 408 408), lower := (rows 35 67 37 76 146 32 64 128 256), losses := [] }

theorem u33965 : Upper (D 7) (R 7) [34,65,33,68,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33965 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33966 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 76 152 434 466 402 402), lower := (rows 35 67 37 76 152 32 64 128 256), losses := [] }

theorem u33966 : Upper (D 7) (R 7) [34,65,33,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33966 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33967 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 76 274 184 216 152 408), lower := (rows 35 67 37 76 274 32 64 128 256), losses := [] }

theorem u33967 : Upper (D 7) (R 7) [34,65,33,68,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33967 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33968 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 76 280 178 210 146 402), lower := (rows 35 67 37 76 280 32 64 128 256), losses := [] }

theorem u33968 : Upper (D 7) (R 7) [34,65,33,68,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33968 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33969 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 76 400 186 218 154 410), lower := (rows 35 67 37 76 400 32 64 128 256), losses := [] }

theorem u33969 : Upper (D 7) (R 7) [34,65,33,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33969 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33970 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 88 146 428 460 396 396), lower := (rows 35 67 37 88 146 32 64 128 256), losses := [] }

theorem u33970 : Upper (D 7) (R 7) [34,65,33,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33970 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33971 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 88 148 426 458 394 394), lower := (rows 35 67 37 88 148 32 64 128 256), losses := [] }

theorem u33971 : Upper (D 7) (R 7) [34,65,33,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33971 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33972 : PairBound 9 := { available := 390, camps := [{ cop := 2, region := 474, targets := 32 },{ cop := 0, region := 4, targets := 2 }], pairs := [(1,5),(2,1),(3,5),(4,5)], upper := (rows 35 67 37 88 152 422 454 390 390), lower := (rows 35 67 37 88 152 32 64 128 256), losses := [] }

theorem u33972 : Upper (D 7) (R 7) [34,65,33,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33972 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33973 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 88 274 172 204 140 396), lower := (rows 35 67 37 88 274 32 64 128 256), losses := [] }

theorem u33973 : Upper (D 7) (R 7) [34,65,33,80,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33974 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 88 276 170 202 138 394), lower := (rows 35 67 37 88 276 32 64 128 256), losses := [] }

theorem u33974 : Upper (D 7) (R 7) [34,65,33,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33974 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33975 : PairBound 9 := { available := 134, camps := [{ cop := 2, region := 474, targets := 32 },{ cop := 0, region := 4, targets := 2 }], pairs := [(1,5),(2,1),(3,5),(4,5)], upper := (rows 35 67 37 88 280 166 198 134 390), lower := (rows 35 67 37 88 280 32 64 128 256), losses := [] }

theorem u33975 : Upper (D 7) (R 7) [34,65,33,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33976 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 88 400 174 206 142 398), lower := (rows 35 67 37 88 400 32 64 128 256), losses := [] }

theorem u33976 : Upper (D 7) (R 7) [34,65,33,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33976 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33977 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 138 148 376 344 472 344), lower := (rows 35 67 37 138 148 32 64 128 256), losses := [] }

theorem u33977 : Upper (D 7) (R 7) [34,65,33,130,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33977 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33978 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 138 208 316 348 412 284), lower := (rows 35 67 37 138 208 32 64 128 256), losses := [] }

theorem u33978 : Upper (D 7) (R 7) [34,65,33,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33978 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33979 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 138 276 248 216 216 472), lower := (rows 35 67 37 138 276 32 64 128 256), losses := [] }

theorem u33979 : Upper (D 7) (R 7) [34,65,33,130,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33980 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 138 280 244 212 212 468), lower := (rows 35 67 37 138 280 32 64 128 256), losses := [] }

theorem u33980 : Upper (D 7) (R 7) [34,65,33,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33980 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33981 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 138 336 188 220 156 412), lower := (rows 35 67 37 138 336 32 64 128 256), losses := [] }

theorem u33981 : Upper (D 7) (R 7) [34,65,33,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33981 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33982 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 138 400 124 92 220 348), lower := (rows 35 67 37 138 400 32 64 128 256), losses := [] }

theorem u33982 : Upper (D 7) (R 7) [34,65,33,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33982 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33983 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 140 208 314 346 410 282), lower := (rows 35 67 37 140 208 32 64 128 256), losses := [] }

theorem u33983 : Upper (D 7) (R 7) [34,65,33,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33983 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33984 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 140 274 248 216 216 472), lower := (rows 35 67 37 140 274 32 64 128 256), losses := [] }

theorem u33984 : Upper (D 7) (R 7) [34,65,33,132,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33984 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33985 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 140 280 242 210 210 466), lower := (rows 35 67 37 140 280 32 64 128 256), losses := [] }

theorem u33985 : Upper (D 7) (R 7) [34,65,33,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33985 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33986 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 140 336 186 218 154 410), lower := (rows 35 67 37 140 336 32 64 128 256), losses := [] }

theorem u33986 : Upper (D 7) (R 7) [34,65,33,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33987 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 140 400 122 90 218 346), lower := (rows 35 67 37 140 400 32 64 128 256), losses := [] }

theorem u33987 : Upper (D 7) (R 7) [34,65,33,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33988 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 152 274 236 204 204 460), lower := (rows 35 67 37 152 274 32 64 128 256), losses := [] }

theorem u33988 : Upper (D 7) (R 7) [34,65,33,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33988 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33989 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 152 276 234 202 202 458), lower := (rows 35 67 37 152 276 32 64 128 256), losses := [] }

theorem u33989 : Upper (D 7) (R 7) [34,65,33,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33990 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 152 280 230 198 198 454), lower := (rows 35 67 37 152 280 32 64 128 256), losses := [] }

theorem u33990 : Upper (D 7) (R 7) [34,65,33,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33990 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33991 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 152 336 174 206 142 398), lower := (rows 35 67 37 152 336 32 64 128 256), losses := [] }

theorem u33991 : Upper (D 7) (R 7) [34,65,33,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33992 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 200 274 188 220 156 412), lower := (rows 35 67 37 200 274 32 64 128 256), losses := [] }

theorem u33992 : Upper (D 7) (R 7) [34,65,33,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33993 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 200 276 186 218 154 410), lower := (rows 35 67 37 200 276 32 64 128 256), losses := [] }

theorem u33993 : Upper (D 7) (R 7) [34,65,33,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33994 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 200 280 182 214 150 406), lower := (rows 35 67 37 200 280 32 64 128 256), losses := [] }

theorem u33994 : Upper (D 7) (R 7) [34,65,33,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33994 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33995 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 200 400 62 94 158 286), lower := (rows 35 67 37 200 400 32 64 128 256), losses := [] }

theorem u33995 : Upper (D 7) (R 7) [34,65,33,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33995 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33996 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 76 145 440 472 408 408), lower := (rows 35 67 38 76 145 32 64 128 256), losses := [] }

theorem u33996 : Upper (D 7) (R 7) [34,65,34,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33996 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33997 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 76 152 433 465 401 401), lower := (rows 35 67 38 76 152 32 64 128 256), losses := [] }

theorem u33997 : Upper (D 7) (R 7) [34,65,34,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33997 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33998 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 76 273 184 216 152 408), lower := (rows 35 67 38 76 273 32 64 128 256), losses := [] }

theorem u33998 : Upper (D 7) (R 7) [34,65,34,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33998 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33999 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 76 280 177 209 145 401), lower := (rows 35 67 38 76 280 32 64 128 256), losses := [] }

theorem u33999 : Upper (D 7) (R 7) [34,65,34,68,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33999 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34000 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 76 400 185 217 153 409), lower := (rows 35 67 38 76 400 32 64 128 256), losses := [] }

theorem u34000 : Upper (D 7) (R 7) [34,65,34,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34000 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34001 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 88 145 428 460 396 396), lower := (rows 35 67 38 88 145 32 64 128 256), losses := [] }

theorem u34001 : Upper (D 7) (R 7) [34,65,34,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34001 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34002 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 88 148 425 457 393 393), lower := (rows 35 67 38 88 148 32 64 128 256), losses := [] }

theorem u34002 : Upper (D 7) (R 7) [34,65,34,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34002 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34003 : PairBound 9 := { available := 389, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 0, region := 4, targets := 1 },{ cop := 0, region := 4, targets := 128 }], pairs := [(0,6),(2,0),(2,6),(2,7)], upper := (rows 35 67 38 88 152 421 453 389 389), lower := (rows 35 67 38 88 152 32 64 128 256), losses := [] }

theorem u34003 : Upper (D 7) (R 7) [34,65,34,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34003 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34004 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 88 273 172 204 140 396), lower := (rows 35 67 38 88 273 32 64 128 256), losses := [] }

theorem u34004 : Upper (D 7) (R 7) [34,65,34,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34004 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34005 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 88 276 169 201 137 393), lower := (rows 35 67 38 88 276 32 64 128 256), losses := [] }

theorem u34005 : Upper (D 7) (R 7) [34,65,34,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34006 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 0, region := 4, targets := 1 },{ cop := 0, region := 4, targets := 128 }], pairs := [(0,6),(2,0),(2,6),(2,7)], upper := (rows 35 67 38 88 280 165 197 133 389), lower := (rows 35 67 38 88 280 32 64 128 256), losses := [] }

theorem u34006 : Upper (D 7) (R 7) [34,65,34,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34006 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34007 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 88 400 173 205 141 397), lower := (rows 35 67 38 88 400 32 64 128 256), losses := [] }

theorem u34007 : Upper (D 7) (R 7) [34,65,34,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34008 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 137 148 376 344 472 344), lower := (rows 35 67 38 137 148 32 64 128 256), losses := [] }

theorem u34008 : Upper (D 7) (R 7) [34,65,34,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34008 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34009 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 137 208 316 348 412 284), lower := (rows 35 67 38 137 208 32 64 128 256), losses := [] }

theorem u34009 : Upper (D 7) (R 7) [34,65,34,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34009 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34010 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 137 276 248 216 216 472), lower := (rows 35 67 38 137 276 32 64 128 256), losses := [] }

theorem u34010 : Upper (D 7) (R 7) [34,65,34,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34010 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34011 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 137 280 244 212 212 468), lower := (rows 35 67 38 137 280 32 64 128 256), losses := [] }

theorem u34011 : Upper (D 7) (R 7) [34,65,34,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34011 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34012 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 137 336 188 220 156 412), lower := (rows 35 67 38 137 336 32 64 128 256), losses := [] }

theorem u34012 : Upper (D 7) (R 7) [34,65,34,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34012 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34013 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 137 400 124 92 220 348), lower := (rows 35 67 38 137 400 32 64 128 256), losses := [] }

theorem u34013 : Upper (D 7) (R 7) [34,65,34,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34013 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34014 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 140 208 313 345 409 281), lower := (rows 35 67 38 140 208 32 64 128 256), losses := [] }

theorem u34014 : Upper (D 7) (R 7) [34,65,34,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34014 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34015 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 140 273 248 216 216 472), lower := (rows 35 67 38 140 273 32 64 128 256), losses := [] }

theorem u34015 : Upper (D 7) (R 7) [34,65,34,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34016 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 140 280 241 209 209 465), lower := (rows 35 67 38 140 280 32 64 128 256), losses := [] }

theorem u34016 : Upper (D 7) (R 7) [34,65,34,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34017 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 140 336 185 217 153 409), lower := (rows 35 67 38 140 336 32 64 128 256), losses := [] }

theorem u34017 : Upper (D 7) (R 7) [34,65,34,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34017 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34018 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 140 400 121 89 217 345), lower := (rows 35 67 38 140 400 32 64 128 256), losses := [] }

theorem u34018 : Upper (D 7) (R 7) [34,65,34,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34018 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34019 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 152 273 236 204 204 460), lower := (rows 35 67 38 152 273 32 64 128 256), losses := [] }

theorem u34019 : Upper (D 7) (R 7) [34,65,34,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34019 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u34019
end Delivery.IrregularNine14.P07
