import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0335
import IrregularNine14P06C0336

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r35940 : Route 9 := (fun mask => (mask,id))

def c35940 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35940 : Upper (D 6) (R 6) [34,68,40,384,5] 13 := by
  apply FastRouting.sound _ _ [34,68,40,384,5] 13 (by decide) (choices 1) [1,2,16,64] r35940 c35940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20120
  · exact u20121
  · exact u20122
  · exact u20123

def b35941 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 35 70 44 392 22 113 81 209 337), lower := (rows 35 70 44 392 22 32 64 128 256), losses := [] }

theorem u35941 : Upper (D 6) (R 6) [34,68,40,384,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35941 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35942 : Route 9 := (fun mask => (mask,id))

def c35942 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35942 : Upper (D 6) (R 6) [34,68,40,384,65] 13 := by
  apply FastRouting.sound _ _ [34,68,40,384,65] 13 (by decide) (choices 1) [1,2,4,16] r35942 c35942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20124
  · exact u20125
  · exact u20126
  · exact u20127

def b35943 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 70 44 392 82 53 85 149 277), lower := (rows 35 70 44 392 82 32 64 128 256), losses := [] }

theorem u35943 : Upper (D 6) (R 6) [34,68,40,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35943 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35944 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 35 70 44 392 84 51 83 147 275), lower := (rows 35 70 44 392 84 32 64 128 256), losses := [] }

theorem u35944 : Upper (D 6) (R 6) [34,68,40,384,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35944 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35945 : PairBound 9 := { available := 368, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 133 11 28 368 368 496 368), lower := (rows 35 70 133 11 28 32 64 128 256), losses := [] }

theorem u35945 : Upper (D 6) (R 6) [34,68,129,3,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35945 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35946 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 133 11 52 376 344 472 344), lower := (rows 35 70 133 11 52 32 64 128 256), losses := [] }

theorem u35946 : Upper (D 6) (R 6) [34,68,129,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35946 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35947 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 70 133 11 56 372 340 468 340), lower := (rows 35 70 133 11 56 32 64 128 256), losses := [] }

theorem u35947 : Upper (D 6) (R 6) [34,68,129,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35948 : PairBound 9 := { available := 308, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 133 11 88 308 372 436 308), lower := (rows 35 70 133 11 88 32 64 128 256), losses := [] }

theorem u35948 : Upper (D 6) (R 6) [34,68,129,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35948 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35949 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 133 11 112 316 348 412 284), lower := (rows 35 70 133 11 112 32 64 128 256), losses := [] }

theorem u35949 : Upper (D 6) (R 6) [34,68,129,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35949 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35950 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 133 11 276 120 120 248 376), lower := (rows 35 70 133 11 276 32 64 128 256), losses := [] }

theorem u35950 : Upper (D 6) (R 6) [34,68,129,3,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35950 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35951 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 133 11 280 116 116 244 372), lower := (rows 35 70 133 11 280 32 64 128 256), losses := [] }

theorem u35951 : Upper (D 6) (R 6) [34,68,129,3,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35952 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 133 11 304 124 92 220 348), lower := (rows 35 70 133 11 304 32 64 128 256), losses := [] }

theorem u35952 : Upper (D 6) (R 6) [34,68,129,3,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35952 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35953 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 133 11 336 60 124 188 316), lower := (rows 35 70 133 11 336 32 64 128 256), losses := [] }

theorem u35953 : Upper (D 6) (R 6) [34,68,129,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35953 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35954 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 70 133 13 26 368 368 496 368), lower := (rows 35 70 133 13 26 32 64 128 256), losses := [] }

theorem u35954 : Upper (D 6) (R 6) [34,68,129,5,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35954 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35955 : PairBound 9 := { available := 338, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 70 133 13 56 370 338 466 338), lower := (rows 35 70 133 13 56 32 64 128 256), losses := [] }

theorem u35955 : Upper (D 6) (R 6) [34,68,129,5,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35955 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35956 : PairBound 9 := { available := 306, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 70 133 13 88 306 370 434 306), lower := (rows 35 70 133 13 88 32 64 128 256), losses := [] }

theorem u35956 : Upper (D 6) (R 6) [34,68,129,5,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35957 : PairBound 9 := { available := 282, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 70 133 13 112 314 346 410 282), lower := (rows 35 70 133 13 112 32 64 128 256), losses := [] }

theorem u35957 : Upper (D 6) (R 6) [34,68,129,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35957 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35958 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 70 133 13 274 120 120 248 376), lower := (rows 35 70 133 13 274 32 64 128 256), losses := [] }

theorem u35958 : Upper (D 6) (R 6) [34,68,129,5,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35958 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35959 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 70 133 13 280 114 114 242 370), lower := (rows 35 70 133 13 280 32 64 128 256), losses := [] }

theorem u35959 : Upper (D 6) (R 6) [34,68,129,5,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35959 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35960 : PairBound 9 := { available := 90, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 70 133 13 304 122 90 218 346), lower := (rows 35 70 133 13 304 32 64 128 256), losses := [] }

theorem u35960 : Upper (D 6) (R 6) [34,68,129,5,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35960 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35961 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 70 133 13 336 58 122 186 314), lower := (rows 35 70 133 13 336 32 64 128 256), losses := [] }

theorem u35961 : Upper (D 6) (R 6) [34,68,129,5,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35961 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35962 : PairBound 9 := { available := 368, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 70 133 14 25 368 368 496 368), lower := (rows 35 70 133 14 25 32 64 128 256), losses := [] }

theorem u35962 : Upper (D 6) (R 6) [34,68,129,6,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35962 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35963 : PairBound 9 := { available := 337, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 70 133 14 56 369 337 465 337), lower := (rows 35 70 133 14 56 32 64 128 256), losses := [] }

theorem u35963 : Upper (D 6) (R 6) [34,68,129,6,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35963 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35964 : PairBound 9 := { available := 312, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 70 133 14 81 312 376 440 312), lower := (rows 35 70 133 14 81 32 64 128 256), losses := [] }

theorem u35964 : Upper (D 6) (R 6) [34,68,129,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35964 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35965 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 70 133 14 88 305 369 433 305), lower := (rows 35 70 133 14 88 32 64 128 256), losses := [] }

theorem u35965 : Upper (D 6) (R 6) [34,68,129,6,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35965 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35966 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 70 133 14 112 313 345 409 281), lower := (rows 35 70 133 14 112 32 64 128 256), losses := [] }

theorem u35966 : Upper (D 6) (R 6) [34,68,129,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35966 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35967 : PairBound 9 := { available := 120, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 70 133 14 273 120 120 248 376), lower := (rows 35 70 133 14 273 32 64 128 256), losses := [] }

theorem u35967 : Upper (D 6) (R 6) [34,68,129,6,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35967 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35968 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 70 133 14 280 113 113 241 369), lower := (rows 35 70 133 14 280 32 64 128 256), losses := [] }

theorem u35968 : Upper (D 6) (R 6) [34,68,129,6,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35968 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35969 : PairBound 9 := { available := 89, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 70 133 14 304 121 89 217 345), lower := (rows 35 70 133 14 304 32 64 128 256), losses := [] }

theorem u35969 : Upper (D 6) (R 6) [34,68,129,6,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35969 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35970 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 70 133 14 336 57 121 185 313), lower := (rows 35 70 133 14 336 32 64 128 256), losses := [] }

theorem u35970 : Upper (D 6) (R 6) [34,68,129,6,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35970 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35971 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 133 25 26 356 356 484 356), lower := (rows 35 70 133 25 26 32 64 128 256), losses := [] }

theorem u35971 : Upper (D 6) (R 6) [34,68,129,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35971 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35972 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 70 133 25 28 354 354 482 354), lower := (rows 35 70 133 25 28 32 64 128 256), losses := [] }

theorem u35972 : Upper (D 6) (R 6) [34,68,129,17,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35972 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35973 : PairBound 9 := { available := 332, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 70 133 25 50 364 332 460 332), lower := (rows 35 70 133 25 50 32 64 128 256), losses := [] }

theorem u35973 : Upper (D 6) (R 6) [34,68,129,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35973 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35974 : Route 9 := (fun mask => (mask,id))

def c35974 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35974 : Upper (D 6) (R 6) [34,68,129,17,36] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,36] 13 (by decide) (choices 1) [2,8,64,256] r35974 c35974
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20128
  · exact u20129
  · exact u20130
  · exact u20131

def b35975 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 70 133 25 56 358 326 454 326), lower := (rows 35 70 133 25 56 32 64 128 256), losses := [] }

theorem u35975 : Upper (D 6) (R 6) [34,68,129,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35975 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35976 : PairBound 9 := { available := 300, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 70 133 25 82 300 364 428 300), lower := (rows 35 70 133 25 82 32 64 128 256), losses := [] }

theorem u35976 : Upper (D 6) (R 6) [34,68,129,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35976 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35977 : PairBound 9 := { available := 298, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 35 70 133 25 84 298 362 426 298), lower := (rows 35 70 133 25 84 32 64 128 256), losses := [] }

theorem u35977 : Upper (D 6) (R 6) [34,68,129,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35977 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35978 : PairBound 9 := { available := 294, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 2, region := 354, targets := 1 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 35 70 133 25 88 294 358 422 294), lower := (rows 35 70 133 25 88 32 64 128 256), losses := [] }

theorem u35978 : Upper (D 6) (R 6) [34,68,129,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35979 : Route 9 := (fun mask => (mask,id))

def c35979 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35979 : Upper (D 6) (R 6) [34,68,129,17,96] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,96] 13 (by decide) (choices 1) [2,4,8,256] r35979 c35979
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20132
  · exact u20133
  · exact u20134
  · exact u20135

def r35980 : Route 9 := (fun mask => (mask,id))

def c35980 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35980 : Upper (D 6) (R 6) [34,68,129,17,258] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,258] 13 (by decide) (choices 1) [4,8,64] r35980 c35980
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20136
  · exact u20137
  · exact u20138

def r35981 : Route 9 := (fun mask => (mask,id))

def c35981 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35981 : Upper (D 6) (R 6) [34,68,129,17,260] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,260] 13 (by decide) (choices 1) [2,8,64] r35981 c35981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20139
  · exact u20140
  · exact u20141

def r35982 : Route 9 := (fun mask => (mask,id))

def c35982 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35982 : Upper (D 6) (R 6) [34,68,129,17,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,264] 13 (by decide) (choices 1) [2,4,64] r35982 c35982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20142
  · exact u20143
  · exact u20144

def r35983 : Route 9 := (fun mask => (mask,id))

def c35983 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35983 : Upper (D 6) (R 6) [34,68,129,17,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,288] 13 (by decide) (choices 1) [2,4,8,64] r35983 c35983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20145
  · exact u20146
  · exact u20147
  · exact u20148

def r35984 : Route 9 := (fun mask => (mask,id))

def c35984 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35984 : Upper (D 6) (R 6) [34,68,129,17,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,320] 13 (by decide) (choices 1) [2,4,8] r35984 c35984
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20149
  · exact u20150
  · exact u20151

def b35985 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 70 133 26 28 353 353 481 353), lower := (rows 35 70 133 26 28 32 64 128 256), losses := [] }

theorem u35985 : Upper (D 6) (R 6) [34,68,129,18,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35985 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35986 : PairBound 9 := { available := 332, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 70 133 26 49 364 332 460 332), lower := (rows 35 70 133 26 49 32 64 128 256), losses := [] }

theorem u35986 : Upper (D 6) (R 6) [34,68,129,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35986 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35987 : Route 9 := (fun mask => (mask,id))

def c35987 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35987 : Upper (D 6) (R 6) [34,68,129,18,36] 13 := by
  apply FastRouting.sound _ _ [34,68,129,18,36] 13 (by decide) (choices 1) [1,8,64,256] r35987 c35987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20152
  · exact u20153
  · exact u20154
  · exact u20155

def b35988 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 70 133 26 56 357 325 453 325), lower := (rows 35 70 133 26 56 32 64 128 256), losses := [] }

theorem u35988 : Upper (D 6) (R 6) [34,68,129,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35988 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35989 : Route 9 := (fun mask => (mask,id))

def c35989 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35989 : Upper (D 6) (R 6) [34,68,129,18,65] 13 := by
  apply FastRouting.sound _ _ [34,68,129,18,65] 13 (by decide) (choices 1) [4,8,256] r35989 c35989
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20156
  · exact u20157
  · exact u20158

def b35990 : PairBound 9 := { available := 297, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 70 133 26 84 297 361 425 297), lower := (rows 35 70 133 26 84 32 64 128 256), losses := [] }

theorem u35990 : Upper (D 6) (R 6) [34,68,129,18,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35990 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35991 : PairBound 9 := { available := 293, camps := [{ cop := 1, region := 24, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 70 133 26 88 293 357 421 293), lower := (rows 35 70 133 26 88 32 64 128 256), losses := [] }

theorem u35991 : Upper (D 6) (R 6) [34,68,129,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35991 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35992 : Route 9 := (fun mask => (mask,id))

def c35992 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35992 : Upper (D 6) (R 6) [34,68,129,18,96] 13 := by
  apply FastRouting.sound _ _ [34,68,129,18,96] 13 (by decide) (choices 1) [1,4,8,256] r35992 c35992
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20159
  · exact u20160
  · exact u20161
  · exact u20162

def r35993 : Route 9 := (fun mask => (mask,id))

def c35993 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35993 : Upper (D 6) (R 6) [34,68,129,18,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,18,257] 13 (by decide) (choices 1) [4,8,64] r35993 c35993
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20163
  · exact u20164
  · exact u20165

def r35994 : Route 9 := (fun mask => (mask,id))

def c35994 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35994 : Upper (D 6) (R 6) [34,68,129,18,260] 13 := by
  apply FastRouting.sound _ _ [34,68,129,18,260] 13 (by decide) (choices 1) [1,8,64] r35994 c35994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20166
  · exact u20167
  · exact u20168

def r35995 : Route 9 := (fun mask => (mask,id))

def c35995 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35995 : Upper (D 6) (R 6) [34,68,129,18,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,18,264] 13 (by decide) (choices 1) [1,4,64] r35995 c35995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20169
  · exact u20170
  · exact u20171

def r35996 : Route 9 := (fun mask => (mask,id))

def c35996 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35996 : Upper (D 6) (R 6) [34,68,129,18,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,18,288] 13 (by decide) (choices 1) [1,4,8,64] r35996 c35996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20172
  · exact u20173
  · exact u20174
  · exact u20175

def r35997 : Route 9 := (fun mask => (mask,id))

def c35997 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35997 : Upper (D 6) (R 6) [34,68,129,18,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,18,320] 13 (by decide) (choices 1) [1,4,8] r35997 c35997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20176
  · exact u20177
  · exact u20178

def b35998 : PairBound 9 := { available := 330, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 70 133 28 49 362 330 458 330), lower := (rows 35 70 133 28 49 32 64 128 256), losses := [] }

theorem u35998 : Upper (D 6) (R 6) [34,68,129,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35998 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35999 : PairBound 9 := { available := 329, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 70 133 28 50 361 329 457 329), lower := (rows 35 70 133 28 50 32 64 128 256), losses := [] }

theorem u35999 : Upper (D 6) (R 6) [34,68,129,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35999 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u35999
end Delivery.IrregularNine14.P06
