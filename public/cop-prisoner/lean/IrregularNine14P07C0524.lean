import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0233
import IrregularNine14P07C0234
import IrregularNine14P07C0235

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r31440 : Route 9 := (fun mask => (mask,id))

def c31440 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31440 : Upper (D 7) (R 7) [6,96,129,18,257] 13 := by
  apply FastRouting.sound _ _ [6,96,129,18,257] 13 (by decide) (choices 1) [8,64,128] r31440 c31440
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14027
  · exact u14028
  · exact u14029

def r31441 : Route 9 := (fun mask => (mask,id))

def c31441 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31441 : Upper (D 7) (R 7) [6,96,129,18,264] 13 := by
  apply FastRouting.sound _ _ [6,96,129,18,264] 13 (by decide) (choices 1) [1,64,128] r31441 c31441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14030
  · exact u14031
  · exact u14032

def r31442 : Route 9 := (fun mask => (mask,id))

def c31442 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31442 : Upper (D 7) (R 7) [6,96,129,18,288] 13 := by
  apply FastRouting.sound _ _ [6,96,129,18,288] 13 (by decide) (choices 1) [1,8,64,128] r31442 c31442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14033
  · exact u14034
  · exact u14035
  · exact u14036

def r31443 : Route 9 := (fun mask => (mask,id))

def c31443 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31443 : Upper (D 7) (R 7) [6,96,129,18,384] 13 := by
  apply FastRouting.sound _ _ [6,96,129,18,384] 13 (by decide) (choices 1) [1,8,64] r31443 c31443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14037
  · exact u14038
  · exact u14039

def b31444 : PairBound 9 := { available := 408, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 7 98 133 41 82 440 472 408 408), lower := (rows 7 98 133 41 82 32 64 128 256), losses := [] }

theorem u31444 : Upper (D 7) (R 7) [6,96,129,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31444 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31445 : Route 9 := (fun mask => (mask,id))

def c31445 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u31445 : Upper (D 7) (R 7) [6,96,129,33,72] 13 := by
  apply FastRouting.sound _ _ [6,96,129,33,72] 13 (by decide) (choices 1) [2,16,128,256] r31445 c31445
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14040
  · exact u14041
  · exact u14042
  · exact u14043

def b31446 : PairBound 9 := { available := 344, camps := [{ cop := 4, region := 5, targets := 96 }], pairs := [(0,5),(0,6),(2,5),(2,6)], upper := (rows 7 98 133 41 146 376 344 472 344), lower := (rows 7 98 133 41 146 32 64 128 256), losses := [] }

theorem u31446 : Upper (D 7) (R 7) [6,96,129,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31446 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31447 : Route 9 := (fun mask => (mask,id))

def c31447 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u31447 : Upper (D 7) (R 7) [6,96,129,33,136] 13 := by
  apply FastRouting.sound _ _ [6,96,129,33,136] 13 (by decide) (choices 1) [2,16,64,256] r31447 c31447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14044
  · exact u14045
  · exact u14046
  · exact u14047

def r31448 : Route 9 := (fun mask => (mask,id))

def c31448 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31448 : Upper (D 7) (R 7) [6,96,129,33,192] 13 := by
  apply FastRouting.sound _ _ [6,96,129,33,192] 13 (by decide) (choices 1) [2,8,16,256] r31448 c31448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14048
  · exact u14049
  · exact u14050
  · exact u14051

def r31449 : Route 9 := (fun mask => (mask,id))

def c31449 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u31449 : Upper (D 7) (R 7) [6,96,129,33,258] 13 := by
  apply FastRouting.sound _ _ [6,96,129,33,258] 13 (by decide) (choices 1) [8,16,64,128] r31449 c31449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14052
  · exact u14053
  · exact u14054
  · exact u14055

def r31450 : Route 9 := (fun mask => (mask,id))

def c31450 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31450 : Upper (D 7) (R 7) [6,96,129,33,264] 13 := by
  apply FastRouting.sound _ _ [6,96,129,33,264] 13 (by decide) (choices 1) [2,16,64,128] r31450 c31450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14056
  · exact u14057
  · exact u14058
  · exact u14059

def r31451 : Route 9 := (fun mask => (mask,id))

def c31451 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31451 : Upper (D 7) (R 7) [6,96,129,33,320] 13 := by
  apply FastRouting.sound _ _ [6,96,129,33,320] 13 (by decide) (choices 1) [2,8,16,128] r31451 c31451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14060
  · exact u14061
  · exact u14062
  · exact u14063

def r31452 : Route 9 := (fun mask => (mask,id))

def c31452 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31452 : Upper (D 7) (R 7) [6,96,129,33,384] 13 := by
  apply FastRouting.sound _ _ [6,96,129,33,384] 13 (by decide) (choices 1) [2,8,16,64] r31452 c31452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14064
  · exact u14065
  · exact u14066
  · exact u14067

def b31453 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 24, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 7 98 133 42 88 433 465 401 401), lower := (rows 7 98 133 42 88 32 64 128 256), losses := [] }

theorem u31453 : Upper (D 7) (R 7) [6,96,129,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31453 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31454 : PairBound 9 := { available := 337, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 98 133 42 152 369 337 465 337), lower := (rows 7 98 133 42 152 32 64 128 256), losses := [] }

theorem u31454 : Upper (D 7) (R 7) [6,96,129,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31454 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31455 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 98 133 42 208 313 345 409 281), lower := (rows 7 98 133 42 208 32 64 128 256), losses := [] }

theorem u31455 : Upper (D 7) (R 7) [6,96,129,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31456 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 98 133 42 273 248 216 216 472), lower := (rows 7 98 133 42 273 32 64 128 256), losses := [] }

theorem u31456 : Upper (D 7) (R 7) [6,96,129,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31456 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31457 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 98 133 42 280 241 209 209 465), lower := (rows 7 98 133 42 280 32 64 128 256), losses := [] }

theorem u31457 : Upper (D 7) (R 7) [6,96,129,34,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31457 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31458 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 98 133 42 336 185 217 153 409), lower := (rows 7 98 133 42 336 32 64 128 256), losses := [] }

theorem u31458 : Upper (D 7) (R 7) [6,96,129,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31458 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31459 : PairBound 9 := { available := 89, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 98 133 42 400 121 89 217 345), lower := (rows 7 98 133 42 400 32 64 128 256), losses := [] }

theorem u31459 : Upper (D 7) (R 7) [6,96,129,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31459 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31460 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 24, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 7 98 133 56 88 419 451 387 387), lower := (rows 7 98 133 56 88 32 64 128 256), losses := [] }

theorem u31460 : Upper (D 7) (R 7) [6,96,129,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31461 : PairBound 9 := { available := 330, camps := [{ cop := 2, region := 16, targets := 98 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,6)], upper := (rows 7 98 133 56 145 362 330 458 330), lower := (rows 7 98 133 56 145 32 64 128 256), losses := [] }

theorem u31461 : Upper (D 7) (R 7) [6,96,129,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31461 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31462 : PairBound 9 := { available := 329, camps := [{ cop := 4, region := 5, targets := 96 }], pairs := [(0,5),(0,6),(2,5),(2,6)], upper := (rows 7 98 133 56 146 361 329 457 329), lower := (rows 7 98 133 56 146 32 64 128 256), losses := [] }

theorem u31462 : Upper (D 7) (R 7) [6,96,129,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31462 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31463 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 389, targets := 32 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,5),(0,7),(1,7),(2,5)], upper := (rows 7 98 133 56 152 355 323 451 323), lower := (rows 7 98 133 56 152 32 64 128 256), losses := [] }

theorem u31463 : Upper (D 7) (R 7) [6,96,129,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31464 : Route 9 := (fun mask => (mask,id))

def c31464 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31464 : Upper (D 7) (R 7) [6,96,129,48,192] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48,192] 13 (by decide) (choices 1) [1,2,8,256] r31464 c31464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14068
  · exact u14069
  · exact u14070
  · exact u14071

def r31465 : Route 9 := (fun mask => (mask,id))

def c31465 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31465 : Upper (D 7) (R 7) [6,96,129,48,257] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48,257] 13 (by decide) (choices 1) [2,8,64,128] r31465 c31465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14072
  · exact u14073
  · exact u14074
  · exact u14075

def r31466 : Route 9 := (fun mask => (mask,id))

def c31466 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31466 : Upper (D 7) (R 7) [6,96,129,48,258] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48,258] 13 (by decide) (choices 1) [1,8,64,128] r31466 c31466
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14076
  · exact u14077
  · exact u14078
  · exact u14079

def r31467 : Route 9 := (fun mask => (mask,id))

def c31467 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31467 : Upper (D 7) (R 7) [6,96,129,48,264] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48,264] 13 (by decide) (choices 1) [1,2,64,128] r31467 c31467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14080
  · exact u14081
  · exact u14082
  · exact u14083

def r31468 : Route 9 := (fun mask => (mask,id))

def c31468 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31468 : Upper (D 7) (R 7) [6,96,129,48,320] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48,320] 13 (by decide) (choices 1) [1,2,8,128] r31468 c31468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14084
  · exact u14085
  · exact u14086
  · exact u14087

def r31469 : Route 9 := (fun mask => (mask,id))

def c31469 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31469 : Upper (D 7) (R 7) [6,96,129,48,384] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48,384] 13 (by decide) (choices 1) [1,2,8,64] r31469 c31469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14088
  · exact u14089
  · exact u14090
  · exact u14091

def b31470 : PairBound 9 := { available := 275, camps := [{ cop := 1, region := 8, targets := 129 },{ cop := 3, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 133 104 152 307 339 403 275), lower := (rows 7 98 133 104 152 32 64 128 256), losses := [] }

theorem u31470 : Upper (D 7) (R 7) [6,96,129,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31470 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31471 : PairBound 9 := { available := 154, camps := [{ cop := 1, region := 8, targets := 129 },{ cop := 3, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 133 104 273 186 218 154 410), lower := (rows 7 98 133 104 273 32 64 128 256), losses := [] }

theorem u31471 : Upper (D 7) (R 7) [6,96,129,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31471 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31472 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 129 },{ cop := 3, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 133 104 274 185 217 153 409), lower := (rows 7 98 133 104 274 32 64 128 256), losses := [] }

theorem u31472 : Upper (D 7) (R 7) [6,96,129,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31472 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31473 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 8, targets := 129 },{ cop := 3, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 133 104 280 179 211 147 403), lower := (rows 7 98 133 104 280 32 64 128 256), losses := [] }

theorem u31473 : Upper (D 7) (R 7) [6,96,129,96,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31473 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31474 : PairBound 9 := { available := 27, camps := [{ cop := 1, region := 8, targets := 129 },{ cop := 3, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 133 104 400 59 91 155 283), lower := (rows 7 98 133 104 400 32 64 128 256), losses := [] }

theorem u31474 : Upper (D 7) (R 7) [6,96,129,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31474 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31475 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 8, targets := 98 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,6)], upper := (rows 7 98 133 137 274 120 120 248 376), lower := (rows 7 98 133 137 274 32 64 128 256), losses := [] }

theorem u31475 : Upper (D 7) (R 7) [6,96,129,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31475 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31476 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 8, targets := 98 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,6)], upper := (rows 7 98 133 137 280 114 114 242 370), lower := (rows 7 98 133 137 280 32 64 128 256), losses := [] }

theorem u31476 : Upper (D 7) (R 7) [6,96,129,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31476 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31477 : PairBound 9 := { available := 90, camps := [{ cop := 2, region := 8, targets := 98 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,6)], upper := (rows 7 98 133 137 304 122 90 218 346), lower := (rows 7 98 133 137 304 32 64 128 256), losses := [] }

theorem u31477 : Upper (D 7) (R 7) [6,96,129,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31477 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31478 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 5, targets := 96 }], pairs := [(0,5),(0,6),(2,5),(2,6)], upper := (rows 7 98 133 138 273 120 120 248 376), lower := (rows 7 98 133 138 273 32 64 128 256), losses := [] }

theorem u31478 : Upper (D 7) (R 7) [6,96,129,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31478 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31479 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 5, targets := 96 }], pairs := [(0,5),(0,6),(2,5),(2,6)], upper := (rows 7 98 133 138 280 113 113 241 369), lower := (rows 7 98 133 138 280 32 64 128 256), losses := [] }

theorem u31479 : Upper (D 7) (R 7) [6,96,129,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31479 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31480 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 5, targets := 96 }], pairs := [(0,5),(0,6),(2,5),(2,6)], upper := (rows 7 98 133 138 304 121 89 217 345), lower := (rows 7 98 133 138 304 32 64 128 256), losses := [] }

theorem u31480 : Upper (D 7) (R 7) [6,96,129,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31481 : Route 9 := (fun mask => (mask,id))

def c31481 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31481 : Upper (D 7) (R 7) [6,96,129,144,257] 13 := by
  apply FastRouting.sound _ _ [6,96,129,144,257] 13 (by decide) (choices 1) [2,8,64] r31481 c31481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14092
  · exact u14093
  · exact u14094

def r31482 : Route 9 := (fun mask => (mask,id))

def c31482 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31482 : Upper (D 7) (R 7) [6,96,129,144,258] 13 := by
  apply FastRouting.sound _ _ [6,96,129,144,258] 13 (by decide) (choices 1) [1,8,64] r31482 c31482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14095
  · exact u14096
  · exact u14097

def r31483 : Route 9 := (fun mask => (mask,id))

def c31483 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31483 : Upper (D 7) (R 7) [6,96,129,144,264] 13 := by
  apply FastRouting.sound _ _ [6,96,129,144,264] 13 (by decide) (choices 1) [1,2,64] r31483 c31483
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14098
  · exact u14099
  · exact u14100

def r31484 : Route 9 := (fun mask => (mask,id))

def c31484 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31484 : Upper (D 7) (R 7) [6,96,129,144,288] 13 := by
  apply FastRouting.sound _ _ [6,96,129,144,288] 13 (by decide) (choices 1) [1,2,8,64] r31484 c31484
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14101
  · exact u14102
  · exact u14103
  · exact u14104

def r31485 : Route 9 := (fun mask => (mask,id))

def c31485 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31485 : Upper (D 7) (R 7) [6,96,129,160,257] 13 := by
  apply FastRouting.sound _ _ [6,96,129,160,257] 13 (by decide) (choices 1) [2,8,16,64] r31485 c31485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14105
  · exact u14106
  · exact u14107
  · exact u14108

def r31486 : Route 9 := (fun mask => (mask,id))

def c31486 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31486 : Upper (D 7) (R 7) [6,96,129,160,258] 13 := by
  apply FastRouting.sound _ _ [6,96,129,160,258] 13 (by decide) (choices 1) [1,8,16,64] r31486 c31486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14109
  · exact u14110
  · exact u14111
  · exact u14112

def r31487 : Route 9 := (fun mask => (mask,id))

def c31487 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31487 : Upper (D 7) (R 7) [6,96,129,160,264] 13 := by
  apply FastRouting.sound _ _ [6,96,129,160,264] 13 (by decide) (choices 1) [1,2,16,64] r31487 c31487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14113
  · exact u14114
  · exact u14115
  · exact u14116

def r31488 : Route 9 := (fun mask => (mask,id))

def c31488 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31488 : Upper (D 7) (R 7) [6,96,129,160,320] 13 := by
  apply FastRouting.sound _ _ [6,96,129,160,320] 13 (by decide) (choices 1) [1,2,8,16] r31488 c31488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14117
  · exact u14118
  · exact u14119
  · exact u14120

def b31489 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 98 140 25 19 480 480 480 480), lower := (rows 7 98 140 25 19 32 64 128 256), losses := [] }

theorem u31489 : Upper (D 7) (R 7) [6,96,136,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31489 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31490 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 7 98 140 25 49 482 450 450 450), lower := (rows 7 98 140 25 49 32 64 128 256), losses := [] }

theorem u31490 : Upper (D 7) (R 7) [6,96,136,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31490 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31491 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 98 140 25 50 481 449 449 449), lower := (rows 7 98 140 25 50 32 64 128 256), losses := [] }

theorem u31491 : Upper (D 7) (R 7) [6,96,136,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31491 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31492 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 7 98 140 25 112 419 451 387 387), lower := (rows 7 98 140 25 112 32 64 128 256), losses := [] }

theorem u31492 : Upper (D 7) (R 7) [6,96,136,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31492 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31493 : PairBound 9 := { available := 354, camps := [{ cop := 4, region := 12, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(3,1)], upper := (rows 7 98 140 25 145 354 354 482 354), lower := (rows 7 98 140 25 145 32 64 128 256), losses := [] }

theorem u31493 : Upper (D 7) (R 7) [6,96,136,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31493 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31494 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 13, targets := 96 }], pairs := [(0,5),(0,6),(2,5),(2,6)], upper := (rows 7 98 140 25 146 353 353 481 353), lower := (rows 7 98 140 25 146 32 64 128 256), losses := [] }

theorem u31494 : Upper (D 7) (R 7) [6,96,136,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31495 : Route 9 := (fun mask => (mask,id))

def c31495 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31495 : Upper (D 7) (R 7) [6,96,136,17,160] 13 := by
  apply FastRouting.sound _ _ [6,96,136,17,160] 13 (by decide) (choices 1) [1,2,64,256] r31495 c31495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14121
  · exact u14122
  · exact u14123
  · exact u14124

def b31496 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 7 98 140 25 273 226 226 226 482), lower := (rows 7 98 140 25 273 32 64 128 256), losses := [] }

theorem u31496 : Upper (D 7) (R 7) [6,96,136,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31497 : Route 9 := (fun mask => (mask,id))

def c31497 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31497 : Upper (D 7) (R 7) [6,96,136,17,258] 13 := by
  apply FastRouting.sound _ _ [6,96,136,17,258] 13 (by decide) (choices 1) [1,64,128] r31497 c31497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14125
  · exact u14126
  · exact u14127

def r31498 : Route 9 := (fun mask => (mask,id))

def c31498 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31498 : Upper (D 7) (R 7) [6,96,136,17,288] 13 := by
  apply FastRouting.sound _ _ [6,96,136,17,288] 13 (by decide) (choices 1) [1,2,64,128] r31498 c31498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14128
  · exact u14129
  · exact u14130
  · exact u14131

def r31499 : Route 9 := (fun mask => (mask,id))

def c31499 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31499 : Upper (D 7) (R 7) [6,96,136,17,384] 13 := by
  apply FastRouting.sound _ _ [6,96,136,17,384] 13 (by decide) (choices 1) [1,2,64] r31499 c31499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14132
  · exact u14133
  · exact u14134

#print axioms u31499
end Delivery.IrregularNine14.P07
