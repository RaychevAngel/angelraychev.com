import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0239
import IrregularNine14P07C0240

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b31620 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 389, targets := 32 },{ cop := 3, region := 242, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,0)], upper := (rows 7 98 261 25 56 226 194 194 450), lower := (rows 7 98 261 25 56 32 64 128 256), losses := [] }

theorem u31620 : Upper (D 7) (R 7) [6,96,257,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31620 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31621 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 7 98 261 25 112 170 202 138 394), lower := (rows 7 98 261 25 112 32 64 128 256), losses := [] }

theorem u31621 : Upper (D 7) (R 7) [6,96,257,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31622 : Route 9 := (fun mask => (mask,id))

def c31622 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31622 : Upper (D 7) (R 7) [6,96,257,17,130] 13 := by
  apply FastRouting.sound _ _ [6,96,257,17,130] 13 (by decide) (choices 1) [8,64,128] r31622 c31622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14341
  · exact u14342
  · exact u14343

def r31623 : Route 9 := (fun mask => (mask,id))

def c31623 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31623 : Upper (D 7) (R 7) [6,96,257,17,136] 13 := by
  apply FastRouting.sound _ _ [6,96,257,17,136] 13 (by decide) (choices 1) [2,64,128] r31623 c31623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14344
  · exact u14345
  · exact u14346

def r31624 : Route 9 := (fun mask => (mask,id))

def c31624 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31624 : Upper (D 7) (R 7) [6,96,257,17,160] 13 := by
  apply FastRouting.sound _ _ [6,96,257,17,160] 13 (by decide) (choices 1) [2,8,64,128] r31624 c31624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14347
  · exact u14348
  · exact u14349
  · exact u14350

def b31625 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 453, targets := 32 },{ cop := 4, region := 202, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,0)], upper := (rows 7 98 261 26 49 232 200 200 456), lower := (rows 7 98 261 26 49 32 64 128 256), losses := [] }

theorem u31625 : Upper (D 7) (R 7) [6,96,257,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31625 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31626 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 24, targets := 193 }], pairs := [(3,0),(3,6),(3,7),(4,0)], upper := (rows 7 98 261 26 56 225 193 193 449), lower := (rows 7 98 261 26 56 32 64 128 256), losses := [] }

theorem u31626 : Upper (D 7) (R 7) [6,96,257,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31626 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31627 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 24, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 7 98 261 26 112 169 201 137 393), lower := (rows 7 98 261 26 112 32 64 128 256), losses := [] }

theorem u31627 : Upper (D 7) (R 7) [6,96,257,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31627 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31628 : Route 9 := (fun mask => (mask,id))

def c31628 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31628 : Upper (D 7) (R 7) [6,96,257,18,129] 13 := by
  apply FastRouting.sound _ _ [6,96,257,18,129] 13 (by decide) (choices 1) [8,64,128] r31628 c31628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14351
  · exact u14352
  · exact u14353

def r31629 : Route 9 := (fun mask => (mask,id))

def c31629 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31629 : Upper (D 7) (R 7) [6,96,257,18,136] 13 := by
  apply FastRouting.sound _ _ [6,96,257,18,136] 13 (by decide) (choices 1) [1,64,128] r31629 c31629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14354
  · exact u14355
  · exact u14356

def r31630 : Route 9 := (fun mask => (mask,id))

def c31630 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31630 : Upper (D 7) (R 7) [6,96,257,18,160] 13 := by
  apply FastRouting.sound _ _ [6,96,257,18,160] 13 (by decide) (choices 1) [1,8,64,128] r31630 c31630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14357
  · exact u14358
  · exact u14359
  · exact u14360

def b31631 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 7 98 261 41 82 184 216 152 408), lower := (rows 7 98 261 41 82 32 64 128 256), losses := [] }

theorem u31631 : Upper (D 7) (R 7) [6,96,257,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31631 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31632 : Route 9 := (fun mask => (mask,id))

def c31632 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31632 : Upper (D 7) (R 7) [6,96,257,33,72] 13 := by
  apply FastRouting.sound _ _ [6,96,257,33,72] 13 (by decide) (choices 1) [2,16,128] r31632 c31632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14361
  · exact u14362
  · exact u14363

def r31633 : Route 9 := (fun mask => (mask,id))

def c31633 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u31633 : Upper (D 7) (R 7) [6,96,257,33,130] 13 := by
  apply FastRouting.sound _ _ [6,96,257,33,130] 13 (by decide) (choices 1) [8,16,64,128] r31633 c31633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14364
  · exact u14365
  · exact u14366
  · exact u14367

def r31634 : Route 9 := (fun mask => (mask,id))

def c31634 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31634 : Upper (D 7) (R 7) [6,96,257,33,136] 13 := by
  apply FastRouting.sound _ _ [6,96,257,33,136] 13 (by decide) (choices 1) [2,16,64,128] r31634 c31634
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14368
  · exact u14369
  · exact u14370
  · exact u14371

def r31635 : Route 9 := (fun mask => (mask,id))

def c31635 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31635 : Upper (D 7) (R 7) [6,96,257,33,192] 13 := by
  apply FastRouting.sound _ _ [6,96,257,33,192] 13 (by decide) (choices 1) [2,8,16,128] r31635 c31635
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14372
  · exact u14373
  · exact u14374
  · exact u14375

def b31636 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 24, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 7 98 261 42 88 177 209 145 401), lower := (rows 7 98 261 42 88 32 64 128 256), losses := [] }

theorem u31636 : Upper (D 7) (R 7) [6,96,257,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31636 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31637 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 98 261 42 145 248 216 216 472), lower := (rows 7 98 261 42 145 32 64 128 256), losses := [] }

theorem u31637 : Upper (D 7) (R 7) [6,96,257,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31638 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 98 261 42 152 241 209 209 465), lower := (rows 7 98 261 42 152 32 64 128 256), losses := [] }

theorem u31638 : Upper (D 7) (R 7) [6,96,257,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31638 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31639 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 98 261 42 208 185 217 153 409), lower := (rows 7 98 261 42 208 32 64 128 256), losses := [] }

theorem u31639 : Upper (D 7) (R 7) [6,96,257,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31639 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31640 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 24, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 7 98 261 56 88 163 195 131 387), lower := (rows 7 98 261 56 88 32 64 128 256), losses := [] }

theorem u31640 : Upper (D 7) (R 7) [6,96,257,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31640 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31641 : Route 9 := (fun mask => (mask,id))

def c31641 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31641 : Upper (D 7) (R 7) [6,96,257,48,129] 13 := by
  apply FastRouting.sound _ _ [6,96,257,48,129] 13 (by decide) (choices 1) [2,8,64,128] r31641 c31641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14376
  · exact u14377
  · exact u14378
  · exact u14379

def r31642 : Route 9 := (fun mask => (mask,id))

def c31642 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31642 : Upper (D 7) (R 7) [6,96,257,48,130] 13 := by
  apply FastRouting.sound _ _ [6,96,257,48,130] 13 (by decide) (choices 1) [1,8,64,128] r31642 c31642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14380
  · exact u14381
  · exact u14382
  · exact u14383

def r31643 : Route 9 := (fun mask => (mask,id))

def c31643 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31643 : Upper (D 7) (R 7) [6,96,257,48,136] 13 := by
  apply FastRouting.sound _ _ [6,96,257,48,136] 13 (by decide) (choices 1) [1,2,64,128] r31643 c31643
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14384
  · exact u14385
  · exact u14386
  · exact u14387

def r31644 : Route 9 := (fun mask => (mask,id))

def c31644 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31644 : Upper (D 7) (R 7) [6,96,257,48,192] 13 := by
  apply FastRouting.sound _ _ [6,96,257,48,192] 13 (by decide) (choices 1) [1,2,8,128] r31644 c31644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14388
  · exact u14389
  · exact u14390
  · exact u14391

def b31645 : PairBound 9 := { available := 154, camps := [{ cop := 1, region := 8, targets := 129 },{ cop := 3, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 261 104 145 186 218 154 410), lower := (rows 7 98 261 104 145 32 64 128 256), losses := [] }

theorem u31645 : Upper (D 7) (R 7) [6,96,257,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31645 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31646 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 129 },{ cop := 3, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 261 104 146 185 217 153 409), lower := (rows 7 98 261 104 146 32 64 128 256), losses := [] }

theorem u31646 : Upper (D 7) (R 7) [6,96,257,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31646 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31647 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 8, targets := 129 },{ cop := 3, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 261 104 152 179 211 147 403), lower := (rows 7 98 261 104 152 32 64 128 256), losses := [] }

theorem u31647 : Upper (D 7) (R 7) [6,96,257,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31647 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31648 : Route 9 := (fun mask => (mask,id))

def c31648 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31648 : Upper (D 7) (R 7) [6,96,257,129,130] 13 := by
  apply FastRouting.sound _ _ [6,96,257,129,130] 13 (by decide) (choices 1) [8,16,64] r31648 c31648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14392
  · exact u14393
  · exact u14394

def b31649 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 359, targets := 128 }], pairs := [(0,7),(4,1),(4,5),(4,6)], upper := (rows 7 98 261 137 152 114 114 242 370), lower := (rows 7 98 261 137 152 32 64 128 256), losses := [] }

theorem u31649 : Upper (D 7) (R 7) [6,96,257,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31649 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31650 : Route 9 := (fun mask => (mask,id))

def c31650 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31650 : Upper (D 7) (R 7) [6,96,257,129,160] 13 := by
  apply FastRouting.sound _ _ [6,96,257,129,160] 13 (by decide) (choices 1) [2,8,16,64] r31650 c31650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14395
  · exact u14396
  · exact u14397
  · exact u14398

def b31651 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 7 98 261 138 152 113 113 241 369), lower := (rows 7 98 261 138 152 32 64 128 256), losses := [] }

theorem u31651 : Upper (D 7) (R 7) [6,96,257,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31651 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31652 : Route 9 := (fun mask => (mask,id))

def c31652 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31652 : Upper (D 7) (R 7) [6,96,257,130,160] 13 := by
  apply FastRouting.sound _ _ [6,96,257,130,160] 13 (by decide) (choices 1) [1,8,16,64] r31652 c31652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14399
  · exact u14400
  · exact u14401
  · exact u14402

def b31653 : PairBound 9 := { available := 99, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 98 261 152 152 99 99 227 355), lower := (rows 7 98 261 152 152 32 64 128 256), losses := [] }

theorem u31653 : Upper (D 7) (R 7) [6,96,257,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31653 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31654 : PairBound 9 := { available := 75, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 98 261 152 176 107 75 203 331), lower := (rows 7 98 261 152 176 32 64 128 256), losses := [] }

theorem u31654 : Upper (D 7) (R 7) [6,96,257,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31654 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31655 : Route 9 := (fun mask => (mask,id))

def c31655 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31655 : Upper (D 7) (R 7) [6,96,257,160,192] 13 := by
  apply FastRouting.sound _ _ [6,96,257,160,192] 13 (by decide) (choices 1) [1,2,8,16] r31655 c31655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14403
  · exact u14404
  · exact u14405
  · exact u14406

def b31656 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 98 268 25 19 224 224 224 480), lower := (rows 7 98 268 25 19 32 64 128 256), losses := [] }

theorem u31656 : Upper (D 7) (R 7) [6,96,264,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31656 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31657 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 7 98 268 25 49 226 194 194 450), lower := (rows 7 98 268 25 49 32 64 128 256), losses := [] }

theorem u31657 : Upper (D 7) (R 7) [6,96,264,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31657 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31658 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 98 268 25 50 225 193 193 449), lower := (rows 7 98 268 25 50 32 64 128 256), losses := [] }

theorem u31658 : Upper (D 7) (R 7) [6,96,264,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31658 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31659 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 7 98 268 25 112 163 195 131 387), lower := (rows 7 98 268 25 112 32 64 128 256), losses := [] }

theorem u31659 : Upper (D 7) (R 7) [6,96,264,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31659 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31660 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 7 98 268 25 145 226 226 226 482), lower := (rows 7 98 268 25 145 32 64 128 256), losses := [] }

theorem u31660 : Upper (D 7) (R 7) [6,96,264,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31661 : Route 9 := (fun mask => (mask,id))

def c31661 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31661 : Upper (D 7) (R 7) [6,96,264,17,130] 13 := by
  apply FastRouting.sound _ _ [6,96,264,17,130] 13 (by decide) (choices 1) [1,64,128] r31661 c31661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14407
  · exact u14408
  · exact u14409

def r31662 : Route 9 := (fun mask => (mask,id))

def c31662 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31662 : Upper (D 7) (R 7) [6,96,264,17,160] 13 := by
  apply FastRouting.sound _ _ [6,96,264,17,160] 13 (by decide) (choices 1) [1,2,64,128] r31662 c31662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14410
  · exact u14411
  · exact u14412
  · exact u14413

def b31663 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 453, targets := 32 },{ cop := 0, region := 240, targets := 2 }], pairs := [(0,5),(2,1),(2,5),(4,1)], upper := (rows 7 98 268 26 49 225 193 193 449), lower := (rows 7 98 268 26 49 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 49 81 145 273), good := (rows 501 96 268 508 497 32 64 128 256) }] }

theorem u31663 : Upper (D 7) (R 7) [6,96,264,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31663 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31664 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 24, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 7 98 268 26 112 161 193 129 385), lower := (rows 7 98 268 26 112 32 64 128 256), losses := [] }

theorem u31664 : Upper (D 7) (R 7) [6,96,264,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31664 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31665 : Route 9 := (fun mask => (mask,id))

def c31665 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31665 : Upper (D 7) (R 7) [6,96,264,18,129] 13 := by
  apply FastRouting.sound _ _ [6,96,264,18,129] 13 (by decide) (choices 1) [1,64,128] r31665 c31665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14414
  · exact u14415
  · exact u14416

def r31666 : Route 9 := (fun mask => (mask,id))

def c31666 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31666 : Upper (D 7) (R 7) [6,96,264,18,160] 13 := by
  apply FastRouting.sound _ _ [6,96,264,18,160] 13 (by decide) (choices 1) [1,64,128] r31666 c31666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14417
  · exact u14418
  · exact u14419

def b31667 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(3,1),(4,6),(4,7)], upper := (rows 7 98 268 41 19 240 208 208 464), lower := (rows 7 98 268 41 19 32 64 128 256), losses := [] }

theorem u31667 : Upper (D 7) (R 7) [6,96,264,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31667 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31668 : Route 9 := (fun mask => (mask,id))

def c31668 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31668 : Upper (D 7) (R 7) [6,96,264,33,65] 13 := by
  apply FastRouting.sound _ _ [6,96,264,33,65] 13 (by decide) (choices 1) [2,16,128] r31668 c31668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14420
  · exact u14421
  · exact u14422

def b31669 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 7 98 268 41 82 177 209 145 401), lower := (rows 7 98 268 41 82 32 64 128 256), losses := [] }

theorem u31669 : Upper (D 7) (R 7) [6,96,264,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31670 : Route 9 := (fun mask => (mask,id))

def c31670 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31670 : Upper (D 7) (R 7) [6,96,264,33,129] 13 := by
  apply FastRouting.sound _ _ [6,96,264,33,129] 13 (by decide) (choices 1) [2,16,64,128] r31670 c31670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14423
  · exact u14424
  · exact u14425
  · exact u14426

def r31671 : Route 9 := (fun mask => (mask,id))

def c31671 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31671 : Upper (D 7) (R 7) [6,96,264,33,130] 13 := by
  apply FastRouting.sound _ _ [6,96,264,33,130] 13 (by decide) (choices 1) [1,16,64,128] r31671 c31671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14427
  · exact u14428
  · exact u14429
  · exact u14430

def r31672 : Route 9 := (fun mask => (mask,id))

def c31672 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31672 : Upper (D 7) (R 7) [6,96,264,33,192] 13 := by
  apply FastRouting.sound _ _ [6,96,264,33,192] 13 (by decide) (choices 1) [1,2,16,128] r31672 c31672
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14431
  · exact u14432
  · exact u14433
  · exact u14434

def b31673 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(3,1),(4,6),(4,7)], upper := (rows 7 98 268 56 19 225 193 193 449), lower := (rows 7 98 268 56 19 32 64 128 256), losses := [] }

theorem u31673 : Upper (D 7) (R 7) [6,96,264,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31673 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31674 : Route 9 := (fun mask => (mask,id))

def c31674 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31674 : Upper (D 7) (R 7) [6,96,264,48,65] 13 := by
  apply FastRouting.sound _ _ [6,96,264,48,65] 13 (by decide) (choices 1) [1,2,128] r31674 c31674
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14435
  · exact u14436
  · exact u14437

def b31675 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 24, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 7 98 268 56 82 161 193 129 385), lower := (rows 7 98 268 56 82 32 64 128 256), losses := [] }

theorem u31675 : Upper (D 7) (R 7) [6,96,264,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31675 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31676 : Route 9 := (fun mask => (mask,id))

def c31676 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31676 : Upper (D 7) (R 7) [6,96,264,48,129] 13 := by
  apply FastRouting.sound _ _ [6,96,264,48,129] 13 (by decide) (choices 1) [1,2,64,128] r31676 c31676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14438
  · exact u14439
  · exact u14440
  · exact u14441

def r31677 : Route 9 := (fun mask => (mask,id))

def c31677 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31677 : Upper (D 7) (R 7) [6,96,264,48,130] 13 := by
  apply FastRouting.sound _ _ [6,96,264,48,130] 13 (by decide) (choices 1) [1,64,128] r31677 c31677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14442
  · exact u14443
  · exact u14444

def r31678 : Route 9 := (fun mask => (mask,id))

def c31678 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31678 : Upper (D 7) (R 7) [6,96,264,48,192] 13 := by
  apply FastRouting.sound _ _ [6,96,264,48,192] 13 (by decide) (choices 1) [1,2,128] r31678 c31678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14445
  · exact u14446
  · exact u14447

def b31679 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 7 98 268 137 19 240 240 240 496), lower := (rows 7 98 268 137 19 32 64 128 256), losses := [] }

theorem u31679 : Upper (D 7) (R 7) [6,96,264,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31679 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u31679
end Delivery.IrregularNine14.P07
