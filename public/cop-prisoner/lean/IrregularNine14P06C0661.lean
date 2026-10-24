import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0436
import IrregularNine14P06C0437
import IrregularNine14P06C0438

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r39660 : Route 9 := (fun mask => (mask,id))

def c39660 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39660 : Upper (D 6) (R 6) [40,96,192,18,257] 13 := by
  apply FastRouting.sound _ _ [40,96,192,18,257] 13 (by decide) (choices 1) [1,2,4] r39660 c39660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26218
  · exact u26219
  · exact u26220

def b39661 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 98 196 26 274 37 69 133 261), lower := (rows 41 98 196 26 274 32 64 128 256), losses := [] }

theorem u39661 : Upper (D 6) (R 6) [40,96,192,18,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39661 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39662 : Route 9 := (fun mask => (mask,id))

def c39662 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39662 : Upper (D 6) (R 6) [40,96,192,18,260] 13 := by
  apply FastRouting.sound _ _ [40,96,192,18,260] 13 (by decide) (choices 1) [1,2,4] r39662 c39662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26221
  · exact u26222
  · exact u26223

def r39663 : Route 9 := (fun mask => (mask,id))

def c39663 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39663 : Upper (D 6) (R 6) [40,96,192,20,3] 13 := by
  apply FastRouting.sound _ _ [40,96,192,20,3] 13 (by decide) (choices 1) [1,2,4,256] r39663 c39663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26224
  · exact u26225
  · exact u26226
  · exact u26227

def b39664 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 98 196 28 21 291 323 387 259), lower := (rows 41 98 196 28 21 32 64 128 256), losses := [] }

theorem u39664 : Upper (D 6) (R 6) [40,96,192,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39664 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39665 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 98 196 28 22 291 323 387 259), lower := (rows 41 98 196 28 22 32 64 128 256), losses := [] }

theorem u39665 : Upper (D 6) (R 6) [40,96,192,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39665 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39666 : Route 9 := (fun mask => (mask,id))

def c39666 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39666 : Upper (D 6) (R 6) [40,96,192,20,257] 13 := by
  apply FastRouting.sound _ _ [40,96,192,20,257] 13 (by decide) (choices 1) [1,2,4] r39666 c39666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26228
  · exact u26229
  · exact u26230

def r39667 : Route 9 := (fun mask => (mask,id))

def c39667 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39667 : Upper (D 6) (R 6) [40,96,192,20,258] 13 := by
  apply FastRouting.sound _ _ [40,96,192,20,258] 13 (by decide) (choices 1) [1,2,4] r39667 c39667
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26231
  · exact u26232
  · exact u26233

def b39668 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 98 196 28 276 35 67 131 259), lower := (rows 41 98 196 28 276 32 64 128 256), losses := [] }

theorem u39668 : Upper (D 6) (R 6) [40,96,192,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39668 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39669 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 196, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 41 98 196 265 19 54 86 150 278), lower := (rows 41 98 196 265 19 32 64 128 256), losses := [] }

theorem u39669 : Upper (D 6) (R 6) [40,96,192,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39669 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39670 : Route 9 := (fun mask => (mask,id))

def c39670 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39670 : Upper (D 6) (R 6) [40,96,192,257,5] 13 := by
  apply FastRouting.sound _ _ [40,96,192,257,5] 13 (by decide) (choices 1) [2,4,16] r39670 c39670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26234
  · exact u26235
  · exact u26236

def r39671 : Route 9 := (fun mask => (mask,id))

def c39671 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39671 : Upper (D 6) (R 6) [40,96,192,257,6] 13 := by
  apply FastRouting.sound _ _ [40,96,192,257,6] 13 (by decide) (choices 1) [1,2,4,16] r39671 c39671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26237
  · exact u26238
  · exact u26239
  · exact u26240

def b39672 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 4, region := 196, targets := 2 }], pairs := [(2,1),(2,5),(3,5)], upper := (rows 41 98 196 266 19 53 85 149 277), lower := (rows 41 98 196 266 19 32 64 128 256), losses := [] }

theorem u39672 : Upper (D 6) (R 6) [40,96,192,258,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39672 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39673 : Route 9 := (fun mask => (mask,id))

def c39673 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39673 : Upper (D 6) (R 6) [40,96,192,258,5] 13 := by
  apply FastRouting.sound _ _ [40,96,192,258,5] 13 (by decide) (choices 1) [1,2,4,16] r39673 c39673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26241
  · exact u26242
  · exact u26243
  · exact u26244

def r39674 : Route 9 := (fun mask => (mask,id))

def c39674 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39674 : Upper (D 6) (R 6) [40,96,192,258,6] 13 := by
  apply FastRouting.sound _ _ [40,96,192,258,6] 13 (by decide) (choices 1) [1,4,16] r39674 c39674
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26245
  · exact u26246
  · exact u26247

def r39675 : Route 9 := (fun mask => (mask,id))

def c39675 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39675 : Upper (D 6) (R 6) [40,96,192,260,3] 13 := by
  apply FastRouting.sound _ _ [40,96,192,260,3] 13 (by decide) (choices 1) [1,2,4,16] r39675 c39675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26248
  · exact u26249
  · exact u26250
  · exact u26251

def r39676 : Route 9 := (fun mask => (mask,id))

def c39676 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39676 : Upper (D 6) (R 6) [40,96,192,260,5] 13 := by
  apply FastRouting.sound _ _ [40,96,192,260,5] 13 (by decide) (choices 1) [1,2,16] r39676 c39676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26252
  · exact u26253
  · exact u26254

def r39677 : Route 9 := (fun mask => (mask,id))

def c39677 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39677 : Upper (D 6) (R 6) [40,96,192,260,6] 13 := by
  apply FastRouting.sound _ _ [40,96,192,260,6] 13 (by decide) (choices 1) [1,2,16] r39677 c39677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26255
  · exact u26256
  · exact u26257

def r39678 : Route 9 := (fun mask => (mask,id))

def c39678 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39678 : Upper (D 6) (R 6) [40,96,192,272,3] 13 := by
  apply FastRouting.sound _ _ [40,96,192,272,3] 13 (by decide) (choices 1) [1,2,4] r39678 c39678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26258
  · exact u26259
  · exact u26260

def r39679 : Route 9 := (fun mask => (mask,id))

def c39679 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39679 : Upper (D 6) (R 6) [40,96,192,272,5] 13 := by
  apply FastRouting.sound _ _ [40,96,192,272,5] 13 (by decide) (choices 1) [1,2,4] r39679 c39679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26261
  · exact u26262
  · exact u26263

def r39680 : Route 9 := (fun mask => (mask,id))

def c39680 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39680 : Upper (D 6) (R 6) [40,96,192,272,6] 13 := by
  apply FastRouting.sound _ _ [40,96,192,272,6] 13 (by decide) (choices 1) [1,2,4] r39680 c39680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26264
  · exact u26265
  · exact u26266

def b39681 : PairBound 9 := { available := 86, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 452, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 41 98 388 13 19 118 86 214 342), lower := (rows 41 98 388 13 19 32 64 128 256), losses := [] }

theorem u39681 : Upper (D 6) (R 6) [40,96,384,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39681 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39682 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 98 388 13 21 114 82 210 338), lower := (rows 41 98 388 13 21 32 64 128 256), losses := [] }

theorem u39682 : Upper (D 6) (R 6) [40,96,384,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39682 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39683 : Route 9 := (fun mask => (mask,id))

def c39683 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39683 : Upper (D 6) (R 6) [40,96,384,5,6] 13 := by
  apply FastRouting.sound _ _ [40,96,384,5,6] 13 (by decide) (choices 1) [1,2,16,64] r39683 c39683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26267
  · exact u26268
  · exact u26269
  · exact u26270

def r39684 : Route 9 := (fun mask => (mask,id))

def c39684 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39684 : Upper (D 6) (R 6) [40,96,384,5,65] 13 := by
  apply FastRouting.sound _ _ [40,96,384,5,65] 13 (by decide) (choices 1) [2,4,16] r39684 c39684
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26271
  · exact u26272
  · exact u26273

def b39685 : PairBound 9 := { available := 23, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 98 388 13 82 55 87 151 279), lower := (rows 41 98 388 13 82 32 64 128 256), losses := [] }

theorem u39685 : Upper (D 6) (R 6) [40,96,384,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39686 : Route 9 := (fun mask => (mask,id))

def c39686 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39686 : Upper (D 6) (R 6) [40,96,384,5,68] 13 := by
  apply FastRouting.sound _ _ [40,96,384,5,68] 13 (by decide) (choices 1) [1,2,16] r39686 c39686
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26274
  · exact u26275
  · exact u26276

def b39687 : PairBound 9 := { available := 85, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 4, region := 452, targets := 2 }], pairs := [(2,1),(2,5),(3,5)], upper := (rows 41 98 388 14 19 117 85 213 341), lower := (rows 41 98 388 14 19 32 64 128 256), losses := [] }

theorem u39687 : Upper (D 6) (R 6) [40,96,384,6,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39687 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39688 : Route 9 := (fun mask => (mask,id))

def c39688 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39688 : Upper (D 6) (R 6) [40,96,384,6,5] 13 := by
  apply FastRouting.sound _ _ [40,96,384,6,5] 13 (by decide) (choices 1) [1,2,16,64] r39688 c39688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26277
  · exact u26278
  · exact u26279
  · exact u26280

def b39689 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 98 388 14 22 113 81 209 337), lower := (rows 41 98 388 14 22 32 64 128 256), losses := [] }

theorem u39689 : Upper (D 6) (R 6) [40,96,384,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39689 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39690 : Route 9 := (fun mask => (mask,id))

def c39690 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39690 : Upper (D 6) (R 6) [40,96,384,6,65] 13 := by
  apply FastRouting.sound _ _ [40,96,384,6,65] 13 (by decide) (choices 1) [1,2,4,16] r39690 c39690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26281
  · exact u26282
  · exact u26283
  · exact u26284

def b39691 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 98 388 14 82 53 85 149 277), lower := (rows 41 98 388 14 82 32 64 128 256), losses := [] }

theorem u39691 : Upper (D 6) (R 6) [40,96,384,6,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39691 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39692 : Route 9 := (fun mask => (mask,id))

def c39692 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39692 : Upper (D 6) (R 6) [40,96,384,6,68] 13 := by
  apply FastRouting.sound _ _ [40,96,384,6,68] 13 (by decide) (choices 1) [1,2,16] r39692 c39692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26285
  · exact u26286
  · exact u26287

def b39693 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 98 388 25 19 102 70 198 326), lower := (rows 41 98 388 25 19 32 64 128 256), losses := [] }

theorem u39693 : Upper (D 6) (R 6) [40,96,384,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39693 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39694 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 41 98 388 25 21 102 70 198 326), lower := (rows 41 98 388 25 21 32 64 128 256), losses := [] }

theorem u39694 : Upper (D 6) (R 6) [40,96,384,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39694 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39695 : Route 9 := (fun mask => (mask,id))

def c39695 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39695 : Upper (D 6) (R 6) [40,96,384,17,6] 13 := by
  apply FastRouting.sound _ _ [40,96,384,17,6] 13 (by decide) (choices 1) [1,2,4,64] r39695 c39695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26288
  · exact u26289
  · exact u26290
  · exact u26291

def b39696 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 41 98 388 25 81 38 70 134 262), lower := (rows 41 98 388 25 81 32 64 128 256), losses := [] }

theorem u39696 : Upper (D 6) (R 6) [40,96,384,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39696 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39697 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 388 25 82 39 71 135 263), lower := (rows 41 98 388 25 82 32 64 128 256), losses := [] }

theorem u39697 : Upper (D 6) (R 6) [40,96,384,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39697 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39698 : Route 9 := (fun mask => (mask,id))

def c39698 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39698 : Upper (D 6) (R 6) [40,96,384,17,68] 13 := by
  apply FastRouting.sound _ _ [40,96,384,17,68] 13 (by decide) (choices 1) [1,2,4] r39698 c39698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26292
  · exact u26293
  · exact u26294

def b39699 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 98 388 26 19 101 69 197 325), lower := (rows 41 98 388 26 19 32 64 128 256), losses := [] }

theorem u39699 : Upper (D 6) (R 6) [40,96,384,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39699 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39700 : Route 9 := (fun mask => (mask,id))

def c39700 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39700 : Upper (D 6) (R 6) [40,96,384,18,5] 13 := by
  apply FastRouting.sound _ _ [40,96,384,18,5] 13 (by decide) (choices 1) [1,2,4,64] r39700 c39700
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26295
  · exact u26296
  · exact u26297
  · exact u26298

def b39701 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 98 388 26 22 101 69 197 325), lower := (rows 41 98 388 26 22 32 64 128 256), losses := [] }

theorem u39701 : Upper (D 6) (R 6) [40,96,384,18,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39702 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 388 26 81 39 71 135 263), lower := (rows 41 98 388 26 81 32 64 128 256), losses := [] }

theorem u39702 : Upper (D 6) (R 6) [40,96,384,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39702 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39703 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 41 98 388 26 82 37 69 133 261), lower := (rows 41 98 388 26 82 32 64 128 256), losses := [] }

theorem u39703 : Upper (D 6) (R 6) [40,96,384,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39703 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39704 : Route 9 := (fun mask => (mask,id))

def c39704 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39704 : Upper (D 6) (R 6) [40,96,384,18,68] 13 := by
  apply FastRouting.sound _ _ [40,96,384,18,68] 13 (by decide) (choices 1) [1,2,4] r39704 c39704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26299
  · exact u26300
  · exact u26301

def r39705 : Route 9 := (fun mask => (mask,id))

def c39705 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39705 : Upper (D 6) (R 6) [40,96,384,20,3] 13 := by
  apply FastRouting.sound _ _ [40,96,384,20,3] 13 (by decide) (choices 1) [1,2,4,64] r39705 c39705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26302
  · exact u26303
  · exact u26304
  · exact u26305

def b39706 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 98 388 28 21 99 67 195 323), lower := (rows 41 98 388 28 21 32 64 128 256), losses := [] }

theorem u39706 : Upper (D 6) (R 6) [40,96,384,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39706 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39707 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 98 388 28 22 99 67 195 323), lower := (rows 41 98 388 28 22 32 64 128 256), losses := [] }

theorem u39707 : Upper (D 6) (R 6) [40,96,384,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39707 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39708 : Route 9 := (fun mask => (mask,id))

def c39708 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39708 : Upper (D 6) (R 6) [40,96,384,20,65] 13 := by
  apply FastRouting.sound _ _ [40,96,384,20,65] 13 (by decide) (choices 1) [1,2,4] r39708 c39708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26306
  · exact u26307
  · exact u26308

def b39709 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 98 388 28 82 39 71 135 263), lower := (rows 41 98 388 28 82 32 64 128 256), losses := [] }

theorem u39709 : Upper (D 6) (R 6) [40,96,384,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39709 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39710 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 98 388 28 84 35 67 131 259), lower := (rows 41 98 388 28 84 32 64 128 256), losses := [] }

theorem u39710 : Upper (D 6) (R 6) [40,96,384,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39711 : PairBound 9 := { available := 23, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 4, region := 388, targets := 64 }], pairs := [(2,5),(2,6),(3,5)], upper := (rows 41 98 388 76 19 55 87 151 279), lower := (rows 41 98 388 76 19 32 64 128 256), losses := [] }

theorem u39711 : Upper (D 6) (R 6) [40,96,384,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39711 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39712 : Route 9 := (fun mask => (mask,id))

def c39712 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39712 : Upper (D 6) (R 6) [40,96,384,68,5] 13 := by
  apply FastRouting.sound _ _ [40,96,384,68,5] 13 (by decide) (choices 1) [1,2,16] r39712 c39712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26309
  · exact u26310
  · exact u26311

def r39713 : Route 9 := (fun mask => (mask,id))

def c39713 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39713 : Upper (D 6) (R 6) [40,96,384,68,6] 13 := by
  apply FastRouting.sound _ _ [40,96,384,68,6] 13 (by decide) (choices 1) [1,2,16] r39713 c39713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26312
  · exact u26313
  · exact u26314

def b39714 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 388 88 19 39 71 135 263), lower := (rows 41 98 388 88 19 32 64 128 256), losses := [] }

theorem u39714 : Upper (D 6) (R 6) [40,96,384,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39714 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39715 : Route 9 := (fun mask => (mask,id))

def c39715 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39715 : Upper (D 6) (R 6) [40,96,384,80,5] 13 := by
  apply FastRouting.sound _ _ [40,96,384,80,5] 13 (by decide) (choices 1) [1,2,4] r39715 c39715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26315
  · exact u26316
  · exact u26317

def r39716 : Route 9 := (fun mask => (mask,id))

def c39716 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39716 : Upper (D 6) (R 6) [40,96,384,80,6] 13 := by
  apply FastRouting.sound _ _ [40,96,384,80,6] 13 (by decide) (choices 1) [1,2,4] r39716 c39716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26318
  · exact u26319
  · exact u26320

def b39717 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 16, targets := 96 },{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5),(4,5),(4,6)], upper := (rows 41 131 261 14 22 112 112 240 368), lower := (rows 41 131 261 14 22 32 64 128 256), losses := [] }

theorem u39717 : Upper (D 6) (R 6) [40,129,257,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39717 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39718 : Route 9 := (fun mask => (mask,id))

def c39718 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39718 : Upper (D 6) (R 6) [40,129,257,6,34] 13 := by
  apply FastRouting.sound _ _ [40,129,257,6,34] 13 (by decide) (choices 1) [4,16,64] r39718 c39718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26321
  · exact u26322
  · exact u26323

def r39719 : Route 9 := (fun mask => (mask,id))

def c39719 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39719 : Upper (D 6) (R 6) [40,129,257,6,66] 13 := by
  apply FastRouting.sound _ _ [40,129,257,6,66] 13 (by decide) (choices 1) [4,16,64] r39719 c39719
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26324
  · exact u26325
  · exact u26326

#print axioms u39719
end Delivery.IrregularNine14.P06
