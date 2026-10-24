import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0353
import IrregularNine14P06C0354

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r36660 : Route 9 := (fun mask => (mask,id))

def c36660 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36660 : Upper (D 6) (R 6) [34,72,130,20,320] 13 := by
  apply FastRouting.sound _ _ [34,72,130,20,320] 13 (by decide) (choices 1) [1,4] r36660 c36660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21194
  · exact u21195

def b36661 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 360, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 35 74 134 44 21 369 337 465 337), lower := (rows 35 74 134 44 21 32 64 128 256), losses := [] }

theorem u36661 : Upper (D 6) (R 6) [34,72,130,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36661 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36662 : Route 9 := (fun mask => (mask,id))

def c36662 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36662 : Upper (D 6) (R 6) [34,72,130,36,65] 13 := by
  apply FastRouting.sound _ _ [34,72,130,36,65] 13 (by decide) (choices 1) [1,4,16,256] r36662 c36662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21196
  · exact u21197
  · exact u21198
  · exact u21199

def r36663 : Route 9 := (fun mask => (mask,id))

def c36663 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36663 : Upper (D 6) (R 6) [34,72,130,36,68] 13 := by
  apply FastRouting.sound _ _ [34,72,130,36,68] 13 (by decide) (choices 1) [1,16,256] r36663 c36663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21200
  · exact u21201
  · exact u21202

def r36664 : Route 9 := (fun mask => (mask,id))

def c36664 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36664 : Upper (D 6) (R 6) [34,72,130,36,257] 13 := by
  apply FastRouting.sound _ _ [34,72,130,36,257] 13 (by decide) (choices 1) [1,4,16,64] r36664 c36664
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21203
  · exact u21204
  · exact u21205
  · exact u21206

def r36665 : Route 9 := (fun mask => (mask,id))

def c36665 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36665 : Upper (D 6) (R 6) [34,72,130,36,260] 13 := by
  apply FastRouting.sound _ _ [34,72,130,36,260] 13 (by decide) (choices 1) [1,16,64] r36665 c36665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21207
  · exact u21208
  · exact u21209

def r36666 : Route 9 := (fun mask => (mask,id))

def c36666 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36666 : Upper (D 6) (R 6) [34,72,130,36,320] 13 := by
  apply FastRouting.sound _ _ [34,72,130,36,320] 13 (by decide) (choices 1) [1,4,16] r36666 c36666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21210
  · exact u21211
  · exact u21212

def b36667 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 360, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 35 74 134 56 21 357 325 453 325), lower := (rows 35 74 134 56 21 32 64 128 256), losses := [] }

theorem u36667 : Upper (D 6) (R 6) [34,72,130,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36667 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36668 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 35 74 134 56 81 293 325 389 261), lower := (rows 35 74 134 56 81 32 64 128 256), losses := [] }

theorem u36668 : Upper (D 6) (R 6) [34,72,130,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36668 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36669 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 35 74 134 56 84 293 325 389 261), lower := (rows 35 74 134 56 84 32 64 128 256), losses := [] }

theorem u36669 : Upper (D 6) (R 6) [34,72,130,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36669 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36670 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 74 134 56 273 101 69 197 325), lower := (rows 35 74 134 56 273 32 64 128 256), losses := [{ target := 5, region := (rows 1 10 13 8 17 0 81 145 273), good := (rows 471 78 134 478 469 0 64 128 256) }] }

theorem u36670 : Upper (D 6) (R 6) [34,72,130,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36670 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36671 : Route 9 := (fun mask => (mask,id))

def c36671 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36671 : Upper (D 6) (R 6) [34,72,130,48,260] 13 := by
  apply FastRouting.sound _ _ [34,72,130,48,260] 13 (by decide) (choices 1) [1,4,64] r36671 c36671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21213
  · exact u21214
  · exact u21215

def b36672 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 35 74 134 56 336 37 69 133 261), lower := (rows 35 74 134 56 336 32 64 128 256), losses := [] }

theorem u36672 : Upper (D 6) (R 6) [34,72,130,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36672 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36673 : Route 9 := (fun mask => (mask,id))

def c36673 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36673 : Upper (D 6) (R 6) [34,72,130,257,5] 13 := by
  apply FastRouting.sound _ _ [34,72,130,257,5] 13 (by decide) (choices 1) [4,16,64] r36673 c36673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21216
  · exact u21217
  · exact u21218

def b36674 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 74 134 265 49 116 84 212 340), lower := (rows 35 74 134 265 49 32 64 128 256), losses := [] }

theorem u36674 : Upper (D 6) (R 6) [34,72,130,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36674 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36675 : Route 9 := (fun mask => (mask,id))

def c36675 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36675 : Upper (D 6) (R 6) [34,72,130,257,36] 13 := by
  apply FastRouting.sound _ _ [34,72,130,257,36] 13 (by decide) (choices 1) [1,4,16,64] r36675 c36675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21219
  · exact u21220
  · exact u21221
  · exact u21222

def r36676 : Route 9 := (fun mask => (mask,id))

def c36676 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36676 : Upper (D 6) (R 6) [34,72,130,257,65] 13 := by
  apply FastRouting.sound _ _ [34,72,130,257,65] 13 (by decide) (choices 1) [4,16] r36676 c36676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21223
  · exact u21224

def r36677 : Route 9 := (fun mask => (mask,id))

def c36677 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36677 : Upper (D 6) (R 6) [34,72,130,257,68] 13 := by
  apply FastRouting.sound _ _ [34,72,130,257,68] 13 (by decide) (choices 1) [1,4,16] r36677 c36677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21225
  · exact u21226
  · exact u21227

def r36678 : Route 9 := (fun mask => (mask,id))

def c36678 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36678 : Upper (D 6) (R 6) [34,72,130,257,96] 13 := by
  apply FastRouting.sound _ _ [34,72,130,257,96] 13 (by decide) (choices 1) [1,4,16] r36678 c36678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21228
  · exact u21229
  · exact u21230

def r36679 : Route 9 := (fun mask => (mask,id))

def c36679 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36679 : Upper (D 6) (R 6) [34,72,130,260,5] 13 := by
  apply FastRouting.sound _ _ [34,72,130,260,5] 13 (by decide) (choices 1) [1,16,64] r36679 c36679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21231
  · exact u21232
  · exact u21233

def b36680 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 74 134 268 49 117 85 213 341), lower := (rows 35 74 134 268 49 32 64 128 256), losses := [] }

theorem u36680 : Upper (D 6) (R 6) [34,72,130,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36680 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36681 : Route 9 := (fun mask => (mask,id))

def c36681 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36681 : Upper (D 6) (R 6) [34,72,130,260,36] 13 := by
  apply FastRouting.sound _ _ [34,72,130,260,36] 13 (by decide) (choices 1) [1,16,64] r36681 c36681
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21234
  · exact u21235
  · exact u21236

def r36682 : Route 9 := (fun mask => (mask,id))

def c36682 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36682 : Upper (D 6) (R 6) [34,72,130,260,65] 13 := by
  apply FastRouting.sound _ _ [34,72,130,260,65] 13 (by decide) (choices 1) [1,4,16] r36682 c36682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21237
  · exact u21238
  · exact u21239

def r36683 : Route 9 := (fun mask => (mask,id))

def c36683 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36683 : Upper (D 6) (R 6) [34,72,130,260,68] 13 := by
  apply FastRouting.sound _ _ [34,72,130,260,68] 13 (by decide) (choices 1) [1,16] r36683 c36683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21240
  · exact u21241

def r36684 : Route 9 := (fun mask => (mask,id))

def c36684 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36684 : Upper (D 6) (R 6) [34,72,130,260,96] 13 := by
  apply FastRouting.sound _ _ [34,72,130,260,96] 13 (by decide) (choices 1) [1,4,16] r36684 c36684
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21242
  · exact u21243
  · exact u21244

def r36685 : Route 9 := (fun mask => (mask,id))

def c36685 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36685 : Upper (D 6) (R 6) [34,72,130,272,5] 13 := by
  apply FastRouting.sound _ _ [34,72,130,272,5] 13 (by decide) (choices 1) [1,4,64] r36685 c36685
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21245
  · exact u21246
  · exact u21247

def b36686 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 74 134 280 49 101 69 197 325), lower := (rows 35 74 134 280 49 32 64 128 256), losses := [] }

theorem u36686 : Upper (D 6) (R 6) [34,72,130,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36686 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36687 : Route 9 := (fun mask => (mask,id))

def c36687 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36687 : Upper (D 6) (R 6) [34,72,130,272,36] 13 := by
  apply FastRouting.sound _ _ [34,72,130,272,36] 13 (by decide) (choices 1) [1,4,64] r36687 c36687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21248
  · exact u21249
  · exact u21250

def b36688 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 74 134 280 81 37 101 165 293), lower := (rows 35 74 134 280 81 32 64 128 256), losses := [{ target := 6, region := (rows 7 2 7 24 16 55 0 151 279), good := (rows 423 431 423 440 445 32 0 128 256) }] }

theorem u36688 : Upper (D 6) (R 6) [34,72,130,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36688 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36689 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 74 134 280 84 37 101 165 293), lower := (rows 35 74 134 280 84 32 64 128 256), losses := [{ target := 6, region := (rows 7 2 7 24 16 55 0 151 279), good := (rows 423 431 423 440 445 32 0 128 256) }] }

theorem u36689 : Upper (D 6) (R 6) [34,72,130,272,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36689 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36690 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 0, region := 132, targets := 32 }], pairs := [(0,6),(2,5),(2,6)], upper := (rows 35 74 134 280 112 37 69 133 261), lower := (rows 35 74 134 280 112 32 64 128 256), losses := [] }

theorem u36690 : Upper (D 6) (R 6) [34,72,130,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36690 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36691 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 4, region := 360, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 35 74 134 296 21 117 85 213 341), lower := (rows 35 74 134 296 21 32 64 128 256), losses := [] }

theorem u36691 : Upper (D 6) (R 6) [34,72,130,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36691 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36692 : Route 9 := (fun mask => (mask,id))

def c36692 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36692 : Upper (D 6) (R 6) [34,72,130,288,65] 13 := by
  apply FastRouting.sound _ _ [34,72,130,288,65] 13 (by decide) (choices 1) [1,4,16] r36692 c36692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21251
  · exact u21252
  · exact u21253

def r36693 : Route 9 := (fun mask => (mask,id))

def c36693 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36693 : Upper (D 6) (R 6) [34,72,130,288,68] 13 := by
  apply FastRouting.sound _ _ [34,72,130,288,68] 13 (by decide) (choices 1) [1,4,16] r36693 c36693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21254
  · exact u21255
  · exact u21256

def b36694 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 148 13 19 356 356 484 356), lower := (rows 35 74 148 13 19 32 64 128 256), losses := [] }

theorem u36694 : Upper (D 6) (R 6) [34,72,144,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36694 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36695 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 35 74 148 13 21 354 354 482 354), lower := (rows 35 74 148 13 21 32 64 128 256), losses := [] }

theorem u36695 : Upper (D 6) (R 6) [34,72,144,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36695 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36696 : Route 9 := (fun mask => (mask,id))

def c36696 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u36696 : Upper (D 6) (R 6) [34,72,144,5,6] 13 := by
  apply FastRouting.sound _ _ [34,72,144,5,6] 13 (by decide) (choices 1) [1,64,256] r36696 c36696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21257
  · exact u21258
  · exact u21259

def b36697 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 74 148 13 49 358 326 454 326), lower := (rows 35 74 148 13 49 32 64 128 256), losses := [] }

theorem u36697 : Upper (D 6) (R 6) [34,72,144,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36697 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36698 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 74 148 13 50 357 325 453 325), lower := (rows 35 74 148 13 50 32 64 128 256), losses := [] }

theorem u36698 : Upper (D 6) (R 6) [34,72,144,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36698 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36699 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 355, targets := 4 },{ cop := 3, region := 322, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 74 148 13 52 355 323 451 323), lower := (rows 35 74 148 13 52 32 64 128 256), losses := [] }

theorem u36699 : Upper (D 6) (R 6) [34,72,144,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36699 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36700 : Route 9 := (fun mask => (mask,id))

def c36700 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36700 : Upper (D 6) (R 6) [34,72,144,5,65] 13 := by
  apply FastRouting.sound _ _ [34,72,144,5,65] 13 (by decide) (choices 1) [2,4,256] r36700 c36700
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21260
  · exact u21261
  · exact u21262

def b36701 : PairBound 9 := { available := 293, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 148 13 82 293 357 421 293), lower := (rows 35 74 148 13 82 32 64 128 256), losses := [] }

theorem u36701 : Upper (D 6) (R 6) [34,72,144,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36702 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 355, targets := 4 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 74 148 13 84 291 355 419 291), lower := (rows 35 74 148 13 84 32 64 128 256), losses := [] }

theorem u36702 : Upper (D 6) (R 6) [34,72,144,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36702 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36703 : Route 9 := (fun mask => (mask,id))

def c36703 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36703 : Upper (D 6) (R 6) [34,72,144,5,96] 13 := by
  apply FastRouting.sound _ _ [34,72,144,5,96] 13 (by decide) (choices 1) [1,2,4,256] r36703 c36703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21263
  · exact u21264
  · exact u21265
  · exact u21266

def r36704 : Route 9 := (fun mask => (mask,id))

def c36704 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36704 : Upper (D 6) (R 6) [34,72,144,5,257] 13 := by
  apply FastRouting.sound _ _ [34,72,144,5,257] 13 (by decide) (choices 1) [2,4,64] r36704 c36704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21267
  · exact u21268
  · exact u21269

def r36705 : Route 9 := (fun mask => (mask,id))

def c36705 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36705 : Upper (D 6) (R 6) [34,72,144,5,258] 13 := by
  apply FastRouting.sound _ _ [34,72,144,5,258] 13 (by decide) (choices 1) [1,4,64] r36705 c36705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21270
  · exact u21271
  · exact u21272

def r36706 : Route 9 := (fun mask => (mask,id))

def c36706 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36706 : Upper (D 6) (R 6) [34,72,144,5,260] 13 := by
  apply FastRouting.sound _ _ [34,72,144,5,260] 13 (by decide) (choices 1) [1,2,64] r36706 c36706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21273
  · exact u21274
  · exact u21275

def r36707 : Route 9 := (fun mask => (mask,id))

def c36707 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36707 : Upper (D 6) (R 6) [34,72,144,5,288] 13 := by
  apply FastRouting.sound _ _ [34,72,144,5,288] 13 (by decide) (choices 1) [1,2,4,64] r36707 c36707
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21276
  · exact u21277
  · exact u21278
  · exact u21279

def r36708 : Route 9 := (fun mask => (mask,id))

def c36708 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36708 : Upper (D 6) (R 6) [34,72,144,5,320] 13 := by
  apply FastRouting.sound _ _ [34,72,144,5,320] 13 (by decide) (choices 1) [1,2,4] r36708 c36708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21280
  · exact u21281
  · exact u21282

def b36709 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 353, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 148 14 21 353 353 481 353), lower := (rows 35 74 148 14 21 32 64 128 256), losses := [] }

theorem u36709 : Upper (D 6) (R 6) [34,72,144,6,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36709 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36710 : PairBound 9 := { available := 325, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 74 148 14 49 357 325 453 325), lower := (rows 35 74 148 14 49 32 64 128 256), losses := [] }

theorem u36710 : Upper (D 6) (R 6) [34,72,144,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36711 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 353, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 148 14 52 353 321 449 321), lower := (rows 35 74 148 14 52 32 64 128 256), losses := [] }

theorem u36711 : Upper (D 6) (R 6) [34,72,144,6,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36711 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36712 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 289, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 74 148 14 81 293 357 421 293), lower := (rows 35 74 148 14 81 32 64 128 256), losses := [] }

theorem u36712 : Upper (D 6) (R 6) [34,72,144,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36712 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36713 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 10, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 148 14 84 289 353 417 289), lower := (rows 35 74 148 14 84 32 64 128 256), losses := [] }

theorem u36713 : Upper (D 6) (R 6) [34,72,144,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36713 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36714 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 289, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 74 148 14 112 293 325 389 261), lower := (rows 35 74 148 14 112 32 64 128 256), losses := [] }

theorem u36714 : Upper (D 6) (R 6) [34,72,144,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36714 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36715 : Route 9 := (fun mask => (mask,id))

def c36715 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36715 : Upper (D 6) (R 6) [34,72,144,6,257] 13 := by
  apply FastRouting.sound _ _ [34,72,144,6,257] 13 (by decide) (choices 1) [1,4,64] r36715 c36715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21283
  · exact u21284
  · exact u21285

def b36716 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 97, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 148 14 276 97 97 225 353), lower := (rows 35 74 148 14 276 32 64 128 256), losses := [] }

theorem u36716 : Upper (D 6) (R 6) [34,72,144,6,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36716 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36717 : Route 9 := (fun mask => (mask,id))

def c36717 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36717 : Upper (D 6) (R 6) [34,72,144,6,288] 13 := by
  apply FastRouting.sound _ _ [34,72,144,6,288] 13 (by decide) (choices 1) [1,4,64] r36717 c36717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21286
  · exact u21287
  · exact u21288

def b36718 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 74 148 14 336 37 101 165 293), lower := (rows 35 74 148 14 336 32 64 128 256), losses := [] }

theorem u36718 : Upper (D 6) (R 6) [34,72,144,6,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36719 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 35 74 148 44 19 357 325 453 325), lower := (rows 35 74 148 44 19 32 64 128 256), losses := [] }

theorem u36719 : Upper (D 6) (R 6) [34,72,144,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36719 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u36719
end Delivery.IrregularNine14.P06
