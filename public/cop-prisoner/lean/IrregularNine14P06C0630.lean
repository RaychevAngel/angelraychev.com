import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0388
import IrregularNine14P06C0389
import IrregularNine14P06C0390

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r37800 : Route 9 := (fun mask => (mask,id))

def c37800 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37800 : Upper (D 6) (R 6) [34,132,257,65,66] 13 := by
  apply FastRouting.sound _ _ [34,132,257,65,66] 13 (by decide) (choices 1) [4,8,16] r37800 c37800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23318
  · exact u23319
  · exact u23320

def r37801 : Route 9 := (fun mask => (mask,id))

def c37801 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37801 : Upper (D 6) (R 6) [34,132,257,65,68] 13 := by
  apply FastRouting.sound _ _ [34,132,257,65,68] 13 (by decide) (choices 1) [2,8,16] r37801 c37801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23321
  · exact u23322
  · exact u23323

def b37802 : PairBound 9 := { available := 54, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 35 134 261 73 88 54 118 182 310), lower := (rows 35 134 261 73 88 32 64 128 256), losses := [] }

theorem u37802 : Upper (D 6) (R 6) [34,132,257,65,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37802 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37803 : Route 9 := (fun mask => (mask,id))

def c37803 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37803 : Upper (D 6) (R 6) [34,132,257,65,96] 13 := by
  apply FastRouting.sound _ _ [34,132,257,65,96] 13 (by decide) (choices 1) [2,4,8,16] r37803 c37803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23324
  · exact u23325
  · exact u23326
  · exact u23327

def r37804 : Route 9 := (fun mask => (mask,id))

def c37804 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37804 : Upper (D 6) (R 6) [34,132,257,66,68] 13 := by
  apply FastRouting.sound _ _ [34,132,257,66,68] 13 (by decide) (choices 1) [1,8,16] r37804 c37804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23328
  · exact u23329
  · exact u23330

def b37805 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 35 134 261 74 88 53 117 181 309), lower := (rows 35 134 261 74 88 32 64 128 256), losses := [] }

theorem u37805 : Upper (D 6) (R 6) [34,132,257,66,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37805 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37806 : Route 9 := (fun mask => (mask,id))

def c37806 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37806 : Upper (D 6) (R 6) [34,132,257,66,96] 13 := by
  apply FastRouting.sound _ _ [34,132,257,66,96] 13 (by decide) (choices 1) [1,4,8,16] r37806 c37806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23331
  · exact u23332
  · exact u23333
  · exact u23334

def b37807 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 35 134 261 76 88 51 115 179 307), lower := (rows 35 134 261 76 88 32 64 128 256), losses := [] }

theorem u37807 : Upper (D 6) (R 6) [34,132,257,68,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37807 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37808 : Route 9 := (fun mask => (mask,id))

def c37808 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37808 : Upper (D 6) (R 6) [34,132,257,68,96] 13 := by
  apply FastRouting.sound _ _ [34,132,257,68,96] 13 (by decide) (choices 1) [1,2,8,16] r37808 c37808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23335
  · exact u23336
  · exact u23337
  · exact u23338

def b37809 : PairBound 9 := { available := 39, camps := [{ cop := 6, region := 24, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 134 261 88 88 39 103 167 295), lower := (rows 35 134 261 88 88 32 64 128 256), losses := [] }

theorem u37809 : Upper (D 6) (R 6) [34,132,257,80,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37809 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37810 : PairBound 9 := { available := 15, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 134 261 88 112 47 79 143 271), lower := (rows 35 134 261 88 112 32 64 128 256), losses := [] }

theorem u37810 : Upper (D 6) (R 6) [34,132,257,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37810 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37811 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 16, targets := 6 },{ cop := 3, region := 16, targets := 32 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 35 134 262 13 25 112 112 240 368), lower := (rows 35 134 262 13 25 32 64 128 256), losses := [] }

theorem u37811 : Upper (D 6) (R 6) [34,132,258,5,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37811 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37812 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 134 262 13 49 120 88 216 344), lower := (rows 35 134 262 13 49 32 64 128 256), losses := [] }

theorem u37812 : Upper (D 6) (R 6) [34,132,258,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37812 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37813 : Route 9 := (fun mask => (mask,id))

def c37813 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37813 : Upper (D 6) (R 6) [34,132,258,5,40] 13 := by
  apply FastRouting.sound _ _ [34,132,258,5,40] 13 (by decide) (choices 1) [1,16,64] r37813 c37813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23339
  · exact u23340
  · exact u23341

def r37814 : Route 9 := (fun mask => (mask,id))

def c37814 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37814 : Upper (D 6) (R 6) [34,132,258,5,65] 13 := by
  apply FastRouting.sound _ _ [34,132,258,5,65] 13 (by decide) (choices 1) [8,16,64] r37814 c37814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23342
  · exact u23343
  · exact u23344

def r37815 : Route 9 := (fun mask => (mask,id))

def c37815 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37815 : Upper (D 6) (R 6) [34,132,258,5,72] 13 := by
  apply FastRouting.sound _ _ [34,132,258,5,72] 13 (by decide) (choices 1) [1,16,64] r37815 c37815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23345
  · exact u23346
  · exact u23347

def r37816 : Route 9 := (fun mask => (mask,id))

def c37816 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37816 : Upper (D 6) (R 6) [34,132,258,5,96] 13 := by
  apply FastRouting.sound _ _ [34,132,258,5,96] 13 (by decide) (choices 1) [1,8,16,64] r37816 c37816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23348
  · exact u23349
  · exact u23350
  · exact u23351

def b37817 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 24, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 134 262 25 25 100 100 228 356), lower := (rows 35 134 262 25 25 32 64 128 256), losses := [] }

theorem u37817 : Upper (D 6) (R 6) [34,132,258,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37818 : Route 9 := (fun mask => (mask,id))

def c37818 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37818 : Upper (D 6) (R 6) [34,132,258,17,12] 13 := by
  apply FastRouting.sound _ _ [34,132,258,17,12] 13 (by decide) (choices 1) [1,64] r37818 c37818
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23352
  · exact u23353

def b37819 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 134 262 25 49 108 76 204 332), lower := (rows 35 134 262 25 49 32 64 128 256), losses := [] }

theorem u37819 : Upper (D 6) (R 6) [34,132,258,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37819 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37820 : Route 9 := (fun mask => (mask,id))

def c37820 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37820 : Upper (D 6) (R 6) [34,132,258,17,36] 13 := by
  apply FastRouting.sound _ _ [34,132,258,17,36] 13 (by decide) (choices 1) [1,8,64] r37820 c37820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23354
  · exact u23355
  · exact u23356

def b37821 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 134 262 25 56 101 69 197 325), lower := (rows 35 134 262 25 56 32 64 128 256), losses := [] }

theorem u37821 : Upper (D 6) (R 6) [34,132,258,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37821 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37822 : PairBound 9 := { available := 108, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 134 262 25 81 108 108 236 364), lower := (rows 35 134 262 25 81 32 64 128 256), losses := [] }

theorem u37822 : Upper (D 6) (R 6) [34,132,258,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37822 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37823 : Route 9 := (fun mask => (mask,id))

def c37823 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37823 : Upper (D 6) (R 6) [34,132,258,17,68] 13 := by
  apply FastRouting.sound _ _ [34,132,258,17,68] 13 (by decide) (choices 1) [1,8,64] r37823 c37823
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23357
  · exact u23358
  · exact u23359

def r37824 : Route 9 := (fun mask => (mask,id))

def c37824 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37824 : Upper (D 6) (R 6) [34,132,258,17,72] 13 := by
  apply FastRouting.sound _ _ [34,132,258,17,72] 13 (by decide) (choices 1) [1,4,64] r37824 c37824
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23360
  · exact u23361
  · exact u23362

def r37825 : Route 9 := (fun mask => (mask,id))

def c37825 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37825 : Upper (D 6) (R 6) [34,132,258,17,96] 13 := by
  apply FastRouting.sound _ _ [34,132,258,17,96] 13 (by decide) (choices 1) [1,4,8,64] r37825 c37825
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23363
  · exact u23364
  · exact u23365
  · exact u23366

def b37826 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 134 262 28 49 105 73 201 329), lower := (rows 35 134 262 28 49 32 64 128 256), losses := [] }

theorem u37826 : Upper (D 6) (R 6) [34,132,258,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37826 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37827 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 35 134 262 28 56 97 65 193 321), lower := (rows 35 134 262 28 56 32 64 128 256), losses := [] }

theorem u37827 : Upper (D 6) (R 6) [34,132,258,20,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37827 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37828 : Route 9 := (fun mask => (mask,id))

def c37828 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37828 : Upper (D 6) (R 6) [34,132,258,20,65] 13 := by
  apply FastRouting.sound _ _ [34,132,258,20,65] 13 (by decide) (choices 1) [1,8,64] r37828 c37828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23367
  · exact u23368
  · exact u23369

def r37829 : Route 9 := (fun mask => (mask,id))

def c37829 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37829 : Upper (D 6) (R 6) [34,132,258,20,72] 13 := by
  apply FastRouting.sound _ _ [34,132,258,20,72] 13 (by decide) (choices 1) [1,64] r37829 c37829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23370
  · exact u23371

def r37830 : Route 9 := (fun mask => (mask,id))

def c37830 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37830 : Upper (D 6) (R 6) [34,132,258,20,96] 13 := by
  apply FastRouting.sound _ _ [34,132,258,20,96] 13 (by decide) (choices 1) [1,8,64] r37830 c37830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23372
  · exact u23373
  · exact u23374

def b37831 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 134 262 41 81 124 92 220 348), lower := (rows 35 134 262 41 81 32 64 128 256), losses := [] }

theorem u37831 : Upper (D 6) (R 6) [34,132,258,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37831 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37832 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 134 262 41 84 121 89 217 345), lower := (rows 35 134 262 41 84 32 64 128 256), losses := [] }

theorem u37832 : Upper (D 6) (R 6) [34,132,258,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37832 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37833 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 134 262 41 88 117 85 213 341), lower := (rows 35 134 262 41 88 32 64 128 256), losses := [] }

theorem u37833 : Upper (D 6) (R 6) [34,132,258,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37833 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37834 : Route 9 := (fun mask => (mask,id))

def c37834 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37834 : Upper (D 6) (R 6) [34,132,258,36,65] 13 := by
  apply FastRouting.sound _ _ [34,132,258,36,65] 13 (by decide) (choices 1) [1,8,16,64] r37834 c37834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23375
  · exact u23376
  · exact u23377
  · exact u23378

def r37835 : Route 9 := (fun mask => (mask,id))

def c37835 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37835 : Upper (D 6) (R 6) [34,132,258,36,72] 13 := by
  apply FastRouting.sound _ _ [34,132,258,36,72] 13 (by decide) (choices 1) [1,16,64] r37835 c37835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23379
  · exact u23380
  · exact u23381

def r37836 : Route 9 := (fun mask => (mask,id))

def c37836 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37836 : Upper (D 6) (R 6) [34,132,258,48,65] 13 := by
  apply FastRouting.sound _ _ [34,132,258,48,65] 13 (by decide) (choices 1) [1,4,8,64] r37836 c37836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23382
  · exact u23383
  · exact u23384
  · exact u23385

def r37837 : Route 9 := (fun mask => (mask,id))

def c37837 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37837 : Upper (D 6) (R 6) [34,132,258,48,68] 13 := by
  apply FastRouting.sound _ _ [34,132,258,48,68] 13 (by decide) (choices 1) [1,8,64] r37837 c37837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23386
  · exact u23387
  · exact u23388

def r37838 : Route 9 := (fun mask => (mask,id))

def c37838 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37838 : Upper (D 6) (R 6) [34,132,258,48,72] 13 := by
  apply FastRouting.sound _ _ [34,132,258,48,72] 13 (by decide) (choices 1) [1,4,64] r37838 c37838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23389
  · exact u23390
  · exact u23391

def b37839 : PairBound 9 := { available := 60, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 35 134 262 73 81 60 124 188 316), lower := (rows 35 134 262 73 81 32 64 128 256), losses := [] }

theorem u37839 : Upper (D 6) (R 6) [34,132,258,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37839 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37840 : Route 9 := (fun mask => (mask,id))

def c37840 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37840 : Upper (D 6) (R 6) [34,132,258,65,68] 13 := by
  apply FastRouting.sound _ _ [34,132,258,65,68] 13 (by decide) (choices 1) [1,8,16] r37840 c37840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23392
  · exact u23393
  · exact u23394

def b37841 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 35 134 262 73 88 53 117 181 309), lower := (rows 35 134 262 73 88 32 64 128 256), losses := [] }

theorem u37841 : Upper (D 6) (R 6) [34,132,258,65,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37841 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37842 : Route 9 := (fun mask => (mask,id))

def c37842 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37842 : Upper (D 6) (R 6) [34,132,258,65,96] 13 := by
  apply FastRouting.sound _ _ [34,132,258,65,96] 13 (by decide) (choices 1) [1,4,8,16] r37842 c37842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23395
  · exact u23396
  · exact u23397
  · exact u23398

def b37843 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 35 134 262 76 88 49 113 177 305), lower := (rows 35 134 262 76 88 32 64 128 256), losses := [] }

theorem u37843 : Upper (D 6) (R 6) [34,132,258,68,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37843 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37844 : Route 9 := (fun mask => (mask,id))

def c37844 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37844 : Upper (D 6) (R 6) [34,132,258,68,96] 13 := by
  apply FastRouting.sound _ _ [34,132,258,68,96] 13 (by decide) (choices 1) [1,8,16] r37844 c37844
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23399
  · exact u23400
  · exact u23401

def b37845 : PairBound 9 := { available := 37, camps := [{ cop := 6, region := 24, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 134 262 88 88 37 101 165 293), lower := (rows 35 134 262 88 88 32 64 128 256), losses := [] }

theorem u37845 : Upper (D 6) (R 6) [34,132,258,80,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37845 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37846 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 134 262 88 112 45 77 141 269), lower := (rows 35 134 262 88 112 32 64 128 256), losses := [] }

theorem u37846 : Upper (D 6) (R 6) [34,132,258,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37846 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37847 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 1, region := 113, targets := 4 }], pairs := [(0,2),(4,5),(4,6)], upper := (rows 35 134 268 13 19 112 112 240 368), lower := (rows 35 134 268 13 19 32 64 128 256), losses := [] }

theorem u37847 : Upper (D 6) (R 6) [34,132,264,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37847 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37848 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 134 268 13 49 114 82 210 338), lower := (rows 35 134 268 13 49 32 64 128 256), losses := [] }

theorem u37848 : Upper (D 6) (R 6) [34,132,264,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37848 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37849 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 0, region := 16, targets := 1 }], pairs := [(0,2),(4,0),(4,2)], upper := (rows 35 134 268 13 50 113 81 209 337), lower := (rows 35 134 268 13 50 32 64 128 256), losses := [] }

theorem u37849 : Upper (D 6) (R 6) [34,132,264,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37850 : Route 9 := (fun mask => (mask,id))

def c37850 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37850 : Upper (D 6) (R 6) [34,132,264,5,65] 13 := by
  apply FastRouting.sound _ _ [34,132,264,5,65] 13 (by decide) (choices 1) [2,16,64] r37850 c37850
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23402
  · exact u23403
  · exact u23404

def r37851 : Route 9 := (fun mask => (mask,id))

def c37851 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37851 : Upper (D 6) (R 6) [34,132,264,5,66] 13 := by
  apply FastRouting.sound _ _ [34,132,264,5,66] 13 (by decide) (choices 1) [1,16,64] r37851 c37851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23405
  · exact u23406
  · exact u23407

def r37852 : Route 9 := (fun mask => (mask,id))

def c37852 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37852 : Upper (D 6) (R 6) [34,132,264,5,96] 13 := by
  apply FastRouting.sound _ _ [34,132,264,5,96] 13 (by decide) (choices 1) [1,2,16,64] r37852 c37852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23408
  · exact u23409
  · exact u23410
  · exact u23411

def b37853 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 268 25 19 100 100 228 356), lower := (rows 35 134 268 25 19 32 64 128 256), losses := [] }

theorem u37853 : Upper (D 6) (R 6) [34,132,264,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37853 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37854 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 134 268 25 21 98 98 226 354), lower := (rows 35 134 268 25 21 32 64 128 256), losses := [] }

theorem u37854 : Upper (D 6) (R 6) [34,132,264,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37854 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37855 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 35 134 268 25 22 97 97 225 353), lower := (rows 35 134 268 25 22 32 64 128 256), losses := [] }

theorem u37855 : Upper (D 6) (R 6) [34,132,264,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37855 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37856 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 134 268 25 49 102 70 198 326), lower := (rows 35 134 268 25 49 32 64 128 256), losses := [] }

theorem u37856 : Upper (D 6) (R 6) [34,132,264,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37856 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37857 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 134 268 25 50 101 69 197 325), lower := (rows 35 134 268 25 50 32 64 128 256), losses := [] }

theorem u37857 : Upper (D 6) (R 6) [34,132,264,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37857 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37858 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 35 134 268 25 52 99 67 195 323), lower := (rows 35 134 268 25 52 32 64 128 256), losses := [] }

theorem u37858 : Upper (D 6) (R 6) [34,132,264,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37858 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37859 : PairBound 9 := { available := 102, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 134 268 25 81 102 102 230 358), lower := (rows 35 134 268 25 81 32 64 128 256), losses := [] }

theorem u37859 : Upper (D 6) (R 6) [34,132,264,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37859 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u37859
end Delivery.IrregularNine14.P06
