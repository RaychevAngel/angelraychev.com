import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0387
import IrregularNine14P06C0388

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b37740 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 134 100 76 273 59 91 155 283), lower := (rows 35 134 100 76 273 32 64 128 256), losses := [] }

theorem u37740 : Upper (D 6) (R 6) [34,132,96,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37740 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37741 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 134 100 76 274 57 89 153 281), lower := (rows 35 134 100 76 274 32 64 128 256), losses := [] }

theorem u37741 : Upper (D 6) (R 6) [34,132,96,68,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37741 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37742 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 134 100 76 280 51 83 147 275), lower := (rows 35 134 100 76 280 32 64 128 256), losses := [] }

theorem u37742 : Upper (D 6) (R 6) [34,132,96,68,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37742 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37743 : Route 9 := (fun mask => (mask,id))

def c37743 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37743 : Upper (D 6) (R 6) [34,132,96,80,257] 13 := by
  apply FastRouting.sound _ _ [34,132,96,80,257] 13 (by decide) (choices 1) [1,2,4,8] r37743 c37743
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23232
  · exact u23233
  · exact u23234
  · exact u23235

def r37744 : Route 9 := (fun mask => (mask,id))

def c37744 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37744 : Upper (D 6) (R 6) [34,132,96,80,258] 13 := by
  apply FastRouting.sound _ _ [34,132,96,80,258] 13 (by decide) (choices 1) [1,4,8] r37744 c37744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23236
  · exact u23237
  · exact u23238

def r37745 : Route 9 := (fun mask => (mask,id))

def c37745 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37745 : Upper (D 6) (R 6) [34,132,96,80,260] 13 := by
  apply FastRouting.sound _ _ [34,132,96,80,260] 13 (by decide) (choices 1) [1,2,8] r37745 c37745
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23239
  · exact u23240
  · exact u23241

def r37746 : Route 9 := (fun mask => (mask,id))

def c37746 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37746 : Upper (D 6) (R 6) [34,132,96,80,264] 13 := by
  apply FastRouting.sound _ _ [34,132,96,80,264] 13 (by decide) (choices 1) [1,2,4] r37746 c37746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23242
  · exact u23243
  · exact u23244

def b37747 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 261 11 28 112 112 240 368), lower := (rows 35 134 261 11 28 32 64 128 256), losses := [] }

theorem u37747 : Upper (D 6) (R 6) [34,132,257,3,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37747 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37748 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 261 11 52 120 88 216 344), lower := (rows 35 134 261 11 52 32 64 128 256), losses := [] }

theorem u37748 : Upper (D 6) (R 6) [34,132,257,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37748 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37749 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 134 261 11 56 116 84 212 340), lower := (rows 35 134 261 11 56 32 64 128 256), losses := [] }

theorem u37749 : Upper (D 6) (R 6) [34,132,257,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37749 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37750 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 261 11 84 120 120 248 376), lower := (rows 35 134 261 11 84 32 64 128 256), losses := [] }

theorem u37750 : Upper (D 6) (R 6) [34,132,257,3,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37750 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37751 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 261 11 88 116 116 244 372), lower := (rows 35 134 261 11 88 32 64 128 256), losses := [] }

theorem u37751 : Upper (D 6) (R 6) [34,132,257,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37751 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37752 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 261 11 112 124 92 220 348), lower := (rows 35 134 261 11 112 32 64 128 256), losses := [] }

theorem u37752 : Upper (D 6) (R 6) [34,132,257,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37752 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37753 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 134 261 13 26 112 112 240 368), lower := (rows 35 134 261 13 26 32 64 128 256), losses := [] }

theorem u37753 : Upper (D 6) (R 6) [34,132,257,5,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37753 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37754 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 134 261 13 56 114 82 210 338), lower := (rows 35 134 261 13 56 32 64 128 256), losses := [] }

theorem u37754 : Upper (D 6) (R 6) [34,132,257,5,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37754 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37755 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 134 261 13 82 120 120 248 376), lower := (rows 35 134 261 13 82 32 64 128 256), losses := [] }

theorem u37755 : Upper (D 6) (R 6) [34,132,257,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37755 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37756 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 134 261 13 88 114 114 242 370), lower := (rows 35 134 261 13 88 32 64 128 256), losses := [] }

theorem u37756 : Upper (D 6) (R 6) [34,132,257,5,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37756 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37757 : PairBound 9 := { available := 90, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 134 261 13 112 122 90 218 346), lower := (rows 35 134 261 13 112 32 64 128 256), losses := [] }

theorem u37757 : Upper (D 6) (R 6) [34,132,257,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37757 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37758 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 261 14 25 112 112 240 368), lower := (rows 35 134 261 14 25 32 64 128 256), losses := [] }

theorem u37758 : Upper (D 6) (R 6) [34,132,257,6,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37758 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37759 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 261 14 56 113 81 209 337), lower := (rows 35 134 261 14 56 32 64 128 256), losses := [] }

theorem u37759 : Upper (D 6) (R 6) [34,132,257,6,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37759 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37760 : PairBound 9 := { available := 120, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 261 14 81 120 120 248 376), lower := (rows 35 134 261 14 81 32 64 128 256), losses := [] }

theorem u37760 : Upper (D 6) (R 6) [34,132,257,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37760 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37761 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 261 14 88 113 113 241 369), lower := (rows 35 134 261 14 88 32 64 128 256), losses := [] }

theorem u37761 : Upper (D 6) (R 6) [34,132,257,6,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37761 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37762 : PairBound 9 := { available := 89, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 261 14 112 121 89 217 345), lower := (rows 35 134 261 14 112 32 64 128 256), losses := [] }

theorem u37762 : Upper (D 6) (R 6) [34,132,257,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37762 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37763 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 261 25 26 100 100 228 356), lower := (rows 35 134 261 25 26 32 64 128 256), losses := [] }

theorem u37763 : Upper (D 6) (R 6) [34,132,257,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37763 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37764 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 134 261 25 28 98 98 226 354), lower := (rows 35 134 261 25 28 32 64 128 256), losses := [] }

theorem u37764 : Upper (D 6) (R 6) [34,132,257,17,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37764 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37765 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 134 261 25 50 108 76 204 332), lower := (rows 35 134 261 25 50 32 64 128 256), losses := [] }

theorem u37765 : Upper (D 6) (R 6) [34,132,257,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37765 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37766 : Route 9 := (fun mask => (mask,id))

def c37766 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37766 : Upper (D 6) (R 6) [34,132,257,17,36] 13 := by
  apply FastRouting.sound _ _ [34,132,257,17,36] 13 (by decide) (choices 1) [2,8,64] r37766 c37766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23245
  · exact u23246
  · exact u23247

def b37767 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 134 261 25 56 102 70 198 326), lower := (rows 35 134 261 25 56 32 64 128 256), losses := [] }

theorem u37767 : Upper (D 6) (R 6) [34,132,257,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37767 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37768 : Route 9 := (fun mask => (mask,id))

def c37768 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37768 : Upper (D 6) (R 6) [34,132,257,17,66] 13 := by
  apply FastRouting.sound _ _ [34,132,257,17,66] 13 (by decide) (choices 1) [4,8,64] r37768 c37768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23248
  · exact u23249
  · exact u23250

def r37769 : Route 9 := (fun mask => (mask,id))

def c37769 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37769 : Upper (D 6) (R 6) [34,132,257,17,68] 13 := by
  apply FastRouting.sound _ _ [34,132,257,17,68] 13 (by decide) (choices 1) [2,8,64] r37769 c37769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23251
  · exact u23252
  · exact u23253

def r37770 : Route 9 := (fun mask => (mask,id))

def c37770 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37770 : Upper (D 6) (R 6) [34,132,257,17,72] 13 := by
  apply FastRouting.sound _ _ [34,132,257,17,72] 13 (by decide) (choices 1) [2,4,64] r37770 c37770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23254
  · exact u23255
  · exact u23256

def r37771 : Route 9 := (fun mask => (mask,id))

def c37771 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37771 : Upper (D 6) (R 6) [34,132,257,17,96] 13 := by
  apply FastRouting.sound _ _ [34,132,257,17,96] 13 (by decide) (choices 1) [2,4,8,64] r37771 c37771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23257
  · exact u23258
  · exact u23259
  · exact u23260

def b37772 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 261 26 28 97 97 225 353), lower := (rows 35 134 261 26 28 32 64 128 256), losses := [] }

theorem u37772 : Upper (D 6) (R 6) [34,132,257,18,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37772 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37773 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 134 261 26 49 108 76 204 332), lower := (rows 35 134 261 26 49 32 64 128 256), losses := [] }

theorem u37773 : Upper (D 6) (R 6) [34,132,257,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37774 : Route 9 := (fun mask => (mask,id))

def c37774 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37774 : Upper (D 6) (R 6) [34,132,257,18,36] 13 := by
  apply FastRouting.sound _ _ [34,132,257,18,36] 13 (by decide) (choices 1) [1,8,64] r37774 c37774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23261
  · exact u23262
  · exact u23263

def b37775 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 134 261 26 56 101 69 197 325), lower := (rows 35 134 261 26 56 32 64 128 256), losses := [] }

theorem u37775 : Upper (D 6) (R 6) [34,132,257,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37776 : Route 9 := (fun mask => (mask,id))

def c37776 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37776 : Upper (D 6) (R 6) [34,132,257,18,65] 13 := by
  apply FastRouting.sound _ _ [34,132,257,18,65] 13 (by decide) (choices 1) [4,8,64] r37776 c37776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23264
  · exact u23265
  · exact u23266

def r37777 : Route 9 := (fun mask => (mask,id))

def c37777 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37777 : Upper (D 6) (R 6) [34,132,257,18,68] 13 := by
  apply FastRouting.sound _ _ [34,132,257,18,68] 13 (by decide) (choices 1) [1,8,64] r37777 c37777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23267
  · exact u23268
  · exact u23269

def r37778 : Route 9 := (fun mask => (mask,id))

def c37778 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37778 : Upper (D 6) (R 6) [34,132,257,18,72] 13 := by
  apply FastRouting.sound _ _ [34,132,257,18,72] 13 (by decide) (choices 1) [1,4,64] r37778 c37778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23270
  · exact u23271
  · exact u23272

def r37779 : Route 9 := (fun mask => (mask,id))

def c37779 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37779 : Upper (D 6) (R 6) [34,132,257,18,96] 13 := by
  apply FastRouting.sound _ _ [34,132,257,18,96] 13 (by decide) (choices 1) [1,4,8,64] r37779 c37779
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23273
  · exact u23274
  · exact u23275
  · exact u23276

def b37780 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 134 261 28 49 106 74 202 330), lower := (rows 35 134 261 28 49 32 64 128 256), losses := [] }

theorem u37780 : Upper (D 6) (R 6) [34,132,257,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37780 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37781 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 134 261 28 50 105 73 201 329), lower := (rows 35 134 261 28 50 32 64 128 256), losses := [] }

theorem u37781 : Upper (D 6) (R 6) [34,132,257,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37782 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 35 134 261 28 56 99 67 195 323), lower := (rows 35 134 261 28 56 32 64 128 256), losses := [] }

theorem u37782 : Upper (D 6) (R 6) [34,132,257,20,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37782 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37783 : Route 9 := (fun mask => (mask,id))

def c37783 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37783 : Upper (D 6) (R 6) [34,132,257,20,65] 13 := by
  apply FastRouting.sound _ _ [34,132,257,20,65] 13 (by decide) (choices 1) [2,8,64] r37783 c37783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23277
  · exact u23278
  · exact u23279

def r37784 : Route 9 := (fun mask => (mask,id))

def c37784 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37784 : Upper (D 6) (R 6) [34,132,257,20,66] 13 := by
  apply FastRouting.sound _ _ [34,132,257,20,66] 13 (by decide) (choices 1) [1,8,64] r37784 c37784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23280
  · exact u23281
  · exact u23282

def r37785 : Route 9 := (fun mask => (mask,id))

def c37785 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37785 : Upper (D 6) (R 6) [34,132,257,20,72] 13 := by
  apply FastRouting.sound _ _ [34,132,257,20,72] 13 (by decide) (choices 1) [1,2,64] r37785 c37785
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23283
  · exact u23284
  · exact u23285

def r37786 : Route 9 := (fun mask => (mask,id))

def c37786 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37786 : Upper (D 6) (R 6) [34,132,257,20,96] 13 := by
  apply FastRouting.sound _ _ [34,132,257,20,96] 13 (by decide) (choices 1) [1,2,8,64] r37786 c37786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23286
  · exact u23287
  · exact u23288
  · exact u23289

def b37787 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 134 261 41 82 124 92 220 348), lower := (rows 35 134 261 41 82 32 64 128 256), losses := [] }

theorem u37787 : Upper (D 6) (R 6) [34,132,257,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37787 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37788 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 134 261 41 84 122 90 218 346), lower := (rows 35 134 261 41 84 32 64 128 256), losses := [] }

theorem u37788 : Upper (D 6) (R 6) [34,132,257,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37788 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37789 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 134 261 41 88 118 86 214 342), lower := (rows 35 134 261 41 88 32 64 128 256), losses := [] }

theorem u37789 : Upper (D 6) (R 6) [34,132,257,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37789 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37790 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 134 261 42 81 124 92 220 348), lower := (rows 35 134 261 42 81 32 64 128 256), losses := [] }

theorem u37790 : Upper (D 6) (R 6) [34,132,257,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37790 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37791 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 134 261 42 84 121 89 217 345), lower := (rows 35 134 261 42 84 32 64 128 256), losses := [] }

theorem u37791 : Upper (D 6) (R 6) [34,132,257,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37792 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 134 261 42 88 117 85 213 341), lower := (rows 35 134 261 42 88 32 64 128 256), losses := [] }

theorem u37792 : Upper (D 6) (R 6) [34,132,257,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37792 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37793 : Route 9 := (fun mask => (mask,id))

def c37793 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37793 : Upper (D 6) (R 6) [34,132,257,36,65] 13 := by
  apply FastRouting.sound _ _ [34,132,257,36,65] 13 (by decide) (choices 1) [2,8,16,64] r37793 c37793
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23290
  · exact u23291
  · exact u23292
  · exact u23293

def r37794 : Route 9 := (fun mask => (mask,id))

def c37794 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37794 : Upper (D 6) (R 6) [34,132,257,36,66] 13 := by
  apply FastRouting.sound _ _ [34,132,257,36,66] 13 (by decide) (choices 1) [1,8,16,64] r37794 c37794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23294
  · exact u23295
  · exact u23296
  · exact u23297

def r37795 : Route 9 := (fun mask => (mask,id))

def c37795 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37795 : Upper (D 6) (R 6) [34,132,257,36,72] 13 := by
  apply FastRouting.sound _ _ [34,132,257,36,72] 13 (by decide) (choices 1) [1,2,16,64] r37795 c37795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23298
  · exact u23299
  · exact u23300
  · exact u23301

def r37796 : Route 9 := (fun mask => (mask,id))

def c37796 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37796 : Upper (D 6) (R 6) [34,132,257,48,65] 13 := by
  apply FastRouting.sound _ _ [34,132,257,48,65] 13 (by decide) (choices 1) [2,4,8,64] r37796 c37796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23302
  · exact u23303
  · exact u23304
  · exact u23305

def r37797 : Route 9 := (fun mask => (mask,id))

def c37797 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37797 : Upper (D 6) (R 6) [34,132,257,48,66] 13 := by
  apply FastRouting.sound _ _ [34,132,257,48,66] 13 (by decide) (choices 1) [1,4,8,64] r37797 c37797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23306
  · exact u23307
  · exact u23308
  · exact u23309

def r37798 : Route 9 := (fun mask => (mask,id))

def c37798 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37798 : Upper (D 6) (R 6) [34,132,257,48,68] 13 := by
  apply FastRouting.sound _ _ [34,132,257,48,68] 13 (by decide) (choices 1) [1,2,8,64] r37798 c37798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23310
  · exact u23311
  · exact u23312
  · exact u23313

def r37799 : Route 9 := (fun mask => (mask,id))

def c37799 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37799 : Upper (D 6) (R 6) [34,132,257,48,72] 13 := by
  apply FastRouting.sound _ _ [34,132,257,48,72] 13 (by decide) (choices 1) [1,2,4,64] r37799 c37799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23314
  · exact u23315
  · exact u23316
  · exact u23317

#print axioms u37799
end Delivery.IrregularNine14.P06
