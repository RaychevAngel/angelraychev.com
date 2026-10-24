import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0032

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8760 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 76 152 400 37 101 165 293), lower := (rows 35 67 76 152 400 32 64 128 256), losses := [] }

theorem u8760 : Upper (D 8) (R 8) [34,65,72,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8760 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8761 : PairBound 9 := { available := 308, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 76 168 145 308 372 436 308), lower := (rows 35 67 76 168 145 32 64 128 256), losses := [] }

theorem u8761 : Upper (D 8) (R 8) [34,65,72,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8761 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8762 : PairBound 9 := { available := 305, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 76 168 148 305 369 433 305), lower := (rows 35 67 76 168 148 32 64 128 256), losses := [] }

theorem u8762 : Upper (D 8) (R 8) [34,65,72,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8762 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8763 : PairBound 9 := { available := 277, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 67 76 168 176 309 341 405 277), lower := (rows 35 67 76 168 176 32 64 128 256), losses := [] }

theorem u8763 : Upper (D 8) (R 8) [34,65,72,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8763 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8764 : PairBound 9 := { available := 180, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 76 168 273 180 244 180 436), lower := (rows 35 67 76 168 273 32 64 128 256), losses := [] }

theorem u8764 : Upper (D 8) (R 8) [34,65,72,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8764 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8765 : Route 9 := (fun mask => (mask,id))

def c8765 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8765 : Upper (D 8) (R 8) [34,65,72,160,260] 13 := by
  apply FastRouting.sound _ _ [34,65,72,160,260] 13 (by decide) (choices 1) [1,16,128] r8765 c8765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1940
  · exact u1941
  · exact u1942

def r8766 : Route 9 := (fun mask => (mask,id))

def c8766 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8766 : Upper (D 8) (R 8) [34,65,72,160,288] 13 := by
  apply FastRouting.sound _ _ [34,65,72,160,288] 13 (by decide) (choices 1) [1,4,16,128] r8766 c8766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1943
  · exact u1944
  · exact u1945
  · exact u1946

def r8767 : Route 9 := (fun mask => (mask,id))

def c8767 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8767 : Upper (D 8) (R 8) [34,65,72,160,384] 13 := by
  apply FastRouting.sound _ _ [34,65,72,160,384] 13 (by decide) (choices 1) [1,4,16] r8767 c8767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1947
  · exact u1948
  · exact u1949

def b8768 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 76 265 148 176 240 176 432), lower := (rows 35 67 76 265 148 32 64 128 256), losses := [] }

theorem u8768 : Upper (D 8) (R 8) [34,65,72,257,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8768 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8769 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 76 265 176 180 244 180 436), lower := (rows 35 67 76 265 176 32 64 128 256), losses := [] }

theorem u8769 : Upper (D 8) (R 8) [34,65,72,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8769 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8770 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 268 176 177 241 177 433), lower := (rows 35 67 76 268 176 32 64 128 256), losses := [] }

theorem u8770 : Upper (D 8) (R 8) [34,65,72,260,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8770 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8771 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 76 280 145 164 228 164 420), lower := (rows 35 67 76 280 145 32 64 128 256), losses := [] }

theorem u8771 : Upper (D 8) (R 8) [34,65,72,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8771 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8772 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 280 148 161 225 161 417), lower := (rows 35 67 76 280 148 32 64 128 256), losses := [] }

theorem u8772 : Upper (D 8) (R 8) [34,65,72,272,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8772 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8773 : Route 9 := (fun mask => (mask,id))

def c8773 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8773 : Upper (D 8) (R 8) [34,65,72,272,160] 13 := by
  apply FastRouting.sound _ _ [34,65,72,272,160] 13 (by decide) (choices 1) [1,4,128] r8773 c8773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1950
  · exact u1951
  · exact u1952

def b8774 : PairBound 9 := { available := 180, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 76 296 145 180 244 180 436), lower := (rows 35 67 76 296 145 32 64 128 256), losses := [] }

theorem u8774 : Upper (D 8) (R 8) [34,65,72,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8774 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8775 : Route 9 := (fun mask => (mask,id))

def c8775 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8775 : Upper (D 8) (R 8) [34,65,72,288,132] 13 := by
  apply FastRouting.sound _ _ [34,65,72,288,132] 13 (by decide) (choices 1) [1,16,128] r8775 c8775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1953
  · exact u1954
  · exact u1955

def r8776 : Route 9 := (fun mask => (mask,id))

def c8776 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8776 : Upper (D 8) (R 8) [34,65,72,288,160] 13 := by
  apply FastRouting.sound _ _ [34,65,72,288,160] 13 (by decide) (choices 1) [1,4,16,128] r8776 c8776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1956
  · exact u1957
  · exact u1958
  · exact u1959

def b8777 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 76 392 145 52 116 180 308), lower := (rows 35 67 76 392 145 32 64 128 256), losses := [] }

theorem u8777 : Upper (D 8) (R 8) [34,65,72,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8777 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8778 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 76 392 148 49 113 177 305), lower := (rows 35 67 76 392 148 32 64 128 256), losses := [] }

theorem u8778 : Upper (D 8) (R 8) [34,65,72,384,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8778 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8779 : Route 9 := (fun mask => (mask,id))

def c8779 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8779 : Upper (D 8) (R 8) [34,65,72,384,160] 13 := by
  apply FastRouting.sound _ _ [34,65,72,384,160] 13 (by decide) (choices 1) [1,4,16] r8779 c8779
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1960
  · exact u1961
  · exact u1962

def b8780 : PairBound 9 := { available := 281, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 140 176 313 345 409 281), lower := (rows 35 67 100 140 176 32 64 128 256), losses := [] }

theorem u8780 : Upper (D 8) (R 8) [34,65,96,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8780 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8781 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 140 280 177 241 177 433), lower := (rows 35 67 100 140 280 32 64 128 256), losses := [] }

theorem u8781 : Upper (D 8) (R 8) [34,65,96,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8781 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8782 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 140 304 185 217 153 409), lower := (rows 35 67 100 140 304 32 64 128 256), losses := [] }

theorem u8782 : Upper (D 8) (R 8) [34,65,96,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8782 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8783 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 140 400 57 121 185 313), lower := (rows 35 67 100 140 400 32 64 128 256), losses := [] }

theorem u8783 : Upper (D 8) (R 8) [34,65,96,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8783 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8784 : PairBound 9 := { available := 169, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 152 276 169 233 169 425), lower := (rows 35 67 100 152 276 32 64 128 256), losses := [] }

theorem u8784 : Upper (D 8) (R 8) [34,65,96,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8784 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8785 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 152 280 165 229 165 421), lower := (rows 35 67 100 152 280 32 64 128 256), losses := [] }

theorem u8785 : Upper (D 8) (R 8) [34,65,96,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8785 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8786 : PairBound 9 := { available := 141, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 152 304 173 205 141 397), lower := (rows 35 67 100 152 304 32 64 128 256), losses := [] }

theorem u8786 : Upper (D 8) (R 8) [34,65,96,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8786 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8787 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 168 276 185 217 153 409), lower := (rows 35 67 100 168 276 32 64 128 256), losses := [] }

theorem u8787 : Upper (D 8) (R 8) [34,65,96,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8787 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8788 : PairBound 9 := { available := 149, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 168 280 181 213 149 405), lower := (rows 35 67 100 168 280 32 64 128 256), losses := [] }

theorem u8788 : Upper (D 8) (R 8) [34,65,96,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8788 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8789 : PairBound 9 := { available := 29, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 168 400 61 93 157 285), lower := (rows 35 67 100 168 400 32 64 128 256), losses := [] }

theorem u8789 : Upper (D 8) (R 8) [34,65,96,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8789 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8790 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 133 140 280 112 112 240 368), lower := (rows 35 67 133 140 280 32 64 128 256), losses := [] }

theorem u8790 : Upper (D 8) (R 8) [34,65,129,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8790 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8791 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 133 140 304 120 120 248 376), lower := (rows 35 67 133 140 304 32 64 128 256), losses := [] }

theorem u8791 : Upper (D 8) (R 8) [34,65,129,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8791 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8792 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 133 140 336 56 120 184 312), lower := (rows 35 67 133 140 336 32 64 128 256), losses := [] }

theorem u8792 : Upper (D 8) (R 8) [34,65,129,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8792 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8793 : PairBound 9 := { available := 104, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 133 152 276 104 104 232 360), lower := (rows 35 67 133 152 276 32 64 128 256), losses := [] }

theorem u8793 : Upper (D 8) (R 8) [34,65,129,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8793 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8794 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 133 152 280 100 100 228 356), lower := (rows 35 67 133 152 280 32 64 128 256), losses := [] }

theorem u8794 : Upper (D 8) (R 8) [34,65,129,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8794 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8795 : PairBound 9 := { available := 108, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 133 152 304 108 108 236 364), lower := (rows 35 67 133 152 304 32 64 128 256), losses := [] }

theorem u8795 : Upper (D 8) (R 8) [34,65,129,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8795 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8796 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 133 152 336 44 108 172 300), lower := (rows 35 67 133 152 336 32 64 128 256), losses := [] }

theorem u8796 : Upper (D 8) (R 8) [34,65,129,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8796 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8797 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 133 168 276 120 120 248 376), lower := (rows 35 67 133 168 276 32 64 128 256), losses := [] }

theorem u8797 : Upper (D 8) (R 8) [34,65,129,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8797 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8798 : PairBound 9 := { available := 116, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 133 168 280 116 116 244 372), lower := (rows 35 67 133 168 280 32 64 128 256), losses := [] }

theorem u8798 : Upper (D 8) (R 8) [34,65,129,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8798 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8799 : PairBound 9 := { available := 92, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 133 168 304 124 92 220 348), lower := (rows 35 67 133 168 304 32 64 128 256), losses := [] }

theorem u8799 : Upper (D 8) (R 8) [34,65,129,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8799 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8800 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 133 168 336 60 124 188 316), lower := (rows 35 67 133 168 336 32 64 128 256), losses := [] }

theorem u8800 : Upper (D 8) (R 8) [34,65,129,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8800 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8801 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 133 200 276 56 120 184 312), lower := (rows 35 67 133 200 276 32 64 128 256), losses := [] }

theorem u8801 : Upper (D 8) (R 8) [34,65,129,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8801 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8802 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 133 200 280 52 116 180 308), lower := (rows 35 67 133 200 280 32 64 128 256), losses := [] }

theorem u8802 : Upper (D 8) (R 8) [34,65,129,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8802 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8803 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 133 200 304 60 124 188 316), lower := (rows 35 67 133 200 304 32 64 128 256), losses := [] }

theorem u8803 : Upper (D 8) (R 8) [34,65,129,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8803 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8804 : PairBound 9 := { available := 113, camps := [{ cop := 7, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 140 140 304 113 113 241 369), lower := (rows 35 67 140 140 304 32 64 128 256), losses := [] }

theorem u8804 : Upper (D 8) (R 8) [34,65,136,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8804 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8805 : PairBound 9 := { available := 49, camps := [{ cop := 7, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 140 140 336 49 113 177 305), lower := (rows 35 67 140 140 336 32 64 128 256), losses := [] }

theorem u8805 : Upper (D 8) (R 8) [34,65,136,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8805 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8806 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 152 276 97 97 225 353), lower := (rows 35 67 140 152 276 32 64 128 256), losses := [] }

theorem u8806 : Upper (D 8) (R 8) [34,65,136,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8806 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8807 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 152 304 101 101 229 357), lower := (rows 35 67 140 152 304 32 64 128 256), losses := [] }

theorem u8807 : Upper (D 8) (R 8) [34,65,136,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8807 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8808 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 152 336 37 101 165 293), lower := (rows 35 67 140 152 336 32 64 128 256), losses := [] }

theorem u8808 : Upper (D 8) (R 8) [34,65,136,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8808 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8809 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 168 276 113 113 241 369), lower := (rows 35 67 140 168 276 32 64 128 256), losses := [] }

theorem u8809 : Upper (D 8) (R 8) [34,65,136,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8809 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8810 : PairBound 9 := { available := 85, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 168 304 117 85 213 341), lower := (rows 35 67 140 168 304 32 64 128 256), losses := [] }

theorem u8810 : Upper (D 8) (R 8) [34,65,136,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8810 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8811 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 168 336 53 117 181 309), lower := (rows 35 67 140 168 336 32 64 128 256), losses := [] }

theorem u8811 : Upper (D 8) (R 8) [34,65,136,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8811 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8812 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 200 276 49 113 177 305), lower := (rows 35 67 140 200 276 32 64 128 256), losses := [] }

theorem u8812 : Upper (D 8) (R 8) [34,65,136,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8812 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8813 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 200 304 53 117 181 309), lower := (rows 35 67 140 200 304 32 64 128 256), losses := [] }

theorem u8813 : Upper (D 8) (R 8) [34,65,136,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8813 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8814 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 140 265 176 116 116 244 372), lower := (rows 35 67 140 265 176 32 64 128 256), losses := [] }

theorem u8814 : Upper (D 8) (R 8) [34,65,136,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8814 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8815 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 140 265 208 52 116 180 308), lower := (rows 35 67 140 265 208 32 64 128 256), losses := [] }

theorem u8815 : Upper (D 8) (R 8) [34,65,136,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8815 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8816 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 268 176 113 113 241 369), lower := (rows 35 67 140 268 176 32 64 128 256), losses := [] }

theorem u8816 : Upper (D 8) (R 8) [34,65,136,260,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8816 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8817 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 268 208 49 113 177 305), lower := (rows 35 67 140 268 208 32 64 128 256), losses := [] }

theorem u8817 : Upper (D 8) (R 8) [34,65,136,260,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8817 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8818 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 280 176 101 101 229 357), lower := (rows 35 67 140 280 176 32 64 128 256), losses := [] }

theorem u8818 : Upper (D 8) (R 8) [34,65,136,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8818 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8819 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 280 208 37 101 165 293), lower := (rows 35 67 140 280 208 32 64 128 256), losses := [] }

theorem u8819 : Upper (D 8) (R 8) [34,65,136,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8819 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u8819
end Delivery.IrregularNine14.P08
