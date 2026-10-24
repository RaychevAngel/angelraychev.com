import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0011

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8760 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 76 265 176 34 80 131 259), lower := (rows 37 194 76 265 176 34 80 128 256), losses := [] }

theorem u8760 : Upper (D 7) (R 7) [36,192,72,257,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8760 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8761 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 117, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 194 76 266 19 48 65 160 416), lower := (rows 37 194 76 266 19 48 65 128 256), losses := [] }

theorem u8761 : Upper (D 7) (R 7) [36,192,72,258,3,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8761 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8762 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 117, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 194 76 266 19 48 96 129 385), lower := (rows 37 194 76 266 19 48 96 128 256), losses := [] }

theorem u8762 : Upper (D 7) (R 7) [36,192,72,258,3,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8762 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8763 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 76 266 19 48 192 161 289), lower := (rows 37 194 76 266 19 48 192 128 256), losses := [] }

theorem u8763 : Upper (D 7) (R 7) [36,192,72,258,3,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8763 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8764 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 424, targets := 65 }], pairs := [(0,1),(2,1),(3,0),(3,6)], upper := (rows 37 194 76 266 19 160 65 176 304), lower := (rows 37 194 76 266 19 160 65 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 178 93 144 272), good := (rows 101 224 77 365 497 160 65 160 256) }] }

theorem u8764 : Upper (D 7) (R 7) [36,192,72,258,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8764 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8765 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 161, targets := 66 },{ cop := 4, region := 424, targets := 64 }], pairs := [(0,1),(0,6),(3,6)], upper := (rows 37 194 76 266 19 160 80 161 289), lower := (rows 37 194 76 266 19 160 80 128 256), losses := [] }

theorem u8765 : Upper (D 7) (R 7) [36,192,72,258,3,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8765 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8766 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 264, targets := 32 },{ cop := 4, region := 264, targets := 64 },{ cop := 4, region := 264, targets := 128 },{ cop := 5, region := 66, targets := 1 }], pairs := [(1,0),(3,5),(3,6),(3,7)], upper := (rows 37 194 76 266 19 160 96 145 273), lower := (rows 37 194 76 266 19 160 96 128 256), losses := [] }

theorem u8766 : Upper (D 7) (R 7) [36,192,72,258,3,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8766 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8767 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 117, targets := 128 },{ cop := 4, region := 392, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 37 194 76 266 50 33 65 144 400), lower := (rows 37 194 76 266 50 33 65 128 256), losses := [] }

theorem u8767 : Upper (D 7) (R 7) [36,192,72,258,34,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8767 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8768 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 117, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 194 76 266 50 33 80 129 385), lower := (rows 37 194 76 266 50 33 80 128 256), losses := [] }

theorem u8768 : Upper (D 7) (R 7) [36,192,72,258,34,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8768 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8769 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 76 266 50 33 192 145 273), lower := (rows 37 194 76 266 50 33 192 128 256), losses := [] }

theorem u8769 : Upper (D 7) (R 7) [36,192,72,258,34,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8769 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8770 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 177, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 194 76 266 145 33 66 176 304), lower := (rows 37 194 76 266 145 33 66 128 256), losses := [] }

theorem u8770 : Upper (D 7) (R 7) [36,192,72,258,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8770 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8771 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 76 266 145 33 80 162 290), lower := (rows 37 194 76 266 145 33 80 128 256), losses := [] }

theorem u8771 : Upper (D 7) (R 7) [36,192,72,258,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8771 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8772 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 76 266 145 33 96 146 274), lower := (rows 37 194 76 266 145 33 96 128 256), losses := [] }

theorem u8772 : Upper (D 7) (R 7) [36,192,72,258,129,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8772 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8773 : Route 9 := (fun mask => (mask,id))

def c8773 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8773 : Upper (D 7) (R 7) [36,192,72,258,129,16,1] 13 := by
  apply FastRouting.sound _ _ [36,192,72,258,129,16,1] 13 (by decide) (choices 1) [2,32] r8773 c8773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u698
  · exact u699

def b8774 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 177, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 194 76 266 145 48 66 161 289), lower := (rows 37 194 76 266 145 48 66 128 256), losses := [] }

theorem u8774 : Upper (D 7) (R 7) [36,192,72,258,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8774 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8775 : Route 9 := (fun mask => (mask,id))

def c8775 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8775 : Upper (D 7) (R 7) [36,192,72,258,129,16,32] 13 := by
  apply FastRouting.sound _ _ [36,192,72,258,129,16,32] 13 (by decide) (choices 1) [1,2] r8775 c8775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u700
  · exact u701

def b8776 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 76 266 176 33 65 146 274), lower := (rows 37 194 76 266 176 33 65 128 256), losses := [] }

theorem u8776 : Upper (D 7) (R 7) [36,192,72,258,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8776 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8777 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 177, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 194 76 266 176 33 66 145 273), lower := (rows 37 194 76 266 176 33 66 128 256), losses := [] }

theorem u8777 : Upper (D 7) (R 7) [36,192,72,258,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8777 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8778 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 76 266 176 33 80 131 259), lower := (rows 37 194 76 266 176 33 80 128 256), losses := [] }

theorem u8778 : Upper (D 7) (R 7) [36,192,72,258,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8778 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8779 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 424, targets := 65 },{ cop := 2, region := 162, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(3,6)], upper := (rows 37 194 76 280 19 34 65 160 416), lower := (rows 37 194 76 280 19 34 65 128 256), losses := [{ target := 1, region := (rows 1 0 28 24 16 32 81 161 289), good := (rows 485 192 76 348 477 416 449 128 256) }] }

theorem u8779 : Upper (D 7) (R 7) [36,192,72,272,3,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8779 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8780 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 392, targets := 34 },{ cop := 4, region := 392, targets := 64 },{ cop := 7, region := 98, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,6)], upper := (rows 37 194 76 280 19 34 96 129 385), lower := (rows 37 194 76 280 19 34 96 128 256), losses := [] }

theorem u8780 : Upper (D 7) (R 7) [36,192,72,272,3,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8780 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8781 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 76 280 19 34 192 161 289), lower := (rows 37 194 76 280 19 34 192 128 256), losses := [] }

theorem u8781 : Upper (D 7) (R 7) [36,192,72,272,3,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8781 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8782 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 424, targets := 65 },{ cop := 2, region := 162, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(3,6)], upper := (rows 37 194 76 280 19 160 65 162 290), lower := (rows 37 194 76 280 19 160 65 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 162 81 128 256), good := (rows 101 224 76 348 113 160 65 160 256) }] }

theorem u8782 : Upper (D 7) (R 7) [36,192,72,272,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8782 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8783 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 161, targets := 66 },{ cop := 4, region := 424, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 194 76 280 19 160 66 161 289), lower := (rows 37 194 76 280 19 160 66 128 256), losses := [] }

theorem u8783 : Upper (D 7) (R 7) [36,192,72,272,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8783 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8784 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 264, targets := 32 },{ cop := 4, region := 264, targets := 64 },{ cop := 4, region := 264, targets := 128 },{ cop := 5, region := 66, targets := 1 }], pairs := [(1,0),(3,5),(3,6),(3,7)], upper := (rows 37 194 76 280 19 160 96 131 259), lower := (rows 37 194 76 280 19 160 96 128 256), losses := [] }

theorem u8784 : Upper (D 7) (R 7) [36,192,72,272,3,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8784 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8785 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 162, targets := 1 },{ cop := 4, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(2,1),(3,0)], upper := (rows 37 194 76 280 145 34 65 162 290), lower := (rows 37 194 76 280 145 34 65 128 256), losses := [{ target := 0, region := (rows 0 70 4 24 16 103 64 231 359), good := (rows 422 482 494 280 440 418 482 128 256) },{ target := 1, region := (rows 1 0 12 8 16 32 81 128 256), good := (rows 101 192 76 348 209 32 65 128 256) }] }

theorem u8785 : Upper (D 7) (R 7) [36,192,72,272,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8785 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8786 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 194 76 280 145 34 66 161 289), lower := (rows 37 194 76 280 145 34 66 128 256), losses := [] }

theorem u8786 : Upper (D 7) (R 7) [36,192,72,272,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8786 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8787 : Route 9 := (fun mask => (mask,id))

def c8787 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8787 : Upper (D 7) (R 7) [36,192,72,272,129,2,32] 13 := by
  apply FastRouting.sound _ _ [36,192,72,272,129,2,32] 13 (by decide) (choices 1) [1,2] r8787 c8787
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u702
  · exact u703

def r8788 : Route 9 := (fun mask => (mask,id))

def c8788 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8788 : Upper (D 7) (R 7) [36,192,72,272,160,2,1] 13 := by
  apply FastRouting.sound _ _ [36,192,72,272,160,2,1] 13 (by decide) (choices 1) [1,2] r8788 c8788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u704
  · exact u705

def b8789 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 194 76 280 176 34 66 129 257), lower := (rows 37 194 76 280 176 34 66 128 256), losses := [] }

theorem u8789 : Upper (D 7) (R 7) [36,192,72,272,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8789 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8790 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 76 296 19 34 65 144 400), lower := (rows 37 194 76 296 19 34 65 128 256), losses := [] }

theorem u8790 : Upper (D 7) (R 7) [36,192,72,288,3,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8790 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8791 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 392, targets := 66 },{ cop := 0, region := 210, targets := 32 }], pairs := [(1,5),(3,1),(3,6)], upper := (rows 37 194 76 296 19 34 80 129 385), lower := (rows 37 194 76 296 19 34 80 128 256), losses := [] }

theorem u8791 : Upper (D 7) (R 7) [36,192,72,288,3,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8791 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8792 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 76 296 19 34 192 145 273), lower := (rows 37 194 76 296 19 34 192 128 256), losses := [] }

theorem u8792 : Upper (D 7) (R 7) [36,192,72,288,3,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8792 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8793 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 76 296 19 160 65 146 274), lower := (rows 37 194 76 296 19 160 65 128 256), losses := [] }

theorem u8793 : Upper (D 7) (R 7) [36,192,72,288,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8793 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8794 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 4, region := 424, targets := 66 }], pairs := [(1,5),(3,1),(3,6),(4,5)], upper := (rows 37 194 76 296 19 160 66 145 273), lower := (rows 37 194 76 296 19 160 66 128 256), losses := [] }

theorem u8794 : Upper (D 7) (R 7) [36,192,72,288,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8794 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8795 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 4, region := 424, targets := 64 }], pairs := [(1,5),(3,6),(4,5)], upper := (rows 37 194 76 296 19 160 80 131 259), lower := (rows 37 194 76 296 19 160 80 128 256), losses := [] }

theorem u8795 : Upper (D 7) (R 7) [36,192,72,288,3,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8795 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8796 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 76 296 145 34 65 146 274), lower := (rows 37 194 76 296 145 34 65 128 256), losses := [] }

theorem u8796 : Upper (D 7) (R 7) [36,192,72,288,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8796 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8797 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 194 76 296 145 34 66 145 273), lower := (rows 37 194 76 296 145 34 66 128 256), losses := [] }

theorem u8797 : Upper (D 7) (R 7) [36,192,72,288,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8797 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8798 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 76 296 145 34 80 131 259), lower := (rows 37 194 76 296 145 34 80 128 256), losses := [] }

theorem u8798 : Upper (D 7) (R 7) [36,192,72,288,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8798 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8799 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 194 76 296 145 48 65 130 258), lower := (rows 37 194 76 296 145 48 65 128 256), losses := [] }

theorem u8799 : Upper (D 7) (R 7) [36,192,72,288,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8799 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8800 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0),(1,5),(4,5)], upper := (rows 37 194 76 296 145 48 66 131 259), lower := (rows 37 194 76 296 145 48 66 128 256), losses := [] }

theorem u8800 : Upper (D 7) (R 7) [36,192,72,288,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8800 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8801 : Route 9 := (fun mask => (mask,id))

def c8801 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8801 : Upper (D 7) (R 7) [36,192,72,384,3,2,1] 13 := by
  apply FastRouting.sound _ _ [36,192,72,384,3,2,1] 13 (by decide) (choices 1) [16,32] r8801 c8801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u706
  · exact u707

def b8802 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 392, targets := 66 }], pairs := [(2,1),(3,1),(3,6)], upper := (rows 37 194 76 392 19 34 80 161 289), lower := (rows 37 194 76 392 19 34 80 128 256), losses := [{ target := 1, region := (rows 1 0 84 25 16 32 80 129 257), good := (rows 429 196 76 392 477 32 92 128 256) }] }

theorem u8802 : Upper (D 7) (R 7) [36,192,72,384,3,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8802 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8803 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 102, targets := 1 },{ cop := 4, region := 392, targets := 34 }], pairs := [(1,0),(2,0),(3,1),(3,5)], upper := (rows 37 194 76 392 19 34 96 145 273), lower := (rows 37 194 76 392 19 34 96 128 256), losses := [] }

theorem u8803 : Upper (D 7) (R 7) [36,192,72,384,3,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8803 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8804 : Route 9 := (fun mask => (mask,id))

def c8804 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8804 : Upper (D 7) (R 7) [36,192,72,384,3,16,1] 13 := by
  apply FastRouting.sound _ _ [36,192,72,384,3,16,1] 13 (by decide) (choices 1) [2,32] r8804 c8804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u708
  · exact u709

def b8805 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 194 76 392 19 48 66 161 289), lower := (rows 37 194 76 392 19 48 66 128 256), losses := [] }

theorem u8805 : Upper (D 7) (R 7) [36,192,72,384,3,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8805 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8806 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 392, targets := 32 },{ cop := 4, region := 392, targets := 64 }], pairs := [(2,5),(3,5),(3,6)], upper := (rows 37 194 76 392 19 48 96 131 259), lower := (rows 37 194 76 392 19 48 96 128 256), losses := [{ target := 5, region := (rows 1 2 68 56 16 0 64 144 272), good := (rows 13 198 76 392 411 408 76 128 256) }] }

theorem u8806 : Upper (D 7) (R 7) [36,192,72,384,3,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8806 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8807 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 76 392 50 33 65 146 274), lower := (rows 37 194 76 392 50 33 65 128 256), losses := [] }

theorem u8807 : Upper (D 7) (R 7) [36,192,72,384,34,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8807 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8808 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 194 76 392 50 33 66 145 273), lower := (rows 37 194 76 392 50 33 66 128 256), losses := [] }

theorem u8808 : Upper (D 7) (R 7) [36,192,72,384,34,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8808 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8809 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7)], upper := (rows 37 194 76 392 50 33 80 131 259), lower := (rows 37 194 76 392 50 33 80 128 256), losses := [] }

theorem u8809 : Upper (D 7) (R 7) [36,192,72,384,34,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8809 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8810 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 421, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 194 261 11 88 48 66 160 416), lower := (rows 37 194 261 11 88 48 66 128 256), losses := [] }

theorem u8810 : Upper (D 7) (R 7) [36,192,257,3,72,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8810 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8811 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 3, region := 112, targets := 2 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 37 194 261 11 88 48 96 130 386), lower := (rows 37 194 261 11 88 48 96 128 256), losses := [] }

theorem u8811 : Upper (D 7) (R 7) [36,192,257,3,72,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8811 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8812 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 261 11 88 48 192 162 290), lower := (rows 37 194 261 11 88 48 192 128 256), losses := [] }

theorem u8812 : Upper (D 7) (R 7) [36,192,257,3,72,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8812 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8813 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 421, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 194 261 11 88 160 66 176 304), lower := (rows 37 194 261 11 88 160 66 128 256), losses := [] }

theorem u8813 : Upper (D 7) (R 7) [36,192,257,3,72,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8813 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8814 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 301, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 194 261 11 88 160 80 162 290), lower := (rows 37 194 261 11 88 160 80 128 256), losses := [] }

theorem u8814 : Upper (D 7) (R 7) [36,192,257,3,72,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8814 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8815 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 4, region := 130, targets := 32 }], pairs := [(1,0),(1,5),(4,0),(4,1)], upper := (rows 37 194 261 11 88 160 96 146 274), lower := (rows 37 194 261 11 88 160 96 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 24 162 235 128 256), good := (rows 101 224 325 121 88 224 96 224 256) }] }

theorem u8815 : Upper (D 7) (R 7) [36,192,257,3,72,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8815 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8816 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 389, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 194 261 11 112 34 72 144 400), lower := (rows 37 194 261 11 112 34 72 128 256), losses := [] }

theorem u8816 : Upper (D 7) (R 7) [36,192,257,3,96,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8816 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8817 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 301, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 194 261 11 112 34 80 136 392), lower := (rows 37 194 261 11 112 34 80 128 256), losses := [] }

theorem u8817 : Upper (D 7) (R 7) [36,192,257,3,96,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8817 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8818 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 261 11 112 34 192 152 280), lower := (rows 37 194 261 11 112 34 192 128 256), losses := [] }

theorem u8818 : Upper (D 7) (R 7) [36,192,257,3,96,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8818 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8819 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 1, region := 48, targets := 2 },{ cop := 5, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(4,0),(4,1)], upper := (rows 37 194 261 11 112 160 66 152 280), lower := (rows 37 194 261 11 112 160 66 128 256), losses := [] }

theorem u8819 : Upper (D 7) (R 7) [36,192,257,3,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8819 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u8819
end Delivery.IrregularNine14.P07
