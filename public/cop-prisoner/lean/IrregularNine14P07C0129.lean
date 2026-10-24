import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0009
import IrregularNine14P07C0010

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r7740 : Route 9 := (fun mask => (mask,id))

def c7740 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7740 : Upper (D 7) (R 7) [36,96,72,130,129,16,256] 13 := by
  apply FastRouting.sound _ _ [36,96,72,130,129,16,256] 13 (by decide) (choices 1) [1,2] r7740 c7740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u588
  · exact u589

def r7741 : Route 9 := (fun mask => (mask,id))

def c7741 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7741 : Upper (D 7) (R 7) [36,96,72,130,129,256,1] 13 := by
  apply FastRouting.sound _ _ [36,96,72,130,129,256,1] 13 (by decide) (choices 1) [2,16] r7741 c7741
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u590
  · exact u591

def b7742 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 98 76 138 145 288 66 145 273), lower := (rows 37 98 76 138 145 288 66 128 256), losses := [] }

theorem u7742 : Upper (D 7) (R 7) [36,96,72,130,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7742 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7743 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 37 98 76 138 145 288 80 131 259), lower := (rows 37 98 76 138 145 288 80 128 256), losses := [] }

theorem u7743 : Upper (D 7) (R 7) [36,96,72,130,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7743 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7744 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 140, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 98 76 138 273 48 65 130 386), lower := (rows 37 98 76 138 273 48 65 128 256), losses := [] }

theorem u7744 : Upper (D 7) (R 7) [36,96,72,130,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7744 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7745 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 98 76 138 273 48 66 129 385), lower := (rows 37 98 76 138 273 48 66 128 256), losses := [] }

theorem u7745 : Upper (D 7) (R 7) [36,96,72,130,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7745 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7746 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 37 98 76 138 273 48 192 131 259), lower := (rows 37 98 76 138 273 48 192 128 256), losses := [] }

theorem u7746 : Upper (D 7) (R 7) [36,96,72,130,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7746 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7747 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7),(2,5),(3,5)], upper := (rows 37 98 76 138 274 48 65 129 385), lower := (rows 37 98 76 138 274 48 65 128 256), losses := [{ target := 5, region := (rows 1 2 6 10 18 0 65 193 321), good := (rows 453 478 460 158 286 16 449 128 256) }] }

theorem u7747 : Upper (D 7) (R 7) [36,96,72,130,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7747 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7748 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 37 98 76 138 274 48 192 129 257), lower := (rows 37 98 76 138 274 48 192 128 256), losses := [] }

theorem u7748 : Upper (D 7) (R 7) [36,96,72,130,258,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7748 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7749 : Route 9 := (fun mask => (mask,id))

def c7749 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7749 : Upper (D 7) (R 7) [36,96,72,130,384,16,1] 13 := by
  apply FastRouting.sound _ _ [36,96,72,130,384,16,1] 13 (by decide) (choices 1) [1,2] r7749 c7749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u592
  · exact u593

def b7750 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 98 76 138 400 48 66 129 257), lower := (rows 37 98 76 138 400 48 66 128 256), losses := [] }

theorem u7750 : Upper (D 7) (R 7) [36,96,72,130,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7750 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7751 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 76 152 273 34 65 130 386), lower := (rows 37 98 76 152 273 34 65 128 256), losses := [] }

theorem u7751 : Upper (D 7) (R 7) [36,96,72,144,257,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7751 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7752 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 98 }], pairs := [(3,1),(3,5),(3,6),(4,1)], upper := (rows 37 98 76 152 273 34 66 129 385), lower := (rows 37 98 76 152 273 34 66 128 256), losses := [] }

theorem u7752 : Upper (D 7) (R 7) [36,96,72,144,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7752 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7753 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 98, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,7)], upper := (rows 37 98 76 152 273 34 192 131 259), lower := (rows 37 98 76 152 273 34 192 128 256), losses := [] }

theorem u7753 : Upper (D 7) (R 7) [36,96,72,144,257,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7753 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7754 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 76 152 274 34 65 129 385), lower := (rows 37 98 76 152 274 34 65 128 256), losses := [] }

theorem u7754 : Upper (D 7) (R 7) [36,96,72,144,258,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7754 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7755 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 98, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,7)], upper := (rows 37 98 76 152 274 34 192 129 257), lower := (rows 37 98 76 152 274 34 192 128 256), losses := [] }

theorem u7755 : Upper (D 7) (R 7) [36,96,72,144,258,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7755 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7756 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 408, targets := 98 }], pairs := [(3,1),(3,5),(3,6),(4,1)], upper := (rows 37 98 76 265 145 34 66 144 400), lower := (rows 37 98 76 265 145 34 66 128 256), losses := [] }

theorem u7756 : Upper (D 7) (R 7) [36,96,72,257,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7756 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7757 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7)], upper := (rows 37 98 76 265 145 34 80 130 386), lower := (rows 37 98 76 265 145 34 80 128 256), losses := [] }

theorem u7757 : Upper (D 7) (R 7) [36,96,72,257,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7757 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7758 : Route 9 := (fun mask => (mask,id))

def c7758 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7758 : Upper (D 7) (R 7) [36,96,72,257,129,2,128] 13 := by
  apply FastRouting.sound _ _ [36,96,72,257,129,2,128] 13 (by decide) (choices 1) [2,16] r7758 c7758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u594
  · exact u595

def b7759 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 66, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(2,0)], upper := (rows 37 98 76 265 145 48 66 130 386), lower := (rows 37 98 76 265 145 48 66 128 256), losses := [{ target := 0, region := (rows 0 51 12 8 16 48 123 251 379), good := (rows 486 482 460 462 498 498 450 128 256) }] }

theorem u7759 : Upper (D 7) (R 7) [36,96,72,257,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7759 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7760 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 76 265 145 48 192 130 258), lower := (rows 37 98 76 265 145 48 192 128 256), losses := [] }

theorem u7760 : Upper (D 7) (R 7) [36,96,72,257,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7760 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7761 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 66, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 37 98 76 265 145 160 66 146 274), lower := (rows 37 98 76 265 145 160 66 128 256), losses := [{ target := 0, region := (rows 0 179 12 8 16 176 251 144 272), good := (rows 102 98 76 334 498 226 66 226 256) },{ target := 7, region := (rows 1 35 28 24 16 32 123 0 272), good := (rows 103 98 76 335 351 98 66 0 256) }] }

theorem u7761 : Upper (D 7) (R 7) [36,96,72,257,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7761 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7762 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 76 265 145 160 80 130 258), lower := (rows 37 98 76 265 145 160 80 128 256), losses := [] }

theorem u7762 : Upper (D 7) (R 7) [36,96,72,257,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7762 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7763 : PairBound 9 := { available := 144, camps := [{ cop := 8, region := 111, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 98 76 265 146 34 65 144 400), lower := (rows 37 98 76 265 146 34 65 128 256), losses := [] }

theorem u7763 : Upper (D 7) (R 7) [36,96,72,257,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7764 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 392, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 37 98 76 265 146 34 80 129 385), lower := (rows 37 98 76 265 146 34 80 128 256), losses := [] }

theorem u7764 : Upper (D 7) (R 7) [36,96,72,257,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7764 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7765 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 6, region := 50, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 37 98 76 265 146 34 192 145 273), lower := (rows 37 98 76 265 146 34 192 128 256), losses := [] }

theorem u7765 : Upper (D 7) (R 7) [36,96,72,257,130,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7765 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7766 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 68, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 37 98 76 265 146 48 65 130 386), lower := (rows 37 98 76 265 146 48 65 128 256), losses := [] }

theorem u7766 : Upper (D 7) (R 7) [36,96,72,257,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7766 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7767 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 392, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 37 98 76 265 146 48 66 129 385), lower := (rows 37 98 76 265 146 48 66 128 256), losses := [] }

theorem u7767 : Upper (D 7) (R 7) [36,96,72,257,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7767 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7768 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 76 265 146 48 192 131 259), lower := (rows 37 98 76 265 146 48 192 128 256), losses := [] }

theorem u7768 : Upper (D 7) (R 7) [36,96,72,257,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7768 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7769 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 68, targets := 162 },{ cop := 1, region := 144, targets := 1 }], pairs := [(2,1),(2,5),(2,7),(4,0)], upper := (rows 37 98 76 265 146 160 65 146 274), lower := (rows 37 98 76 265 146 160 65 128 256), losses := [] }

theorem u7769 : Upper (D 7) (R 7) [36,96,72,257,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7769 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7770 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 82, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(4,0)], upper := (rows 37 98 76 265 146 160 66 145 273), lower := (rows 37 98 76 265 146 160 66 128 256), losses := [{ target := 0, region := (rows 0 179 12 8 176 176 251 128 256), good := (rows 118 114 76 334 242 242 66 242 256) }] }

theorem u7770 : Upper (D 7) (R 7) [36,96,72,257,130,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7770 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7771 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 76 265 146 160 80 131 259), lower := (rows 37 98 76 265 146 160 80 128 256), losses := [] }

theorem u7771 : Upper (D 7) (R 7) [36,96,72,257,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7771 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7772 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 82, targets := 128 },{ cop := 4, region := 392, targets := 65 }], pairs := [(1,7),(3,0),(3,6),(4,7)], upper := (rows 37 98 76 266 19 160 65 144 400), lower := (rows 37 98 76 266 19 160 65 128 256), losses := [] }

theorem u7772 : Upper (D 7) (R 7) [36,96,72,258,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7772 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7773 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 82, targets := 128 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(1,7),(4,7)], upper := (rows 37 98 76 266 19 160 80 129 385), lower := (rows 37 98 76 266 19 160 80 128 256), losses := [] }

theorem u7773 : Upper (D 7) (R 7) [36,96,72,258,3,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7773 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7774 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 76 266 19 160 192 145 273), lower := (rows 37 98 76 266 19 160 192 128 256), losses := [] }

theorem u7774 : Upper (D 7) (R 7) [36,96,72,258,3,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7774 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7775 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 396, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 98 76 266 145 48 65 130 386), lower := (rows 37 98 76 266 145 48 65 128 256), losses := [] }

theorem u7775 : Upper (D 7) (R 7) [36,96,72,258,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7775 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7776 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 177, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 98 76 266 145 48 66 129 385), lower := (rows 37 98 76 266 145 48 66 128 256), losses := [] }

theorem u7776 : Upper (D 7) (R 7) [36,96,72,258,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7776 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7777 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 76 266 145 48 192 131 259), lower := (rows 37 98 76 266 145 48 192 128 256), losses := [] }

theorem u7777 : Upper (D 7) (R 7) [36,96,72,258,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7777 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7778 : Route 9 := (fun mask => (mask,id))

def c7778 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7778 : Upper (D 7) (R 7) [36,96,72,258,129,128,1] 13 := by
  apply FastRouting.sound _ _ [36,96,72,258,129,128,1] 13 (by decide) (choices 1) [2,16] r7778 c7778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u596
  · exact u597

def b7779 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 177, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 98 76 266 145 160 66 145 273), lower := (rows 37 98 76 266 145 160 66 128 256), losses := [] }

theorem u7779 : Upper (D 7) (R 7) [36,96,72,258,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7779 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7780 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 76 266 145 160 80 131 259), lower := (rows 37 98 76 266 145 160 80 128 256), losses := [] }

theorem u7780 : Upper (D 7) (R 7) [36,96,72,258,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7780 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7781 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7),(2,5),(3,5)], upper := (rows 37 98 76 266 146 48 65 129 385), lower := (rows 37 98 76 266 146 48 65 128 256), losses := [{ target := 5, region := (rows 1 2 6 10 18 0 65 193 321), good := (rows 453 478 460 286 158 16 449 128 256) }] }

theorem u7781 : Upper (D 7) (R 7) [36,96,72,258,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7781 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7782 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 76 266 146 48 192 129 257), lower := (rows 37 98 76 266 146 48 192 128 256), losses := [] }

theorem u7782 : Upper (D 7) (R 7) [36,96,72,258,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7782 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7783 : Route 9 := (fun mask => (mask,id))

def c7783 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7783 : Upper (D 7) (R 7) [36,96,72,258,130,128,1] 13 := by
  apply FastRouting.sound _ _ [36,96,72,258,130,128,1] 13 (by decide) (choices 1) [1,16] r7783 c7783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u598
  · exact u599

def b7784 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 76 266 146 160 80 129 257), lower := (rows 37 98 76 266 146 160 80 128 256), losses := [] }

theorem u7784 : Upper (D 7) (R 7) [36,96,72,258,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7784 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7785 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 76 280 145 34 65 130 386), lower := (rows 37 98 76 280 145 34 65 128 256), losses := [] }

theorem u7785 : Upper (D 7) (R 7) [36,96,72,272,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7785 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7786 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 98 }], pairs := [(3,1),(3,5),(3,6),(4,1)], upper := (rows 37 98 76 280 145 34 66 129 385), lower := (rows 37 98 76 280 145 34 66 128 256), losses := [] }

theorem u7786 : Upper (D 7) (R 7) [36,96,72,272,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7786 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7787 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,0)], upper := (rows 37 98 76 280 145 34 192 131 259), lower := (rows 37 98 76 280 145 34 192 128 256), losses := [{ target := 0, region := (rows 0 222 12 8 16 255 208 128 256), good := (rows 38 98 110 382 242 34 226 226 256) }] }

theorem u7787 : Upper (D 7) (R 7) [36,96,72,272,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7787 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7788 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 66, targets := 128 },{ cop := 2, region := 162, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(3,0)], upper := (rows 37 98 76 280 145 160 65 130 258), lower := (rows 37 98 76 280 145 160 65 128 256), losses := [{ target := 0, region := (rows 0 70 4 24 16 247 64 199 327), good := (rows 422 482 494 312 440 160 482 160 256) },{ target := 1, region := (rows 9 0 12 8 16 176 93 128 256), good := (rows 101 96 77 381 241 160 65 160 256) }] }

theorem u7788 : Upper (D 7) (R 7) [36,96,72,272,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7789 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 66, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 37 98 76 280 145 160 66 131 259), lower := (rows 37 98 76 280 145 160 66 128 256), losses := [{ target := 0, region := (rows 0 187 12 8 16 176 255 128 256), good := (rows 102 98 78 382 242 226 66 226 256) },{ target := 7, region := (rows 1 35 28 24 16 32 115 0 273), good := (rows 359 98 76 348 351 98 66 0 256) }] }

theorem u7789 : Upper (D 7) (R 7) [36,96,72,272,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7789 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7790 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 76 280 146 34 65 129 385), lower := (rows 37 98 76 280 146 34 65 128 256), losses := [] }

theorem u7790 : Upper (D 7) (R 7) [36,96,72,272,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7790 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7791 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 6, region := 50, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 37 98 76 280 146 34 192 129 257), lower := (rows 37 98 76 280 146 34 192 128 256), losses := [] }

theorem u7791 : Upper (D 7) (R 7) [36,96,72,272,130,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7792 : Route 9 := (fun mask => (mask,id))

def c7792 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7792 : Upper (D 7) (R 7) [36,96,72,272,130,128,1] 13 := by
  apply FastRouting.sound _ _ [36,96,72,272,130,128,1] 13 (by decide) (choices 1) [1,2] r7792 c7792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u600
  · exact u601

def b7793 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 161, targets := 66 },{ cop := 5, region := 82, targets := 1 }], pairs := [(0,1),(0,6),(1,0),(4,0)], upper := (rows 37 98 76 280 146 160 66 129 257), lower := (rows 37 98 76 280 146 160 66 128 256), losses := [] }

theorem u7793 : Upper (D 7) (R 7) [36,96,72,272,130,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7793 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7794 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 76 392 145 34 65 146 274), lower := (rows 37 98 76 392 145 34 65 128 256), losses := [] }

theorem u7794 : Upper (D 7) (R 7) [36,96,72,384,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7794 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7795 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 98 }], pairs := [(3,1),(3,5),(3,6),(4,1)], upper := (rows 37 98 76 392 145 34 66 145 273), lower := (rows 37 98 76 392 145 34 66 128 256), losses := [] }

theorem u7795 : Upper (D 7) (R 7) [36,96,72,384,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7795 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7796 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7)], upper := (rows 37 98 76 392 145 34 80 131 259), lower := (rows 37 98 76 392 145 34 80 128 256), losses := [] }

theorem u7796 : Upper (D 7) (R 7) [36,96,72,384,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7796 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7797 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 396, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 98 76 392 145 48 65 130 258), lower := (rows 37 98 76 392 145 48 65 128 256), losses := [] }

theorem u7797 : Upper (D 7) (R 7) [36,96,72,384,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7797 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7798 : Route 9 := (fun mask => (mask,id))

def c7798 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7798 : Upper (D 7) (R 7) [36,96,72,384,129,16,2] 13 := by
  apply FastRouting.sound _ _ [36,96,72,384,129,16,2] 13 (by decide) (choices 1) [1,2] r7798 c7798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u602
  · exact u603

def b7799 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 76 392 146 34 65 145 273), lower := (rows 37 98 76 392 146 34 65 128 256), losses := [] }

theorem u7799 : Upper (D 7) (R 7) [36,96,72,384,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7799 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u7799
end Delivery.IrregularNine14.P07
