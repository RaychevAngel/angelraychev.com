import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0062
import IrregularNine14P08C0063

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11760 : PairBound 9 := { available := 180, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 44 265 81 180 244 180 436), lower := (rows 67 162 44 265 81 32 64 128 256), losses := [] }

theorem u11760 : Upper (D 8) (R 8) [66,160,40,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11760 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11761 : Route 9 := (fun mask => (mask,id))

def c11761 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11761 : Upper (D 8) (R 8) [66,160,40,257,68] 13 := by
  apply FastRouting.sound _ _ [66,160,40,257,68] 13 (by decide) (choices 1) [1,16,128] r11761 c11761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3754
  · exact u3755
  · exact u3756

def r11762 : Route 9 := (fun mask => (mask,id))

def c11762 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11762 : Upper (D 8) (R 8) [66,160,40,257,96] 13 := by
  apply FastRouting.sound _ _ [66,160,40,257,96] 13 (by decide) (choices 1) [1,4,16,128] r11762 c11762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3757
  · exact u3758
  · exact u3759
  · exact u3760

def b11763 : PairBound 9 := { available := 116, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 44 265 145 116 116 244 372), lower := (rows 67 162 44 265 145 32 64 128 256), losses := [] }

theorem u11763 : Upper (D 8) (R 8) [66,160,40,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11763 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11764 : Route 9 := (fun mask => (mask,id))

def c11764 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11764 : Upper (D 8) (R 8) [66,160,40,257,132] 13 := by
  apply FastRouting.sound _ _ [66,160,40,257,132] 13 (by decide) (choices 1) [1,16,64] r11764 c11764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3761
  · exact u3762
  · exact u3763

def b11765 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 162 44 265 176 117 85 213 341), lower := (rows 67 162 44 265 176 32 64 128 256), losses := [] }

theorem u11765 : Upper (D 8) (R 8) [66,160,40,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11765 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11766 : Route 9 := (fun mask => (mask,id))

def c11766 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11766 : Upper (D 8) (R 8) [66,160,40,257,192] 13 := by
  apply FastRouting.sound _ _ [66,160,40,257,192] 13 (by decide) (choices 1) [1,4,16] r11766 c11766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3764
  · exact u3765
  · exact u3766

def b11767 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 44 268 81 177 241 177 433), lower := (rows 67 162 44 268 81 32 64 128 256), losses := [] }

theorem u11767 : Upper (D 8) (R 8) [66,160,40,260,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11767 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11768 : Route 9 := (fun mask => (mask,id))

def c11768 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11768 : Upper (D 8) (R 8) [66,160,40,260,96] 13 := by
  apply FastRouting.sound _ _ [66,160,40,260,96] 13 (by decide) (choices 1) [1,16,128] r11768 c11768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3767
  · exact u3768
  · exact u3769

def b11769 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 44 268 145 113 113 241 369), lower := (rows 67 162 44 268 145 32 64 128 256), losses := [] }

theorem u11769 : Upper (D 8) (R 8) [66,160,40,260,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11769 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11770 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 162 44 268 176 113 81 209 337), lower := (rows 67 162 44 268 176 32 64 128 256), losses := [] }

theorem u11770 : Upper (D 8) (R 8) [66,160,40,260,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11770 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11771 : Route 9 := (fun mask => (mask,id))

def c11771 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11771 : Upper (D 8) (R 8) [66,160,40,260,192] 13 := by
  apply FastRouting.sound _ _ [66,160,40,260,192] 13 (by decide) (choices 1) [1,16] r11771 c11771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3770
  · exact u3771

def b11772 : PairBound 9 := { available := 165, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 44 280 81 165 229 165 421), lower := (rows 67 162 44 280 81 32 64 128 256), losses := [] }

theorem u11772 : Upper (D 8) (R 8) [66,160,40,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11772 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11773 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 44 280 84 161 225 161 417), lower := (rows 67 162 44 280 84 32 64 128 256), losses := [] }

theorem u11773 : Upper (D 8) (R 8) [66,160,40,272,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11773 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11774 : Route 9 := (fun mask => (mask,id))

def c11774 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11774 : Upper (D 8) (R 8) [66,160,40,272,96] 13 := by
  apply FastRouting.sound _ _ [66,160,40,272,96] 13 (by decide) (choices 1) [1,4,128] r11774 c11774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3772
  · exact u3773
  · exact u3774

def b11775 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 44 280 145 101 101 229 357), lower := (rows 67 162 44 280 145 32 64 128 256), losses := [] }

theorem u11775 : Upper (D 8) (R 8) [66,160,40,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11775 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11776 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 44 280 148 97 97 225 353), lower := (rows 67 162 44 280 148 32 64 128 256), losses := [] }

theorem u11776 : Upper (D 8) (R 8) [66,160,40,272,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11776 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11777 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 162 44 280 176 101 69 197 325), lower := (rows 67 162 44 280 176 32 64 128 256), losses := [] }

theorem u11777 : Upper (D 8) (R 8) [66,160,40,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11777 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11778 : Route 9 := (fun mask => (mask,id))

def c11778 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11778 : Upper (D 8) (R 8) [66,160,40,272,192] 13 := by
  apply FastRouting.sound _ _ [66,160,40,272,192] 13 (by decide) (choices 1) [1,4] r11778 c11778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3775
  · exact u3776

def b11779 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 296 84 177 209 145 401), lower := (rows 67 162 44 296 84 32 64 128 256), losses := [] }

theorem u11779 : Upper (D 8) (R 8) [66,160,40,288,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11779 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11780 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 296 148 113 81 209 337), lower := (rows 67 162 44 296 148 32 64 128 256), losses := [] }

theorem u11780 : Upper (D 8) (R 8) [66,160,40,288,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11780 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11781 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 296 208 53 85 149 277), lower := (rows 67 162 44 296 208 32 64 128 256), losses := [] }

theorem u11781 : Upper (D 8) (R 8) [66,160,40,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11781 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11782 : PairBound 9 := { available := 53, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 44 328 145 53 117 181 309), lower := (rows 67 162 44 328 145 32 64 128 256), losses := [] }

theorem u11782 : Upper (D 8) (R 8) [66,160,40,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11782 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11783 : Route 9 := (fun mask => (mask,id))

def c11783 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11783 : Upper (D 8) (R 8) [66,160,40,320,132] 13 := by
  apply FastRouting.sound _ _ [66,160,40,320,132] 13 (by decide) (choices 1) [1,16] r11783 c11783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3777
  · exact u3778

def b11784 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 162 44 328 176 53 85 149 277), lower := (rows 67 162 44 328 176 32 64 128 256), losses := [] }

theorem u11784 : Upper (D 8) (R 8) [66,160,40,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11784 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11785 : PairBound 9 := { available := 53, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 44 392 81 53 117 181 309), lower := (rows 67 162 44 392 81 32 64 128 256), losses := [] }

theorem u11785 : Upper (D 8) (R 8) [66,160,40,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11785 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11786 : Route 9 := (fun mask => (mask,id))

def c11786 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11786 : Upper (D 8) (R 8) [66,160,40,384,68] 13 := by
  apply FastRouting.sound _ _ [66,160,40,384,68] 13 (by decide) (choices 1) [1,16] r11786 c11786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3779
  · exact u3780

def r11787 : Route 9 := (fun mask => (mask,id))

def c11787 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11787 : Upper (D 8) (R 8) [66,160,40,384,96] 13 := by
  apply FastRouting.sound _ _ [66,160,40,384,96] 13 (by decide) (choices 1) [1,4,16] r11787 c11787
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3781
  · exact u3782
  · exact u3783

def b11788 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 69 140 273 56 120 184 312), lower := (rows 67 162 69 140 273 32 64 128 256), losses := [] }

theorem u11788 : Upper (D 8) (R 8) [66,160,65,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11788 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11789 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 69 140 280 49 113 177 305), lower := (rows 67 162 69 140 280 32 64 128 256), losses := [] }

theorem u11789 : Upper (D 8) (R 8) [66,160,65,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11789 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11790 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 69 140 304 57 121 185 313), lower := (rows 67 162 69 140 304 32 64 128 256), losses := [] }

theorem u11790 : Upper (D 8) (R 8) [66,160,65,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11790 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11791 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 69 152 273 44 108 172 300), lower := (rows 67 162 69 152 273 32 64 128 256), losses := [] }

theorem u11791 : Upper (D 8) (R 8) [66,160,65,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11791 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11792 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 69 152 276 41 105 169 297), lower := (rows 67 162 69 152 276 32 64 128 256), losses := [] }

theorem u11792 : Upper (D 8) (R 8) [66,160,65,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11792 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11793 : PairBound 9 := { available := 45, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 69 152 304 45 109 173 301), lower := (rows 67 162 69 152 304 32 64 128 256), losses := [] }

theorem u11793 : Upper (D 8) (R 8) [66,160,65,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11793 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11794 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 76 137 273 52 116 180 308), lower := (rows 67 162 76 137 273 32 64 128 256), losses := [] }

theorem u11794 : Upper (D 8) (R 8) [66,160,72,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11794 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11795 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 76 137 276 49 113 177 305), lower := (rows 67 162 76 137 276 32 64 128 256), losses := [] }

theorem u11795 : Upper (D 8) (R 8) [66,160,72,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11795 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11796 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 76 137 304 53 117 181 309), lower := (rows 67 162 76 137 304 32 64 128 256), losses := [] }

theorem u11796 : Upper (D 8) (R 8) [66,160,72,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11796 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11797 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 76 140 273 49 113 177 305), lower := (rows 67 162 76 140 273 32 64 128 256), losses := [] }

theorem u11797 : Upper (D 8) (R 8) [66,160,72,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11797 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11798 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 76 140 304 49 113 177 305), lower := (rows 67 162 76 140 304 32 64 128 256), losses := [] }

theorem u11798 : Upper (D 8) (R 8) [66,160,72,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11798 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11799 : Route 9 := (fun mask => (mask,id))

def c11799 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11799 : Upper (D 8) (R 8) [66,160,72,144,257] 13 := by
  apply FastRouting.sound _ _ [66,160,72,144,257] 13 (by decide) (choices 1) [1,4] r11799 c11799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3784
  · exact u3785

def b11800 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 76 152 276 33 97 161 289), lower := (rows 67 162 76 152 276 32 64 128 256), losses := [] }

theorem u11800 : Upper (D 8) (R 8) [66,160,72,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11800 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11801 : Route 9 := (fun mask => (mask,id))

def c11801 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11801 : Upper (D 8) (R 8) [66,160,72,144,288] 13 := by
  apply FastRouting.sound _ _ [66,160,72,144,288] 13 (by decide) (choices 1) [1,4] r11801 c11801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3786
  · exact u3787

def b11802 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 76 168 273 53 117 181 309), lower := (rows 67 162 76 168 273 32 64 128 256), losses := [] }

theorem u11802 : Upper (D 8) (R 8) [66,160,72,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11802 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11803 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 76 168 276 49 113 177 305), lower := (rows 67 162 76 168 276 32 64 128 256), losses := [] }

theorem u11803 : Upper (D 8) (R 8) [66,160,72,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11803 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11804 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 76 168 304 53 85 149 277), lower := (rows 67 162 76 168 304 32 64 128 256), losses := [] }

theorem u11804 : Upper (D 8) (R 8) [66,160,72,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11804 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11805 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 76 265 145 52 116 180 308), lower := (rows 67 162 76 265 145 32 64 128 256), losses := [] }

theorem u11805 : Upper (D 8) (R 8) [66,160,72,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11805 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11806 : Route 9 := (fun mask => (mask,id))

def c11806 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11806 : Upper (D 8) (R 8) [66,160,72,257,132] 13 := by
  apply FastRouting.sound _ _ [66,160,72,257,132] 13 (by decide) (choices 1) [1,16] r11806 c11806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3788
  · exact u3789

def b11807 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 162 76 265 176 53 117 181 309), lower := (rows 67 162 76 265 176 32 64 128 256), losses := [] }

theorem u11807 : Upper (D 8) (R 8) [66,160,72,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11807 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11808 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 76 280 145 37 101 165 293), lower := (rows 67 162 76 280 145 32 64 128 256), losses := [] }

theorem u11808 : Upper (D 8) (R 8) [66,160,72,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11808 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11809 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 76 280 148 33 97 161 289), lower := (rows 67 162 76 280 148 32 64 128 256), losses := [] }

theorem u11809 : Upper (D 8) (R 8) [66,160,72,272,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11809 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11810 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 162 76 280 176 37 101 165 293), lower := (rows 67 162 76 280 176 32 64 128 256), losses := [] }

theorem u11810 : Upper (D 8) (R 8) [66,160,72,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11810 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11811 : PairBound 9 := { available := 53, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 76 296 145 53 117 181 309), lower := (rows 67 162 76 296 145 32 64 128 256), losses := [] }

theorem u11811 : Upper (D 8) (R 8) [66,160,72,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11811 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11812 : Route 9 := (fun mask => (mask,id))

def c11812 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11812 : Upper (D 8) (R 8) [66,160,72,288,132] 13 := by
  apply FastRouting.sound _ _ [66,160,72,288,132] 13 (by decide) (choices 1) [1,16] r11812 c11812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3790
  · exact u3791

def b11813 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 162 76 296 176 53 85 149 277), lower := (rows 67 162 76 296 176 32 64 128 256), losses := [] }

theorem u11813 : Upper (D 8) (R 8) [66,160,72,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11813 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11814 : PairBound 9 := { available := 60, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 100 137 273 60 124 188 316), lower := (rows 67 162 100 137 273 32 64 128 256), losses := [] }

theorem u11814 : Upper (D 8) (R 8) [66,160,96,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11814 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11815 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 100 137 276 57 121 185 313), lower := (rows 67 162 100 137 276 32 64 128 256), losses := [] }

theorem u11815 : Upper (D 8) (R 8) [66,160,96,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11815 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11816 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 100 137 280 53 117 181 309), lower := (rows 67 162 100 137 280 32 64 128 256), losses := [] }

theorem u11816 : Upper (D 8) (R 8) [66,160,96,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11816 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11817 : PairBound 9 := { available := 29, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 100 137 304 61 93 157 285), lower := (rows 67 162 100 137 304 32 64 128 256), losses := [] }

theorem u11817 : Upper (D 8) (R 8) [66,160,96,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11817 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11818 : Route 9 := (fun mask => (mask,id))

def c11818 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11818 : Upper (D 8) (R 8) [66,160,96,132,257] 13 := by
  apply FastRouting.sound _ _ [66,160,96,132,257] 13 (by decide) (choices 1) [1,8,16] r11818 c11818
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3792
  · exact u3793
  · exact u3794

def r11819 : Route 9 := (fun mask => (mask,id))

def c11819 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11819 : Upper (D 8) (R 8) [66,160,96,132,264] 13 := by
  apply FastRouting.sound _ _ [66,160,96,132,264] 13 (by decide) (choices 1) [1,16] r11819 c11819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3795
  · exact u3796

#print axioms u11819
end Delivery.IrregularNine14.P08
