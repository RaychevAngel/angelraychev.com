import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0063

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r11820 : Route 9 := (fun mask => (mask,id))

def c11820 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11820 : Upper (D 8) (R 8) [66,160,96,132,288] 13 := by
  apply FastRouting.sound _ _ [66,160,96,132,288] 13 (by decide) (choices 1) [1,8,16] r11820 c11820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3797
  · exact u3798
  · exact u3799

def r11821 : Route 9 := (fun mask => (mask,id))

def c11821 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11821 : Upper (D 8) (R 8) [66,160,96,144,257] 13 := by
  apply FastRouting.sound _ _ [66,160,96,144,257] 13 (by decide) (choices 1) [1,4,8] r11821 c11821
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3800
  · exact u3801
  · exact u3802

def r11822 : Route 9 := (fun mask => (mask,id))

def c11822 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11822 : Upper (D 8) (R 8) [66,160,96,144,260] 13 := by
  apply FastRouting.sound _ _ [66,160,96,144,260] 13 (by decide) (choices 1) [1,8] r11822 c11822
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3803
  · exact u3804

def b11823 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 100 152 280 37 101 165 293), lower := (rows 67 162 100 152 280 32 64 128 256), losses := [] }

theorem u11823 : Upper (D 8) (R 8) [66,160,96,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11823 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11824 : Route 9 := (fun mask => (mask,id))

def c11824 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11824 : Upper (D 8) (R 8) [66,160,96,144,288] 13 := by
  apply FastRouting.sound _ _ [66,160,96,144,288] 13 (by decide) (choices 1) [1,4,8] r11824 c11824
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3805
  · exact u3806
  · exact u3807

def b11825 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 100 168 273 61 93 157 285), lower := (rows 67 162 100 168 273 32 64 128 256), losses := [] }

theorem u11825 : Upper (D 8) (R 8) [66,160,96,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11825 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11826 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 100 168 276 57 89 153 281), lower := (rows 67 162 100 168 276 32 64 128 256), losses := [] }

theorem u11826 : Upper (D 8) (R 8) [66,160,96,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11826 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11827 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 100 168 280 53 85 149 277), lower := (rows 67 162 100 168 280 32 64 128 256), losses := [] }

theorem u11827 : Upper (D 8) (R 8) [66,160,96,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11827 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11828 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 28 112 160 224 160 416), lower := (rows 67 259 13 28 112 32 64 128 256), losses := [] }

theorem u11828 : Upper (D 8) (R 8) [66,257,9,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11828 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11829 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 28 176 224 224 224 480), lower := (rows 67 259 13 28 176 32 64 128 256), losses := [] }

theorem u11829 : Upper (D 8) (R 8) [66,257,9,20,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11829 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11830 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 28 208 160 224 160 416), lower := (rows 67 259 13 28 208 32 64 128 256), losses := [] }

theorem u11830 : Upper (D 8) (R 8) [66,257,9,20,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11830 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11831 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 44 112 176 240 176 432), lower := (rows 67 259 13 44 112 32 64 128 256), losses := [] }

theorem u11831 : Upper (D 8) (R 8) [66,257,9,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11831 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11832 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 44 176 240 240 240 496), lower := (rows 67 259 13 44 176 32 64 128 256), losses := [] }

theorem u11832 : Upper (D 8) (R 8) [66,257,9,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11832 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11833 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 44 208 176 240 176 432), lower := (rows 67 259 13 44 208 32 64 128 256), losses := [] }

theorem u11833 : Upper (D 8) (R 8) [66,257,9,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11833 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11834 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 56 84 160 224 160 416), lower := (rows 67 259 13 56 84 32 64 128 256), losses := [] }

theorem u11834 : Upper (D 8) (R 8) [66,257,9,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11834 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11835 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 56 148 224 224 224 480), lower := (rows 67 259 13 56 148 32 64 128 256), losses := [] }

theorem u11835 : Upper (D 8) (R 8) [66,257,9,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11835 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11836 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 56 208 164 228 164 420), lower := (rows 67 259 13 56 208 32 64 128 256), losses := [] }

theorem u11836 : Upper (D 8) (R 8) [66,257,9,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11836 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11837 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 259 13 76 176 176 240 176 432), lower := (rows 67 259 13 76 176 32 64 128 256), losses := [] }

theorem u11837 : Upper (D 8) (R 8) [66,257,9,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11837 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11838 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 88 52 160 224 160 416), lower := (rows 67 259 13 88 52 32 64 128 256), losses := [] }

theorem u11838 : Upper (D 8) (R 8) [66,257,9,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11838 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11839 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 88 148 160 224 160 416), lower := (rows 67 259 13 88 148 32 64 128 256), losses := [] }

theorem u11839 : Upper (D 8) (R 8) [66,257,9,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11839 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11840 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 88 176 164 228 164 420), lower := (rows 67 259 13 88 176 32 64 128 256), losses := [] }

theorem u11840 : Upper (D 8) (R 8) [66,257,9,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11840 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11841 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 104 52 176 240 176 432), lower := (rows 67 259 13 104 52 32 64 128 256), losses := [] }

theorem u11841 : Upper (D 8) (R 8) [66,257,9,96,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11841 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11842 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 104 148 176 240 176 432), lower := (rows 67 259 13 104 148 32 64 128 256), losses := [] }

theorem u11842 : Upper (D 8) (R 8) [66,257,9,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11842 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11843 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 104 176 180 244 180 436), lower := (rows 67 259 13 104 176 32 64 128 256), losses := [] }

theorem u11843 : Upper (D 8) (R 8) [66,257,9,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11843 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11844 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 140 112 176 240 176 432), lower := (rows 67 259 13 140 112 32 64 128 256), losses := [] }

theorem u11844 : Upper (D 8) (R 8) [66,257,9,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11844 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11845 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 140 176 112 112 240 368), lower := (rows 67 259 13 140 176 32 64 128 256), losses := [] }

theorem u11845 : Upper (D 8) (R 8) [66,257,9,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11845 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11846 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 140 208 48 112 176 304), lower := (rows 67 259 13 140 208 32 64 128 256), losses := [] }

theorem u11846 : Upper (D 8) (R 8) [66,257,9,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11846 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11847 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 152 52 224 224 224 480), lower := (rows 67 259 13 152 52 32 64 128 256), losses := [] }

theorem u11847 : Upper (D 8) (R 8) [66,257,9,144,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11847 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11848 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 152 84 160 224 160 416), lower := (rows 67 259 13 152 84 32 64 128 256), losses := [] }

theorem u11848 : Upper (D 8) (R 8) [66,257,9,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11848 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11849 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 152 112 164 228 164 420), lower := (rows 67 259 13 152 112 32 64 128 256), losses := [] }

theorem u11849 : Upper (D 8) (R 8) [66,257,9,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11849 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11850 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 168 52 240 240 240 496), lower := (rows 67 259 13 168 52 32 64 128 256), losses := [] }

theorem u11850 : Upper (D 8) (R 8) [66,257,9,160,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11850 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11851 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 168 84 176 240 176 432), lower := (rows 67 259 13 168 84 32 64 128 256), losses := [] }

theorem u11851 : Upper (D 8) (R 8) [66,257,9,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11851 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11852 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 168 112 180 244 180 436), lower := (rows 67 259 13 168 112 32 64 128 256), losses := [] }

theorem u11852 : Upper (D 8) (R 8) [66,257,9,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11852 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11853 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 168 148 112 112 240 368), lower := (rows 67 259 13 168 148 32 64 128 256), losses := [] }

theorem u11853 : Upper (D 8) (R 8) [66,257,9,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11853 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11854 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 168 208 52 116 180 308), lower := (rows 67 259 13 168 208 32 64 128 256), losses := [] }

theorem u11854 : Upper (D 8) (R 8) [66,257,9,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11854 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11855 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 200 52 176 240 176 432), lower := (rows 67 259 13 200 52 32 64 128 256), losses := [] }

theorem u11855 : Upper (D 8) (R 8) [66,257,9,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11855 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11856 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 200 148 48 112 176 304), lower := (rows 67 259 13 200 148 32 64 128 256), losses := [] }

theorem u11856 : Upper (D 8) (R 8) [66,257,9,192,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11856 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11857 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 13 200 176 52 116 180 308), lower := (rows 67 259 13 200 176 32 64 128 256), losses := [] }

theorem u11857 : Upper (D 8) (R 8) [66,257,9,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11857 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11858 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 67 259 28 41 52 224 224 224 480), lower := (rows 67 259 28 41 52 32 64 128 256), losses := [] }

theorem u11858 : Upper (D 8) (R 8) [66,257,24,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11858 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11859 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 28 41 112 164 228 164 420), lower := (rows 67 259 28 41 112 32 64 128 256), losses := [] }

theorem u11859 : Upper (D 8) (R 8) [66,257,24,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11859 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11860 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 28 41 148 224 224 224 480), lower := (rows 67 259 28 41 148 32 64 128 256), losses := [] }

theorem u11860 : Upper (D 8) (R 8) [66,257,24,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11860 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11861 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 28 41 176 228 228 228 484), lower := (rows 67 259 28 41 176 32 64 128 256), losses := [] }

theorem u11861 : Upper (D 8) (R 8) [66,257,24,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11861 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11862 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 28 41 208 164 228 164 420), lower := (rows 67 259 28 41 208 32 64 128 256), losses := [] }

theorem u11862 : Upper (D 8) (R 8) [66,257,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11862 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11863 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 259 28 44 81 160 224 160 416), lower := (rows 67 259 28 44 81 32 64 128 256), losses := [] }

theorem u11863 : Upper (D 8) (R 8) [66,257,24,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11863 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11864 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 28 44 112 161 225 161 417), lower := (rows 67 259 28 44 112 32 64 128 256), losses := [] }

theorem u11864 : Upper (D 8) (R 8) [66,257,24,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11864 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11865 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 108, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 28 44 145 224 224 224 480), lower := (rows 67 259 28 44 145 32 64 128 256), losses := [] }

theorem u11865 : Upper (D 8) (R 8) [66,257,24,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11865 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11866 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 28 44 176 225 225 225 481), lower := (rows 67 259 28 44 176 32 64 128 256), losses := [] }

theorem u11866 : Upper (D 8) (R 8) [66,257,24,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11866 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11867 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 259 28 44 208 161 225 161 417), lower := (rows 67 259 28 44 208 32 64 128 256), losses := [] }

theorem u11867 : Upper (D 8) (R 8) [66,257,24,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11867 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11868 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 259 28 73 148 160 224 160 416), lower := (rows 67 259 28 73 148 32 64 128 256), losses := [] }

theorem u11868 : Upper (D 8) (R 8) [66,257,24,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11868 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11869 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 259 28 73 176 164 228 164 420), lower := (rows 67 259 28 73 176 32 64 128 256), losses := [] }

theorem u11869 : Upper (D 8) (R 8) [66,257,24,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11869 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11870 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 259 28 76 176 161 225 161 417), lower := (rows 67 259 28 76 176 32 64 128 256), losses := [] }

theorem u11870 : Upper (D 8) (R 8) [66,257,24,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11870 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11871 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 108, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 28 104 145 164 228 164 420), lower := (rows 67 259 28 104 145 32 64 128 256), losses := [] }

theorem u11871 : Upper (D 8) (R 8) [66,257,24,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11871 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11872 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 259 28 104 148 161 225 161 417), lower := (rows 67 259 28 104 148 32 64 128 256), losses := [] }

theorem u11872 : Upper (D 8) (R 8) [66,257,24,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11872 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11873 : Route 9 := (fun mask => (mask,id))

def c11873 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11873 : Upper (D 8) (R 8) [66,257,24,96,160] 13 := by
  apply FastRouting.sound _ _ [66,257,24,96,160] 13 (by decide) (choices 1) [1,4,128] r11873 c11873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3808
  · exact u3809
  · exact u3810

def b11874 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 67 259 28 137 148 96 96 224 352), lower := (rows 67 259 28 137 148 32 64 128 256), losses := [] }

theorem u11874 : Upper (D 8) (R 8) [66,257,24,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11874 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11875 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 259 28 137 176 100 100 228 356), lower := (rows 67 259 28 137 176 32 64 128 256), losses := [] }

theorem u11875 : Upper (D 8) (R 8) [66,257,24,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11875 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11876 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 259 28 137 208 36 100 164 292), lower := (rows 67 259 28 137 208 32 64 128 256), losses := [] }

theorem u11876 : Upper (D 8) (R 8) [66,257,24,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11876 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11877 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 28 140 176 97 97 225 353), lower := (rows 67 259 28 140 176 32 64 128 256), losses := [] }

theorem u11877 : Upper (D 8) (R 8) [66,257,24,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11877 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11878 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 28 140 208 33 97 161 289), lower := (rows 67 259 28 140 208 32 64 128 256), losses := [] }

theorem u11878 : Upper (D 8) (R 8) [66,257,24,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11878 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11879 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 28 168 176 101 101 229 357), lower := (rows 67 259 28 168 176 32 64 128 256), losses := [] }

theorem u11879 : Upper (D 8) (R 8) [66,257,24,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11879 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u11879
end Delivery.IrregularNine14.P08
