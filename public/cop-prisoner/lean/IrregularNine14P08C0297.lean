import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0110

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17820 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 14 25 176 224 224 224 480), lower := (rows 321 7 14 25 176 32 64 128 256), losses := [] }

theorem u17820 : Upper (D 8) (R 8) [320,5,10,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17820 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17821 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 14 25 208 160 224 160 416), lower := (rows 321 7 14 25 208 32 64 128 256), losses := [] }

theorem u17821 : Upper (D 8) (R 8) [320,5,10,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17821 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17822 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 14 41 112 176 240 176 432), lower := (rows 321 7 14 41 112 32 64 128 256), losses := [] }

theorem u17822 : Upper (D 8) (R 8) [320,5,10,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17822 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17823 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 14 41 176 240 240 240 496), lower := (rows 321 7 14 41 176 32 64 128 256), losses := [] }

theorem u17823 : Upper (D 8) (R 8) [320,5,10,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17823 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17824 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 14 41 208 176 240 176 432), lower := (rows 321 7 14 41 208 32 64 128 256), losses := [] }

theorem u17824 : Upper (D 8) (R 8) [320,5,10,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17824 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17825 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 14 56 49 224 224 224 480), lower := (rows 321 7 14 56 49 32 64 128 256), losses := [] }

theorem u17825 : Upper (D 8) (R 8) [320,5,10,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17825 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17826 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 14 56 81 160 224 160 416), lower := (rows 321 7 14 56 81 32 64 128 256), losses := [] }

theorem u17826 : Upper (D 8) (R 8) [320,5,10,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17826 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17827 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 14 56 112 161 225 161 417), lower := (rows 321 7 14 56 112 32 64 128 256), losses := [] }

theorem u17827 : Upper (D 8) (R 8) [320,5,10,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17827 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17828 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 14 56 145 224 224 224 480), lower := (rows 321 7 14 56 145 32 64 128 256), losses := [] }

theorem u17828 : Upper (D 8) (R 8) [320,5,10,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17828 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17829 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 14 56 176 225 225 225 481), lower := (rows 321 7 14 56 176 32 64 128 256), losses := [] }

theorem u17829 : Upper (D 8) (R 8) [320,5,10,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17829 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17830 : Route 9 := (fun mask => (mask,id))

def c17830 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17830 : Upper (D 8) (R 8) [320,5,10,48,192] 13 := by
  apply FastRouting.sound _ _ [320,5,10,48,192] 13 (by decide) (choices 1) [1,128] r17830 c17830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6618
  · exact u6619

def b17831 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 14 73 176 176 240 176 432), lower := (rows 321 7 14 73 176 32 64 128 256), losses := [] }

theorem u17831 : Upper (D 8) (R 8) [320,5,10,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17831 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17832 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 14 88 49 160 224 160 416), lower := (rows 321 7 14 88 49 32 64 128 256), losses := [] }

theorem u17832 : Upper (D 8) (R 8) [320,5,10,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17832 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17833 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 14 88 145 160 224 160 416), lower := (rows 321 7 14 88 145 32 64 128 256), losses := [] }

theorem u17833 : Upper (D 8) (R 8) [320,5,10,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17833 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17834 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 14 88 176 161 225 161 417), lower := (rows 321 7 14 88 176 32 64 128 256), losses := [] }

theorem u17834 : Upper (D 8) (R 8) [320,5,10,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17834 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17835 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 14 104 49 176 240 176 432), lower := (rows 321 7 14 104 49 32 64 128 256), losses := [] }

theorem u17835 : Upper (D 8) (R 8) [320,5,10,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17835 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17836 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 14 104 145 176 240 176 432), lower := (rows 321 7 14 104 145 32 64 128 256), losses := [] }

theorem u17836 : Upper (D 8) (R 8) [320,5,10,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17836 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17837 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 14 104 176 177 241 177 433), lower := (rows 321 7 14 104 176 32 64 128 256), losses := [] }

theorem u17837 : Upper (D 8) (R 8) [320,5,10,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17837 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17838 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 14 137 112 176 240 176 432), lower := (rows 321 7 14 137 112 32 64 128 256), losses := [] }

theorem u17838 : Upper (D 8) (R 8) [320,5,10,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17838 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17839 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 14 137 176 112 112 240 368), lower := (rows 321 7 14 137 176 32 64 128 256), losses := [] }

theorem u17839 : Upper (D 8) (R 8) [320,5,10,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17839 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17840 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 14 137 208 48 112 176 304), lower := (rows 321 7 14 137 208 32 64 128 256), losses := [] }

theorem u17840 : Upper (D 8) (R 8) [320,5,10,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17840 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17841 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 14 152 49 224 224 224 480), lower := (rows 321 7 14 152 49 32 64 128 256), losses := [] }

theorem u17841 : Upper (D 8) (R 8) [320,5,10,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17841 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17842 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 14 152 81 160 224 160 416), lower := (rows 321 7 14 152 81 32 64 128 256), losses := [] }

theorem u17842 : Upper (D 8) (R 8) [320,5,10,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17842 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17843 : Route 9 := (fun mask => (mask,id))

def c17843 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17843 : Upper (D 8) (R 8) [320,5,10,144,96] 13 := by
  apply FastRouting.sound _ _ [320,5,10,144,96] 13 (by decide) (choices 1) [1,128] r17843 c17843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6620
  · exact u6621

def b17844 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 14 152 145 96 96 224 352), lower := (rows 321 7 14 152 145 32 64 128 256), losses := [] }

theorem u17844 : Upper (D 8) (R 8) [320,5,10,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17844 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17845 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 14 152 176 97 97 225 353), lower := (rows 321 7 14 152 176 32 64 128 256), losses := [] }

theorem u17845 : Upper (D 8) (R 8) [320,5,10,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17845 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17846 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 14 152 208 33 97 161 289), lower := (rows 321 7 14 152 208 32 64 128 256), losses := [] }

theorem u17846 : Upper (D 8) (R 8) [320,5,10,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17846 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17847 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 14 168 49 240 240 240 496), lower := (rows 321 7 14 168 49 32 64 128 256), losses := [] }

theorem u17847 : Upper (D 8) (R 8) [320,5,10,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17847 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17848 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 14 168 81 176 240 176 432), lower := (rows 321 7 14 168 81 32 64 128 256), losses := [] }

theorem u17848 : Upper (D 8) (R 8) [320,5,10,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17848 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17849 : Route 9 := (fun mask => (mask,id))

def c17849 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17849 : Upper (D 8) (R 8) [320,5,10,160,96] 13 := by
  apply FastRouting.sound _ _ [320,5,10,160,96] 13 (by decide) (choices 1) [1,16,128] r17849 c17849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6622
  · exact u6623
  · exact u6624

def b17850 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 14 168 145 112 112 240 368), lower := (rows 321 7 14 168 145 32 64 128 256), losses := [] }

theorem u17850 : Upper (D 8) (R 8) [320,5,10,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17850 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17851 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 14 168 176 113 113 241 369), lower := (rows 321 7 14 168 176 32 64 128 256), losses := [] }

theorem u17851 : Upper (D 8) (R 8) [320,5,10,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17851 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17852 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 289, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 14 168 208 49 113 177 305), lower := (rows 321 7 14 168 208 32 64 128 256), losses := [] }

theorem u17852 : Upper (D 8) (R 8) [320,5,10,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17852 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17853 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 14 200 49 176 240 176 432), lower := (rows 321 7 14 200 49 32 64 128 256), losses := [] }

theorem u17853 : Upper (D 8) (R 8) [320,5,10,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17853 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17854 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 14 200 145 48 112 176 304), lower := (rows 321 7 14 200 145 32 64 128 256), losses := [] }

theorem u17854 : Upper (D 8) (R 8) [320,5,10,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17854 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17855 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 14 200 176 49 113 177 305), lower := (rows 321 7 14 200 176 32 64 128 256), losses := [] }

theorem u17855 : Upper (D 8) (R 8) [320,5,10,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17855 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17856 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 22, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 28 41 50 224 224 224 480), lower := (rows 321 7 28 41 50 32 64 128 256), losses := [] }

theorem u17856 : Upper (D 8) (R 8) [320,5,24,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17856 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17857 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 28 41 82 160 224 160 416), lower := (rows 321 7 28 41 82 32 64 128 256), losses := [] }

theorem u17857 : Upper (D 8) (R 8) [320,5,24,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17857 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17858 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 28 41 112 162 226 162 418), lower := (rows 321 7 28 41 112 32 64 128 256), losses := [] }

theorem u17858 : Upper (D 8) (R 8) [320,5,24,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17858 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17859 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 28 41 146 224 224 224 480), lower := (rows 321 7 28 41 146 32 64 128 256), losses := [] }

theorem u17859 : Upper (D 8) (R 8) [320,5,24,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17859 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17860 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 28 41 176 226 226 226 482), lower := (rows 321 7 28 41 176 32 64 128 256), losses := [] }

theorem u17860 : Upper (D 8) (R 8) [320,5,24,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17860 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17861 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 28 41 208 162 226 162 418), lower := (rows 321 7 28 41 208 32 64 128 256), losses := [] }

theorem u17861 : Upper (D 8) (R 8) [320,5,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17861 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17862 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 28 42 81 160 224 160 416), lower := (rows 321 7 28 42 81 32 64 128 256), losses := [] }

theorem u17862 : Upper (D 8) (R 8) [320,5,24,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17862 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17863 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 28 42 112 161 225 161 417), lower := (rows 321 7 28 42 112 32 64 128 256), losses := [] }

theorem u17863 : Upper (D 8) (R 8) [320,5,24,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17863 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17864 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 28 42 145 224 224 224 480), lower := (rows 321 7 28 42 145 32 64 128 256), losses := [] }

theorem u17864 : Upper (D 8) (R 8) [320,5,24,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17864 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17865 : Route 9 := (fun mask => (mask,id))

def c17865 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17865 : Upper (D 8) (R 8) [320,5,24,34,160] 13 := by
  apply FastRouting.sound _ _ [320,5,24,34,160] 13 (by decide) (choices 1) [1,64,128] r17865 c17865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6625
  · exact u6626
  · exact u6627

def b17866 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 28 42 208 161 225 161 417), lower := (rows 321 7 28 42 208 32 64 128 256), losses := [] }

theorem u17866 : Upper (D 8) (R 8) [320,5,24,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17866 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17867 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 28 73 146 160 224 160 416), lower := (rows 321 7 28 73 146 32 64 128 256), losses := [] }

theorem u17867 : Upper (D 8) (R 8) [320,5,24,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17867 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17868 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 28 73 176 162 226 162 418), lower := (rows 321 7 28 73 176 32 64 128 256), losses := [] }

theorem u17868 : Upper (D 8) (R 8) [320,5,24,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17868 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17869 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 28 74 145 160 224 160 416), lower := (rows 321 7 28 74 145 32 64 128 256), losses := [] }

theorem u17869 : Upper (D 8) (R 8) [320,5,24,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17869 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17870 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 28 74 176 161 225 161 417), lower := (rows 321 7 28 74 176 32 64 128 256), losses := [] }

theorem u17870 : Upper (D 8) (R 8) [320,5,24,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17870 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17871 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 28 104 145 162 226 162 418), lower := (rows 321 7 28 104 145 32 64 128 256), losses := [] }

theorem u17871 : Upper (D 8) (R 8) [320,5,24,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17871 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17872 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 28 104 146 161 225 161 417), lower := (rows 321 7 28 104 146 32 64 128 256), losses := [] }

theorem u17872 : Upper (D 8) (R 8) [320,5,24,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17872 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17873 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 28 104 176 163 227 163 419), lower := (rows 321 7 28 104 176 32 64 128 256), losses := [] }

theorem u17873 : Upper (D 8) (R 8) [320,5,24,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17873 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17874 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 28 137 146 96 96 224 352), lower := (rows 321 7 28 137 146 32 64 128 256), losses := [] }

theorem u17874 : Upper (D 8) (R 8) [320,5,24,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17874 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17875 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 28 137 176 98 98 226 354), lower := (rows 321 7 28 137 176 32 64 128 256), losses := [] }

theorem u17875 : Upper (D 8) (R 8) [320,5,24,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17875 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17876 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 28 137 208 34 98 162 290), lower := (rows 321 7 28 137 208 32 64 128 256), losses := [] }

theorem u17876 : Upper (D 8) (R 8) [320,5,24,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17876 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17877 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 28 138 176 97 97 225 353), lower := (rows 321 7 28 138 176 32 64 128 256), losses := [] }

theorem u17877 : Upper (D 8) (R 8) [320,5,24,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17877 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17878 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 28 138 208 33 97 161 289), lower := (rows 321 7 28 138 208 32 64 128 256), losses := [] }

theorem u17878 : Upper (D 8) (R 8) [320,5,24,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17878 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17879 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 28 168 176 99 99 227 355), lower := (rows 321 7 28 168 176 32 64 128 256), losses := [] }

theorem u17879 : Upper (D 8) (R 8) [320,5,24,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17879 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u17879
end Delivery.IrregularNine14.P08
