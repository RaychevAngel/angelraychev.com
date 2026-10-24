import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0011
import IrregularNine14P08C0012

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5880 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 13 104 208 33 240 176 432), lower := (rows 259 38 13 104 208 33 64 128 256), losses := [] }

theorem u5880 : Upper (D 8) (R 8) [258,36,9,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5880 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5881 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 38 13 104 208 48 225 161 417), lower := (rows 259 38 13 104 208 48 64 128 256), losses := [] }

theorem u5881 : Upper (D 8) (R 8) [258,36,9,96,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5881 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5882 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 40, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 13 104 208 160 113 177 305), lower := (rows 259 38 13 104 208 160 64 128 256), losses := [] }

theorem u5882 : Upper (D 8) (R 8) [258,36,9,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5882 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5883 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 13 200 112 33 240 176 432), lower := (rows 259 38 13 200 112 33 64 128 256), losses := [] }

theorem u5883 : Upper (D 8) (R 8) [258,36,9,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5883 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5884 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 38 13 200 112 48 225 161 417), lower := (rows 259 38 13 200 112 48 64 128 256), losses := [] }

theorem u5884 : Upper (D 8) (R 8) [258,36,9,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5884 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5885 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 13 200 112 160 113 177 305), lower := (rows 259 38 13 200 112 160 64 128 256), losses := [] }

theorem u5885 : Upper (D 8) (R 8) [258,36,9,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5885 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5886 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 214, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 28 41 208 33 224 224 480), lower := (rows 259 38 28 41 208 33 64 128 256), losses := [] }

theorem u5886 : Upper (D 8) (R 8) [258,36,24,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5886 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5887 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 28 41 208 96 225 161 417), lower := (rows 259 38 28 41 208 96 64 128 256), losses := [] }

theorem u5887 : Upper (D 8) (R 8) [258,36,24,33,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5887 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5888 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 28 73 176 33 224 224 480), lower := (rows 259 38 28 73 176 33 64 128 256), losses := [] }

theorem u5888 : Upper (D 8) (R 8) [258,36,24,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5888 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5889 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 28 73 176 96 225 161 417), lower := (rows 259 38 28 73 176 96 64 128 256), losses := [] }

theorem u5889 : Upper (D 8) (R 8) [258,36,24,65,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5889 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5890 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 28 73 176 160 97 225 353), lower := (rows 259 38 28 73 176 160 64 128 256), losses := [] }

theorem u5890 : Upper (D 8) (R 8) [258,36,24,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5890 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5891 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 69 56 152 33 224 224 480), lower := (rows 259 38 69 56 152 33 64 128 256), losses := [] }

theorem u5891 : Upper (D 8) (R 8) [258,36,65,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5891 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5892 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 69 56 152 96 225 161 417), lower := (rows 259 38 69 56 152 96 64 128 256), losses := [] }

theorem u5892 : Upper (D 8) (R 8) [258,36,65,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5892 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5893 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 69 56 152 160 97 225 353), lower := (rows 259 38 69 56 152 160 64 128 256), losses := [] }

theorem u5893 : Upper (D 8) (R 8) [258,36,65,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5893 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5894 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 69 56 208 33 232 168 424), lower := (rows 259 38 69 56 208 33 64 128 256), losses := [] }

theorem u5894 : Upper (D 8) (R 8) [258,36,65,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5894 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5895 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 38 69 56 208 40 225 161 417), lower := (rows 259 38 69 56 208 40 64 128 256), losses := [] }

theorem u5895 : Upper (D 8) (R 8) [258,36,65,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5895 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5896 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 69 56 208 160 105 169 297), lower := (rows 259 38 69 56 208 160 64 128 256), losses := [] }

theorem u5896 : Upper (D 8) (R 8) [258,36,65,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5896 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5897 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 69 88 176 33 232 168 424), lower := (rows 259 38 69 88 176 33 64 128 256), losses := [] }

theorem u5897 : Upper (D 8) (R 8) [258,36,65,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5897 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5898 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 38 69 88 176 40 225 161 417), lower := (rows 259 38 69 88 176 40 64 128 256), losses := [] }

theorem u5898 : Upper (D 8) (R 8) [258,36,65,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5898 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5899 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 69 88 176 160 105 169 297), lower := (rows 259 38 69 88 176 160 64 128 256), losses := [] }

theorem u5899 : Upper (D 8) (R 8) [258,36,65,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5899 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5900 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 69 104 152 33 240 176 432), lower := (rows 259 38 69 104 152 33 64 128 256), losses := [] }

theorem u5900 : Upper (D 8) (R 8) [258,36,65,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5900 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5901 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 38 69 104 152 48 225 161 417), lower := (rows 259 38 69 104 152 48 64 128 256), losses := [] }

theorem u5901 : Upper (D 8) (R 8) [258,36,65,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5901 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r5902 : Route 9 := (fun mask => (mask,id))

def c5902 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5902 : Upper (D 8) (R 8) [258,36,65,96,136,128] 13 := by
  apply FastRouting.sound _ _ [258,36,65,96,136,128] 13 (by decide) (choices 1) [1,16,32] r5902 c5902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u718
  · exact u719
  · exact u720

def b5903 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 69 104 176 33 216 152 408), lower := (rows 259 38 69 104 176 33 64 128 256), losses := [] }

theorem u5903 : Upper (D 8) (R 8) [258,36,65,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5903 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5904 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 259 38 69 104 176 40 209 145 401), lower := (rows 259 38 69 104 176 40 64 128 256), losses := [] }

theorem u5904 : Upper (D 8) (R 8) [258,36,65,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5904 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5905 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 259 38 69 104 176 48 201 137 393), lower := (rows 259 38 69 104 176 48 64 128 256), losses := [] }

theorem u5905 : Upper (D 8) (R 8) [258,36,65,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5905 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5906 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 69 104 176 160 89 153 281), lower := (rows 259 38 69 104 176 160 64 128 256), losses := [] }

theorem u5906 : Upper (D 8) (R 8) [258,36,65,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5906 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5907 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 69 168 208 33 120 184 312), lower := (rows 259 38 69 168 208 33 64 128 256), losses := [] }

theorem u5907 : Upper (D 8) (R 8) [258,36,65,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5907 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5908 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 259 38 69 168 208 40 113 177 305), lower := (rows 259 38 69 168 208 40 64 128 256), losses := [] }

theorem u5908 : Upper (D 8) (R 8) [258,36,65,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5908 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5909 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 259 38 69 168 208 48 105 169 297), lower := (rows 259 38 69 168 208 48 64 128 256), losses := [] }

theorem u5909 : Upper (D 8) (R 8) [258,36,65,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5909 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5910 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 76 25 176 33 224 224 480), lower := (rows 259 38 76 25 176 33 64 128 256), losses := [] }

theorem u5910 : Upper (D 8) (R 8) [258,36,72,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5910 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5911 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 76 25 176 96 225 161 417), lower := (rows 259 38 76 25 176 96 64 128 256), losses := [] }

theorem u5911 : Upper (D 8) (R 8) [258,36,72,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5911 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5912 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 76 25 176 160 97 225 353), lower := (rows 259 38 76 25 176 160 64 128 256), losses := [] }

theorem u5912 : Upper (D 8) (R 8) [258,36,72,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5912 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5913 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 214, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 76 41 112 33 208 144 400), lower := (rows 259 38 76 41 112 33 64 128 256), losses := [] }

theorem u5913 : Upper (D 8) (R 8) [258,36,72,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5913 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5914 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 259 38 76 41 112 48 193 129 385), lower := (rows 259 38 76 41 112 48 64 128 256), losses := [] }

theorem u5914 : Upper (D 8) (R 8) [258,36,72,33,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5914 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r5915 : Route 9 := (fun mask => (mask,id))

def c5915 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5915 : Upper (D 8) (R 8) [258,36,72,33,96,128] 13 := by
  apply FastRouting.sound _ _ [258,36,72,33,96,128] 13 (by decide) (choices 1) [1,16,128] r5915 c5915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u721
  · exact u722
  · exact u723

def b5916 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 259 38 76 41 145 48 224 224 480), lower := (rows 259 38 76 41 145 48 64 128 256), losses := [] }

theorem u5916 : Upper (D 8) (R 8) [258,36,72,33,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5916 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5917 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 76 41 145 96 240 176 432), lower := (rows 259 38 76 41 145 96 64 128 256), losses := [] }

theorem u5917 : Upper (D 8) (R 8) [258,36,72,33,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5917 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5918 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 259 38 76 41 145 160 112 240 368), lower := (rows 259 38 76 41 145 160 64 128 256), losses := [] }

theorem u5918 : Upper (D 8) (R 8) [258,36,72,33,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5918 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5919 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 214, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 76 41 176 33 208 208 464), lower := (rows 259 38 76 41 176 33 64 128 256), losses := [] }

theorem u5919 : Upper (D 8) (R 8) [258,36,72,33,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5919 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5920 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 259 38 76 41 176 48 193 193 449), lower := (rows 259 38 76 41 176 48 64 128 256), losses := [] }

theorem u5920 : Upper (D 8) (R 8) [258,36,72,33,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5920 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5921 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 76 41 176 96 209 145 401), lower := (rows 259 38 76 41 176 96 64 128 256), losses := [] }

theorem u5921 : Upper (D 8) (R 8) [258,36,72,33,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5921 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5922 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 76 41 176 160 81 209 337), lower := (rows 259 38 76 41 176 160 64 128 256), losses := [] }

theorem u5922 : Upper (D 8) (R 8) [258,36,72,33,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5922 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5923 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 214, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 76 41 208 33 240 176 432), lower := (rows 259 38 76 41 208 33 64 128 256), losses := [] }

theorem u5923 : Upper (D 8) (R 8) [258,36,72,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5923 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5924 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 38 76 41 208 48 225 161 417), lower := (rows 259 38 76 41 208 48 64 128 256), losses := [] }

theorem u5924 : Upper (D 8) (R 8) [258,36,72,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5924 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r5925 : Route 9 := (fun mask => (mask,id))

def c5925 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5925 : Upper (D 8) (R 8) [258,36,72,33,192,128] 13 := by
  apply FastRouting.sound _ _ [258,36,72,33,192,128] 13 (by decide) (choices 1) [1,16,32] r5925 c5925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u724
  · exact u725
  · exact u726

def b5926 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 198, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 76 56 145 33 224 224 480), lower := (rows 259 38 76 56 145 33 64 128 256), losses := [] }

theorem u5926 : Upper (D 8) (R 8) [258,36,72,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5926 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5927 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 76 56 145 96 225 161 417), lower := (rows 259 38 76 56 145 96 64 128 256), losses := [] }

theorem u5927 : Upper (D 8) (R 8) [258,36,72,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5927 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5928 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 76 56 145 160 97 225 353), lower := (rows 259 38 76 56 145 160 64 128 256), losses := [] }

theorem u5928 : Upper (D 8) (R 8) [258,36,72,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5928 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5929 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 259 38 76 137 49 48 224 224 480), lower := (rows 259 38 76 137 49 48 64 128 256), losses := [] }

theorem u5929 : Upper (D 8) (R 8) [258,36,72,129,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5929 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5930 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 76 137 49 96 240 176 432), lower := (rows 259 38 76 137 49 96 64 128 256), losses := [] }

theorem u5930 : Upper (D 8) (R 8) [258,36,72,129,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5930 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5931 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 76 137 49 160 112 240 368), lower := (rows 259 38 76 137 49 160 64 128 256), losses := [] }

theorem u5931 : Upper (D 8) (R 8) [258,36,72,129,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5931 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5932 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 76 137 112 33 240 176 432), lower := (rows 259 38 76 137 112 33 64 128 256), losses := [] }

theorem u5932 : Upper (D 8) (R 8) [258,36,72,129,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5932 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5933 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 38 76 137 112 48 225 161 417), lower := (rows 259 38 76 137 112 48 64 128 256), losses := [] }

theorem u5933 : Upper (D 8) (R 8) [258,36,72,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5933 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5934 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 76 137 112 160 113 177 305), lower := (rows 259 38 76 137 112 160 64 128 256), losses := [] }

theorem u5934 : Upper (D 8) (R 8) [258,36,72,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5934 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5935 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 76 137 176 33 112 240 368), lower := (rows 259 38 76 137 176 33 64 128 256), losses := [] }

theorem u5935 : Upper (D 8) (R 8) [258,36,72,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5935 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5936 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 259 38 76 137 176 48 97 225 353), lower := (rows 259 38 76 137 176 48 64 128 256), losses := [] }

theorem u5936 : Upper (D 8) (R 8) [258,36,72,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5936 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5937 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 76 137 176 96 113 177 305), lower := (rows 259 38 76 137 176 96 64 128 256), losses := [] }

theorem u5937 : Upper (D 8) (R 8) [258,36,72,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5937 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5938 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 76 137 208 33 112 176 304), lower := (rows 259 38 76 137 208 33 64 128 256), losses := [] }

theorem u5938 : Upper (D 8) (R 8) [258,36,72,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5938 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5939 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 38 76 137 208 48 97 161 289), lower := (rows 259 38 76 137 208 48 64 128 256), losses := [] }

theorem u5939 : Upper (D 8) (R 8) [258,36,72,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5939 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u5939
end Delivery.IrregularNine14.P08
