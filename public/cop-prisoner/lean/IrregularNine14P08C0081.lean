import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0011

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4860 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 38 76 56 273 34 193 129 385), lower := (rows 97 38 76 56 273 34 64 128 256), losses := [] }

theorem u4860 : Upper (D 8) (R 8) [96,36,72,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4860 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4861 : Route 9 := (fun mask => (mask,id))

def c4861 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4861 : Upper (D 8) (R 8) [96,36,72,48,257,128] 13 := by
  apply FastRouting.sound _ _ [96,36,72,48,257,128] 13 (by decide) (choices 1) [1,2,128] r4861 c4861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u665
  · exact u666
  · exact u667

def b4862 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 56 274 33 193 129 385), lower := (rows 97 38 76 56 274 33 64 128 256), losses := [] }

theorem u4862 : Upper (D 8) (R 8) [96,36,72,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4862 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4863 : Route 9 := (fun mask => (mask,id))

def c4863 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4863 : Upper (D 8) (R 8) [96,36,72,48,258,128] 13 := by
  apply FastRouting.sound _ _ [96,36,72,48,258,128] 13 (by decide) (choices 1) [1,128] r4863 c4863
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u668
  · exact u669

def b4864 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 56 400 33 195 131 387), lower := (rows 97 38 76 56 400 33 64 128 256), losses := [] }

theorem u4864 : Upper (D 8) (R 8) [96,36,72,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4864 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4865 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 38 76 56 400 34 193 129 385), lower := (rows 97 38 76 56 400 34 64 128 256), losses := [] }

theorem u4865 : Upper (D 8) (R 8) [96,36,72,48,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4865 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4866 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 56 400 160 67 131 259), lower := (rows 97 38 76 56 400 160 64 128 256), losses := [] }

theorem u4866 : Upper (D 8) (R 8) [96,36,72,48,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4866 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4867 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 137 176 33 338 402 274), lower := (rows 97 38 76 137 176 33 64 128 256), losses := [] }

theorem u4867 : Upper (D 8) (R 8) [96,36,72,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4867 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4868 : PairBound 9 := { available := 273, camps := [], pairs := [], upper := (rows 97 38 76 137 176 34 337 401 273), lower := (rows 97 38 76 137 176 34 64 128 256), losses := [] }

theorem u4868 : Upper (D 8) (R 8) [96,36,72,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4868 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4869 : PairBound 9 := { available := 259, camps := [], pairs := [], upper := (rows 97 38 76 137 176 48 323 387 259), lower := (rows 97 38 76 137 176 48 64 128 256), losses := [] }

theorem u4869 : Upper (D 8) (R 8) [96,36,72,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4869 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4870 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 97 38 76 137 176 288 83 147 275), lower := (rows 97 38 76 137 176 288 64 128 256), losses := [] }

theorem u4870 : Upper (D 8) (R 8) [96,36,72,129,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4870 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4871 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 97 38 76 137 273 34 240 176 432), lower := (rows 97 38 76 137 273 34 64 128 256), losses := [] }

theorem u4871 : Upper (D 8) (R 8) [96,36,72,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4871 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4872 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 97 38 76 137 273 48 226 162 418), lower := (rows 97 38 76 137 273 48 64 128 256), losses := [] }

theorem u4872 : Upper (D 8) (R 8) [96,36,72,129,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4872 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4873 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 137 273 160 114 178 306), lower := (rows 97 38 76 137 273 160 64 128 256), losses := [] }

theorem u4873 : Upper (D 8) (R 8) [96,36,72,129,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4873 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4874 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 137 274 33 240 176 432), lower := (rows 97 38 76 137 274 33 64 128 256), losses := [] }

theorem u4874 : Upper (D 8) (R 8) [96,36,72,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4874 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4875 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 38 76 137 274 48 225 161 417), lower := (rows 97 38 76 137 274 48 64 128 256), losses := [] }

theorem u4875 : Upper (D 8) (R 8) [96,36,72,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4875 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4876 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 137 274 160 113 177 305), lower := (rows 97 38 76 137 274 160 64 128 256), losses := [] }

theorem u4876 : Upper (D 8) (R 8) [96,36,72,129,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4876 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4877 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 137 304 33 210 146 402), lower := (rows 97 38 76 137 304 33 64 128 256), losses := [] }

theorem u4877 : Upper (D 8) (R 8) [96,36,72,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4877 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4878 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 97 38 76 137 304 34 209 145 401), lower := (rows 97 38 76 137 304 34 64 128 256), losses := [] }

theorem u4878 : Upper (D 8) (R 8) [96,36,72,129,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4878 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4879 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 97 38 76 137 304 48 195 131 387), lower := (rows 97 38 76 137 304 48 64 128 256), losses := [] }

theorem u4879 : Upper (D 8) (R 8) [96,36,72,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4879 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4880 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 137 304 160 83 147 275), lower := (rows 97 38 76 137 304 160 64 128 256), losses := [] }

theorem u4880 : Upper (D 8) (R 8) [96,36,72,129,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4880 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4881 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 137 400 33 114 178 306), lower := (rows 97 38 76 137 400 33 64 128 256), losses := [] }

theorem u4881 : Upper (D 8) (R 8) [96,36,72,129,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4881 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4882 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 38 76 137 400 34 113 177 305), lower := (rows 97 38 76 137 400 34 64 128 256), losses := [] }

theorem u4882 : Upper (D 8) (R 8) [96,36,72,129,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4882 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4883 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 38 76 137 400 48 99 163 291), lower := (rows 97 38 76 137 400 48 64 128 256), losses := [] }

theorem u4883 : Upper (D 8) (R 8) [96,36,72,129,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4883 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4884 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 152 273 33 226 162 418), lower := (rows 97 38 76 152 273 33 64 128 256), losses := [] }

theorem u4884 : Upper (D 8) (R 8) [96,36,72,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4884 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4885 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 38 76 152 273 34 225 161 417), lower := (rows 97 38 76 152 273 34 64 128 256), losses := [] }

theorem u4885 : Upper (D 8) (R 8) [96,36,72,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4885 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4886 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 152 273 160 99 163 291), lower := (rows 97 38 76 152 273 160 64 128 256), losses := [] }

theorem u4886 : Upper (D 8) (R 8) [96,36,72,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4886 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4887 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 152 274 33 225 161 417), lower := (rows 97 38 76 152 274 33 64 128 256), losses := [] }

theorem u4887 : Upper (D 8) (R 8) [96,36,72,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4887 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4888 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 152 274 160 97 161 289), lower := (rows 97 38 76 152 274 160 64 128 256), losses := [] }

theorem u4888 : Upper (D 8) (R 8) [96,36,72,144,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4888 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4889 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 152 304 33 195 131 387), lower := (rows 97 38 76 152 304 33 64 128 256), losses := [] }

theorem u4889 : Upper (D 8) (R 8) [96,36,72,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4889 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4890 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 38 76 152 304 34 193 129 385), lower := (rows 97 38 76 152 304 34 64 128 256), losses := [] }

theorem u4890 : Upper (D 8) (R 8) [96,36,72,144,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4890 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4891 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 152 304 160 67 131 259), lower := (rows 97 38 76 152 304 160 64 128 256), losses := [] }

theorem u4891 : Upper (D 8) (R 8) [96,36,72,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4891 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4892 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 168 145 33 338 402 274), lower := (rows 97 38 76 168 145 33 64 128 256), losses := [] }

theorem u4892 : Upper (D 8) (R 8) [96,36,72,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4892 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4893 : PairBound 9 := { available := 273, camps := [], pairs := [], upper := (rows 97 38 76 168 145 34 337 401 273), lower := (rows 97 38 76 168 145 34 64 128 256), losses := [] }

theorem u4893 : Upper (D 8) (R 8) [96,36,72,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4893 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4894 : PairBound 9 := { available := 259, camps := [], pairs := [], upper := (rows 97 38 76 168 145 48 323 387 259), lower := (rows 97 38 76 168 145 48 64 128 256), losses := [] }

theorem u4894 : Upper (D 8) (R 8) [96,36,72,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4894 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4895 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 97 38 76 168 145 288 83 147 275), lower := (rows 97 38 76 168 145 288 64 128 256), losses := [] }

theorem u4895 : Upper (D 8) (R 8) [96,36,72,160,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4895 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4896 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 168 273 33 210 146 402), lower := (rows 97 38 76 168 273 33 64 128 256), losses := [] }

theorem u4896 : Upper (D 8) (R 8) [96,36,72,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4896 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4897 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 97 38 76 168 273 34 209 145 401), lower := (rows 97 38 76 168 273 34 64 128 256), losses := [] }

theorem u4897 : Upper (D 8) (R 8) [96,36,72,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4897 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4898 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 97 38 76 168 273 48 195 131 387), lower := (rows 97 38 76 168 273 48 64 128 256), losses := [] }

theorem u4898 : Upper (D 8) (R 8) [96,36,72,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4898 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4899 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 168 273 160 83 147 275), lower := (rows 97 38 76 168 273 160 64 128 256), losses := [] }

theorem u4899 : Upper (D 8) (R 8) [96,36,72,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4899 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4900 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 168 274 33 209 145 401), lower := (rows 97 38 76 168 274 33 64 128 256), losses := [] }

theorem u4900 : Upper (D 8) (R 8) [96,36,72,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4900 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4901 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 38 76 168 274 48 193 129 385), lower := (rows 97 38 76 168 274 48 64 128 256), losses := [] }

theorem u4901 : Upper (D 8) (R 8) [96,36,72,160,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4901 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4902 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 168 274 160 81 145 273), lower := (rows 97 38 76 168 274 160 64 128 256), losses := [] }

theorem u4902 : Upper (D 8) (R 8) [96,36,72,160,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4902 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4903 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 168 400 33 83 147 275), lower := (rows 97 38 76 168 400 33 64 128 256), losses := [] }

theorem u4903 : Upper (D 8) (R 8) [96,36,72,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4903 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4904 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 38 76 168 400 34 81 145 273), lower := (rows 97 38 76 168 400 34 64 128 256), losses := [] }

theorem u4904 : Upper (D 8) (R 8) [96,36,72,160,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4904 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4905 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 38 76 168 400 48 67 131 259), lower := (rows 97 38 76 168 400 48 64 128 256), losses := [] }

theorem u4905 : Upper (D 8) (R 8) [96,36,72,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4905 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4906 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 97 38 76 265 145 34 240 176 432), lower := (rows 97 38 76 265 145 34 64 128 256), losses := [] }

theorem u4906 : Upper (D 8) (R 8) [96,36,72,257,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4906 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4907 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 97 38 76 265 145 48 226 162 418), lower := (rows 97 38 76 265 145 48 64 128 256), losses := [] }

theorem u4907 : Upper (D 8) (R 8) [96,36,72,257,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4907 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4908 : Route 9 := (fun mask => (mask,id))

def c4908 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4908 : Upper (D 8) (R 8) [96,36,72,257,129,128] 13 := by
  apply FastRouting.sound _ _ [96,36,72,257,129,128] 13 (by decide) (choices 1) [2,16,32] r4908 c4908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u670
  · exact u671
  · exact u672

def b4909 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 265 146 33 240 176 432), lower := (rows 97 38 76 265 146 33 64 128 256), losses := [] }

theorem u4909 : Upper (D 8) (R 8) [96,36,72,257,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4909 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4910 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 38 76 265 146 48 225 161 417), lower := (rows 97 38 76 265 146 48 64 128 256), losses := [] }

theorem u4910 : Upper (D 8) (R 8) [96,36,72,257,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4910 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4911 : Route 9 := (fun mask => (mask,id))

def c4911 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4911 : Upper (D 8) (R 8) [96,36,72,257,130,128] 13 := by
  apply FastRouting.sound _ _ [96,36,72,257,130,128] 13 (by decide) (choices 1) [1,16,32] r4911 c4911
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u673
  · exact u674
  · exact u675

def b4912 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 265 176 33 210 146 402), lower := (rows 97 38 76 265 176 33 64 128 256), losses := [] }

theorem u4912 : Upper (D 8) (R 8) [96,36,72,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4912 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4913 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 97 38 76 265 176 34 209 145 401), lower := (rows 97 38 76 265 176 34 64 128 256), losses := [] }

theorem u4913 : Upper (D 8) (R 8) [96,36,72,257,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4913 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4914 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 97 38 76 265 176 48 195 131 387), lower := (rows 97 38 76 265 176 48 64 128 256), losses := [] }

theorem u4914 : Upper (D 8) (R 8) [96,36,72,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4914 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4915 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 265 176 160 83 147 275), lower := (rows 97 38 76 265 176 160 64 128 256), losses := [] }

theorem u4915 : Upper (D 8) (R 8) [96,36,72,257,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4915 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4916 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 280 145 33 226 162 418), lower := (rows 97 38 76 280 145 33 64 128 256), losses := [] }

theorem u4916 : Upper (D 8) (R 8) [96,36,72,272,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4916 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4917 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 38 76 280 145 34 225 161 417), lower := (rows 97 38 76 280 145 34 64 128 256), losses := [] }

theorem u4917 : Upper (D 8) (R 8) [96,36,72,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4917 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4918 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 280 145 160 99 163 291), lower := (rows 97 38 76 280 145 160 64 128 256), losses := [] }

theorem u4918 : Upper (D 8) (R 8) [96,36,72,272,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4918 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4919 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 280 146 33 225 161 417), lower := (rows 97 38 76 280 146 33 64 128 256), losses := [] }

theorem u4919 : Upper (D 8) (R 8) [96,36,72,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4919 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u4919
end Delivery.IrregularNine14.P08
