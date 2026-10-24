import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0043
import IrregularNine14P08C0044

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9840 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 28 137 148 97 97 225 353), lower := (rows 35 322 28 137 148 32 64 128 256), losses := [] }

theorem u9840 : Upper (D 8) (R 8) [34,320,24,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9840 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9841 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 28 137 176 101 101 229 357), lower := (rows 35 322 28 137 176 32 64 128 256), losses := [] }

theorem u9841 : Upper (D 8) (R 8) [34,320,24,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9841 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9842 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 28 137 208 37 101 165 293), lower := (rows 35 322 28 137 208 32 64 128 256), losses := [] }

theorem u9842 : Upper (D 8) (R 8) [34,320,24,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9842 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9843 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 28 140 176 97 97 225 353), lower := (rows 35 322 28 140 176 32 64 128 256), losses := [] }

theorem u9843 : Upper (D 8) (R 8) [34,320,24,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9843 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9844 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 28 140 208 33 97 161 289), lower := (rows 35 322 28 140 208 32 64 128 256), losses := [] }

theorem u9844 : Upper (D 8) (R 8) [34,320,24,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9844 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9845 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 28 168 176 101 69 197 325), lower := (rows 35 322 28 168 176 32 64 128 256), losses := [] }

theorem u9845 : Upper (D 8) (R 8) [34,320,24,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9845 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9846 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 28 168 208 37 101 165 293), lower := (rows 35 322 28 168 208 32 64 128 256), losses := [] }

theorem u9846 : Upper (D 8) (R 8) [34,320,24,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9846 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9847 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 37 44 88 177 209 145 401), lower := (rows 35 322 37 44 88 32 64 128 256), losses := [] }

theorem u9847 : Upper (D 8) (R 8) [34,320,33,36,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9847 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9848 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 37 44 145 248 216 216 472), lower := (rows 35 322 37 44 145 32 64 128 256), losses := [] }

theorem u9848 : Upper (D 8) (R 8) [34,320,33,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9848 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9849 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 37 44 152 241 209 209 465), lower := (rows 35 322 37 44 152 32 64 128 256), losses := [] }

theorem u9849 : Upper (D 8) (R 8) [34,320,33,36,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9849 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9850 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 37 44 208 185 217 153 409), lower := (rows 35 322 37 44 208 32 64 128 256), losses := [] }

theorem u9850 : Upper (D 8) (R 8) [34,320,33,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9850 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9851 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 37 56 84 169 201 137 393), lower := (rows 35 322 37 56 84 32 64 128 256), losses := [] }

theorem u9851 : Upper (D 8) (R 8) [34,320,33,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9851 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9852 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 37 56 145 236 204 204 460), lower := (rows 35 322 37 56 145 32 64 128 256), losses := [] }

theorem u9852 : Upper (D 8) (R 8) [34,320,33,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9852 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9853 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 37 56 148 233 201 201 457), lower := (rows 35 322 37 56 148 32 64 128 256), losses := [] }

theorem u9853 : Upper (D 8) (R 8) [34,320,33,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9853 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9854 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 37 56 152 229 197 197 453), lower := (rows 35 322 37 56 152 32 64 128 256), losses := [] }

theorem u9854 : Upper (D 8) (R 8) [34,320,33,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9854 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9855 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 37 56 208 173 205 141 397), lower := (rows 35 322 37 56 208 32 64 128 256), losses := [] }

theorem u9855 : Upper (D 8) (R 8) [34,320,33,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9855 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9856 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 37 76 145 184 248 184 440), lower := (rows 35 322 37 76 145 32 64 128 256), losses := [] }

theorem u9856 : Upper (D 8) (R 8) [34,320,33,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9856 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9857 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 37 76 152 177 241 177 433), lower := (rows 35 322 37 76 152 32 64 128 256), losses := [] }

theorem u9857 : Upper (D 8) (R 8) [34,320,33,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9857 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9858 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 37 76 176 185 217 153 409), lower := (rows 35 322 37 76 176 32 64 128 256), losses := [] }

theorem u9858 : Upper (D 8) (R 8) [34,320,33,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9858 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9859 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 37 88 145 172 236 172 428), lower := (rows 35 322 37 88 145 32 64 128 256), losses := [] }

theorem u9859 : Upper (D 8) (R 8) [34,320,33,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9859 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9860 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 37 88 148 169 233 169 425), lower := (rows 35 322 37 88 148 32 64 128 256), losses := [] }

theorem u9860 : Upper (D 8) (R 8) [34,320,33,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9860 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9861 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 37 88 176 173 205 141 397), lower := (rows 35 322 37 88 176 32 64 128 256), losses := [] }

theorem u9861 : Upper (D 8) (R 8) [34,320,33,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9861 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9862 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 37 104 145 188 220 156 412), lower := (rows 35 322 37 104 145 32 64 128 256), losses := [] }

theorem u9862 : Upper (D 8) (R 8) [34,320,33,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9862 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9863 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 37 104 148 185 217 153 409), lower := (rows 35 322 37 104 148 32 64 128 256), losses := [] }

theorem u9863 : Upper (D 8) (R 8) [34,320,33,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9863 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9864 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 37 104 152 181 213 149 405), lower := (rows 35 322 37 104 152 32 64 128 256), losses := [] }

theorem u9864 : Upper (D 8) (R 8) [34,320,33,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9864 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9865 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 37 137 148 120 120 248 376), lower := (rows 35 322 37 137 148 32 64 128 256), losses := [] }

theorem u9865 : Upper (D 8) (R 8) [34,320,33,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9865 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9866 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 37 137 176 124 92 220 348), lower := (rows 35 322 37 137 176 32 64 128 256), losses := [] }

theorem u9866 : Upper (D 8) (R 8) [34,320,33,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9866 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9867 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 37 137 208 60 124 188 316), lower := (rows 35 322 37 137 208 32 64 128 256), losses := [] }

theorem u9867 : Upper (D 8) (R 8) [34,320,33,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9867 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9868 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 37 140 176 121 89 217 345), lower := (rows 35 322 37 140 176 32 64 128 256), losses := [] }

theorem u9868 : Upper (D 8) (R 8) [34,320,33,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9868 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9869 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 37 140 208 57 121 185 313), lower := (rows 35 322 37 140 208 32 64 128 256), losses := [] }

theorem u9869 : Upper (D 8) (R 8) [34,320,33,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9869 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9870 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 37 168 208 61 93 157 285), lower := (rows 35 322 37 168 208 32 64 128 256), losses := [] }

theorem u9870 : Upper (D 8) (R 8) [34,320,33,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9870 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9871 : PairBound 9 := { available := 209, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 44 44 145 241 209 209 465), lower := (rows 35 322 44 44 145 32 64 128 256), losses := [] }

theorem u9871 : Upper (D 8) (R 8) [34,320,40,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9871 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9872 : PairBound 9 := { available := 145, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 44 44 208 177 209 145 401), lower := (rows 35 322 44 44 208 32 64 128 256), losses := [] }

theorem u9872 : Upper (D 8) (R 8) [34,320,40,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9872 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9873 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 44 56 84 161 193 129 385), lower := (rows 35 322 44 56 84 32 64 128 256), losses := [] }

theorem u9873 : Upper (D 8) (R 8) [34,320,40,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9873 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9874 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 44 56 145 229 197 197 453), lower := (rows 35 322 44 56 145 32 64 128 256), losses := [] }

theorem u9874 : Upper (D 8) (R 8) [34,320,40,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9874 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9875 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 44 56 148 225 193 193 449), lower := (rows 35 322 44 56 148 32 64 128 256), losses := [] }

theorem u9875 : Upper (D 8) (R 8) [34,320,40,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9875 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9876 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 44 56 208 165 197 133 389), lower := (rows 35 322 44 56 208 32 64 128 256), losses := [] }

theorem u9876 : Upper (D 8) (R 8) [34,320,40,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9876 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9877 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 44 73 145 180 244 180 436), lower := (rows 35 322 44 73 145 32 64 128 256), losses := [] }

theorem u9877 : Upper (D 8) (R 8) [34,320,40,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9877 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9878 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 44 73 148 177 241 177 433), lower := (rows 35 322 44 73 148 32 64 128 256), losses := [] }

theorem u9878 : Upper (D 8) (R 8) [34,320,40,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9878 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9879 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 44 73 176 181 213 149 405), lower := (rows 35 322 44 73 176 32 64 128 256), losses := [] }

theorem u9879 : Upper (D 8) (R 8) [34,320,40,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9879 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9880 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 44 76 145 177 241 177 433), lower := (rows 35 322 44 76 145 32 64 128 256), losses := [] }

theorem u9880 : Upper (D 8) (R 8) [34,320,40,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9880 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9881 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 44 76 176 177 209 145 401), lower := (rows 35 322 44 76 176 32 64 128 256), losses := [] }

theorem u9881 : Upper (D 8) (R 8) [34,320,40,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9881 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9882 : Route 9 := (fun mask => (mask,id))

def c9882 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9882 : Upper (D 8) (R 8) [34,320,40,80,129] 13 := by
  apply FastRouting.sound _ _ [34,320,40,80,129] 13 (by decide) (choices 1) [1,4,128] r9882 c9882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2635
  · exact u2636
  · exact u2637

def b9883 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 44 88 148 161 225 161 417), lower := (rows 35 322 44 88 148 32 64 128 256), losses := [] }

theorem u9883 : Upper (D 8) (R 8) [34,320,40,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9883 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9884 : Route 9 := (fun mask => (mask,id))

def c9884 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9884 : Upper (D 8) (R 8) [34,320,40,80,160] 13 := by
  apply FastRouting.sound _ _ [34,320,40,80,160] 13 (by decide) (choices 1) [1,4,128] r9884 c9884
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2638
  · exact u2639
  · exact u2640

def b9885 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 44 104 145 181 213 149 405), lower := (rows 35 322 44 104 145 32 64 128 256), losses := [] }

theorem u9885 : Upper (D 8) (R 8) [34,320,40,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9885 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9886 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 44 104 148 177 209 145 401), lower := (rows 35 322 44 104 148 32 64 128 256), losses := [] }

theorem u9886 : Upper (D 8) (R 8) [34,320,40,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9886 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9887 : PairBound 9 := { available := 180, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 44 137 81 180 244 180 436), lower := (rows 35 322 44 137 81 32 64 128 256), losses := [] }

theorem u9887 : Upper (D 8) (R 8) [34,320,40,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9887 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9888 : Route 9 := (fun mask => (mask,id))

def c9888 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9888 : Upper (D 8) (R 8) [34,320,40,129,68] 13 := by
  apply FastRouting.sound _ _ [34,320,40,129,68] 13 (by decide) (choices 1) [1,16,128] r9888 c9888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2641
  · exact u2642
  · exact u2643

def r9889 : Route 9 := (fun mask => (mask,id))

def c9889 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9889 : Upper (D 8) (R 8) [34,320,40,129,96] 13 := by
  apply FastRouting.sound _ _ [34,320,40,129,96] 13 (by decide) (choices 1) [1,4,16,128] r9889 c9889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2644
  · exact u2645
  · exact u2646
  · exact u2647

def b9890 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 322 44 137 145 116 116 244 372), lower := (rows 35 322 44 137 145 32 64 128 256), losses := [] }

theorem u9890 : Upper (D 8) (R 8) [34,320,40,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9890 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9891 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 44 137 148 113 113 241 369), lower := (rows 35 322 44 137 148 32 64 128 256), losses := [] }

theorem u9891 : Upper (D 8) (R 8) [34,320,40,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9891 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9892 : Route 9 := (fun mask => (mask,id))

def c9892 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9892 : Upper (D 8) (R 8) [34,320,40,129,160] 13 := by
  apply FastRouting.sound _ _ [34,320,40,129,160] 13 (by decide) (choices 1) [1,4,16,64] r9892 c9892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2648
  · exact u2649
  · exact u2650
  · exact u2651

def r9893 : Route 9 := (fun mask => (mask,id))

def c9893 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9893 : Upper (D 8) (R 8) [34,320,40,129,192] 13 := by
  apply FastRouting.sound _ _ [34,320,40,129,192] 13 (by decide) (choices 1) [1,4,16] r9893 c9893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2652
  · exact u2653
  · exact u2654

def b9894 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 44 140 81 177 241 177 433), lower := (rows 35 322 44 140 81 32 64 128 256), losses := [] }

theorem u9894 : Upper (D 8) (R 8) [34,320,40,132,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9894 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9895 : Route 9 := (fun mask => (mask,id))

def c9895 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9895 : Upper (D 8) (R 8) [34,320,40,132,96] 13 := by
  apply FastRouting.sound _ _ [34,320,40,132,96] 13 (by decide) (choices 1) [1,16,128] r9895 c9895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2655
  · exact u2656
  · exact u2657

def b9896 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 44 140 145 113 113 241 369), lower := (rows 35 322 44 140 145 32 64 128 256), losses := [] }

theorem u9896 : Upper (D 8) (R 8) [34,320,40,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9896 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9897 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 44 140 176 113 81 209 337), lower := (rows 35 322 44 140 176 32 64 128 256), losses := [] }

theorem u9897 : Upper (D 8) (R 8) [34,320,40,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9897 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9898 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 44 140 208 49 113 177 305), lower := (rows 35 322 44 140 208 32 64 128 256), losses := [] }

theorem u9898 : Upper (D 8) (R 8) [34,320,40,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9898 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9899 : PairBound 9 := { available := 165, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 44 152 81 165 229 165 421), lower := (rows 35 322 44 152 81 32 64 128 256), losses := [] }

theorem u9899 : Upper (D 8) (R 8) [34,320,40,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9899 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u9899
end Delivery.IrregularNine14.P08
