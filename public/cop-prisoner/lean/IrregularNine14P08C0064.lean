import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0008

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3840 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 262 37 88 176 33 232 168 424), lower := (rows 67 262 37 88 176 33 64 128 256), losses := [] }

theorem u3840 : Upper (D 8) (R 8) [66,260,33,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3840 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3841 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 262 37 88 176 40 225 161 417), lower := (rows 67 262 37 88 176 40 64 128 256), losses := [] }

theorem u3841 : Upper (D 8) (R 8) [66,260,33,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3841 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3842 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 37 88 176 160 105 169 297), lower := (rows 67 262 37 88 176 160 64 128 256), losses := [] }

theorem u3842 : Upper (D 8) (R 8) [66,260,33,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3842 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3843 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 262 37 104 152 33 240 176 432), lower := (rows 67 262 37 104 152 33 64 128 256), losses := [] }

theorem u3843 : Upper (D 8) (R 8) [66,260,33,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3843 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3844 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 262 37 104 152 48 225 161 417), lower := (rows 67 262 37 104 152 48 64 128 256), losses := [] }

theorem u3844 : Upper (D 8) (R 8) [66,260,33,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3844 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3845 : Route 9 := (fun mask => (mask,id))

def c3845 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3845 : Upper (D 8) (R 8) [66,260,33,96,136,128] 13 := by
  apply FastRouting.sound _ _ [66,260,33,96,136,128] 13 (by decide) (choices 1) [1,16,32] r3845 c3845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u524
  · exact u525
  · exact u526

def b3846 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 262 37 104 176 33 216 152 408), lower := (rows 67 262 37 104 176 33 64 128 256), losses := [] }

theorem u3846 : Upper (D 8) (R 8) [66,260,33,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3846 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3847 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 262 37 104 176 40 209 145 401), lower := (rows 67 262 37 104 176 40 64 128 256), losses := [] }

theorem u3847 : Upper (D 8) (R 8) [66,260,33,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3847 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3848 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 67 262 37 104 176 48 201 137 393), lower := (rows 67 262 37 104 176 48 64 128 256), losses := [] }

theorem u3848 : Upper (D 8) (R 8) [66,260,33,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3848 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3849 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 37 104 176 160 89 153 281), lower := (rows 67 262 37 104 176 160 64 128 256), losses := [] }

theorem u3849 : Upper (D 8) (R 8) [66,260,33,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3849 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3850 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 262 37 168 208 33 120 184 312), lower := (rows 67 262 37 168 208 33 64 128 256), losses := [] }

theorem u3850 : Upper (D 8) (R 8) [66,260,33,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3850 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3851 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 262 37 168 208 40 113 177 305), lower := (rows 67 262 37 168 208 40 64 128 256), losses := [] }

theorem u3851 : Upper (D 8) (R 8) [66,260,33,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3851 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3852 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 262 37 168 208 48 105 169 297), lower := (rows 67 262 37 168 208 48 64 128 256), losses := [] }

theorem u3852 : Upper (D 8) (R 8) [66,260,33,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3852 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3853 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0)], upper := (rows 67 262 44 25 176 33 224 224 480), lower := (rows 67 262 44 25 176 33 64 128 256), losses := [] }

theorem u3853 : Upper (D 8) (R 8) [66,260,40,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3853 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3854 : PairBound 9 := { available := 161, camps := [], pairs := [(2,0)], upper := (rows 67 262 44 25 176 96 225 161 417), lower := (rows 67 262 44 25 176 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 97 64 128 256), good := (rows 98 262 44 60 176 96 96 128 256) }] }

theorem u3854 : Upper (D 8) (R 8) [66,260,40,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3854 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3855 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 44 25 176 160 97 225 353), lower := (rows 67 262 44 25 176 160 64 128 256), losses := [] }

theorem u3855 : Upper (D 8) (R 8) [66,260,40,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3855 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3856 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 67 262 44 137 49 48 224 224 480), lower := (rows 67 262 44 137 49 48 64 128 256), losses := [] }

theorem u3856 : Upper (D 8) (R 8) [66,260,40,129,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3856 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3857 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 44 137 49 96 240 176 432), lower := (rows 67 262 44 137 49 96 64 128 256), losses := [] }

theorem u3857 : Upper (D 8) (R 8) [66,260,40,129,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3857 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3858 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 44 137 49 160 112 240 368), lower := (rows 67 262 44 137 49 160 64 128 256), losses := [] }

theorem u3858 : Upper (D 8) (R 8) [66,260,40,129,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3858 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3859 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0)], upper := (rows 67 262 44 137 112 33 240 176 432), lower := (rows 67 262 44 137 112 33 64 128 256), losses := [] }

theorem u3859 : Upper (D 8) (R 8) [66,260,40,129,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3859 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3860 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 262 44 137 112 48 225 161 417), lower := (rows 67 262 44 137 112 48 64 128 256), losses := [] }

theorem u3860 : Upper (D 8) (R 8) [66,260,40,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3860 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3861 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 44 137 112 160 113 177 305), lower := (rows 67 262 44 137 112 160 64 128 256), losses := [] }

theorem u3861 : Upper (D 8) (R 8) [66,260,40,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3861 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3862 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0)], upper := (rows 67 262 44 137 176 33 112 240 368), lower := (rows 67 262 44 137 176 33 64 128 256), losses := [] }

theorem u3862 : Upper (D 8) (R 8) [66,260,40,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3862 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3863 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 262 44 137 176 48 97 225 353), lower := (rows 67 262 44 137 176 48 64 128 256), losses := [] }

theorem u3863 : Upper (D 8) (R 8) [66,260,40,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3863 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3864 : PairBound 9 := { available := 49, camps := [], pairs := [(2,0)], upper := (rows 67 262 44 137 176 96 113 177 305), lower := (rows 67 262 44 137 176 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 97 64 128 256), good := (rows 98 262 60 188 176 96 96 128 256) }] }

theorem u3864 : Upper (D 8) (R 8) [66,260,40,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3864 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3865 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0)], upper := (rows 67 262 44 137 208 33 112 176 304), lower := (rows 67 262 44 137 208 33 64 128 256), losses := [] }

theorem u3865 : Upper (D 8) (R 8) [66,260,40,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3865 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3866 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 262 44 137 208 48 97 161 289), lower := (rows 67 262 44 137 208 48 64 128 256), losses := [] }

theorem u3866 : Upper (D 8) (R 8) [66,260,40,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3866 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3867 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 67 262 44 152 49 33 224 224 480), lower := (rows 67 262 44 152 49 33 64 128 256), losses := [] }

theorem u3867 : Upper (D 8) (R 8) [66,260,40,144,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3867 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3868 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 44 152 49 96 225 161 417), lower := (rows 67 262 44 152 49 96 64 128 256), losses := [] }

theorem u3868 : Upper (D 8) (R 8) [66,260,40,144,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3868 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3869 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 44 152 49 160 97 225 353), lower := (rows 67 262 44 152 49 160 64 128 256), losses := [] }

theorem u3869 : Upper (D 8) (R 8) [66,260,40,144,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3869 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3870 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 67 262 44 152 112 33 225 161 417), lower := (rows 67 262 44 152 112 33 64 128 256), losses := [] }

theorem u3870 : Upper (D 8) (R 8) [66,260,40,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3870 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3871 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 44 152 112 160 97 161 289), lower := (rows 67 262 44 152 112 160 64 128 256), losses := [] }

theorem u3871 : Upper (D 8) (R 8) [66,260,40,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3871 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3872 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 133 56 208 33 104 168 296), lower := (rows 67 262 133 56 208 33 64 128 256), losses := [] }

theorem u3872 : Upper (D 8) (R 8) [66,260,129,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3872 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3873 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 262 133 56 208 40 97 161 289), lower := (rows 67 262 133 56 208 40 64 128 256), losses := [] }

theorem u3873 : Upper (D 8) (R 8) [66,260,129,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3873 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3874 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 133 88 176 33 104 168 296), lower := (rows 67 262 133 88 176 33 64 128 256), losses := [] }

theorem u3874 : Upper (D 8) (R 8) [66,260,129,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3874 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3875 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 262 133 88 176 40 97 161 289), lower := (rows 67 262 133 88 176 40 64 128 256), losses := [] }

theorem u3875 : Upper (D 8) (R 8) [66,260,129,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3875 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3876 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 133 104 152 33 112 176 304), lower := (rows 67 262 133 104 152 33 64 128 256), losses := [] }

theorem u3876 : Upper (D 8) (R 8) [66,260,129,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3876 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3877 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 262 133 104 152 48 97 161 289), lower := (rows 67 262 133 104 152 48 64 128 256), losses := [] }

theorem u3877 : Upper (D 8) (R 8) [66,260,129,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3877 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3878 : PairBound 9 := { available := 56, camps := [{ cop := 5, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 133 104 176 33 120 184 312), lower := (rows 67 262 133 104 176 33 64 128 256), losses := [] }

theorem u3878 : Upper (D 8) (R 8) [66,260,129,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3878 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3879 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 262 133 104 176 40 113 177 305), lower := (rows 67 262 133 104 176 40 64 128 256), losses := [] }

theorem u3879 : Upper (D 8) (R 8) [66,260,129,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3879 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3880 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 262 133 104 176 48 105 169 297), lower := (rows 67 262 133 104 176 48 64 128 256), losses := [] }

theorem u3880 : Upper (D 8) (R 8) [66,260,129,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3880 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3881 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 262 140 41 112 33 240 176 432), lower := (rows 67 262 140 41 112 33 64 128 256), losses := [] }

theorem u3881 : Upper (D 8) (R 8) [66,260,136,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3881 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3882 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 262 140 41 112 48 225 161 417), lower := (rows 67 262 140 41 112 48 64 128 256), losses := [] }

theorem u3882 : Upper (D 8) (R 8) [66,260,136,33,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3882 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3883 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 80, targets := 128 }], pairs := [(4,7)], upper := (rows 67 262 140 41 112 160 113 177 305), lower := (rows 67 262 140 41 112 160 64 128 256), losses := [] }

theorem u3883 : Upper (D 8) (R 8) [66,260,136,33,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3883 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3884 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 262 140 41 176 33 112 240 368), lower := (rows 67 262 140 41 176 33 64 128 256), losses := [] }

theorem u3884 : Upper (D 8) (R 8) [66,260,136,33,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3884 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3885 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 262 140 41 176 48 97 225 353), lower := (rows 67 262 140 41 176 48 64 128 256), losses := [] }

theorem u3885 : Upper (D 8) (R 8) [66,260,136,33,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3885 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3886 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 140 41 176 96 113 177 305), lower := (rows 67 262 140 41 176 96 64 128 256), losses := [] }

theorem u3886 : Upper (D 8) (R 8) [66,260,136,33,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3886 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3887 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 262 140 41 208 33 112 176 304), lower := (rows 67 262 140 41 208 33 64 128 256), losses := [] }

theorem u3887 : Upper (D 8) (R 8) [66,260,136,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3887 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3888 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 262 140 41 208 48 97 161 289), lower := (rows 67 262 140 41 208 48 64 128 256), losses := [] }

theorem u3888 : Upper (D 8) (R 8) [66,260,136,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3888 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3889 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 56, targets := 64 }], pairs := [(3,6)], upper := (rows 67 262 164 25 56 33 224 224 480), lower := (rows 67 262 164 25 56 33 64 128 256), losses := [] }

theorem u3889 : Upper (D 8) (R 8) [66,260,160,17,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3889 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3890 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 56, targets := 128 }], pairs := [(3,7)], upper := (rows 67 262 164 25 56 96 225 161 417), lower := (rows 67 262 164 25 56 96 64 128 256), losses := [] }

theorem u3890 : Upper (D 8) (R 8) [66,260,160,17,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3890 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3891 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 164 25 56 160 97 225 353), lower := (rows 67 262 164 25 56 160 64 128 256), losses := [] }

theorem u3891 : Upper (D 8) (R 8) [66,260,160,17,40,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3891 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3892 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 262 164 41 88 33 240 176 432), lower := (rows 67 262 164 41 88 33 64 128 256), losses := [] }

theorem u3892 : Upper (D 8) (R 8) [66,260,160,33,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3892 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3893 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 262 164 41 88 48 225 161 417), lower := (rows 67 262 164 41 88 48 64 128 256), losses := [] }

theorem u3893 : Upper (D 8) (R 8) [66,260,160,33,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3893 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3894 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 164 41 88 160 113 177 305), lower := (rows 67 262 164 41 88 160 64 128 256), losses := [] }

theorem u3894 : Upper (D 8) (R 8) [66,260,160,33,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3894 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3895 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 262 164 41 112 33 216 152 408), lower := (rows 67 262 164 41 112 33 64 128 256), losses := [] }

theorem u3895 : Upper (D 8) (R 8) [66,260,160,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3895 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3896 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 262 164 41 112 40 209 145 401), lower := (rows 67 262 164 41 112 40 64 128 256), losses := [] }

theorem u3896 : Upper (D 8) (R 8) [66,260,160,33,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3896 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3897 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 67 262 164 41 112 48 201 137 393), lower := (rows 67 262 164 41 112 48 64 128 256), losses := [] }

theorem u3897 : Upper (D 8) (R 8) [66,260,160,33,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3897 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3898 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 164 41 112 160 89 153 281), lower := (rows 67 262 164 41 112 160 64 128 256), losses := [] }

theorem u3898 : Upper (D 8) (R 8) [66,260,160,33,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3898 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3899 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 262 164 41 152 33 112 240 368), lower := (rows 67 262 164 41 152 33 64 128 256), losses := [] }

theorem u3899 : Upper (D 8) (R 8) [66,260,160,33,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3899 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u3899
end Delivery.IrregularNine14.P08
