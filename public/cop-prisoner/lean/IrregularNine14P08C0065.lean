import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0008
import IrregularNine14P08C0009

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3900 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 262 164 41 152 48 97 225 353), lower := (rows 67 262 164 41 152 48 64 128 256), losses := [] }

theorem u3900 : Upper (D 8) (R 8) [66,260,160,33,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3900 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3901 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 164 41 152 96 113 177 305), lower := (rows 67 262 164 41 152 96 64 128 256), losses := [] }

theorem u3901 : Upper (D 8) (R 8) [66,260,160,33,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3901 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3902 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 262 164 41 208 33 120 184 312), lower := (rows 67 262 164 41 208 33 64 128 256), losses := [] }

theorem u3902 : Upper (D 8) (R 8) [66,260,160,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3902 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3903 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 262 164 41 208 40 113 177 305), lower := (rows 67 262 164 41 208 40 64 128 256), losses := [] }

theorem u3903 : Upper (D 8) (R 8) [66,260,160,33,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3903 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3904 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 262 164 41 208 48 105 169 297), lower := (rows 67 262 164 41 208 48 64 128 256), losses := [] }

theorem u3904 : Upper (D 8) (R 8) [66,260,160,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3904 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3905 : Route 9 := (fun mask => (mask,id))

def c3905 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3905 : Upper (D 8) (R 8) [66,260,160,48,192,1] 13 := by
  apply FastRouting.sound _ _ [66,260,160,48,192,1] 13 (by decide) (choices 1) [1,8,32] r3905 c3905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u527
  · exact u528
  · exact u529

def b3906 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 262 164 56 208 40 97 161 289), lower := (rows 67 262 164 56 208 40 64 128 256), losses := [] }

theorem u3906 : Upper (D 8) (R 8) [66,260,160,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3906 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3907 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 40, targets := 128 }], pairs := [(3,7)], upper := (rows 67 262 164 104 152 33 113 177 305), lower := (rows 67 262 164 104 152 33 64 128 256), losses := [] }

theorem u3907 : Upper (D 8) (R 8) [66,260,160,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3907 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3908 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 262 164 104 152 48 97 161 289), lower := (rows 67 262 164 104 152 48 64 128 256), losses := [] }

theorem u3908 : Upper (D 8) (R 8) [66,260,160,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3908 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3909 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 450, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 13 28 176 33 224 224 480), lower := (rows 67 290 13 28 176 33 64 128 256), losses := [] }

theorem u3909 : Upper (D 8) (R 8) [66,288,9,20,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3909 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3910 : Route 9 := (fun mask => (mask,id))

def c3910 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3910 : Upper (D 8) (R 8) [66,288,9,20,160,64] 13 := by
  apply FastRouting.sound _ _ [66,288,9,20,160,64] 13 (by decide) (choices 1) [1,32,128] r3910 c3910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u530
  · exact u531
  · exact u532

def b3911 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 13 28 176 160 97 225 353), lower := (rows 67 290 13 28 176 160 64 128 256), losses := [] }

theorem u3911 : Upper (D 8) (R 8) [66,288,9,20,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3911 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3912 : PairBound 9 := { available := 144, camps := [{ cop := 5, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 67 290 13 44 112 33 208 144 400), lower := (rows 67 290 13 44 112 33 64 128 256), losses := [] }

theorem u3912 : Upper (D 8) (R 8) [66,288,9,36,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3912 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3913 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 290 13 44 112 48 193 129 385), lower := (rows 67 290 13 44 112 48 64 128 256), losses := [] }

theorem u3913 : Upper (D 8) (R 8) [66,288,9,36,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3913 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3914 : Route 9 := (fun mask => (mask,id))

def c3914 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3914 : Upper (D 8) (R 8) [66,288,9,36,96,128] 13 := by
  apply FastRouting.sound _ _ [66,288,9,36,96,128] 13 (by decide) (choices 1) [1,16,128] r3914 c3914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u533
  · exact u534
  · exact u535

def b3915 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 44, targets := 64 }], pairs := [(2,6)], upper := (rows 67 290 13 44 176 33 208 208 464), lower := (rows 67 290 13 44 176 33 64 128 256), losses := [] }

theorem u3915 : Upper (D 8) (R 8) [66,288,9,36,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3915 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3916 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 67 290 13 44 176 48 193 193 449), lower := (rows 67 290 13 44 176 48 64 128 256), losses := [] }

theorem u3916 : Upper (D 8) (R 8) [66,288,9,36,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3916 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3917 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 44, targets := 128 }], pairs := [(2,7)], upper := (rows 67 290 13 44 176 96 209 145 401), lower := (rows 67 290 13 44 176 96 64 128 256), losses := [] }

theorem u3917 : Upper (D 8) (R 8) [66,288,9,36,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3917 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3918 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 13 44 176 160 81 209 337), lower := (rows 67 290 13 44 176 160 64 128 256), losses := [] }

theorem u3918 : Upper (D 8) (R 8) [66,288,9,36,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3918 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3919 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 44, targets := 64 }], pairs := [(2,6)], upper := (rows 67 290 13 44 208 33 240 176 432), lower := (rows 67 290 13 44 208 33 64 128 256), losses := [] }

theorem u3919 : Upper (D 8) (R 8) [66,288,9,36,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3919 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3920 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 290 13 44 208 48 225 161 417), lower := (rows 67 290 13 44 208 48 64 128 256), losses := [] }

theorem u3920 : Upper (D 8) (R 8) [66,288,9,36,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3920 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3921 : Route 9 := (fun mask => (mask,id))

def c3921 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3921 : Upper (D 8) (R 8) [66,288,9,36,192,128] 13 := by
  apply FastRouting.sound _ _ [66,288,9,36,192,128] 13 (by decide) (choices 1) [1,16,32] r3921 c3921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u536
  · exact u537
  · exact u538

def b3922 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 450, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 13 56 148 33 224 224 480), lower := (rows 67 290 13 56 148 33 64 128 256), losses := [] }

theorem u3922 : Upper (D 8) (R 8) [66,288,9,48,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3922 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3923 : Route 9 := (fun mask => (mask,id))

def c3923 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3923 : Upper (D 8) (R 8) [66,288,9,48,132,64] 13 := by
  apply FastRouting.sound _ _ [66,288,9,48,132,64] 13 (by decide) (choices 1) [1,32,128] r3923 c3923
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u539
  · exact u540
  · exact u541

def b3924 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 13 56 148 160 97 225 353), lower := (rows 67 290 13 56 148 160 64 128 256), losses := [] }

theorem u3924 : Upper (D 8) (R 8) [66,288,9,48,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3924 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3925 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 466, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 13 140 112 33 240 176 432), lower := (rows 67 290 13 140 112 33 64 128 256), losses := [] }

theorem u3925 : Upper (D 8) (R 8) [66,288,9,132,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3925 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3926 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 290 13 140 112 48 225 161 417), lower := (rows 67 290 13 140 112 48 64 128 256), losses := [] }

theorem u3926 : Upper (D 8) (R 8) [66,288,9,132,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3926 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3927 : PairBound 9 := { available := 49, camps := [{ cop := 5, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 13 140 112 160 113 177 305), lower := (rows 67 290 13 140 112 160 64 128 256), losses := [] }

theorem u3927 : Upper (D 8) (R 8) [66,288,9,132,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3927 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3928 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 67 290 13 152 52 33 224 224 480), lower := (rows 67 290 13 152 52 33 64 128 256), losses := [] }

theorem u3928 : Upper (D 8) (R 8) [66,288,9,144,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3928 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3929 : PairBound 9 := { available := 161, camps := [], pairs := [(4,0)], upper := (rows 67 290 13 152 52 96 225 161 417), lower := (rows 67 290 13 152 52 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 97 64 128 256), good := (rows 98 290 60 152 52 96 96 128 256) }] }

theorem u3929 : Upper (D 8) (R 8) [66,288,9,144,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3929 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3930 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 13 152 52 160 97 225 353), lower := (rows 67 290 13 152 52 160 64 128 256), losses := [] }

theorem u3930 : Upper (D 8) (R 8) [66,288,9,144,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3930 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3931 : PairBound 9 := { available := 208, camps := [], pairs := [], upper := (rows 67 290 13 168 49 36 208 208 464), lower := (rows 67 290 13 168 49 36 64 128 256), losses := [] }

theorem u3931 : Upper (D 8) (R 8) [66,288,9,160,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3931 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3932 : PairBound 9 := { available := 196, camps := [], pairs := [], upper := (rows 67 290 13 168 49 48 196 196 452), lower := (rows 67 290 13 168 49 48 64 128 256), losses := [] }

theorem u3932 : Upper (D 8) (R 8) [66,288,9,160,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3932 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3933 : PairBound 9 := { available := 148, camps := [{ cop := 4, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 168 49 96 212 148 404), lower := (rows 67 290 13 168 49 96 64 128 256), losses := [] }

theorem u3933 : Upper (D 8) (R 8) [66,288,9,160,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3933 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3934 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 13 168 49 160 84 212 340), lower := (rows 67 290 13 168 49 160 64 128 256), losses := [] }

theorem u3934 : Upper (D 8) (R 8) [66,288,9,160,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3934 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3935 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 67 290 13 168 52 33 208 208 464), lower := (rows 67 290 13 168 52 33 64 128 256), losses := [] }

theorem u3935 : Upper (D 8) (R 8) [66,288,9,160,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3935 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3936 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 67 290 13 168 52 48 193 193 449), lower := (rows 67 290 13 168 52 48 64 128 256), losses := [] }

theorem u3936 : Upper (D 8) (R 8) [66,288,9,160,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3936 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3937 : PairBound 9 := { available := 145, camps := [], pairs := [(4,0)], upper := (rows 67 290 13 168 52 96 209 145 401), lower := (rows 67 290 13 168 52 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 97 64 128 256), good := (rows 98 290 60 168 52 96 96 128 256) }] }

theorem u3937 : Upper (D 8) (R 8) [66,288,9,160,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3937 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3938 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 13 168 52 160 81 209 337), lower := (rows 67 290 13 168 52 160 64 128 256), losses := [] }

theorem u3938 : Upper (D 8) (R 8) [66,288,9,160,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3938 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3939 : PairBound 9 := { available := 176, camps := [], pairs := [(1,6)], upper := (rows 67 290 13 168 84 33 240 176 432), lower := (rows 67 290 13 168 84 33 64 128 256), losses := [{ target := 6, region := (rows 1 18 4 24 16 37 0 144 272), good := (rows 35 290 45 168 446 33 0 128 256) }] }

theorem u3939 : Upper (D 8) (R 8) [66,288,9,160,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3939 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3940 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 290 13 168 84 48 225 161 417), lower := (rows 67 290 13 168 84 48 64 128 256), losses := [] }

theorem u3940 : Upper (D 8) (R 8) [66,288,9,160,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3940 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3941 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 13 168 84 160 113 177 305), lower := (rows 67 290 13 168 84 160 64 128 256), losses := [] }

theorem u3941 : Upper (D 8) (R 8) [66,288,9,160,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3941 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3942 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 67 290 13 168 112 33 212 148 404), lower := (rows 67 290 13 168 112 33 64 128 256), losses := [] }

theorem u3942 : Upper (D 8) (R 8) [66,288,9,160,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3942 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3943 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 290 13 168 112 36 209 145 401), lower := (rows 67 290 13 168 112 36 64 128 256), losses := [] }

theorem u3943 : Upper (D 8) (R 8) [66,288,9,160,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3943 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3944 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 67 290 13 168 112 48 197 133 389), lower := (rows 67 290 13 168 112 48 64 128 256), losses := [] }

theorem u3944 : Upper (D 8) (R 8) [66,288,9,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3944 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3945 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 13 168 112 160 85 149 277), lower := (rows 67 290 13 168 112 160 64 128 256), losses := [] }

theorem u3945 : Upper (D 8) (R 8) [66,288,9,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3945 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3946 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 67 290 13 168 145 36 112 240 368), lower := (rows 67 290 13 168 145 36 64 128 256), losses := [] }

theorem u3946 : Upper (D 8) (R 8) [66,288,9,160,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3946 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3947 : PairBound 9 := { available := 100, camps := [], pairs := [], upper := (rows 67 290 13 168 145 48 100 228 356), lower := (rows 67 290 13 168 145 48 64 128 256), losses := [] }

theorem u3947 : Upper (D 8) (R 8) [66,288,9,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3947 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3948 : PairBound 9 := { available := 52, camps := [], pairs := [(3,0)], upper := (rows 67 290 13 168 145 96 116 180 308), lower := (rows 67 290 13 168 145 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 97 64 128 256), good := (rows 98 290 44 168 184 96 96 128 256) }] }

theorem u3948 : Upper (D 8) (R 8) [66,288,9,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3948 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3949 : Route 9 := (fun mask => (mask,id))

def c3949 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3949 : Upper (D 8) (R 8) [66,288,9,160,192,1] 13 := by
  apply FastRouting.sound _ _ [66,288,9,160,192,1] 13 (by decide) (choices 1) [4,16,32] r3949 c3949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u542
  · exact u543
  · exact u544

def b3950 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 290 13 168 208 36 113 177 305), lower := (rows 67 290 13 168 208 36 64 128 256), losses := [] }

theorem u3950 : Upper (D 8) (R 8) [66,288,9,160,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3950 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3951 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 290 13 168 208 48 101 165 293), lower := (rows 67 290 13 168 208 48 64 128 256), losses := [] }

theorem u3951 : Upper (D 8) (R 8) [66,288,9,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3951 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3952 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 60, targets := 128 }], pairs := [(2,7)], upper := (rows 67 290 28 41 112 33 196 132 388), lower := (rows 67 290 28 41 112 33 64 128 256), losses := [] }

theorem u3952 : Upper (D 8) (R 8) [66,288,24,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3952 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3953 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 290 28 41 112 36 193 129 385), lower := (rows 67 290 28 41 112 36 64 128 256), losses := [] }

theorem u3953 : Upper (D 8) (R 8) [66,288,24,33,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3953 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3954 : Route 9 := (fun mask => (mask,id))

def c3954 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3954 : Upper (D 8) (R 8) [66,288,24,33,96,128] 13 := by
  apply FastRouting.sound _ _ [66,288,24,33,96,128] 13 (by decide) (choices 1) [1,4,128] r3954 c3954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u545
  · exact u546
  · exact u547

def b3955 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 450, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 28 41 148 33 224 224 480), lower := (rows 67 290 28 41 148 33 64 128 256), losses := [] }

theorem u3955 : Upper (D 8) (R 8) [66,288,24,33,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3955 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3956 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 386, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 28 41 148 96 225 161 417), lower := (rows 67 290 28 41 148 96 64 128 256), losses := [] }

theorem u3956 : Upper (D 8) (R 8) [66,288,24,33,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3956 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3957 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 28 41 148 160 97 225 353), lower := (rows 67 290 28 41 148 160 64 128 256), losses := [] }

theorem u3957 : Upper (D 8) (R 8) [66,288,24,33,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3957 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3958 : PairBound 9 := { available := 196, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 28 41 176 33 196 196 452), lower := (rows 67 290 28 41 176 33 64 128 256), losses := [] }

theorem u3958 : Upper (D 8) (R 8) [66,288,24,33,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3958 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3959 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 67 290 28 41 176 36 193 193 449), lower := (rows 67 290 28 41 176 36 64 128 256), losses := [] }

theorem u3959 : Upper (D 8) (R 8) [66,288,24,33,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3959 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u3959
end Delivery.IrregularNine14.P08
