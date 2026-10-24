import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0103

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r16920 : Route 9 := (fun mask => (mask,id))

def c16920 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16920 : Upper (D 8) (R 8) [258,96,40,129,68] 13 := by
  apply FastRouting.sound _ _ [258,96,40,129,68] 13 (by decide) (choices 1) [1,16,128] r16920 c16920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6185
  · exact u6186
  · exact u6187

def b16921 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 98 44 137 112 181 213 149 405), lower := (rows 259 98 44 137 112 32 64 128 256), losses := [] }

theorem u16921 : Upper (D 8) (R 8) [258,96,40,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16921 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16922 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 259 98 44 137 145 116 116 244 372), lower := (rows 259 98 44 137 145 32 64 128 256), losses := [] }

theorem u16922 : Upper (D 8) (R 8) [258,96,40,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16922 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16923 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 44 137 148 113 113 241 369), lower := (rows 259 98 44 137 148 32 64 128 256), losses := [] }

theorem u16923 : Upper (D 8) (R 8) [258,96,40,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16923 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16924 : Route 9 := (fun mask => (mask,id))

def c16924 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16924 : Upper (D 8) (R 8) [258,96,40,129,160] 13 := by
  apply FastRouting.sound _ _ [258,96,40,129,160] 13 (by decide) (choices 1) [1,4,16,64] r16924 c16924
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6188
  · exact u6189
  · exact u6190
  · exact u6191

def r16925 : Route 9 := (fun mask => (mask,id))

def c16925 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16925 : Upper (D 8) (R 8) [258,96,40,129,192] 13 := by
  apply FastRouting.sound _ _ [258,96,40,129,192] 13 (by decide) (choices 1) [1,4,16] r16925 c16925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6192
  · exact u6193
  · exact u6194

def b16926 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 44 140 81 177 241 177 433), lower := (rows 259 98 44 140 81 32 64 128 256), losses := [] }

theorem u16926 : Upper (D 8) (R 8) [258,96,40,132,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16926 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16927 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 98 44 140 112 177 209 145 401), lower := (rows 259 98 44 140 112 32 64 128 256), losses := [] }

theorem u16927 : Upper (D 8) (R 8) [258,96,40,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16927 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16928 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 44 140 145 113 113 241 369), lower := (rows 259 98 44 140 145 32 64 128 256), losses := [] }

theorem u16928 : Upper (D 8) (R 8) [258,96,40,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16928 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16929 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 44 140 176 113 81 209 337), lower := (rows 259 98 44 140 176 32 64 128 256), losses := [] }

theorem u16929 : Upper (D 8) (R 8) [258,96,40,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16929 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16930 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 44 140 208 49 113 177 305), lower := (rows 259 98 44 140 208 32 64 128 256), losses := [] }

theorem u16930 : Upper (D 8) (R 8) [258,96,40,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16930 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16931 : PairBound 9 := { available := 165, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 44 152 81 165 229 165 421), lower := (rows 259 98 44 152 81 32 64 128 256), losses := [] }

theorem u16931 : Upper (D 8) (R 8) [258,96,40,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16931 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16932 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 44 152 84 161 225 161 417), lower := (rows 259 98 44 152 84 32 64 128 256), losses := [] }

theorem u16932 : Upper (D 8) (R 8) [258,96,40,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16932 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16933 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 98 44 152 112 165 197 133 389), lower := (rows 259 98 44 152 112 32 64 128 256), losses := [] }

theorem u16933 : Upper (D 8) (R 8) [258,96,40,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16933 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16934 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 44 152 145 101 101 229 357), lower := (rows 259 98 44 152 145 32 64 128 256), losses := [] }

theorem u16934 : Upper (D 8) (R 8) [258,96,40,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16934 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16935 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 44 152 148 97 97 225 353), lower := (rows 259 98 44 152 148 32 64 128 256), losses := [] }

theorem u16935 : Upper (D 8) (R 8) [258,96,40,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16935 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16936 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 44 152 176 101 69 197 325), lower := (rows 259 98 44 152 176 32 64 128 256), losses := [] }

theorem u16936 : Upper (D 8) (R 8) [258,96,40,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16936 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16937 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 44 152 208 37 101 165 293), lower := (rows 259 98 44 152 208 32 64 128 256), losses := [] }

theorem u16937 : Upper (D 8) (R 8) [258,96,40,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16937 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16938 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 44 168 84 177 209 145 401), lower := (rows 259 98 44 168 84 32 64 128 256), losses := [] }

theorem u16938 : Upper (D 8) (R 8) [258,96,40,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16938 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16939 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 44 168 145 117 85 213 341), lower := (rows 259 98 44 168 145 32 64 128 256), losses := [] }

theorem u16939 : Upper (D 8) (R 8) [258,96,40,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16939 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16940 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 44 168 148 113 81 209 337), lower := (rows 259 98 44 168 148 32 64 128 256), losses := [] }

theorem u16940 : Upper (D 8) (R 8) [258,96,40,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16940 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16941 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 44 168 208 53 85 149 277), lower := (rows 259 98 44 168 208 32 64 128 256), losses := [] }

theorem u16941 : Upper (D 8) (R 8) [258,96,40,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16941 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16942 : Route 9 := (fun mask => (mask,id))

def c16942 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16942 : Upper (D 8) (R 8) [258,96,40,192,129] 13 := by
  apply FastRouting.sound _ _ [258,96,40,192,129] 13 (by decide) (choices 1) [1,4,16] r16942 c16942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6195
  · exact u6196
  · exact u6197

def b16943 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 44 200 148 49 113 177 305), lower := (rows 259 98 44 200 148 32 64 128 256), losses := [] }

theorem u16943 : Upper (D 8) (R 8) [258,96,40,192,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16943 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16944 : Route 9 := (fun mask => (mask,id))

def c16944 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16944 : Upper (D 8) (R 8) [258,96,40,192,160] 13 := by
  apply FastRouting.sound _ _ [258,96,40,192,160] 13 (by decide) (choices 1) [1,4,16] r16944 c16944
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6198
  · exact u6199
  · exact u6200

def b16945 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 259 98 69 137 148 56 120 184 312), lower := (rows 259 98 69 137 148 32 64 128 256), losses := [] }

theorem u16945 : Upper (D 8) (R 8) [258,96,65,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16945 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16946 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 259 98 69 137 176 60 124 188 316), lower := (rows 259 98 69 137 176 32 64 128 256), losses := [] }

theorem u16946 : Upper (D 8) (R 8) [258,96,65,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16946 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16947 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 259 98 69 140 176 57 121 185 313), lower := (rows 259 98 69 140 176 32 64 128 256), losses := [] }

theorem u16947 : Upper (D 8) (R 8) [258,96,65,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16947 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16948 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 259 98 76 137 145 52 116 180 308), lower := (rows 259 98 76 137 145 32 64 128 256), losses := [] }

theorem u16948 : Upper (D 8) (R 8) [258,96,72,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16948 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16949 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 76 137 148 49 113 177 305), lower := (rows 259 98 76 137 148 32 64 128 256), losses := [] }

theorem u16949 : Upper (D 8) (R 8) [258,96,72,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16949 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16950 : Route 9 := (fun mask => (mask,id))

def c16950 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16950 : Upper (D 8) (R 8) [258,96,72,129,160] 13 := by
  apply FastRouting.sound _ _ [258,96,72,129,160] 13 (by decide) (choices 1) [1,4,16] r16950 c16950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6201
  · exact u6202
  · exact u6203

def b16951 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 76 140 145 49 113 177 305), lower := (rows 259 98 76 140 145 32 64 128 256), losses := [] }

theorem u16951 : Upper (D 8) (R 8) [258,96,72,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16951 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16952 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 76 140 176 49 113 177 305), lower := (rows 259 98 76 140 176 32 64 128 256), losses := [] }

theorem u16952 : Upper (D 8) (R 8) [258,96,72,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16952 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16953 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 76 152 145 37 101 165 293), lower := (rows 259 98 76 152 145 32 64 128 256), losses := [] }

theorem u16953 : Upper (D 8) (R 8) [258,96,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16953 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16954 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 76 152 148 33 97 161 289), lower := (rows 259 98 76 152 148 32 64 128 256), losses := [] }

theorem u16954 : Upper (D 8) (R 8) [258,96,72,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16954 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16955 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 76 152 176 37 101 165 293), lower := (rows 259 98 76 152 176 32 64 128 256), losses := [] }

theorem u16955 : Upper (D 8) (R 8) [258,96,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16955 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16956 : Route 9 := (fun mask => (mask,id))

def c16956 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16956 : Upper (D 8) (R 8) [258,96,72,160,129] 13 := by
  apply FastRouting.sound _ _ [258,96,72,160,129] 13 (by decide) (choices 1) [1,4,16] r16956 c16956
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6204
  · exact u6205
  · exact u6206

def b16957 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 76 168 148 49 113 177 305), lower := (rows 259 98 76 168 148 32 64 128 256), losses := [] }

theorem u16957 : Upper (D 8) (R 8) [258,96,72,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16957 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16958 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 98 76 168 176 53 85 149 277), lower := (rows 259 98 76 168 176 32 64 128 256), losses := [] }

theorem u16958 : Upper (D 8) (R 8) [258,96,72,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16958 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16959 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 100 137 148 57 121 185 313), lower := (rows 259 98 100 137 148 32 64 128 256), losses := [] }

theorem u16959 : Upper (D 8) (R 8) [258,96,96,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16959 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16960 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 100 137 176 61 93 157 285), lower := (rows 259 98 100 137 176 32 64 128 256), losses := [] }

theorem u16960 : Upper (D 8) (R 8) [258,96,96,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16960 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16961 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 100 140 176 57 89 153 281), lower := (rows 259 98 100 140 176 32 64 128 256), losses := [] }

theorem u16961 : Upper (D 8) (R 8) [258,96,96,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16961 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16962 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 194 13 13 112 176 240 176 432), lower := (rows 259 194 13 13 112 32 64 128 256), losses := [] }

theorem u16962 : Upper (D 8) (R 8) [258,192,9,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16962 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16963 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 194 13 25 52 224 224 224 480), lower := (rows 259 194 13 25 52 32 64 128 256), losses := [] }

theorem u16963 : Upper (D 8) (R 8) [258,192,9,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16963 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16964 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 259 194 13 25 84 160 224 160 416), lower := (rows 259 194 13 25 84 32 64 128 256), losses := [] }

theorem u16964 : Upper (D 8) (R 8) [258,192,9,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16964 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16965 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 259 194 13 25 112 164 228 164 420), lower := (rows 259 194 13 25 112 32 64 128 256), losses := [] }

theorem u16965 : Upper (D 8) (R 8) [258,192,9,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16965 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16966 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 194 13 28 49 224 224 224 480), lower := (rows 259 194 13 28 49 32 64 128 256), losses := [] }

theorem u16966 : Upper (D 8) (R 8) [258,192,9,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16966 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16967 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 194 13 28 81 160 224 160 416), lower := (rows 259 194 13 28 81 32 64 128 256), losses := [] }

theorem u16967 : Upper (D 8) (R 8) [258,192,9,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16967 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16968 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 259 194 13 28 112 161 225 161 417), lower := (rows 259 194 13 28 112 32 64 128 256), losses := [] }

theorem u16968 : Upper (D 8) (R 8) [258,192,9,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16968 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16969 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 194 13 28 208 33 97 161 289), lower := (rows 259 194 13 28 208 32 64 128 256), losses := [] }

theorem u16969 : Upper (D 8) (R 8) [258,192,9,20,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16969 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16970 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 194 13 41 52 240 240 240 496), lower := (rows 259 194 13 41 52 32 64 128 256), losses := [] }

theorem u16970 : Upper (D 8) (R 8) [258,192,9,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16970 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16971 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 194 13 41 84 176 240 176 432), lower := (rows 259 194 13 41 84 32 64 128 256), losses := [] }

theorem u16971 : Upper (D 8) (R 8) [258,192,9,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16971 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16972 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 194 13 41 112 180 244 180 436), lower := (rows 259 194 13 41 112 32 64 128 256), losses := [] }

theorem u16972 : Upper (D 8) (R 8) [258,192,9,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16972 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16973 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 259 194 13 44 49 240 240 240 496), lower := (rows 259 194 13 44 49 32 64 128 256), losses := [] }

theorem u16973 : Upper (D 8) (R 8) [258,192,9,36,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16973 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16974 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 194 13 44 81 176 240 176 432), lower := (rows 259 194 13 44 81 32 64 128 256), losses := [] }

theorem u16974 : Upper (D 8) (R 8) [258,192,9,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16974 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16975 : Route 9 := (fun mask => (mask,id))

def c16975 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16975 : Upper (D 8) (R 8) [258,192,9,36,96] 13 := by
  apply FastRouting.sound _ _ [258,192,9,36,96] 13 (by decide) (choices 1) [1,16,128] r16975 c16975
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6207
  · exact u6208
  · exact u6209

def b16976 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 194 13 44 208 49 113 177 305), lower := (rows 259 194 13 44 208 32 64 128 256), losses := [] }

theorem u16976 : Upper (D 8) (R 8) [258,192,9,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16976 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16977 : PairBound 9 := { available := 228, camps := [{ cop := 4, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 259 194 13 56 49 228 228 228 484), lower := (rows 259 194 13 56 49 32 64 128 256), losses := [] }

theorem u16977 : Upper (D 8) (R 8) [258,192,9,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16977 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16978 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 194 13 56 52 225 225 225 481), lower := (rows 259 194 13 56 52 32 64 128 256), losses := [] }

theorem u16978 : Upper (D 8) (R 8) [258,192,9,48,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16978 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16979 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 194 13 56 81 164 228 164 420), lower := (rows 259 194 13 56 81 32 64 128 256), losses := [] }

theorem u16979 : Upper (D 8) (R 8) [258,192,9,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16979 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u16979
end Delivery.IrregularNine14.P08
