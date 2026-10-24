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

def b4920 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 280 146 160 97 161 289), lower := (rows 97 38 76 280 146 160 64 128 256), losses := [] }

theorem u4920 : Upper (D 8) (R 8) [96,36,72,272,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4920 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4921 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 280 176 33 195 131 387), lower := (rows 97 38 76 280 176 33 64 128 256), losses := [] }

theorem u4921 : Upper (D 8) (R 8) [96,36,72,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4921 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4922 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 38 76 280 176 34 193 129 385), lower := (rows 97 38 76 280 176 34 64 128 256), losses := [] }

theorem u4922 : Upper (D 8) (R 8) [96,36,72,272,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4922 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4923 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 280 176 160 67 131 259), lower := (rows 97 38 76 280 176 160 64 128 256), losses := [] }

theorem u4923 : Upper (D 8) (R 8) [96,36,72,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4923 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4924 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 296 145 33 210 146 402), lower := (rows 97 38 76 296 145 33 64 128 256), losses := [] }

theorem u4924 : Upper (D 8) (R 8) [96,36,72,288,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4924 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4925 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 97 38 76 296 145 34 209 145 401), lower := (rows 97 38 76 296 145 34 64 128 256), losses := [] }

theorem u4925 : Upper (D 8) (R 8) [96,36,72,288,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4925 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4926 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 97 38 76 296 145 48 195 131 387), lower := (rows 97 38 76 296 145 48 64 128 256), losses := [] }

theorem u4926 : Upper (D 8) (R 8) [96,36,72,288,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4926 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4927 : Route 9 := (fun mask => (mask,id))

def c4927 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4927 : Upper (D 8) (R 8) [96,36,72,288,129,128] 13 := by
  apply FastRouting.sound _ _ [96,36,72,288,129,128] 13 (by decide) (choices 1) [1,2,16] r4927 c4927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u676
  · exact u677
  · exact u678

def b4928 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 296 146 33 209 145 401), lower := (rows 97 38 76 296 146 33 64 128 256), losses := [] }

theorem u4928 : Upper (D 8) (R 8) [96,36,72,288,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4928 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4929 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 38 76 296 146 48 193 129 385), lower := (rows 97 38 76 296 146 48 64 128 256), losses := [] }

theorem u4929 : Upper (D 8) (R 8) [96,36,72,288,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4929 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4930 : Route 9 := (fun mask => (mask,id))

def c4930 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4930 : Upper (D 8) (R 8) [96,36,72,288,130,128] 13 := by
  apply FastRouting.sound _ _ [96,36,72,288,130,128] 13 (by decide) (choices 1) [1,16] r4930 c4930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u679
  · exact u680

def b4931 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 392 145 33 114 178 306), lower := (rows 97 38 76 392 145 33 64 128 256), losses := [] }

theorem u4931 : Upper (D 8) (R 8) [96,36,72,384,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4931 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4932 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 38 76 392 145 34 113 177 305), lower := (rows 97 38 76 392 145 34 64 128 256), losses := [] }

theorem u4932 : Upper (D 8) (R 8) [96,36,72,384,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4932 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4933 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 38 76 392 145 48 99 163 291), lower := (rows 97 38 76 392 145 48 64 128 256), losses := [] }

theorem u4933 : Upper (D 8) (R 8) [96,36,72,384,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4933 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4934 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 392 176 33 83 147 275), lower := (rows 97 38 76 392 176 33 64 128 256), losses := [] }

theorem u4934 : Upper (D 8) (R 8) [96,36,72,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4934 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4935 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 38 76 392 176 34 81 145 273), lower := (rows 97 38 76 392 176 34 64 128 256), losses := [] }

theorem u4935 : Upper (D 8) (R 8) [96,36,72,384,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4935 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4936 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 38 76 392 176 48 67 131 259), lower := (rows 97 38 76 392 176 48 64 128 256), losses := [] }

theorem u4936 : Upper (D 8) (R 8) [96,36,72,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4936 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4937 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 133 56 208 33 330 394 266), lower := (rows 97 38 133 56 208 33 64 128 256), losses := [] }

theorem u4937 : Upper (D 8) (R 8) [96,36,129,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4937 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4938 : PairBound 9 := { available := 265, camps := [], pairs := [], upper := (rows 97 38 133 56 208 34 329 393 265), lower := (rows 97 38 133 56 208 34 64 128 256), losses := [] }

theorem u4938 : Upper (D 8) (R 8) [96,36,129,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4938 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4939 : PairBound 9 := { available := 259, camps := [], pairs := [], upper := (rows 97 38 133 56 208 40 323 387 259), lower := (rows 97 38 133 56 208 40 64 128 256), losses := [] }

theorem u4939 : Upper (D 8) (R 8) [96,36,129,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4939 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4940 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 97 38 133 56 208 288 75 139 267), lower := (rows 97 38 133 56 208 288 64 128 256), losses := [] }

theorem u4940 : Upper (D 8) (R 8) [96,36,129,48,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4940 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4941 : PairBound 9 := { available := 200, camps := [], pairs := [], upper := (rows 97 38 133 56 273 34 200 200 456), lower := (rows 97 38 133 56 273 34 64 128 256), losses := [] }

theorem u4941 : Upper (D 8) (R 8) [96,36,129,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4941 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4942 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 97 38 133 56 273 40 194 194 450), lower := (rows 97 38 133 56 273 40 64 128 256), losses := [] }

theorem u4942 : Upper (D 8) (R 8) [96,36,129,48,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4942 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4943 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 56 273 96 202 138 394), lower := (rows 97 38 133 56 273 96 64 128 256), losses := [] }

theorem u4943 : Upper (D 8) (R 8) [96,36,129,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4943 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4944 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 345, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 56 273 160 74 202 330), lower := (rows 97 38 133 56 273 160 64 128 256), losses := [] }

theorem u4944 : Upper (D 8) (R 8) [96,36,129,48,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4944 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4945 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 133 56 274 33 200 200 456), lower := (rows 97 38 133 56 274 33 64 128 256), losses := [] }

theorem u4945 : Upper (D 8) (R 8) [96,36,129,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4945 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4946 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 38 133 56 274 40 193 193 449), lower := (rows 97 38 133 56 274 40 64 128 256), losses := [] }

theorem u4946 : Upper (D 8) (R 8) [96,36,129,48,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4946 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4947 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 56 274 96 201 137 393), lower := (rows 97 38 133 56 274 96 64 128 256), losses := [] }

theorem u4947 : Upper (D 8) (R 8) [96,36,129,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4947 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4948 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 345, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 56 274 160 73 201 329), lower := (rows 97 38 133 56 274 160 64 128 256), losses := [] }

theorem u4948 : Upper (D 8) (R 8) [96,36,129,48,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4948 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4949 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 133 56 280 33 194 194 450), lower := (rows 97 38 133 56 280 33 64 128 256), losses := [] }

theorem u4949 : Upper (D 8) (R 8) [96,36,129,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4949 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4950 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 38 133 56 280 34 193 193 449), lower := (rows 97 38 133 56 280 34 64 128 256), losses := [] }

theorem u4950 : Upper (D 8) (R 8) [96,36,129,48,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4950 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4951 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 134, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 56 280 96 195 131 387), lower := (rows 97 38 133 56 280 96 64 128 256), losses := [] }

theorem u4951 : Upper (D 8) (R 8) [96,36,129,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4951 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4952 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 56 280 160 67 195 323), lower := (rows 97 38 133 56 280 160 64 128 256), losses := [] }

theorem u4952 : Upper (D 8) (R 8) [96,36,129,48,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4952 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4953 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 133 56 336 33 202 138 394), lower := (rows 97 38 133 56 336 33 64 128 256), losses := [] }

theorem u4953 : Upper (D 8) (R 8) [96,36,129,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4953 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4954 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 97 38 133 56 336 34 201 137 393), lower := (rows 97 38 133 56 336 34 64 128 256), losses := [] }

theorem u4954 : Upper (D 8) (R 8) [96,36,129,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4954 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4955 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 97 38 133 56 336 40 195 131 387), lower := (rows 97 38 133 56 336 40 64 128 256), losses := [] }

theorem u4955 : Upper (D 8) (R 8) [96,36,129,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4955 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4956 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 345, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 56 336 160 75 139 267), lower := (rows 97 38 133 56 336 160 64 128 256), losses := [] }

theorem u4956 : Upper (D 8) (R 8) [96,36,129,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4956 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4957 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 133 56 400 33 74 202 330), lower := (rows 97 38 133 56 400 33 64 128 256), losses := [] }

theorem u4957 : Upper (D 8) (R 8) [96,36,129,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4957 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4958 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 97 38 133 56 400 34 73 201 329), lower := (rows 97 38 133 56 400 34 64 128 256), losses := [] }

theorem u4958 : Upper (D 8) (R 8) [96,36,129,48,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4958 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4959 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 97 38 133 56 400 40 67 195 323), lower := (rows 97 38 133 56 400 40 64 128 256), losses := [] }

theorem u4959 : Upper (D 8) (R 8) [96,36,129,48,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4959 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4960 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 56 400 96 75 139 267), lower := (rows 97 38 133 56 400 96 64 128 256), losses := [] }

theorem u4960 : Upper (D 8) (R 8) [96,36,129,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4960 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4961 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 133 74 176 33 344 408 280), lower := (rows 97 38 133 74 176 33 64 128 256), losses := [] }

theorem u4961 : Upper (D 8) (R 8) [96,36,129,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4961 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4962 : PairBound 9 := { available := 273, camps := [], pairs := [], upper := (rows 97 38 133 74 176 40 337 401 273), lower := (rows 97 38 133 74 176 40 64 128 256), losses := [] }

theorem u4962 : Upper (D 8) (R 8) [96,36,129,66,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4962 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4963 : PairBound 9 := { available := 265, camps := [], pairs := [], upper := (rows 97 38 133 74 176 48 329 393 265), lower := (rows 97 38 133 74 176 48 64 128 256), losses := [] }

theorem u4963 : Upper (D 8) (R 8) [96,36,129,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4963 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4964 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 97 38 133 74 176 288 89 153 281), lower := (rows 97 38 133 74 176 288 64 128 256), losses := [] }

theorem u4964 : Upper (D 8) (R 8) [96,36,129,66,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4964 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4965 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 97 38 133 74 273 40 240 176 432), lower := (rows 97 38 133 74 273 40 64 128 256), losses := [] }

theorem u4965 : Upper (D 8) (R 8) [96,36,129,66,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4965 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4966 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 97 38 133 74 273 48 232 168 424), lower := (rows 97 38 133 74 273 48 64 128 256), losses := [] }

theorem u4966 : Upper (D 8) (R 8) [96,36,129,66,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4966 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4967 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 345, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 74 273 160 120 184 312), lower := (rows 97 38 133 74 273 160 64 128 256), losses := [] }

theorem u4967 : Upper (D 8) (R 8) [96,36,129,66,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4967 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4968 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 133 74 280 33 240 176 432), lower := (rows 97 38 133 74 280 33 64 128 256), losses := [] }

theorem u4968 : Upper (D 8) (R 8) [96,36,129,66,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4968 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4969 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 38 133 74 280 48 225 161 417), lower := (rows 97 38 133 74 280 48 64 128 256), losses := [] }

theorem u4969 : Upper (D 8) (R 8) [96,36,129,66,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4969 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4970 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 345, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 74 280 160 113 177 305), lower := (rows 97 38 133 74 280 160 64 128 256), losses := [] }

theorem u4970 : Upper (D 8) (R 8) [96,36,129,66,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4970 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4971 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 133 74 304 33 216 152 408), lower := (rows 97 38 133 74 304 33 64 128 256), losses := [] }

theorem u4971 : Upper (D 8) (R 8) [96,36,129,66,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4971 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4972 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 97 38 133 74 304 40 209 145 401), lower := (rows 97 38 133 74 304 40 64 128 256), losses := [] }

theorem u4972 : Upper (D 8) (R 8) [96,36,129,66,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4972 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4973 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 97 38 133 74 304 48 201 137 393), lower := (rows 97 38 133 74 304 48 64 128 256), losses := [] }

theorem u4973 : Upper (D 8) (R 8) [96,36,129,66,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4973 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4974 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 345, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 74 304 160 89 153 281), lower := (rows 97 38 133 74 304 160 64 128 256), losses := [] }

theorem u4974 : Upper (D 8) (R 8) [96,36,129,66,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4974 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4975 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 133 74 400 33 120 184 312), lower := (rows 97 38 133 74 400 33 64 128 256), losses := [] }

theorem u4975 : Upper (D 8) (R 8) [96,36,129,66,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4975 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4976 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 38 133 74 400 40 113 177 305), lower := (rows 97 38 133 74 400 40 64 128 256), losses := [] }

theorem u4976 : Upper (D 8) (R 8) [96,36,129,66,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4976 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4977 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 38 133 74 400 48 105 169 297), lower := (rows 97 38 133 74 400 48 64 128 256), losses := [] }

theorem u4977 : Upper (D 8) (R 8) [96,36,129,66,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4977 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4978 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 133 88 176 33 330 394 266), lower := (rows 97 38 133 88 176 33 64 128 256), losses := [] }

theorem u4978 : Upper (D 8) (R 8) [96,36,129,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4978 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4979 : PairBound 9 := { available := 265, camps := [], pairs := [], upper := (rows 97 38 133 88 176 34 329 393 265), lower := (rows 97 38 133 88 176 34 64 128 256), losses := [] }

theorem u4979 : Upper (D 8) (R 8) [96,36,129,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4979 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u4979
end Delivery.IrregularNine14.P08
