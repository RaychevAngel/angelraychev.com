import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0006

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4920 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 44 137 148 288 80 194 322), lower := (rows 35 67 44 137 148 288 80 128 256), losses := [] }

theorem u4920 : Upper (D 7) (R 7) [34,65,40,129,132,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4920 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4921 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 137 208 288 66 148 276), lower := (rows 35 67 44 137 208 288 66 128 256), losses := [] }

theorem u4921 : Upper (D 7) (R 7) [34,65,40,129,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4921 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4922 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 152, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 35 67 44 137 208 288 68 146 274), lower := (rows 35 67 44 137 208 288 68 128 256), losses := [] }

theorem u4922 : Upper (D 7) (R 7) [34,65,40,129,192,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4922 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4923 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 44 137 208 288 80 134 262), lower := (rows 35 67 44 137 208 288 80 128 256), losses := [] }

theorem u4923 : Upper (D 7) (R 7) [34,65,40,129,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4923 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4924 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 137 400 48 66 196 324), lower := (rows 35 67 44 137 400 48 66 128 256), losses := [] }

theorem u4924 : Upper (D 7) (R 7) [34,65,40,129,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4924 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4925 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 35 67 44 137 400 48 68 194 322), lower := (rows 35 67 44 137 400 48 68 128 256), losses := [] }

theorem u4925 : Upper (D 7) (R 7) [34,65,40,129,384,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4925 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4926 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 152, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 35 67 44 138 145 288 68 208 336), lower := (rows 35 67 44 138 145 288 68 128 256), losses := [] }

theorem u4926 : Upper (D 7) (R 7) [34,65,40,130,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4926 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4927 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 44 138 145 288 80 196 324), lower := (rows 35 67 44 138 145 288 80 128 256), losses := [] }

theorem u4927 : Upper (D 7) (R 7) [34,65,40,130,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4927 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4928 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 138 148 288 65 208 336), lower := (rows 35 67 44 138 148 288 65 128 256), losses := [] }

theorem u4928 : Upper (D 7) (R 7) [34,65,40,130,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4928 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4929 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 44 138 148 288 80 193 321), lower := (rows 35 67 44 138 148 288 80 128 256), losses := [] }

theorem u4929 : Upper (D 7) (R 7) [34,65,40,130,132,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4929 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4930 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 138 208 288 65 148 276), lower := (rows 35 67 44 138 208 288 65 128 256), losses := [] }

theorem u4930 : Upper (D 7) (R 7) [34,65,40,130,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4930 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4931 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 152, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 35 67 44 138 208 288 68 145 273), lower := (rows 35 67 44 138 208 288 68 128 256), losses := [] }

theorem u4931 : Upper (D 7) (R 7) [34,65,40,130,192,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4931 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4932 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 44 138 208 288 80 133 261), lower := (rows 35 67 44 138 208 288 80 128 256), losses := [] }

theorem u4932 : Upper (D 7) (R 7) [34,65,40,130,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4932 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4933 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 44 138 273 48 68 192 448), lower := (rows 35 67 44 138 273 48 68 128 256), losses := [] }

theorem u4933 : Upper (D 7) (R 7) [34,65,40,130,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4933 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4934 : Route 9 := (fun mask => (mask,id))

def c4934 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4934 : Upper (D 7) (R 7) [34,65,40,130,257,16,128] 13 := by
  apply FastRouting.sound _ _ [34,65,40,130,257,16,128] 13 (by decide) (choices 1) [4,64] r4934 c4934
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u378
  · exact u379

def b4935 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 138 400 48 65 196 324), lower := (rows 35 67 44 138 400 48 65 128 256), losses := [] }

theorem u4935 : Upper (D 7) (R 7) [34,65,40,130,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4935 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4936 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 35 67 44 138 400 48 68 193 321), lower := (rows 35 67 44 138 400 48 68 128 256), losses := [] }

theorem u4936 : Upper (D 7) (R 7) [34,65,40,130,384,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4936 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4937 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 200 145 288 66 148 276), lower := (rows 35 67 44 200 145 288 66 128 256), losses := [] }

theorem u4937 : Upper (D 7) (R 7) [34,65,40,192,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4937 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4938 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 152, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 35 67 44 200 145 288 68 146 274), lower := (rows 35 67 44 200 145 288 68 128 256), losses := [] }

theorem u4938 : Upper (D 7) (R 7) [34,65,40,192,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4938 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4939 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 44 200 145 288 80 134 262), lower := (rows 35 67 44 200 145 288 80 128 256), losses := [] }

theorem u4939 : Upper (D 7) (R 7) [34,65,40,192,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4939 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4940 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 200 146 288 65 148 276), lower := (rows 35 67 44 200 146 288 65 128 256), losses := [] }

theorem u4940 : Upper (D 7) (R 7) [34,65,40,192,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4940 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4941 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 152, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 35 67 44 200 146 288 68 145 273), lower := (rows 35 67 44 200 146 288 68 128 256), losses := [] }

theorem u4941 : Upper (D 7) (R 7) [34,65,40,192,130,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4941 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4942 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 44 200 146 288 80 133 261), lower := (rows 35 67 44 200 146 288 80 128 256), losses := [] }

theorem u4942 : Upper (D 7) (R 7) [34,65,40,192,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4942 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4943 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 200 148 288 65 146 274), lower := (rows 35 67 44 200 148 288 65 128 256), losses := [] }

theorem u4943 : Upper (D 7) (R 7) [34,65,40,192,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4943 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4944 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 200 148 288 66 145 273), lower := (rows 35 67 44 200 148 288 66 128 256), losses := [] }

theorem u4944 : Upper (D 7) (R 7) [34,65,40,192,132,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4944 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4945 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 291, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 44 200 148 288 80 131 259), lower := (rows 35 67 44 200 148 288 80 128 256), losses := [] }

theorem u4945 : Upper (D 7) (R 7) [34,65,40,192,132,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4945 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4946 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 200 273 48 66 132 388), lower := (rows 35 67 44 200 273 48 66 128 256), losses := [] }

theorem u4946 : Upper (D 7) (R 7) [34,65,40,192,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4946 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4947 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 44 200 273 48 68 130 386), lower := (rows 35 67 44 200 273 48 68 128 256), losses := [] }

theorem u4947 : Upper (D 7) (R 7) [34,65,40,192,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4947 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4948 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 44 200 273 48 192 134 262), lower := (rows 35 67 44 200 273 48 192 128 256), losses := [] }

theorem u4948 : Upper (D 7) (R 7) [34,65,40,192,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4948 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4949 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 200 276 48 65 130 386), lower := (rows 35 67 44 200 276 48 65 128 256), losses := [] }

theorem u4949 : Upper (D 7) (R 7) [34,65,40,192,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4949 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4950 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 200 276 48 66 129 385), lower := (rows 35 67 44 200 276 48 66 128 256), losses := [] }

theorem u4950 : Upper (D 7) (R 7) [34,65,40,192,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4950 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4951 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 44 200 276 48 192 131 259), lower := (rows 35 67 44 200 276 48 192 128 256), losses := [] }

theorem u4951 : Upper (D 7) (R 7) [34,65,40,192,260,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4951 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4952 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 200 400 48 65 134 262), lower := (rows 35 67 44 200 400 48 65 128 256), losses := [] }

theorem u4952 : Upper (D 7) (R 7) [34,65,40,192,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4952 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4953 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 200 400 48 66 133 261), lower := (rows 35 67 44 200 400 48 66 128 256), losses := [] }

theorem u4953 : Upper (D 7) (R 7) [34,65,40,192,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4953 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4954 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 44 200 400 48 68 131 259), lower := (rows 35 67 44 200 400 48 68 128 256), losses := [] }

theorem u4954 : Upper (D 7) (R 7) [34,65,40,192,384,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4954 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4955 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 408, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 35 67 44 265 146 160 68 208 336), lower := (rows 35 67 44 265 146 160 68 128 256), losses := [] }

theorem u4955 : Upper (D 7) (R 7) [34,65,40,257,130,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4955 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4956 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 428, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 67 44 265 146 160 80 196 324), lower := (rows 35 67 44 265 146 160 80 128 256), losses := [] }

theorem u4956 : Upper (D 7) (R 7) [34,65,40,257,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4956 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4957 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 265 148 160 66 208 336), lower := (rows 35 67 44 265 148 160 66 128 256), losses := [] }

theorem u4957 : Upper (D 7) (R 7) [34,65,40,257,132,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4957 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4958 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 264, targets := 32 },{ cop := 1, region := 264, targets := 128 }], pairs := [(2,0),(3,5),(3,7)], upper := (rows 35 67 44 265 148 160 80 194 322), lower := (rows 35 67 44 265 148 160 80 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 179 80 130 258), good := (rows 418 482 44 300 244 160 112 160 256) }] }

theorem u4958 : Upper (D 7) (R 7) [34,65,40,257,132,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4958 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4959 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 265 208 160 66 148 276), lower := (rows 35 67 44 265 208 160 66 128 256), losses := [] }

theorem u4959 : Upper (D 7) (R 7) [34,65,40,257,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4960 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 408, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 35 67 44 265 208 160 68 146 274), lower := (rows 35 67 44 265 208 160 68 128 256), losses := [] }

theorem u4960 : Upper (D 7) (R 7) [34,65,40,257,192,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4960 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4961 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 67 44 265 208 160 80 134 262), lower := (rows 35 67 44 265 208 160 80 128 256), losses := [] }

theorem u4961 : Upper (D 7) (R 7) [34,65,40,257,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4961 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4962 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 44 266 145 48 68 192 448), lower := (rows 35 67 44 266 145 48 68 128 256), losses := [] }

theorem u4962 : Upper (D 7) (R 7) [34,65,40,258,129,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4962 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4963 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 460, targets := 1 },{ cop := 4, region := 66, targets := 32 }], pairs := [(1,5),(2,0),(3,0)], upper := (rows 35 67 44 266 145 48 192 196 324), lower := (rows 35 67 44 266 145 48 192 128 256), losses := [] }

theorem u4963 : Upper (D 7) (R 7) [34,65,40,258,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4963 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4964 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 408, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 35 67 44 266 145 160 68 208 336), lower := (rows 35 67 44 266 145 160 68 128 256), losses := [] }

theorem u4964 : Upper (D 7) (R 7) [34,65,40,258,129,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4964 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4965 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 428, targets := 1 },{ cop := 4, region := 66, targets := 32 }], pairs := [(1,5),(2,0),(3,0)], upper := (rows 35 67 44 266 145 160 80 196 324), lower := (rows 35 67 44 266 145 160 80 128 256), losses := [] }

theorem u4965 : Upper (D 7) (R 7) [34,65,40,258,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4965 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4966 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 444, targets := 1 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 266 148 160 65 208 336), lower := (rows 35 67 44 266 148 160 65 128 256), losses := [] }

theorem u4966 : Upper (D 7) (R 7) [34,65,40,258,132,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4966 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4967 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 264, targets := 32 },{ cop := 1, region := 264, targets := 128 }], pairs := [(2,1),(3,5),(3,7)], upper := (rows 35 67 44 266 148 160 80 193 321), lower := (rows 35 67 44 266 148 160 80 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 24 187 92 130 258), good := (rows 417 481 124 508 244 160 112 160 256) }] }

theorem u4967 : Upper (D 7) (R 7) [34,65,40,258,132,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4967 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4968 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 444, targets := 1 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 266 208 160 65 148 276), lower := (rows 35 67 44 266 208 160 65 128 256), losses := [] }

theorem u4968 : Upper (D 7) (R 7) [34,65,40,258,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4968 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4969 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 408, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 35 67 44 266 208 160 68 145 273), lower := (rows 35 67 44 266 208 160 68 128 256), losses := [] }

theorem u4969 : Upper (D 7) (R 7) [34,65,40,258,192,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4969 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4970 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 67 44 266 208 160 80 133 261), lower := (rows 35 67 44 266 208 160 80 128 256), losses := [] }

theorem u4970 : Upper (D 7) (R 7) [34,65,40,258,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4970 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4971 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 268 145 160 66 208 336), lower := (rows 35 67 44 268 145 160 66 128 256), losses := [] }

theorem u4971 : Upper (D 7) (R 7) [34,65,40,260,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4971 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4972 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 1, region := 428, targets := 1 }], pairs := [(1,5),(2,0),(4,5)], upper := (rows 35 67 44 268 145 160 80 194 322), lower := (rows 35 67 44 268 145 160 80 128 256), losses := [] }

theorem u4972 : Upper (D 7) (R 7) [34,65,40,260,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4972 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4973 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 444, targets := 1 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 268 146 160 65 208 336), lower := (rows 35 67 44 268 146 160 65 128 256), losses := [] }

theorem u4973 : Upper (D 7) (R 7) [34,65,40,260,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4974 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 1, region := 428, targets := 2 }], pairs := [(1,5),(2,1),(4,5)], upper := (rows 35 67 44 268 146 160 80 193 321), lower := (rows 35 67 44 268 146 160 80 128 256), losses := [] }

theorem u4974 : Upper (D 7) (R 7) [34,65,40,260,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4974 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4975 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 444, targets := 1 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 268 208 160 65 146 274), lower := (rows 35 67 44 268 208 160 65 128 256), losses := [] }

theorem u4975 : Upper (D 7) (R 7) [34,65,40,260,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4976 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 268 208 160 66 145 273), lower := (rows 35 67 44 268 208 160 66 128 256), losses := [] }

theorem u4976 : Upper (D 7) (R 7) [34,65,40,260,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4976 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4977 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 67 44 268 208 160 80 131 259), lower := (rows 35 67 44 268 208 160 80 128 256), losses := [] }

theorem u4977 : Upper (D 7) (R 7) [34,65,40,260,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4977 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4978 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 328 145 48 66 132 388), lower := (rows 35 67 44 328 145 48 66 128 256), losses := [] }

theorem u4978 : Upper (D 7) (R 7) [34,65,40,320,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4978 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4979 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 44 328 145 48 68 130 386), lower := (rows 35 67 44 328 145 48 68 128 256), losses := [] }

theorem u4979 : Upper (D 7) (R 7) [34,65,40,320,129,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4979 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u4979
end Delivery.IrregularNine14.P07
