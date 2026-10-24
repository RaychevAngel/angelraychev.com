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

def r17940 : Route 9 := (fun mask => (mask,id))

def c17940 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17940 : Upper (D 8) (R 8) [320,5,34,160,192] 13 := by
  apply FastRouting.sound _ _ [320,5,34,160,192] 13 (by decide) (choices 1) [1,8,16] r17940 c17940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6644
  · exact u6645
  · exact u6646

def b17941 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 44 25 50 224 224 224 480), lower := (rows 321 7 44 25 50 32 64 128 256), losses := [] }

theorem u17941 : Upper (D 8) (R 8) [320,5,40,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17941 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17942 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 44 25 82 160 224 160 416), lower := (rows 321 7 44 25 82 32 64 128 256), losses := [] }

theorem u17942 : Upper (D 8) (R 8) [320,5,40,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17942 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17943 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 44 25 112 162 226 162 418), lower := (rows 321 7 44 25 112 32 64 128 256), losses := [] }

theorem u17943 : Upper (D 8) (R 8) [320,5,40,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17943 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17944 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 44 25 146 224 224 224 480), lower := (rows 321 7 44 25 146 32 64 128 256), losses := [] }

theorem u17944 : Upper (D 8) (R 8) [320,5,40,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17944 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17945 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 44 25 176 226 226 226 482), lower := (rows 321 7 44 25 176 32 64 128 256), losses := [] }

theorem u17945 : Upper (D 8) (R 8) [320,5,40,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17945 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17946 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 44 25 208 162 226 162 418), lower := (rows 321 7 44 25 208 32 64 128 256), losses := [] }

theorem u17946 : Upper (D 8) (R 8) [320,5,40,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17946 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17947 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 44 26 49 224 224 224 480), lower := (rows 321 7 44 26 49 32 64 128 256), losses := [] }

theorem u17947 : Upper (D 8) (R 8) [320,5,40,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17947 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17948 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 44 26 81 160 224 160 416), lower := (rows 321 7 44 26 81 32 64 128 256), losses := [] }

theorem u17948 : Upper (D 8) (R 8) [320,5,40,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17948 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17949 : PairBound 9 := { available := 161, camps := [], pairs := [(2,6)], upper := (rows 321 7 44 26 112 161 225 161 417), lower := (rows 321 7 44 26 112 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 16 35 0 131 259), good := (rows 417 423 44 446 48 32 0 128 256) }] }

theorem u17949 : Upper (D 8) (R 8) [320,5,40,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17949 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17950 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 26 145 224 224 224 480), lower := (rows 321 7 44 26 145 32 64 128 256), losses := [] }

theorem u17950 : Upper (D 8) (R 8) [320,5,40,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17950 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17951 : Route 9 := (fun mask => (mask,id))

def c17951 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17951 : Upper (D 8) (R 8) [320,5,40,18,160] 13 := by
  apply FastRouting.sound _ _ [320,5,40,18,160] 13 (by decide) (choices 1) [1,64,128] r17951 c17951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6647
  · exact u6648
  · exact u6649

def b17952 : PairBound 9 := { available := 161, camps := [], pairs := [(2,6)], upper := (rows 321 7 44 26 208 161 225 161 417), lower := (rows 321 7 44 26 208 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 16 35 0 131 259), good := (rows 417 423 44 446 144 32 0 128 256) }] }

theorem u17952 : Upper (D 8) (R 8) [320,5,40,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17952 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17953 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 44 41 50 240 208 208 464), lower := (rows 321 7 44 41 50 32 64 128 256), losses := [] }

theorem u17953 : Upper (D 8) (R 8) [320,5,40,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17953 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17954 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 44 41 82 176 240 176 432), lower := (rows 321 7 44 41 82 32 64 128 256), losses := [] }

theorem u17954 : Upper (D 8) (R 8) [320,5,40,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17954 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17955 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 44 41 112 178 210 146 402), lower := (rows 321 7 44 41 112 32 64 128 256), losses := [] }

theorem u17955 : Upper (D 8) (R 8) [320,5,40,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17955 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17956 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 44 41 146 240 240 240 496), lower := (rows 321 7 44 41 146 32 64 128 256), losses := [] }

theorem u17956 : Upper (D 8) (R 8) [320,5,40,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17956 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17957 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 44 41 176 242 210 210 466), lower := (rows 321 7 44 41 176 32 64 128 256), losses := [] }

theorem u17957 : Upper (D 8) (R 8) [320,5,40,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17957 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17958 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 44 41 208 178 242 178 434), lower := (rows 321 7 44 41 208 32 64 128 256), losses := [] }

theorem u17958 : Upper (D 8) (R 8) [320,5,40,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17958 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17959 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 44 42 49 240 208 208 464), lower := (rows 321 7 44 42 49 32 64 128 256), losses := [] }

theorem u17959 : Upper (D 8) (R 8) [320,5,40,34,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17959 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17960 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 42 112 177 209 145 401), lower := (rows 321 7 44 42 112 32 64 128 256), losses := [] }

theorem u17960 : Upper (D 8) (R 8) [320,5,40,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17960 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17961 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 42 145 240 240 240 496), lower := (rows 321 7 44 42 145 32 64 128 256), losses := [] }

theorem u17961 : Upper (D 8) (R 8) [320,5,40,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17961 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17962 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 42 176 241 209 209 465), lower := (rows 321 7 44 42 176 32 64 128 256), losses := [] }

theorem u17962 : Upper (D 8) (R 8) [320,5,40,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17962 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17963 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 42 208 177 241 177 433), lower := (rows 321 7 44 42 208 32 64 128 256), losses := [] }

theorem u17963 : Upper (D 8) (R 8) [320,5,40,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17963 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17964 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 44 56 49 226 194 194 450), lower := (rows 321 7 44 56 49 32 64 128 256), losses := [] }

theorem u17964 : Upper (D 8) (R 8) [320,5,40,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17964 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17965 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 56 50 225 193 193 449), lower := (rows 321 7 44 56 50 32 64 128 256), losses := [] }

theorem u17965 : Upper (D 8) (R 8) [320,5,40,48,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17965 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17966 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 56 82 161 225 161 417), lower := (rows 321 7 44 56 82 32 64 128 256), losses := [] }

theorem u17966 : Upper (D 8) (R 8) [320,5,40,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17966 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17967 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 56 112 163 195 131 387), lower := (rows 321 7 44 56 112 32 64 128 256), losses := [] }

theorem u17967 : Upper (D 8) (R 8) [320,5,40,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17967 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17968 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 56 145 226 226 226 482), lower := (rows 321 7 44 56 145 32 64 128 256), losses := [] }

theorem u17968 : Upper (D 8) (R 8) [320,5,40,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17968 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17969 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 56 146 225 225 225 481), lower := (rows 321 7 44 56 146 32 64 128 256), losses := [] }

theorem u17969 : Upper (D 8) (R 8) [320,5,40,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17969 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17970 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 56 176 227 195 195 451), lower := (rows 321 7 44 56 176 32 64 128 256), losses := [] }

theorem u17970 : Upper (D 8) (R 8) [320,5,40,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17970 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17971 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 56 208 163 227 163 419), lower := (rows 321 7 44 56 208 32 64 128 256), losses := [] }

theorem u17971 : Upper (D 8) (R 8) [320,5,40,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17971 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17972 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 44 73 50 176 240 176 432), lower := (rows 321 7 44 73 50 32 64 128 256), losses := [] }

theorem u17972 : Upper (D 8) (R 8) [320,5,40,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17972 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17973 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 44 73 146 176 240 176 432), lower := (rows 321 7 44 73 146 32 64 128 256), losses := [] }

theorem u17973 : Upper (D 8) (R 8) [320,5,40,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17973 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17974 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 44 73 176 178 242 178 434), lower := (rows 321 7 44 73 176 32 64 128 256), losses := [] }

theorem u17974 : Upper (D 8) (R 8) [320,5,40,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17974 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17975 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 44 74 49 176 240 176 432), lower := (rows 321 7 44 74 49 32 64 128 256), losses := [] }

theorem u17975 : Upper (D 8) (R 8) [320,5,40,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17975 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17976 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 44 74 145 176 240 176 432), lower := (rows 321 7 44 74 145 32 64 128 256), losses := [] }

theorem u17976 : Upper (D 8) (R 8) [320,5,40,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17976 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17977 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 44 74 176 177 241 177 433), lower := (rows 321 7 44 74 176 32 64 128 256), losses := [] }

theorem u17977 : Upper (D 8) (R 8) [320,5,40,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17977 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17978 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 44 88 49 162 226 162 418), lower := (rows 321 7 44 88 49 32 64 128 256), losses := [] }

theorem u17978 : Upper (D 8) (R 8) [320,5,40,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17978 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17979 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 44 88 50 161 225 161 417), lower := (rows 321 7 44 88 50 32 64 128 256), losses := [] }

theorem u17979 : Upper (D 8) (R 8) [320,5,40,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17979 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17980 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 44 88 145 162 226 162 418), lower := (rows 321 7 44 88 145 32 64 128 256), losses := [] }

theorem u17980 : Upper (D 8) (R 8) [320,5,40,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17980 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17981 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 44 88 146 161 225 161 417), lower := (rows 321 7 44 88 146 32 64 128 256), losses := [] }

theorem u17981 : Upper (D 8) (R 8) [320,5,40,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17981 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17982 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 44 88 176 163 227 163 419), lower := (rows 321 7 44 88 176 32 64 128 256), losses := [] }

theorem u17982 : Upper (D 8) (R 8) [320,5,40,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17982 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17983 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 104 49 178 210 146 402), lower := (rows 321 7 44 104 49 32 64 128 256), losses := [] }

theorem u17983 : Upper (D 8) (R 8) [320,5,40,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17983 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17984 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 104 50 177 209 145 401), lower := (rows 321 7 44 104 50 32 64 128 256), losses := [] }

theorem u17984 : Upper (D 8) (R 8) [320,5,40,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17984 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17985 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 104 145 178 242 178 434), lower := (rows 321 7 44 104 145 32 64 128 256), losses := [] }

theorem u17985 : Upper (D 8) (R 8) [320,5,40,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17985 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17986 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 104 146 177 241 177 433), lower := (rows 321 7 44 104 146 32 64 128 256), losses := [] }

theorem u17986 : Upper (D 8) (R 8) [320,5,40,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17986 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17987 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 104 176 179 211 147 403), lower := (rows 321 7 44 104 176 32 64 128 256), losses := [] }

theorem u17987 : Upper (D 8) (R 8) [320,5,40,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17987 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17988 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 44 137 50 240 240 240 496), lower := (rows 321 7 44 137 50 32 64 128 256), losses := [] }

theorem u17988 : Upper (D 8) (R 8) [320,5,40,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17988 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17989 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 44 137 82 176 240 176 432), lower := (rows 321 7 44 137 82 32 64 128 256), losses := [] }

theorem u17989 : Upper (D 8) (R 8) [320,5,40,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17989 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17990 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 44 137 112 178 242 178 434), lower := (rows 321 7 44 137 112 32 64 128 256), losses := [] }

theorem u17990 : Upper (D 8) (R 8) [320,5,40,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17990 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17991 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 44 137 146 112 112 240 368), lower := (rows 321 7 44 137 146 32 64 128 256), losses := [] }

theorem u17991 : Upper (D 8) (R 8) [320,5,40,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17991 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17992 : PairBound 9 := { available := 114, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 44 137 176 114 114 242 370), lower := (rows 321 7 44 137 176 32 64 128 256), losses := [] }

theorem u17992 : Upper (D 8) (R 8) [320,5,40,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17992 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17993 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 44 137 208 50 114 178 306), lower := (rows 321 7 44 137 208 32 64 128 256), losses := [] }

theorem u17993 : Upper (D 8) (R 8) [320,5,40,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17993 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17994 : Route 9 := (fun mask => (mask,id))

def c17994 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u17994 : Upper (D 8) (R 8) [320,5,40,130,33] 13 := by
  apply FastRouting.sound _ _ [320,5,40,130,33] 13 (by decide) (choices 1) [16,64,128] r17994 c17994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6650
  · exact u6651
  · exact u6652

def b17995 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 44 138 81 176 240 176 432), lower := (rows 321 7 44 138 81 32 64 128 256), losses := [] }

theorem u17995 : Upper (D 8) (R 8) [320,5,40,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17995 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17996 : Route 9 := (fun mask => (mask,id))

def c17996 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17996 : Upper (D 8) (R 8) [320,5,40,130,96] 13 := by
  apply FastRouting.sound _ _ [320,5,40,130,96] 13 (by decide) (choices 1) [1,16,128] r17996 c17996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6653
  · exact u6654
  · exact u6655

def b17997 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 44 138 145 112 112 240 368), lower := (rows 321 7 44 138 145 32 64 128 256), losses := [] }

theorem u17997 : Upper (D 8) (R 8) [320,5,40,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17997 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17998 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 44 138 176 113 113 241 369), lower := (rows 321 7 44 138 176 32 64 128 256), losses := [] }

theorem u17998 : Upper (D 8) (R 8) [320,5,40,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17998 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17999 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 289, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 44 138 208 49 113 177 305), lower := (rows 321 7 44 138 208 32 64 128 256), losses := [] }

theorem u17999 : Upper (D 8) (R 8) [320,5,40,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17999 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u17999
end Delivery.IrregularNine14.P08
