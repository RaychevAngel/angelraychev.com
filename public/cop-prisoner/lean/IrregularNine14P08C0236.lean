import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0079
import IrregularNine14P08C0080

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14160 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 134 328 145 49 113 177 305), lower := (rows 97 14 134 328 145 32 64 128 256), losses := [] }

theorem u14160 : Upper (D 8) (R 8) [96,12,130,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14160 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14161 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 134 328 176 49 113 177 305), lower := (rows 97 14 134 328 176 32 64 128 256), losses := [] }

theorem u14161 : Upper (D 8) (R 8) [96,12,130,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14161 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14162 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 22, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 148 168 50 353 321 449 321), lower := (rows 97 14 148 168 50 32 64 128 256), losses := [] }

theorem u14162 : Upper (D 8) (R 8) [96,12,144,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14162 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14163 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 168 82 289 353 417 289), lower := (rows 97 14 148 168 82 32 64 128 256), losses := [] }

theorem u14163 : Upper (D 8) (R 8) [96,12,144,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14163 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14164 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 168 273 99 99 227 355), lower := (rows 97 14 148 168 273 32 64 128 256), losses := [] }

theorem u14164 : Upper (D 8) (R 8) [96,12,144,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14164 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14165 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 168 274 97 97 225 353), lower := (rows 97 14 148 168 274 32 64 128 256), losses := [] }

theorem u14165 : Upper (D 8) (R 8) [96,12,144,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14165 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14166 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 168 304 99 67 195 323), lower := (rows 97 14 148 168 304 32 64 128 256), losses := [] }

theorem u14166 : Upper (D 8) (R 8) [96,12,144,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14166 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14167 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 168 336 35 99 163 291), lower := (rows 97 14 148 168 336 32 64 128 256), losses := [] }

theorem u14167 : Upper (D 8) (R 8) [96,12,144,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14167 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14168 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 200 50 289 353 417 289), lower := (rows 97 14 148 200 50 32 64 128 256), losses := [] }

theorem u14168 : Upper (D 8) (R 8) [96,12,144,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14168 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14169 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 200 273 35 99 163 291), lower := (rows 97 14 148 200 273 32 64 128 256), losses := [] }

theorem u14169 : Upper (D 8) (R 8) [96,12,144,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14169 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14170 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 200 274 33 97 161 289), lower := (rows 97 14 148 200 274 32 64 128 256), losses := [] }

theorem u14170 : Upper (D 8) (R 8) [96,12,144,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14170 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14171 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 200 304 35 99 163 291), lower := (rows 97 14 148 200 304 32 64 128 256), losses := [] }

theorem u14171 : Upper (D 8) (R 8) [96,12,144,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14171 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14172 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 148 265 49 226 226 226 482), lower := (rows 97 14 148 265 49 32 64 128 256), losses := [] }

theorem u14172 : Upper (D 8) (R 8) [96,12,144,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14172 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14173 : Route 9 := (fun mask => (mask,id))

def c14173 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14173 : Upper (D 8) (R 8) [96,12,144,257,34] 13 := by
  apply FastRouting.sound _ _ [96,12,144,257,34] 13 (by decide) (choices 1) [1,64,128] r14173 c14173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4793
  · exact u4794
  · exact u4795

def b14174 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 148 265 81 162 226 162 418), lower := (rows 97 14 148 265 81 32 64 128 256), losses := [] }

theorem u14174 : Upper (D 8) (R 8) [96,12,144,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14174 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14175 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 148 265 82 161 225 161 417), lower := (rows 97 14 148 265 82 32 64 128 256), losses := [] }

theorem u14175 : Upper (D 8) (R 8) [96,12,144,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14175 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14176 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 148 265 112 163 227 163 419), lower := (rows 97 14 148 265 112 32 64 128 256), losses := [] }

theorem u14176 : Upper (D 8) (R 8) [96,12,144,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14176 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14177 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 265 145 98 98 226 354), lower := (rows 97 14 148 265 145 32 64 128 256), losses := [] }

theorem u14177 : Upper (D 8) (R 8) [96,12,144,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14177 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14178 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 265 146 97 97 225 353), lower := (rows 97 14 148 265 146 32 64 128 256), losses := [] }

theorem u14178 : Upper (D 8) (R 8) [96,12,144,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14178 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14179 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 265 176 99 99 227 355), lower := (rows 97 14 148 265 176 32 64 128 256), losses := [] }

theorem u14179 : Upper (D 8) (R 8) [96,12,144,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14179 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14180 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 265 208 35 99 163 291), lower := (rows 97 14 148 265 208 32 64 128 256), losses := [] }

theorem u14180 : Upper (D 8) (R 8) [96,12,144,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14180 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14181 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 148 266 49 225 225 225 481), lower := (rows 97 14 148 266 49 32 64 128 256), losses := [] }

theorem u14181 : Upper (D 8) (R 8) [96,12,144,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14181 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14182 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 148 266 81 161 225 161 417), lower := (rows 97 14 148 266 81 32 64 128 256), losses := [] }

theorem u14182 : Upper (D 8) (R 8) [96,12,144,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14182 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14183 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 148 266 112 161 225 161 417), lower := (rows 97 14 148 266 112 32 64 128 256), losses := [] }

theorem u14183 : Upper (D 8) (R 8) [96,12,144,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14183 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14184 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 266 145 97 97 225 353), lower := (rows 97 14 148 266 145 32 64 128 256), losses := [] }

theorem u14184 : Upper (D 8) (R 8) [96,12,144,258,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14184 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14185 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 266 176 97 97 225 353), lower := (rows 97 14 148 266 176 32 64 128 256), losses := [] }

theorem u14185 : Upper (D 8) (R 8) [96,12,144,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14185 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14186 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 266 208 33 97 161 289), lower := (rows 97 14 148 266 208 32 64 128 256), losses := [] }

theorem u14186 : Upper (D 8) (R 8) [96,12,144,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14186 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14187 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 148 296 49 227 195 195 451), lower := (rows 97 14 148 296 49 32 64 128 256), losses := [] }

theorem u14187 : Upper (D 8) (R 8) [96,12,144,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14187 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14188 : Route 9 := (fun mask => (mask,id))

def c14188 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14188 : Upper (D 8) (R 8) [96,12,144,288,34] 13 := by
  apply FastRouting.sound _ _ [96,12,144,288,34] 13 (by decide) (choices 1) [1,64,128] r14188 c14188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4796
  · exact u4797
  · exact u4798

def b14189 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 148 296 81 163 227 163 419), lower := (rows 97 14 148 296 81 32 64 128 256), losses := [] }

theorem u14189 : Upper (D 8) (R 8) [96,12,144,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14189 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14190 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 148 296 82 161 225 161 417), lower := (rows 97 14 148 296 82 32 64 128 256), losses := [] }

theorem u14190 : Upper (D 8) (R 8) [96,12,144,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14190 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14191 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 148 296 112 163 195 131 387), lower := (rows 97 14 148 296 112 32 64 128 256), losses := [] }

theorem u14191 : Upper (D 8) (R 8) [96,12,144,288,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14191 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14192 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 296 145 99 99 227 355), lower := (rows 97 14 148 296 145 32 64 128 256), losses := [] }

theorem u14192 : Upper (D 8) (R 8) [96,12,144,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14192 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14193 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 296 146 97 97 225 353), lower := (rows 97 14 148 296 146 32 64 128 256), losses := [] }

theorem u14193 : Upper (D 8) (R 8) [96,12,144,288,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14193 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14194 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 296 176 99 67 195 323), lower := (rows 97 14 148 296 176 32 64 128 256), losses := [] }

theorem u14194 : Upper (D 8) (R 8) [96,12,144,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14194 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14195 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 296 208 35 99 163 291), lower := (rows 97 14 148 296 208 32 64 128 256), losses := [] }

theorem u14195 : Upper (D 8) (R 8) [96,12,144,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14195 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14196 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 148 328 49 163 227 163 419), lower := (rows 97 14 148 328 49 32 64 128 256), losses := [] }

theorem u14196 : Upper (D 8) (R 8) [96,12,144,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14196 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14197 : Route 9 := (fun mask => (mask,id))

def c14197 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14197 : Upper (D 8) (R 8) [96,12,144,320,34] 13 := by
  apply FastRouting.sound _ _ [96,12,144,320,34] 13 (by decide) (choices 1) [1,128] r14197 c14197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4799
  · exact u4800

def b14198 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 328 145 35 99 163 291), lower := (rows 97 14 148 328 145 32 64 128 256), losses := [] }

theorem u14198 : Upper (D 8) (R 8) [96,12,144,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14198 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14199 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 328 146 33 97 161 289), lower := (rows 97 14 148 328 146 32 64 128 256), losses := [] }

theorem u14199 : Upper (D 8) (R 8) [96,12,144,320,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14199 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14200 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 328 176 35 99 163 291), lower := (rows 97 14 148 328 176 32 64 128 256), losses := [] }

theorem u14200 : Upper (D 8) (R 8) [96,12,144,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14200 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14201 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 392 50 97 97 225 353), lower := (rows 97 14 148 392 50 32 64 128 256), losses := [] }

theorem u14201 : Upper (D 8) (R 8) [96,12,144,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14201 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14202 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 392 82 33 97 161 289), lower := (rows 97 14 148 392 82 32 64 128 256), losses := [] }

theorem u14202 : Upper (D 8) (R 8) [96,12,144,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14202 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14203 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 164 168 82 305 337 401 273), lower := (rows 97 14 164 168 82 32 64 128 256), losses := [] }

theorem u14203 : Upper (D 8) (R 8) [96,12,160,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14203 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14204 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 164 168 273 115 83 211 339), lower := (rows 97 14 164 168 273 32 64 128 256), losses := [] }

theorem u14204 : Upper (D 8) (R 8) [96,12,160,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14204 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14205 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 164 168 274 113 81 209 337), lower := (rows 97 14 164 168 274 32 64 128 256), losses := [] }

theorem u14205 : Upper (D 8) (R 8) [96,12,160,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14205 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14206 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 164 168 336 51 83 147 275), lower := (rows 97 14 164 168 336 32 64 128 256), losses := [] }

theorem u14206 : Upper (D 8) (R 8) [96,12,160,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14206 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14207 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 200 50 305 337 401 273), lower := (rows 97 14 164 200 50 32 64 128 256), losses := [] }

theorem u14207 : Upper (D 8) (R 8) [96,12,160,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14207 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14208 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 200 273 51 115 179 307), lower := (rows 97 14 164 200 273 32 64 128 256), losses := [] }

theorem u14208 : Upper (D 8) (R 8) [96,12,160,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14208 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14209 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 200 274 49 113 177 305), lower := (rows 97 14 164 200 274 32 64 128 256), losses := [] }

theorem u14209 : Upper (D 8) (R 8) [96,12,160,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14209 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14210 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 200 304 51 83 147 275), lower := (rows 97 14 164 200 304 32 64 128 256), losses := [] }

theorem u14210 : Upper (D 8) (R 8) [96,12,160,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14210 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14211 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 164 265 49 242 210 210 466), lower := (rows 97 14 164 265 49 32 64 128 256), losses := [] }

theorem u14211 : Upper (D 8) (R 8) [96,12,160,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14211 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14212 : Route 9 := (fun mask => (mask,id))

def c14212 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u14212 : Upper (D 8) (R 8) [96,12,160,257,34] 13 := by
  apply FastRouting.sound _ _ [96,12,160,257,34] 13 (by decide) (choices 1) [1,16,64,128] r14212 c14212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4801
  · exact u4802
  · exact u4803
  · exact u4804

def b14213 : PairBound 9 := { available := 178, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 164 265 81 178 242 178 434), lower := (rows 97 14 164 265 81 32 64 128 256), losses := [] }

theorem u14213 : Upper (D 8) (R 8) [96,12,160,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14213 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14214 : Route 9 := (fun mask => (mask,id))

def c14214 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14214 : Upper (D 8) (R 8) [96,12,160,257,66] 13 := by
  apply FastRouting.sound _ _ [96,12,160,257,66] 13 (by decide) (choices 1) [1,16,128] r14214 c14214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4805
  · exact u4806
  · exact u4807

def b14215 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 164 265 112 179 211 147 403), lower := (rows 97 14 164 265 112 32 64 128 256), losses := [] }

theorem u14215 : Upper (D 8) (R 8) [96,12,160,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14215 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14216 : Route 9 := (fun mask => (mask,id))

def c14216 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14216 : Upper (D 8) (R 8) [96,12,160,257,129] 13 := by
  apply FastRouting.sound _ _ [96,12,160,257,129] 13 (by decide) (choices 1) [2,16,64] r14216 c14216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4808
  · exact u4809
  · exact u4810

def b14217 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 265 146 113 113 241 369), lower := (rows 97 14 164 265 146 32 64 128 256), losses := [] }

theorem u14217 : Upper (D 8) (R 8) [96,12,160,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14217 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14218 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 164 265 176 115 83 211 339), lower := (rows 97 14 164 265 176 32 64 128 256), losses := [] }

theorem u14218 : Upper (D 8) (R 8) [96,12,160,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14218 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14219 : Route 9 := (fun mask => (mask,id))

def c14219 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14219 : Upper (D 8) (R 8) [96,12,160,257,192] 13 := by
  apply FastRouting.sound _ _ [96,12,160,257,192] 13 (by decide) (choices 1) [1,2,16] r14219 c14219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4811
  · exact u4812
  · exact u4813

#print axioms u14219
end Delivery.IrregularNine14.P08
