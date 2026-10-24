import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0085
import IrregularNine14P09C0086

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r7800 : Route 9 := (fun mask => (mask,id))

def c7800 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7800 : Upper (D 9) (R 9) [34,192,24,96,257] 13 := by
  apply FastRouting.sound _ _ [34,192,24,96,257] 13 (by decide) (choices 1) [1,4,128,256] r7800 c7800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5111
  · exact u5112
  · exact u5113
  · exact u5114

def r7801 : Route 9 := (fun mask => (mask,id))

def c7801 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7801 : Upper (D 9) (R 9) [34,192,24,96,260] 13 := by
  apply FastRouting.sound _ _ [34,192,24,96,260] 13 (by decide) (choices 1) [1,128,256] r7801 c7801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5115
  · exact u5116
  · exact u5117

def r7802 : Route 9 := (fun mask => (mask,id))

def c7802 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7802 : Upper (D 9) (R 9) [34,192,24,96,384] 13 := by
  apply FastRouting.sound _ _ [34,192,24,96,384] 13 (by decide) (choices 1) [1,4,256] r7802 c7802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5118
  · exact u5119
  · exact u5120

def b7803 : PairBound 9 := { available := 293, camps := [{ cop := 1, region := 8, targets := 289 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5),(3,8)], upper := (rows 35 194 28 200 273 293 357 421 293), lower := (rows 35 194 28 200 273 32 64 128 256), losses := [] }

theorem u7803 : Upper (D 9) (R 9) [34,192,24,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7803 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7804 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 8, targets := 289 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5),(3,8)], upper := (rows 35 194 28 200 276 289 353 417 289), lower := (rows 35 194 28 200 276 32 64 128 256), losses := [] }

theorem u7804 : Upper (D 9) (R 9) [34,192,24,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7804 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7805 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 8, targets := 289 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5),(3,8)], upper := (rows 35 194 28 200 304 293 325 389 261), lower := (rows 35 194 28 200 304 32 64 128 256), losses := [] }

theorem u7805 : Upper (D 9) (R 9) [34,192,24,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7805 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7806 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 20, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(4,5),(4,6)], upper := (rows 35 194 28 265 273 228 228 228 484), lower := (rows 35 194 28 265 273 32 64 128 256), losses := [] }

theorem u7806 : Upper (D 9) (R 9) [34,192,24,257,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7806 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7807 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 20, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7),(4,0)], upper := (rows 35 194 28 265 276 225 225 225 481), lower := (rows 35 194 28 265 276 32 64 128 256), losses := [] }

theorem u7807 : Upper (D 9) (R 9) [34,192,24,257,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7807 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7808 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7808 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7808 : Upper (D 9) (R 9) [34,192,24,257,288] 13 := by
  apply FastRouting.sound _ _ [34,192,24,257,288] 13 (by decide) (choices 1) [1,4,64] r7808 c7808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5121
  · exact u5122
  · exact u5123

def r7809 : Route 9 := (fun mask => (mask,id))

def c7809 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7809 : Upper (D 9) (R 9) [34,192,24,257,320] 13 := by
  apply FastRouting.sound _ _ [34,192,24,257,320] 13 (by decide) (choices 1) [1,4,128] r7809 c7809
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5124
  · exact u5125
  · exact u5126

def b7810 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 12, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7),(3,0)], upper := (rows 35 194 28 268 304 225 193 193 449), lower := (rows 35 194 28 268 304 32 64 128 256), losses := [] }

theorem u7810 : Upper (D 9) (R 9) [34,192,24,260,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7810 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7811 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 12, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7),(3,0)], upper := (rows 35 194 28 268 336 161 225 161 417), lower := (rows 35 194 28 268 336 32 64 128 256), losses := [] }

theorem u7811 : Upper (D 9) (R 9) [34,192,24,260,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7811 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7812 : Route 9 := (fun mask => (mask,id))

def c7812 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7812 : Upper (D 9) (R 9) [34,192,24,288,320] 13 := by
  apply FastRouting.sound _ _ [34,192,24,288,320] 13 (by decide) (choices 1) [1,4,128] r7812 c7812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5127
  · exact u5128
  · exact u5129

def r7813 : Route 9 := (fun mask => (mask,id))

def c7813 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7813 : Upper (D 9) (R 9) [34,192,24,320,384] 13 := by
  apply FastRouting.sound _ _ [34,192,24,320,384] 13 (by decide) (choices 1) [1,4] r7813 c7813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5130
  · exact u5131

def b7814 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 194 37 73 148 312 344 408 280), lower := (rows 35 194 37 73 148 32 64 128 256), losses := [] }

theorem u7814 : Upper (D 9) (R 9) [34,192,33,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7814 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7815 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 194 37 73 152 308 340 404 276), lower := (rows 35 194 37 73 152 32 64 128 256), losses := [] }

theorem u7815 : Upper (D 9) (R 9) [34,192,33,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7815 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7816 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 194 37 73 276 440 472 408 408), lower := (rows 35 194 37 73 276 32 64 128 256), losses := [] }

theorem u7816 : Upper (D 9) (R 9) [34,192,33,65,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7816 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7817 : PairBound 9 := { available := 404, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 194 37 73 280 436 468 404 404), lower := (rows 35 194 37 73 280 32 64 128 256), losses := [] }

theorem u7817 : Upper (D 9) (R 9) [34,192,33,65,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7817 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7818 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 194 37 73 400 316 348 412 284), lower := (rows 35 194 37 73 400 32 64 128 256), losses := [] }

theorem u7818 : Upper (D 9) (R 9) [34,192,33,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7818 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7819 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 194 37 76 152 305 337 401 273), lower := (rows 35 194 37 76 152 32 64 128 256), losses := [] }

theorem u7819 : Upper (D 9) (R 9) [34,192,33,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7819 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7820 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 194 37 76 273 440 472 408 408), lower := (rows 35 194 37 76 273 32 64 128 256), losses := [] }

theorem u7820 : Upper (D 9) (R 9) [34,192,33,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7820 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7821 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 194 37 76 280 433 465 401 401), lower := (rows 35 194 37 76 280 32 64 128 256), losses := [] }

theorem u7821 : Upper (D 9) (R 9) [34,192,33,68,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7821 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7822 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 194 37 76 400 313 345 409 281), lower := (rows 35 194 37 76 400 32 64 128 256), losses := [] }

theorem u7822 : Upper (D 9) (R 9) [34,192,33,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7822 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7823 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 194 37 88 273 428 460 396 396), lower := (rows 35 194 37 88 273 32 64 128 256), losses := [] }

theorem u7823 : Upper (D 9) (R 9) [34,192,33,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7823 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7824 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 194 37 88 276 425 457 393 393), lower := (rows 35 194 37 88 276 32 64 128 256), losses := [] }

theorem u7824 : Upper (D 9) (R 9) [34,192,33,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7824 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7825 : PairBound 9 := { available := 389, camps := [{ cop := 2, region := 474, targets := 32 },{ cop := 0, region := 4, targets := 384 }], pairs := [(1,5),(2,7),(2,8),(3,5),(4,5)], upper := (rows 35 194 37 88 280 421 453 389 389), lower := (rows 35 194 37 88 280 32 64 128 256), losses := [] }

theorem u7825 : Upper (D 9) (R 9) [34,192,33,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7825 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7826 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 194 37 88 400 301 333 397 269), lower := (rows 35 194 37 88 400 32 64 128 256), losses := [] }

theorem u7826 : Upper (D 9) (R 9) [34,192,33,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7826 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7827 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 194 37 265 276 248 216 216 472), lower := (rows 35 194 37 265 276 32 64 128 256), losses := [] }

theorem u7827 : Upper (D 9) (R 9) [34,192,33,257,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7827 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7828 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 194 37 265 336 188 220 156 412), lower := (rows 35 194 37 265 336 32 64 128 256), losses := [] }

theorem u7828 : Upper (D 9) (R 9) [34,192,33,257,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7828 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7829 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 194 37 268 336 185 217 153 409), lower := (rows 35 194 37 268 336 32 64 128 256), losses := [] }

theorem u7829 : Upper (D 9) (R 9) [34,192,33,260,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7829 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7830 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 194 37 328 400 61 93 157 285), lower := (rows 35 194 37 328 400 32 64 128 256), losses := [] }

theorem u7830 : Upper (D 9) (R 9) [34,192,33,320,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7830 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7831 : Route 9 := (fun mask => (mask,id))

def c7831 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7831 : Upper (D 9) (R 9) [34,192,40,65,129] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65,129] 13 (by decide) (choices 1) [4,16,256] r7831 c7831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5132
  · exact u5133
  · exact u5134

def r7832 : Route 9 := (fun mask => (mask,id))

def c7832 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7832 : Upper (D 9) (R 9) [34,192,40,65,132] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65,132] 13 (by decide) (choices 1) [1,16,256] r7832 c7832
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5135
  · exact u5136
  · exact u5137

def r7833 : Route 9 := (fun mask => (mask,id))

def c7833 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7833 : Upper (D 9) (R 9) [34,192,40,65,257] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65,257] 13 (by decide) (choices 1) [4,16,128,256] r7833 c7833
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5138
  · exact u5139
  · exact u5140
  · exact u5141

def r7834 : Route 9 := (fun mask => (mask,id))

def c7834 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7834 : Upper (D 9) (R 9) [34,192,40,65,260] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65,260] 13 (by decide) (choices 1) [1,16,128,256] r7834 c7834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5142
  · exact u5143
  · exact u5144
  · exact u5145

def r7835 : Route 9 := (fun mask => (mask,id))

def c7835 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7835 : Upper (D 9) (R 9) [34,192,40,65,384] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65,384] 13 (by decide) (choices 1) [1,4,16,256] r7835 c7835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5146
  · exact u5147
  · exact u5148
  · exact u5149

def b7836 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 305, targets := 64 },{ cop := 4, region := 364, targets := 128 }], pairs := [(0,6),(1,5),(2,7),(4,5),(4,6)], upper := (rows 35 194 44 76 145 305 337 401 273), lower := (rows 35 194 44 76 145 32 64 128 256), losses := [] }

theorem u7836 : Upper (D 9) (R 9) [34,192,40,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7836 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7837 : Route 9 := (fun mask => (mask,id))

def c7837 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7837 : Upper (D 9) (R 9) [34,192,40,68,257] 13 := by
  apply FastRouting.sound _ _ [34,192,40,68,257] 13 (by decide) (choices 1) [1,16,128,256] r7837 c7837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5150
  · exact u5151
  · exact u5152
  · exact u5153

def r7838 : Route 9 := (fun mask => (mask,id))

def c7838 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7838 : Upper (D 9) (R 9) [34,192,40,68,384] 13 := by
  apply FastRouting.sound _ _ [34,192,40,68,384] 13 (by decide) (choices 1) [1,16,256] r7838 c7838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5154
  · exact u5155
  · exact u5156

def r7839 : Route 9 := (fun mask => (mask,id))

def c7839 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7839 : Upper (D 9) (R 9) [34,192,40,80,129] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,129] 13 (by decide) (choices 1) [1,4,256] r7839 c7839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5157
  · exact u5158
  · exact u5159

def r7840 : Route 9 := (fun mask => (mask,id))

def c7840 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7840 : Upper (D 9) (R 9) [34,192,40,80,132] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,132] 13 (by decide) (choices 1) [1,256] r7840 c7840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5160
  · exact u5161

def r7841 : Route 9 := (fun mask => (mask,id))

def c7841 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7841 : Upper (D 9) (R 9) [34,192,40,80,257] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,257] 13 (by decide) (choices 1) [1,4,128,256] r7841 c7841
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5162
  · exact u5163
  · exact u5164
  · exact u5165

def r7842 : Route 9 := (fun mask => (mask,id))

def c7842 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7842 : Upper (D 9) (R 9) [34,192,40,80,260] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,260] 13 (by decide) (choices 1) [1,128,256] r7842 c7842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5166
  · exact u5167
  · exact u5168

def r7843 : Route 9 := (fun mask => (mask,id))

def c7843 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7843 : Upper (D 9) (R 9) [34,192,40,80,384] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,384] 13 (by decide) (choices 1) [1,4,256] r7843 c7843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5169
  · exact u5170
  · exact u5171

def b7844 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 8, targets := 289 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5),(3,8)], upper := (rows 35 194 44 200 273 309 341 405 277), lower := (rows 35 194 44 200 273 32 64 128 256), losses := [] }

theorem u7844 : Upper (D 9) (R 9) [34,192,40,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7844 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7845 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 8, targets := 289 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5),(3,8)], upper := (rows 35 194 44 200 276 305 337 401 273), lower := (rows 35 194 44 200 276 32 64 128 256), losses := [] }

theorem u7845 : Upper (D 9) (R 9) [34,192,40,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7845 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7846 : Route 9 := (fun mask => (mask,id))

def c7846 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7846 : Upper (D 9) (R 9) [34,192,40,257,65] 13 := by
  apply FastRouting.sound _ _ [34,192,40,257,65] 13 (by decide) (choices 1) [4,16,128,256] r7846 c7846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5172
  · exact u5173
  · exact u5174
  · exact u5175

def r7847 : Route 9 := (fun mask => (mask,id))

def c7847 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7847 : Upper (D 9) (R 9) [34,192,40,257,68] 13 := by
  apply FastRouting.sound _ _ [34,192,40,257,68] 13 (by decide) (choices 1) [1,16,128,256] r7847 c7847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5176
  · exact u5177
  · exact u5178
  · exact u5179

def b7848 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 16, targets := 289 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5),(4,8)], upper := (rows 35 194 44 265 208 309 341 405 277), lower := (rows 35 194 44 265 208 32 64 128 256), losses := [] }

theorem u7848 : Upper (D 9) (R 9) [34,192,40,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7848 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7849 : PairBound 9 := { available := 212, camps := [{ cop := 3, region := 16, targets := 224 },{ cop := 4, region := 8, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6),(4,7)], upper := (rows 35 194 44 265 273 244 212 212 468), lower := (rows 35 194 44 265 273 32 64 128 256), losses := [] }

theorem u7849 : Upper (D 9) (R 9) [34,192,40,257,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7849 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7850 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7850 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7850 : Upper (D 9) (R 9) [34,192,40,257,260] 13 := by
  apply FastRouting.sound _ _ [34,192,40,257,260] 13 (by decide) (choices 1) [1,16,64] r7850 c7850
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5180
  · exact u5181
  · exact u5182

def r7851 : Route 9 := (fun mask => (mask,id))

def c7851 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7851 : Upper (D 9) (R 9) [34,192,40,257,320] 13 := by
  apply FastRouting.sound _ _ [34,192,40,257,320] 13 (by decide) (choices 1) [1,4,16,128] r7851 c7851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5183
  · exact u5184
  · exact u5185
  · exact u5186

def r7852 : Route 9 := (fun mask => (mask,id))

def c7852 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7852 : Upper (D 9) (R 9) [34,192,40,260,65] 13 := by
  apply FastRouting.sound _ _ [34,192,40,260,65] 13 (by decide) (choices 1) [1,16,128,256] r7852 c7852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5187
  · exact u5188
  · exact u5189
  · exact u5190

def b7853 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 16, targets := 289 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5),(4,8)], upper := (rows 35 194 44 268 208 305 337 401 273), lower := (rows 35 194 44 268 208 32 64 128 256), losses := [] }

theorem u7853 : Upper (D 9) (R 9) [34,192,40,260,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7853 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7854 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7854 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7854 : Upper (D 9) (R 9) [34,192,40,260,257] 13 := by
  apply FastRouting.sound _ _ [34,192,40,260,257] 13 (by decide) (choices 1) [1,16,64] r7854 c7854
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5191
  · exact u5192
  · exact u5193

def r7855 : Route 9 := (fun mask => (mask,id))

def c7855 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7855 : Upper (D 9) (R 9) [34,192,40,260,320] 13 := by
  apply FastRouting.sound _ _ [34,192,40,260,320] 13 (by decide) (choices 1) [1,16,128] r7855 c7855
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5194
  · exact u5195
  · exact u5196

def r7856 : Route 9 := (fun mask => (mask,id))

def c7856 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7856 : Upper (D 9) (R 9) [34,192,40,272,65] 13 := by
  apply FastRouting.sound _ _ [34,192,40,272,65] 13 (by decide) (choices 1) [1,4,128,256] r7856 c7856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5197
  · exact u5198
  · exact u5199
  · exact u5200

def r7857 : Route 9 := (fun mask => (mask,id))

def c7857 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7857 : Upper (D 9) (R 9) [34,192,40,272,68] 13 := by
  apply FastRouting.sound _ _ [34,192,40,272,68] 13 (by decide) (choices 1) [1,128,256] r7857 c7857
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5201
  · exact u5202
  · exact u5203

def b7858 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 289 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5),(4,8)], upper := (rows 35 194 44 280 208 293 325 389 261), lower := (rows 35 194 44 280 208 32 64 128 256), losses := [] }

theorem u7858 : Upper (D 9) (R 9) [34,192,40,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7858 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7859 : PairBound 9 := { available := 197, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 194 44 280 273 229 197 197 453), lower := (rows 35 194 44 280 273 32 64 128 256), losses := [] }

theorem u7859 : Upper (D 9) (R 9) [34,192,40,272,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7859 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u7859
end Delivery.IrregularNine14.P09
