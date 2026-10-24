import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0400
import IrregularNine14P06C0401
import IrregularNine14P06C0402

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b38280 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 138 100 266 84 53 85 149 277), lower := (rows 35 138 100 266 84 32 64 128 256), losses := [] }

theorem u38280 : Upper (D 6) (R 6) [34,136,96,258,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38280 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38281 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 100 268 19 117 85 213 341), lower := (rows 35 138 100 268 19 32 64 128 256), losses := [] }

theorem u38281 : Upper (D 6) (R 6) [34,136,96,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38281 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38282 : Route 9 := (fun mask => (mask,id))

def c38282 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38282 : Upper (D 6) (R 6) [34,136,96,260,5] 13 := by
  apply FastRouting.sound _ _ [34,136,96,260,5] 13 (by decide) (choices 1) [1,2,16,64] r38282 c38282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24050
  · exact u24051
  · exact u24052
  · exact u24053

def r38283 : Route 9 := (fun mask => (mask,id))

def c38283 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38283 : Upper (D 6) (R 6) [34,136,96,260,6] 13 := by
  apply FastRouting.sound _ _ [34,136,96,260,6] 13 (by decide) (choices 1) [1,16,64] r38283 c38283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24054
  · exact u24055
  · exact u24056

def r38284 : Route 9 := (fun mask => (mask,id))

def c38284 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38284 : Upper (D 6) (R 6) [34,136,96,260,65] 13 := by
  apply FastRouting.sound _ _ [34,136,96,260,65] 13 (by decide) (choices 1) [1,2,4,16] r38284 c38284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24057
  · exact u24058
  · exact u24059
  · exact u24060

def r38285 : Route 9 := (fun mask => (mask,id))

def c38285 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38285 : Upper (D 6) (R 6) [34,136,96,260,66] 13 := by
  apply FastRouting.sound _ _ [34,136,96,260,66] 13 (by decide) (choices 1) [1,4,16] r38285 c38285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24061
  · exact u24062
  · exact u24063

def b38286 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 138 100 268 84 51 83 147 275), lower := (rows 35 138 100 268 84 32 64 128 256), losses := [] }

theorem u38286 : Upper (D 6) (R 6) [34,136,96,260,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38286 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38287 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 100 280 19 101 69 197 325), lower := (rows 35 138 100 280 19 32 64 128 256), losses := [] }

theorem u38287 : Upper (D 6) (R 6) [34,136,96,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38288 : Route 9 := (fun mask => (mask,id))

def c38288 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38288 : Upper (D 6) (R 6) [34,136,96,272,5] 13 := by
  apply FastRouting.sound _ _ [34,136,96,272,5] 13 (by decide) (choices 1) [1,2,4,64] r38288 c38288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24064
  · exact u24065
  · exact u24066
  · exact u24067

def r38289 : Route 9 := (fun mask => (mask,id))

def c38289 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38289 : Upper (D 6) (R 6) [34,136,96,272,6] 13 := by
  apply FastRouting.sound _ _ [34,136,96,272,6] 13 (by decide) (choices 1) [1,4,64] r38289 c38289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24068
  · exact u24069
  · exact u24070

def r38290 : Route 9 := (fun mask => (mask,id))

def c38290 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38290 : Upper (D 6) (R 6) [34,136,96,272,65] 13 := by
  apply FastRouting.sound _ _ [34,136,96,272,65] 13 (by decide) (choices 1) [1,2,4] r38290 c38290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24071
  · exact u24072
  · exact u24073

def r38291 : Route 9 := (fun mask => (mask,id))

def c38291 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38291 : Upper (D 6) (R 6) [34,136,96,272,66] 13 := by
  apply FastRouting.sound _ _ [34,136,96,272,66] 13 (by decide) (choices 1) [1,4] r38291 c38291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24074
  · exact u24075

def b38292 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 138 100 280 84 39 71 135 263), lower := (rows 35 138 100 280 84 32 64 128 256), losses := [] }

theorem u38292 : Upper (D 6) (R 6) [34,136,96,272,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38293 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 100 328 19 53 85 149 277), lower := (rows 35 138 100 328 19 32 64 128 256), losses := [] }

theorem u38293 : Upper (D 6) (R 6) [34,136,96,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38293 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38294 : Route 9 := (fun mask => (mask,id))

def c38294 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38294 : Upper (D 6) (R 6) [34,136,96,320,5] 13 := by
  apply FastRouting.sound _ _ [34,136,96,320,5] 13 (by decide) (choices 1) [1,2,4,16] r38294 c38294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24076
  · exact u24077
  · exact u24078
  · exact u24079

def r38295 : Route 9 := (fun mask => (mask,id))

def c38295 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38295 : Upper (D 6) (R 6) [34,136,96,320,6] 13 := by
  apply FastRouting.sound _ _ [34,136,96,320,6] 13 (by decide) (choices 1) [1,4,16] r38295 c38295
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24080
  · exact u24081
  · exact u24082

def b38296 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 2, region := 16, targets := 32 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 35 138 261 14 21 112 112 240 368), lower := (rows 35 138 261 14 21 32 64 128 256), losses := [] }

theorem u38296 : Upper (D 6) (R 6) [34,136,257,6,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38296 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38297 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 138 261 14 49 116 84 212 340), lower := (rows 35 138 261 14 49 32 64 128 256), losses := [] }

theorem u38297 : Upper (D 6) (R 6) [34,136,257,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38297 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38298 : Route 9 := (fun mask => (mask,id))

def c38298 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38298 : Upper (D 6) (R 6) [34,136,257,6,36] 13 := by
  apply FastRouting.sound _ _ [34,136,257,6,36] 13 (by decide) (choices 1) [1,16,64] r38298 c38298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24083
  · exact u24084
  · exact u24085

def r38299 : Route 9 := (fun mask => (mask,id))

def c38299 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38299 : Upper (D 6) (R 6) [34,136,257,6,65] 13 := by
  apply FastRouting.sound _ _ [34,136,257,6,65] 13 (by decide) (choices 1) [4,16,64] r38299 c38299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24086
  · exact u24087
  · exact u24088

def r38300 : Route 9 := (fun mask => (mask,id))

def c38300 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38300 : Upper (D 6) (R 6) [34,136,257,6,68] 13 := by
  apply FastRouting.sound _ _ [34,136,257,6,68] 13 (by decide) (choices 1) [1,16,64] r38300 c38300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24089
  · exact u24090
  · exact u24091

def r38301 : Route 9 := (fun mask => (mask,id))

def c38301 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38301 : Upper (D 6) (R 6) [34,136,257,6,96] 13 := by
  apply FastRouting.sound _ _ [34,136,257,6,96] 13 (by decide) (choices 1) [1,4,16,64] r38301 c38301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24092
  · exact u24093
  · exact u24094
  · exact u24095

def r38302 : Route 9 := (fun mask => (mask,id))

def c38302 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38302 : Upper (D 6) (R 6) [34,136,257,17,6] 13 := by
  apply FastRouting.sound _ _ [34,136,257,17,6] 13 (by decide) (choices 1) [4,64] r38302 c38302
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24096
  · exact u24097

def b38303 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 138 261 25 50 100 68 196 324), lower := (rows 35 138 261 25 50 32 64 128 256), losses := [] }

theorem u38303 : Upper (D 6) (R 6) [34,136,257,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38304 : Route 9 := (fun mask => (mask,id))

def c38304 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38304 : Upper (D 6) (R 6) [34,136,257,17,36] 13 := by
  apply FastRouting.sound _ _ [34,136,257,17,36] 13 (by decide) (choices 1) [2,4,64] r38304 c38304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24098
  · exact u24099
  · exact u24100

def r38305 : Route 9 := (fun mask => (mask,id))

def c38305 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38305 : Upper (D 6) (R 6) [34,136,257,17,66] 13 := by
  apply FastRouting.sound _ _ [34,136,257,17,66] 13 (by decide) (choices 1) [4,64] r38305 c38305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24101
  · exact u24102

def r38306 : Route 9 := (fun mask => (mask,id))

def c38306 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38306 : Upper (D 6) (R 6) [34,136,257,17,68] 13 := by
  apply FastRouting.sound _ _ [34,136,257,17,68] 13 (by decide) (choices 1) [2,4,64] r38306 c38306
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24103
  · exact u24104
  · exact u24105

def r38307 : Route 9 := (fun mask => (mask,id))

def c38307 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38307 : Upper (D 6) (R 6) [34,136,257,17,96] 13 := by
  apply FastRouting.sound _ _ [34,136,257,17,96] 13 (by decide) (choices 1) [2,4,64] r38307 c38307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24106
  · exact u24107
  · exact u24108

def b38308 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 2, region := 16, targets := 32 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 35 138 261 26 21 100 100 228 356), lower := (rows 35 138 261 26 21 32 64 128 256), losses := [] }

theorem u38308 : Upper (D 6) (R 6) [34,136,257,18,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38308 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38309 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 138 261 26 49 100 68 196 324), lower := (rows 35 138 261 26 49 32 64 128 256), losses := [] }

theorem u38309 : Upper (D 6) (R 6) [34,136,257,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38309 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38310 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 324, targets := 32 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 35 138 261 26 52 101 69 197 325), lower := (rows 35 138 261 26 52 32 64 128 256), losses := [] }

theorem u38310 : Upper (D 6) (R 6) [34,136,257,18,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38310 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38311 : Route 9 := (fun mask => (mask,id))

def c38311 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38311 : Upper (D 6) (R 6) [34,136,257,18,65] 13 := by
  apply FastRouting.sound _ _ [34,136,257,18,65] 13 (by decide) (choices 1) [4,64] r38311 c38311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24109
  · exact u24110

def r38312 : Route 9 := (fun mask => (mask,id))

def c38312 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38312 : Upper (D 6) (R 6) [34,136,257,18,68] 13 := by
  apply FastRouting.sound _ _ [34,136,257,18,68] 13 (by decide) (choices 1) [1,4,64] r38312 c38312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24111
  · exact u24112
  · exact u24113

def b38313 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 324, targets := 32 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 35 138 261 26 112 101 69 197 325), lower := (rows 35 138 261 26 112 32 64 128 256), losses := [] }

theorem u38313 : Upper (D 6) (R 6) [34,136,257,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38313 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38314 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 261 28 19 100 100 228 356), lower := (rows 35 138 261 28 19 32 64 128 256), losses := [] }

theorem u38314 : Upper (D 6) (R 6) [34,136,257,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38314 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38315 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 138 261 28 21 98 98 226 354), lower := (rows 35 138 261 28 21 32 64 128 256), losses := [] }

theorem u38315 : Upper (D 6) (R 6) [34,136,257,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38316 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 138 261 28 22 97 97 225 353), lower := (rows 35 138 261 28 22 32 64 128 256), losses := [] }

theorem u38316 : Upper (D 6) (R 6) [34,136,257,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38317 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 138 261 28 49 102 70 198 326), lower := (rows 35 138 261 28 49 32 64 128 256), losses := [] }

theorem u38317 : Upper (D 6) (R 6) [34,136,257,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38317 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38318 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 138 261 28 50 101 69 197 325), lower := (rows 35 138 261 28 50 32 64 128 256), losses := [] }

theorem u38318 : Upper (D 6) (R 6) [34,136,257,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38319 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 138 261 28 52 99 67 195 323), lower := (rows 35 138 261 28 52 32 64 128 256), losses := [] }

theorem u38319 : Upper (D 6) (R 6) [34,136,257,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38319 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38320 : Route 9 := (fun mask => (mask,id))

def c38320 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38320 : Upper (D 6) (R 6) [34,136,257,20,65] 13 := by
  apply FastRouting.sound _ _ [34,136,257,20,65] 13 (by decide) (choices 1) [2,4,64] r38320 c38320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24114
  · exact u24115
  · exact u24116

def r38321 : Route 9 := (fun mask => (mask,id))

def c38321 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38321 : Upper (D 6) (R 6) [34,136,257,20,66] 13 := by
  apply FastRouting.sound _ _ [34,136,257,20,66] 13 (by decide) (choices 1) [1,4,64] r38321 c38321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24117
  · exact u24118
  · exact u24119

def b38322 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 138 261 28 84 99 99 227 355), lower := (rows 35 138 261 28 84 32 64 128 256), losses := [] }

theorem u38322 : Upper (D 6) (R 6) [34,136,257,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38322 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38323 : Route 9 := (fun mask => (mask,id))

def c38323 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38323 : Upper (D 6) (R 6) [34,136,257,20,96] 13 := by
  apply FastRouting.sound _ _ [34,136,257,20,96] 13 (by decide) (choices 1) [1,2,4,64] r38323 c38323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24120
  · exact u24121
  · exact u24122
  · exact u24123

def b38324 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 35 138 261 44 19 116 84 212 340), lower := (rows 35 138 261 44 19 32 64 128 256), losses := [] }

theorem u38324 : Upper (D 6) (R 6) [34,136,257,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38324 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38325 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 35 138 261 44 21 114 82 210 338), lower := (rows 35 138 261 44 21 32 64 128 256), losses := [] }

theorem u38325 : Upper (D 6) (R 6) [34,136,257,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38325 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38326 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 97, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 261 44 22 113 81 209 337), lower := (rows 35 138 261 44 22 32 64 128 256), losses := [] }

theorem u38326 : Upper (D 6) (R 6) [34,136,257,36,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38326 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38327 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 138 261 44 81 118 86 214 342), lower := (rows 35 138 261 44 81 32 64 128 256), losses := [{ target := 5, region := (rows 1 10 21 8 21 0 73 137 265), good := (rows 471 458 469 478 469 0 64 128 256) }] }

theorem u38327 : Upper (D 6) (R 6) [34,136,257,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38327 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38328 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 138 261 44 82 117 85 213 341), lower := (rows 35 138 261 44 82 32 64 128 256), losses := [{ target := 5, region := (rows 1 10 5 8 25 0 69 133 261), good := (rows 471 154 469 478 82 0 64 128 256) }] }

theorem u38328 : Upper (D 6) (R 6) [34,136,257,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38328 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38329 : Route 9 := (fun mask => (mask,id))

def c38329 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38329 : Upper (D 6) (R 6) [34,136,257,36,68] 13 := by
  apply FastRouting.sound _ _ [34,136,257,36,68] 13 (by decide) (choices 1) [1,2,16,64] r38329 c38329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24124
  · exact u24125
  · exact u24126
  · exact u24127

def b38330 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 138 261 56 19 100 68 196 324), lower := (rows 35 138 261 56 19 32 64 128 256), losses := [] }

theorem u38330 : Upper (D 6) (R 6) [34,136,257,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38330 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38331 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 35 138 261 56 21 102 70 198 326), lower := (rows 35 138 261 56 21 32 64 128 256), losses := [] }

theorem u38331 : Upper (D 6) (R 6) [34,136,257,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38331 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38332 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 0, region := 324, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 35 138 261 56 22 101 69 197 325), lower := (rows 35 138 261 56 22 32 64 128 256), losses := [] }

theorem u38332 : Upper (D 6) (R 6) [34,136,257,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38332 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38333 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 138 261 56 81 102 70 198 326), lower := (rows 35 138 261 56 81 32 64 128 256), losses := [{ target := 5, region := (rows 1 10 21 8 21 0 73 137 265), good := (rows 471 458 469 478 469 0 64 128 256) }] }

theorem u38333 : Upper (D 6) (R 6) [34,136,257,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38334 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 0, region := 324, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 35 138 261 56 82 101 69 197 325), lower := (rows 35 138 261 56 82 32 64 128 256), losses := [] }

theorem u38334 : Upper (D 6) (R 6) [34,136,257,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38334 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38335 : Route 9 := (fun mask => (mask,id))

def c38335 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38335 : Upper (D 6) (R 6) [34,136,257,48,68] 13 := by
  apply FastRouting.sound _ _ [34,136,257,48,68] 13 (by decide) (choices 1) [1,2,4,64] r38335 c38335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24128
  · exact u24129
  · exact u24130
  · exact u24131

def r38336 : Route 9 := (fun mask => (mask,id))

def c38336 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38336 : Upper (D 6) (R 6) [34,136,257,65,6] 13 := by
  apply FastRouting.sound _ _ [34,136,257,65,6] 13 (by decide) (choices 1) [4,16,64] r38336 c38336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24132
  · exact u24133
  · exact u24134

def b38337 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 138 261 73 50 116 84 212 340), lower := (rows 35 138 261 73 50 32 64 128 256), losses := [] }

theorem u38337 : Upper (D 6) (R 6) [34,136,257,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38337 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38338 : Route 9 := (fun mask => (mask,id))

def c38338 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38338 : Upper (D 6) (R 6) [34,136,257,65,36] 13 := by
  apply FastRouting.sound _ _ [34,136,257,65,36] 13 (by decide) (choices 1) [2,4,16,64] r38338 c38338
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24135
  · exact u24136
  · exact u24137
  · exact u24138

def r38339 : Route 9 := (fun mask => (mask,id))

def c38339 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38339 : Upper (D 6) (R 6) [34,136,257,65,66] 13 := by
  apply FastRouting.sound _ _ [34,136,257,65,66] 13 (by decide) (choices 1) [4,16] r38339 c38339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24139
  · exact u24140

#print axioms u38339
end Delivery.IrregularNine14.P06
