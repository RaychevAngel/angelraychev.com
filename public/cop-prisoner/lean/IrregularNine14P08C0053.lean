import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0006
import IrregularNine14P08C0007

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3180 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 140 296 49 33 208 208 464), lower := (rows 67 38 140 296 49 33 64 128 256), losses := [] }

theorem u3180 : Upper (D 8) (R 8) [66,36,136,288,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3180 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3181 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 67 38 140 296 49 48 193 193 449), lower := (rows 67 38 140 296 49 48 64 128 256), losses := [] }

theorem u3181 : Upper (D 8) (R 8) [66,36,136,288,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3181 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3182 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 140 296 49 96 209 145 401), lower := (rows 67 38 140 296 49 96 64 128 256), losses := [] }

theorem u3182 : Upper (D 8) (R 8) [66,36,136,288,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3182 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3183 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 81, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 296 49 160 81 209 337), lower := (rows 67 38 140 296 49 160 64 128 256), losses := [] }

theorem u3183 : Upper (D 8) (R 8) [66,36,136,288,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3183 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3184 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 67 38 140 296 112 33 209 145 401), lower := (rows 67 38 140 296 112 33 64 128 256), losses := [] }

theorem u3184 : Upper (D 8) (R 8) [66,36,136,288,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3184 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3185 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 38 140 296 112 48 193 129 385), lower := (rows 67 38 140 296 112 48 64 128 256), losses := [] }

theorem u3185 : Upper (D 8) (R 8) [66,36,136,288,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3185 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3186 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 81, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 296 112 160 81 145 273), lower := (rows 67 38 140 296 112 160 64 128 256), losses := [] }

theorem u3186 : Upper (D 8) (R 8) [66,36,136,288,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3186 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3187 : Route 9 := (fun mask => (mask,id))

def c3187 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3187 : Upper (D 8) (R 8) [66,36,136,288,160,1] 13 := by
  apply FastRouting.sound _ _ [66,36,136,288,160,1] 13 (by decide) (choices 1) [1,16] r3187 c3187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u411
  · exact u412

def b3188 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 67 38 140 296 176 48 65 193 321), lower := (rows 67 38 140 296 176 48 64 128 256), losses := [] }

theorem u3188 : Upper (D 8) (R 8) [66,36,136,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3188 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3189 : Route 9 := (fun mask => (mask,id))

def c3189 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3189 : Upper (D 8) (R 8) [66,36,136,288,160,64] 13 := by
  apply FastRouting.sound _ _ [66,36,136,288,160,64] 13 (by decide) (choices 1) [1,16] r3189 c3189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u413
  · exact u414

def r3190 : Route 9 := (fun mask => (mask,id))

def c3190 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3190 : Upper (D 8) (R 8) [66,36,136,288,192,1] 13 := by
  apply FastRouting.sound _ _ [66,36,136,288,192,1] 13 (by decide) (choices 1) [1,16,32] r3190 c3190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u415
  · exact u416
  · exact u417

def b3191 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 38 140 296 208 48 97 161 289), lower := (rows 67 38 140 296 208 48 64 128 256), losses := [] }

theorem u3191 : Upper (D 8) (R 8) [66,36,136,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3191 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3192 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 261 56 152 33 224 224 480), lower := (rows 67 38 261 56 152 33 64 128 256), losses := [] }

theorem u3192 : Upper (D 8) (R 8) [66,36,257,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3192 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3193 : PairBound 9 := { available := 161, camps := [], pairs := [(1,0)], upper := (rows 67 38 261 56 152 96 225 161 417), lower := (rows 67 38 261 56 152 96 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 97 64 128 256), good := (rows 98 38 294 56 152 96 96 128 256) }] }

theorem u3193 : Upper (D 8) (R 8) [66,36,257,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3193 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3194 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 261 56 152 160 97 225 353), lower := (rows 67 38 261 56 152 160 64 128 256), losses := [] }

theorem u3194 : Upper (D 8) (R 8) [66,36,257,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3194 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3195 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 261 56 208 33 232 168 424), lower := (rows 67 38 261 56 208 33 64 128 256), losses := [] }

theorem u3195 : Upper (D 8) (R 8) [66,36,257,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3195 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3196 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 38 261 56 208 40 225 161 417), lower := (rows 67 38 261 56 208 40 64 128 256), losses := [] }

theorem u3196 : Upper (D 8) (R 8) [66,36,257,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3196 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3197 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 261 56 208 160 105 169 297), lower := (rows 67 38 261 56 208 160 64 128 256), losses := [] }

theorem u3197 : Upper (D 8) (R 8) [66,36,257,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3197 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3198 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 261 88 176 33 232 168 424), lower := (rows 67 38 261 88 176 33 64 128 256), losses := [] }

theorem u3198 : Upper (D 8) (R 8) [66,36,257,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3198 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3199 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 38 261 88 176 40 225 161 417), lower := (rows 67 38 261 88 176 40 64 128 256), losses := [] }

theorem u3199 : Upper (D 8) (R 8) [66,36,257,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3199 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3200 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 261 88 176 160 105 169 297), lower := (rows 67 38 261 88 176 160 64 128 256), losses := [] }

theorem u3200 : Upper (D 8) (R 8) [66,36,257,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3200 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3201 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 261 104 152 33 240 176 432), lower := (rows 67 38 261 104 152 33 64 128 256), losses := [] }

theorem u3201 : Upper (D 8) (R 8) [66,36,257,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3201 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3202 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 38 261 104 152 48 225 161 417), lower := (rows 67 38 261 104 152 48 64 128 256), losses := [] }

theorem u3202 : Upper (D 8) (R 8) [66,36,257,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3202 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3203 : Route 9 := (fun mask => (mask,id))

def c3203 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3203 : Upper (D 8) (R 8) [66,36,257,96,136,128] 13 := by
  apply FastRouting.sound _ _ [66,36,257,96,136,128] 13 (by decide) (choices 1) [1,16,32] r3203 c3203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u418
  · exact u419
  · exact u420

def b3204 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 261 104 176 33 216 152 408), lower := (rows 67 38 261 104 176 33 64 128 256), losses := [] }

theorem u3204 : Upper (D 8) (R 8) [66,36,257,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3204 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3205 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 38 261 104 176 40 209 145 401), lower := (rows 67 38 261 104 176 40 64 128 256), losses := [] }

theorem u3205 : Upper (D 8) (R 8) [66,36,257,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3205 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3206 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 67 38 261 104 176 48 201 137 393), lower := (rows 67 38 261 104 176 48 64 128 256), losses := [] }

theorem u3206 : Upper (D 8) (R 8) [66,36,257,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3206 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3207 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 261 104 176 160 89 153 281), lower := (rows 67 38 261 104 176 160 64 128 256), losses := [] }

theorem u3207 : Upper (D 8) (R 8) [66,36,257,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3207 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3208 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 261 168 208 33 120 184 312), lower := (rows 67 38 261 168 208 33 64 128 256), losses := [] }

theorem u3208 : Upper (D 8) (R 8) [66,36,257,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3208 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3209 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 38 261 168 208 40 113 177 305), lower := (rows 67 38 261 168 208 40 64 128 256), losses := [] }

theorem u3209 : Upper (D 8) (R 8) [66,36,257,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3209 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3210 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 38 261 168 208 48 105 169 297), lower := (rows 67 38 261 168 208 48 64 128 256), losses := [] }

theorem u3210 : Upper (D 8) (R 8) [66,36,257,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3210 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3211 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 268 25 176 33 224 224 480), lower := (rows 67 38 268 25 176 33 64 128 256), losses := [] }

theorem u3211 : Upper (D 8) (R 8) [66,36,264,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3211 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3212 : Route 9 := (fun mask => (mask,id))

def c3212 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3212 : Upper (D 8) (R 8) [66,36,264,17,160,64] 13 := by
  apply FastRouting.sound _ _ [66,36,264,17,160,64] 13 (by decide) (choices 1) [1,32,128] r3212 c3212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u421
  · exact u422
  · exact u423

def b3213 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 268 25 176 160 97 225 353), lower := (rows 67 38 268 25 176 160 64 128 256), losses := [] }

theorem u3213 : Upper (D 8) (R 8) [66,36,264,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3213 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3214 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 268 41 112 33 208 144 400), lower := (rows 67 38 268 41 112 33 64 128 256), losses := [] }

theorem u3214 : Upper (D 8) (R 8) [66,36,264,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3214 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3215 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 38 268 41 112 48 193 129 385), lower := (rows 67 38 268 41 112 48 64 128 256), losses := [] }

theorem u3215 : Upper (D 8) (R 8) [66,36,264,33,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3215 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3216 : Route 9 := (fun mask => (mask,id))

def c3216 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3216 : Upper (D 8) (R 8) [66,36,264,33,96,128] 13 := by
  apply FastRouting.sound _ _ [66,36,264,33,96,128] 13 (by decide) (choices 1) [1,16,128] r3216 c3216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u424
  · exact u425
  · exact u426

def b3217 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 67 38 268 41 145 48 224 224 480), lower := (rows 67 38 268 41 145 48 64 128 256), losses := [] }

theorem u3217 : Upper (D 8) (R 8) [66,36,264,33,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3217 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3218 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 268 41 145 96 240 176 432), lower := (rows 67 38 268 41 145 96 64 128 256), losses := [] }

theorem u3218 : Upper (D 8) (R 8) [66,36,264,33,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3218 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3219 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 67 38 268 41 145 160 112 240 368), lower := (rows 67 38 268 41 145 160 64 128 256), losses := [] }

theorem u3219 : Upper (D 8) (R 8) [66,36,264,33,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3219 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3220 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 268 41 176 33 208 208 464), lower := (rows 67 38 268 41 176 33 64 128 256), losses := [] }

theorem u3220 : Upper (D 8) (R 8) [66,36,264,33,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3220 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3221 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 67 38 268 41 176 48 193 193 449), lower := (rows 67 38 268 41 176 48 64 128 256), losses := [] }

theorem u3221 : Upper (D 8) (R 8) [66,36,264,33,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3221 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3222 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 268 41 176 96 209 145 401), lower := (rows 67 38 268 41 176 96 64 128 256), losses := [] }

theorem u3222 : Upper (D 8) (R 8) [66,36,264,33,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3222 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3223 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 268 41 176 160 81 209 337), lower := (rows 67 38 268 41 176 160 64 128 256), losses := [] }

theorem u3223 : Upper (D 8) (R 8) [66,36,264,33,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3223 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3224 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 268 41 208 33 240 176 432), lower := (rows 67 38 268 41 208 33 64 128 256), losses := [] }

theorem u3224 : Upper (D 8) (R 8) [66,36,264,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3224 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3225 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 38 268 41 208 48 225 161 417), lower := (rows 67 38 268 41 208 48 64 128 256), losses := [] }

theorem u3225 : Upper (D 8) (R 8) [66,36,264,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3225 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3226 : Route 9 := (fun mask => (mask,id))

def c3226 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3226 : Upper (D 8) (R 8) [66,36,264,33,192,128] 13 := by
  apply FastRouting.sound _ _ [66,36,264,33,192,128] 13 (by decide) (choices 1) [1,16,32] r3226 c3226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u427
  · exact u428
  · exact u429

def b3227 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 454, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 268 56 145 33 224 224 480), lower := (rows 67 38 268 56 145 33 64 128 256), losses := [] }

theorem u3227 : Upper (D 8) (R 8) [66,36,264,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3227 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3228 : PairBound 9 := { available := 161, camps := [], pairs := [(3,0)], upper := (rows 67 38 268 56 145 96 225 161 417), lower := (rows 67 38 268 56 145 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 97 64 128 256), good := (rows 98 38 268 56 184 96 96 128 256) }] }

theorem u3228 : Upper (D 8) (R 8) [66,36,264,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3228 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3229 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 268 56 145 160 97 225 353), lower := (rows 67 38 268 56 145 160 64 128 256), losses := [] }

theorem u3229 : Upper (D 8) (R 8) [66,36,264,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3229 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3230 : PairBound 9 := { available := 161, camps := [], pairs := [(1,6)], upper := (rows 67 38 268 56 208 33 225 161 417), lower := (rows 67 38 268 56 208 33 64 128 256), losses := [{ target := 6, region := (rows 1 10 12 8 16 33 0 161 289), good := (rows 419 422 270 446 144 417 0 128 256) }] }

theorem u3230 : Upper (D 8) (R 8) [66,36,264,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3230 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3231 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 268 56 208 160 97 161 289), lower := (rows 67 38 268 56 208 160 64 128 256), losses := [] }

theorem u3231 : Upper (D 8) (R 8) [66,36,264,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3231 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3232 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 67 38 268 137 49 48 224 224 480), lower := (rows 67 38 268 137 49 48 64 128 256), losses := [] }

theorem u3232 : Upper (D 8) (R 8) [66,36,264,129,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3232 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3233 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 268 137 49 96 240 176 432), lower := (rows 67 38 268 137 49 96 64 128 256), losses := [] }

theorem u3233 : Upper (D 8) (R 8) [66,36,264,129,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3233 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3234 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 81, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 268 137 49 160 112 240 368), lower := (rows 67 38 268 137 49 160 64 128 256), losses := [] }

theorem u3234 : Upper (D 8) (R 8) [66,36,264,129,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3234 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3235 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 67 38 268 137 112 33 240 176 432), lower := (rows 67 38 268 137 112 33 64 128 256), losses := [] }

theorem u3235 : Upper (D 8) (R 8) [66,36,264,129,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3235 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3236 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 38 268 137 112 48 225 161 417), lower := (rows 67 38 268 137 112 48 64 128 256), losses := [] }

theorem u3236 : Upper (D 8) (R 8) [66,36,264,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3236 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3237 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 81, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 268 137 112 160 113 177 305), lower := (rows 67 38 268 137 112 160 64 128 256), losses := [] }

theorem u3237 : Upper (D 8) (R 8) [66,36,264,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3237 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3238 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 268 137 176 33 112 240 368), lower := (rows 67 38 268 137 176 33 64 128 256), losses := [] }

theorem u3238 : Upper (D 8) (R 8) [66,36,264,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3238 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3239 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 38 268 137 176 48 97 225 353), lower := (rows 67 38 268 137 176 48 64 128 256), losses := [] }

theorem u3239 : Upper (D 8) (R 8) [66,36,264,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3239 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u3239
end Delivery.IrregularNine14.P08
