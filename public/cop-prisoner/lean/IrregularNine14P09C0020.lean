import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0000

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1200 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 83, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 35 67 133 296 336 36 72 144 400), lower := (rows 35 67 133 296 336 36 72 128 256), losses := [] }

theorem u1200 : Upper (D 9) (R 9) [34,65,129,288,320,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1200 [(5,2),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1201 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 67 133 296 336 36 80 136 392), lower := (rows 35 67 133 296 336 36 80 128 256), losses := [] }

theorem u1201 : Upper (D 9) (R 9) [34,65,129,288,320,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1201 [(5,2),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1202 : PairBound 9 := { available := 24, camps := [{ cop := 6, region := 39, targets := 256 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 67 133 296 336 36 192 152 280), lower := (rows 35 67 133 296 336 36 192 128 256), losses := [] }

theorem u1202 : Upper (D 9) (R 9) [34,65,129,288,320,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1202 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1203 : PairBound 9 := { available := 24, camps := [{ cop := 5, region := 71, targets := 256 },{ cop := 1, region := 440, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 67 133 296 336 160 68 152 280), lower := (rows 35 67 133 296 336 160 68 128 256), losses := [] }

theorem u1203 : Upper (D 9) (R 9) [34,65,129,288,320,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1203 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1204 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 83, targets := 128 },{ cop := 4, region := 167, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(4,7)], upper := (rows 35 67 133 296 336 160 72 148 276), lower := (rows 35 67 133 296 336 160 72 128 256), losses := [] }

theorem u1204 : Upper (D 9) (R 9) [34,65,129,288,320,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1204 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1205 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 429, targets := 64 },{ cop := 3, region := 83, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(3,6)], upper := (rows 35 67 133 296 336 160 80 140 268), lower := (rows 35 67 133 296 336 160 80 128 256), losses := [] }

theorem u1205 : Upper (D 9) (R 9) [34,65,129,288,320,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1205 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1206 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7)], upper := (rows 35 67 133 296 400 36 72 208 336), lower := (rows 35 67 133 296 400 36 72 128 256), losses := [] }

theorem u1206 : Upper (D 9) (R 9) [34,65,129,288,384,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1206 [(5,2),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1207 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 103, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 35 67 133 296 400 36 80 200 328), lower := (rows 35 67 133 296 400 36 80 128 256), losses := [] }

theorem u1207 : Upper (D 9) (R 9) [34,65,129,288,384,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1207 [(5,2),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1208 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 67 133 328 400 36 72 176 304), lower := (rows 35 67 133 328 400 36 72 128 256), losses := [] }

theorem u1208 : Upper (D 9) (R 9) [34,65,129,320,384,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1208 [(5,2),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1209 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 167, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 35 67 133 328 400 36 80 168 296), lower := (rows 35 67 133 328 400 36 80 128 256), losses := [] }

theorem u1209 : Upper (D 9) (R 9) [34,65,129,320,384,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1209 [(5,2),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1210 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 99, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 133 328 400 36 96 152 280), lower := (rows 35 67 133 328 400 36 96 128 256), losses := [] }

theorem u1210 : Upper (D 9) (R 9) [34,65,129,320,384,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1210 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1211 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 66, targets := 416 }], pairs := [(1,5),(1,7),(1,8)], upper := (rows 35 67 133 328 400 48 68 168 296), lower := (rows 35 67 133 328 400 48 68 128 256), losses := [] }

theorem u1211 : Upper (D 9) (R 9) [34,65,129,320,384,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1211 [(5,4),(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1212 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 67 133 328 400 48 72 164 292), lower := (rows 35 67 133 328 400 48 72 128 256), losses := [] }

theorem u1212 : Upper (D 9) (R 9) [34,65,129,320,384,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1212 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1213 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 133 328 400 48 96 140 268), lower := (rows 35 67 133 328 400 48 96 128 256), losses := [] }

theorem u1213 : Upper (D 9) (R 9) [34,65,129,320,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1213 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1214 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 67, targets := 384 },{ cop := 1, region := 444, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 140 280 176 288 65 196 324), lower := (rows 35 67 140 280 176 288 65 128 256), losses := [] }

theorem u1214 : Upper (D 9) (R 9) [34,65,136,272,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1214 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1215 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(4,0),(4,6)], upper := (rows 35 67 140 280 176 288 68 193 321), lower := (rows 35 67 140 280 176 288 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 296 68 128 256), good := (rows 34 66 252 312 176 288 84 128 288) },{ target := 6, region := (rows 1 2 4 8 20 296 0 128 256), good := (rows 35 3 188 312 176 288 20 128 288) }] }

theorem u1215 : Upper (D 9) (R 9) [34,65,136,272,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1215 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1216 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 300, targets := 65 }], pairs := [(2,0),(2,6),(3,0),(3,6)], upper := (rows 35 67 140 280 208 36 65 416 288), lower := (rows 35 67 140 280 208 36 65 128 256), losses := [] }

theorem u1216 : Upper (D 9) (R 9) [34,65,136,272,192,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1216 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1217 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8),(2,5),(3,5),(4,5)], upper := (rows 35 67 140 280 208 36 96 385 257), lower := (rows 35 67 140 280 208 36 96 128 256), losses := [] }

theorem u1217 : Upper (D 9) (R 9) [34,65,136,272,192,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1217 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1218 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(4,0),(4,5)], upper := (rows 35 67 140 280 208 36 320 161 289), lower := (rows 35 67 140 280 208 36 320 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 36 328 128 256), good := (rows 34 66 252 344 208 52 320 128 320) },{ target := 5, region := (rows 1 2 4 8 20 0 328 128 256), good := (rows 3 67 220 344 208 20 320 128 320) }] }

theorem u1218 : Upper (D 9) (R 9) [34,65,136,272,192,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1218 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1219 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 300, targets := 65 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(2,0),(2,6),(3,0),(3,6)], upper := (rows 35 67 140 280 208 288 65 164 292), lower := (rows 35 67 140 280 208 288 65 128 256), losses := [] }

theorem u1219 : Upper (D 9) (R 9) [34,65,136,272,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1219 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1220 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 80, targets := 289 },{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,8)], upper := (rows 35 67 140 280 208 288 68 161 289), lower := (rows 35 67 140 280 208 288 68 128 256), losses := [] }

theorem u1220 : Upper (D 9) (R 9) [34,65,136,272,192,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1220 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1221 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 67, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 140 280 208 288 96 133 261), lower := (rows 35 67 140 280 208 288 96 128 256), losses := [] }

theorem u1221 : Upper (D 9) (R 9) [34,65,136,272,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1221 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1222 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 140 296 208 36 65 400 272), lower := (rows 35 67 140 296 208 36 65 128 256), losses := [] }

theorem u1222 : Upper (D 9) (R 9) [34,65,136,288,192,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1222 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1223 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 67 140 296 208 36 80 385 257), lower := (rows 35 67 140 296 208 36 80 128 256), losses := [] }

theorem u1223 : Upper (D 9) (R 9) [34,65,136,288,192,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1223 [(5,2),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1224 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 3, region := 67, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(4,5)], upper := (rows 35 67 140 296 208 36 320 145 273), lower := (rows 35 67 140 296 208 36 320 128 256), losses := [] }

theorem u1224 : Upper (D 9) (R 9) [34,65,136,288,192,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1224 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1225 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 99, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 140 296 336 36 65 144 400), lower := (rows 35 67 140 296 336 36 65 128 256), losses := [] }

theorem u1225 : Upper (D 9) (R 9) [34,65,136,288,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1225 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1226 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 67 140 296 336 36 80 129 385), lower := (rows 35 67 140 296 336 36 80 128 256), losses := [] }

theorem u1226 : Upper (D 9) (R 9) [34,65,136,288,320,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1226 [(5,2),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1227 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8),(1,5),(1,8),(4,5)], upper := (rows 35 67 140 296 336 36 192 145 273), lower := (rows 35 67 140 296 336 36 192 128 256), losses := [] }

theorem u1227 : Upper (D 9) (R 9) [34,65,136,288,320,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1227 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1228 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 172, targets := 65 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(2,0),(2,6),(3,0),(3,6)], upper := (rows 35 67 140 296 336 160 65 148 276), lower := (rows 35 67 140 296 336 160 65 128 256), losses := [] }

theorem u1228 : Upper (D 9) (R 9) [34,65,136,288,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1228 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1229 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 99, targets := 256 },{ cop := 1, region := 272, targets := 32 },{ cop := 1, region := 272, targets := 128 }], pairs := [(0,8),(1,8),(4,5),(4,7)], upper := (rows 35 67 140 296 336 160 68 145 273), lower := (rows 35 67 140 296 336 160 68 128 256), losses := [] }

theorem u1229 : Upper (D 9) (R 9) [34,65,136,288,320,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1229 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1230 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 429, targets := 64 },{ cop := 3, region := 83, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(3,6)], upper := (rows 35 67 140 296 336 160 80 133 261), lower := (rows 35 67 140 296 336 160 80 128 256), losses := [] }

theorem u1230 : Upper (D 9) (R 9) [34,65,136,288,320,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1230 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1231 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 180, targets := 65 },{ cop := 4, region := 67, targets := 128 }], pairs := [(0,7),(2,0),(2,6),(4,0),(4,6)], upper := (rows 35 67 140 328 176 288 65 148 276), lower := (rows 35 67 140 328 176 288 65 128 256), losses := [] }

theorem u1231 : Upper (D 9) (R 9) [34,65,136,320,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1231 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1232 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 67 140 328 176 288 68 145 273), lower := (rows 35 67 140 328 176 288 68 128 256), losses := [] }

theorem u1232 : Upper (D 9) (R 9) [34,65,136,320,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1232 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1233 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 140 328 176 288 80 133 261), lower := (rows 35 67 140 328 176 288 80 128 256), losses := [] }

theorem u1233 : Upper (D 9) (R 9) [34,65,136,320,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1233 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1234 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 99, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 140 328 304 36 65 144 400), lower := (rows 35 67 140 328 304 36 65 128 256), losses := [] }

theorem u1234 : Upper (D 9) (R 9) [34,65,136,320,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1234 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1235 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 167, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 35 67 140 328 304 36 80 129 385), lower := (rows 35 67 140 328 304 36 80 128 256), losses := [] }

theorem u1235 : Upper (D 9) (R 9) [34,65,136,320,288,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1235 [(5,2),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1236 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 99, targets := 256 },{ cop := 0, region := 272, targets := 64 },{ cop := 0, region := 272, targets := 128 }], pairs := [(0,8),(1,8),(4,6),(4,7)], upper := (rows 35 67 140 328 304 36 192 145 273), lower := (rows 35 67 140 328 304 36 192 128 256), losses := [] }

theorem u1236 : Upper (D 9) (R 9) [34,65,136,320,288,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1236 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1237 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 180, targets := 65 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(2,0),(2,6),(4,0),(4,6)], upper := (rows 35 67 140 328 304 160 65 148 276), lower := (rows 35 67 140 328 304 160 65 128 256), losses := [] }

theorem u1237 : Upper (D 9) (R 9) [34,65,136,320,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1237 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1238 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,6),(0,8),(1,8),(4,6)], upper := (rows 35 67 140 328 304 160 68 145 273), lower := (rows 35 67 140 328 304 160 68 128 256), losses := [] }

theorem u1238 : Upper (D 9) (R 9) [34,65,136,320,288,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1238 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1239 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 167, targets := 256 },{ cop := 4, region := 67, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8)], upper := (rows 35 67 140 328 304 160 80 133 261), lower := (rows 35 67 140 328 304 160 80 128 256), losses := [] }

theorem u1239 : Upper (D 9) (R 9) [34,65,136,320,288,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1239 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1240 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 99, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 140 328 400 36 65 176 304), lower := (rows 35 67 140 328 400 36 65 128 256), losses := [] }

theorem u1240 : Upper (D 9) (R 9) [34,65,136,320,384,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1240 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1241 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 167, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 35 67 140 328 400 36 80 161 289), lower := (rows 35 67 140 328 400 36 80 128 256), losses := [] }

theorem u1241 : Upper (D 9) (R 9) [34,65,136,320,384,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1241 [(5,2),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1242 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 99, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 140 328 400 36 96 145 273), lower := (rows 35 67 140 328 400 36 96 128 256), losses := [] }

theorem u1242 : Upper (D 9) (R 9) [34,65,136,320,384,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1242 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1243 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 180, targets := 65 }], pairs := [(2,0),(2,6),(4,0),(4,6)], upper := (rows 35 67 140 328 400 48 65 164 292), lower := (rows 35 67 140 328 400 48 65 128 256), losses := [] }

theorem u1243 : Upper (D 9) (R 9) [34,65,136,320,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1243 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1244 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 4, region := 76, targets := 1 }], pairs := [(0,6),(2,0),(4,6)], upper := (rows 35 67 140 328 400 48 68 161 289), lower := (rows 35 67 140 328 400 48 68 128 256), losses := [] }

theorem u1244 : Upper (D 9) (R 9) [34,65,136,320,384,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1244 [(5,4),(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1245 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 140 328 400 48 96 133 261), lower := (rows 35 67 140 328 400 48 96 128 256), losses := [] }

theorem u1245 : Upper (D 9) (R 9) [34,65,136,320,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1245 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1246 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 1, region := 289, targets := 128 },{ cop := 2, region := 450, targets := 1 },{ cop := 4, region := 360, targets := 1 }], pairs := [(0,7),(1,0),(1,5),(3,0),(4,5)], upper := (rows 35 70 13 56 145 288 192 448 320), lower := (rows 35 70 13 56 145 288 192 128 256), losses := [] }

theorem u1246 : Upper (D 9) (R 9) [34,68,9,48,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1246 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1247 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 2, region := 450, targets := 1 },{ cop := 4, region := 360, targets := 1 }], pairs := [(0,6),(1,0),(1,5),(3,0),(4,5)], upper := (rows 35 70 13 56 145 288 320 192 448), lower := (rows 35 70 13 56 145 288 320 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 352 0 128 256), good := (rows 35 39 13 56 145 288 288 128 288) }] }

theorem u1247 : Upper (D 9) (R 9) [34,68,9,48,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1247 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1248 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 70 13 56 208 288 65 384 384), lower := (rows 35 70 13 56 208 288 65 128 256), losses := [] }

theorem u1248 : Upper (D 9) (R 9) [34,68,9,48,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1248 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1249 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 303, targets := 128 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,7),(4,0)], upper := (rows 35 70 13 56 208 288 192 385 257), lower := (rows 35 70 13 56 208 288 192 128 256), losses := [] }

theorem u1249 : Upper (D 9) (R 9) [34,68,9,48,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1249 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1250 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(1,5),(3,0),(3,6),(4,5)], upper := (rows 35 70 13 56 208 288 320 129 385), lower := (rows 35 70 13 56 208 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 352 352 128 256), good := (rows 98 102 12 120 248 352 352 128 352) },{ target := 6, region := (rows 3 2 4 24 16 359 0 135 263), good := (rows 419 423 429 56 184 288 288 128 288) }] }

theorem u1250 : Upper (D 9) (R 9) [34,68,9,48,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1250 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1251 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 400, targets := 32 },{ cop := 2, region := 482, targets := 1 },{ cop := 4, region := 360, targets := 1 }], pairs := [(0,6),(1,0),(3,0),(4,5),(4,6)], upper := (rows 35 70 13 88 145 288 96 384 384), lower := (rows 35 70 13 88 145 288 96 128 256), losses := [] }

theorem u1251 : Upper (D 9) (R 9) [34,68,9,80,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1251 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1252 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 78, targets := 288 }], pairs := [(1,5),(1,8),(2,5),(2,8),(3,5)], upper := (rows 35 70 13 88 145 288 192 416 288), lower := (rows 35 70 13 88 145 288 192 128 256), losses := [] }

theorem u1252 : Upper (D 9) (R 9) [34,68,9,80,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1252 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1253 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 144, targets := 256 },{ cop := 2, region := 482, targets := 1 },{ cop := 4, region := 360, targets := 1 }], pairs := [(0,6),(1,0),(3,0),(4,6),(4,8)], upper := (rows 35 70 13 88 145 288 320 160 416), lower := (rows 35 70 13 88 145 288 320 128 256), losses := [] }

theorem u1253 : Upper (D 9) (R 9) [34,68,9,80,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1253 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1254 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 79, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 70 13 88 176 288 65 384 384), lower := (rows 35 70 13 88 176 288 65 128 256), losses := [] }

theorem u1254 : Upper (D 9) (R 9) [34,68,9,80,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1254 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1255 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 13 88 176 288 192 385 257), lower := (rows 35 70 13 88 176 288 192 128 256), losses := [] }

theorem u1255 : Upper (D 9) (R 9) [34,68,9,80,160,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1255 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1256 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 144, targets := 256 },{ cop := 2, region := 450, targets := 32 }], pairs := [(0,6),(1,5),(3,0),(4,6),(4,8)], upper := (rows 35 70 13 88 176 288 320 129 385), lower := (rows 35 70 13 88 176 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 352 352 128 256), good := (rows 98 102 12 120 248 352 352 128 352) }] }

theorem u1256 : Upper (D 9) (R 9) [34,68,9,80,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1256 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1257 : Route 9 := (fun mask => (mask,id))

def c1257 : Nat → Fin 9 := (fun mask => match mask with | 1 => 8 | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | _ => 0)

theorem u1257 : Upper (D 9) (R 9) [34,68,9,144,96,128,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,144,96,128,256] 13 (by decide) (choices 1) [256] r1257 c1257
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u51

def b1258 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 80, targets := 384 },{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 66, targets := 128 }], pairs := [(1,7),(3,0),(4,0),(4,7),(4,8)], upper := (rows 35 70 13 152 112 288 65 384 384), lower := (rows 35 70 13 152 112 288 65 128 256), losses := [] }

theorem u1258 : Upper (D 9) (R 9) [34,68,9,144,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1258 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1259 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 305, targets := 128 },{ cop := 1, region := 289, targets := 64 },{ cop := 2, region := 450, targets := 32 }], pairs := [(0,6),(0,7),(1,0),(1,5),(4,7)], upper := (rows 35 70 13 152 112 288 192 385 257), lower := (rows 35 70 13 152 112 288 192 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 288 200 128 256), good := (rows 34 70 78 216 112 288 192 192 288) }] }

theorem u1259 : Upper (D 9) (R 9) [34,68,9,144,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1259 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u1259
end Delivery.IrregularNine14.P09
