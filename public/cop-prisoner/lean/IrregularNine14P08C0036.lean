import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2160 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 140 56 273 96 225 161 417), lower := (rows 35 70 140 56 273 96 64 128 256), losses := [] }

theorem u2160 : Upper (D 8) (R 8) [34,68,136,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2160 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2161 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 140 56 273 160 97 225 353), lower := (rows 35 70 140 56 273 160 64 128 256), losses := [] }

theorem u2161 : Upper (D 8) (R 8) [34,68,136,48,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2161 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2162 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 265 112 33 240 176 432), lower := (rows 35 70 140 265 112 33 64 128 256), losses := [] }

theorem u2162 : Upper (D 8) (R 8) [34,68,136,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2162 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2163 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 70 140 265 112 48 225 161 417), lower := (rows 35 70 140 265 112 48 64 128 256), losses := [] }

theorem u2163 : Upper (D 8) (R 8) [34,68,136,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2163 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2164 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 140 265 112 160 113 177 305), lower := (rows 35 70 140 265 112 160 64 128 256), losses := [] }

theorem u2164 : Upper (D 8) (R 8) [34,68,136,257,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2164 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2165 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 140 265 176 33 112 240 368), lower := (rows 35 70 140 265 176 33 64 128 256), losses := [] }

theorem u2165 : Upper (D 8) (R 8) [34,68,136,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2165 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2166 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 35 70 140 265 176 48 97 225 353), lower := (rows 35 70 140 265 176 48 64 128 256), losses := [] }

theorem u2166 : Upper (D 8) (R 8) [34,68,136,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2166 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2167 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 140 265 176 96 113 177 305), lower := (rows 35 70 140 265 176 96 64 128 256), losses := [] }

theorem u2167 : Upper (D 8) (R 8) [34,68,136,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2167 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2168 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 140 265 208 33 112 176 304), lower := (rows 35 70 140 265 208 33 64 128 256), losses := [] }

theorem u2168 : Upper (D 8) (R 8) [34,68,136,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2168 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2169 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 70 140 265 208 48 97 161 289), lower := (rows 35 70 140 265 208 48 64 128 256), losses := [] }

theorem u2169 : Upper (D 8) (R 8) [34,68,136,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2169 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2170 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 296 112 33 209 145 401), lower := (rows 35 70 140 296 112 33 64 128 256), losses := [] }

theorem u2170 : Upper (D 8) (R 8) [34,68,136,288,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2170 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2171 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 70 140 296 112 48 193 129 385), lower := (rows 35 70 140 296 112 48 64 128 256), losses := [] }

theorem u2171 : Upper (D 8) (R 8) [34,68,136,288,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2171 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2172 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 140 296 112 160 81 145 273), lower := (rows 35 70 140 296 112 160 64 128 256), losses := [] }

theorem u2172 : Upper (D 8) (R 8) [34,68,136,288,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2172 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2173 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 140 296 176 33 81 209 337), lower := (rows 35 70 140 296 176 33 64 128 256), losses := [] }

theorem u2173 : Upper (D 8) (R 8) [34,68,136,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2173 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2174 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 35 70 140 296 176 48 65 193 321), lower := (rows 35 70 140 296 176 48 64 128 256), losses := [] }

theorem u2174 : Upper (D 8) (R 8) [34,68,136,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2174 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2175 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 140 296 176 96 81 145 273), lower := (rows 35 70 140 296 176 96 64 128 256), losses := [] }

theorem u2175 : Upper (D 8) (R 8) [34,68,136,288,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2175 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2176 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 140 296 208 33 113 177 305), lower := (rows 35 70 140 296 208 33 64 128 256), losses := [] }

theorem u2176 : Upper (D 8) (R 8) [34,68,136,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2176 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2177 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 70 140 296 208 48 97 161 289), lower := (rows 35 70 140 296 208 48 64 128 256), losses := [] }

theorem u2177 : Upper (D 8) (R 8) [34,68,136,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2177 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2178 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 198, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 164 25 280 33 224 224 480), lower := (rows 35 70 164 25 280 33 64 128 256), losses := [] }

theorem u2178 : Upper (D 8) (R 8) [34,68,160,17,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2178 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2179 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 132, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 25 280 96 225 161 417), lower := (rows 35 70 164 25 280 96 64 128 256), losses := [] }

theorem u2179 : Upper (D 8) (R 8) [34,68,160,17,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2179 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2180 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 25 280 160 97 225 353), lower := (rows 35 70 164 25 280 160 64 128 256), losses := [] }

theorem u2180 : Upper (D 8) (R 8) [34,68,160,17,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2180 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2181 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 25 304 33 200 200 456), lower := (rows 35 70 164 25 304 33 64 128 256), losses := [] }

theorem u2181 : Upper (D 8) (R 8) [34,68,160,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2181 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2182 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 70 164 25 304 40 193 193 449), lower := (rows 35 70 164 25 304 40 64 128 256), losses := [] }

theorem u2182 : Upper (D 8) (R 8) [34,68,160,17,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2182 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2183 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 25 304 96 201 137 393), lower := (rows 35 70 164 25 304 96 64 128 256), losses := [] }

theorem u2183 : Upper (D 8) (R 8) [34,68,160,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2183 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2184 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 25 304 160 73 201 329), lower := (rows 35 70 164 25 304 160 64 128 256), losses := [] }

theorem u2184 : Upper (D 8) (R 8) [34,68,160,17,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2184 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2185 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 25 400 33 104 232 360), lower := (rows 35 70 164 25 400 33 64 128 256), losses := [] }

theorem u2185 : Upper (D 8) (R 8) [34,68,160,17,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2185 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2186 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 35 70 164 25 400 40 97 225 353), lower := (rows 35 70 164 25 400 40 64 128 256), losses := [] }

theorem u2186 : Upper (D 8) (R 8) [34,68,160,17,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2186 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2187 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 25 400 96 105 169 297), lower := (rows 35 70 164 25 400 96 64 128 256), losses := [] }

theorem u2187 : Upper (D 8) (R 8) [34,68,160,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2187 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2188 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 56 208 33 329 393 265), lower := (rows 35 70 164 56 208 33 64 128 256), losses := [] }

theorem u2188 : Upper (D 8) (R 8) [34,68,160,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2188 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2189 : PairBound 9 := { available := 257, camps := [], pairs := [], upper := (rows 35 70 164 56 208 40 321 385 257), lower := (rows 35 70 164 56 208 40 64 128 256), losses := [] }

theorem u2189 : Upper (D 8) (R 8) [34,68,160,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2189 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2190 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 35 70 164 56 208 288 73 137 265), lower := (rows 35 70 164 56 208 288 64 128 256), losses := [] }

theorem u2190 : Upper (D 8) (R 8) [34,68,160,48,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2190 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2191 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 56 273 33 200 200 456), lower := (rows 35 70 164 56 273 33 64 128 256), losses := [] }

theorem u2191 : Upper (D 8) (R 8) [34,68,160,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2191 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2192 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 70 164 56 273 40 193 193 449), lower := (rows 35 70 164 56 273 40 64 128 256), losses := [] }

theorem u2192 : Upper (D 8) (R 8) [34,68,160,48,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2192 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2193 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 56 273 96 201 137 393), lower := (rows 35 70 164 56 273 96 64 128 256), losses := [] }

theorem u2193 : Upper (D 8) (R 8) [34,68,160,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2193 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2194 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 56 273 160 73 201 329), lower := (rows 35 70 164 56 273 160 64 128 256), losses := [] }

theorem u2194 : Upper (D 8) (R 8) [34,68,160,48,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2194 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2195 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 56 280 33 193 193 449), lower := (rows 35 70 164 56 280 33 64 128 256), losses := [] }

theorem u2195 : Upper (D 8) (R 8) [34,68,160,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2195 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2196 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 132, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 56 280 96 193 129 385), lower := (rows 35 70 164 56 280 96 64 128 256), losses := [] }

theorem u2196 : Upper (D 8) (R 8) [34,68,160,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2196 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2197 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 56 280 160 65 193 321), lower := (rows 35 70 164 56 280 160 64 128 256), losses := [] }

theorem u2197 : Upper (D 8) (R 8) [34,68,160,48,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2197 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2198 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 56 336 33 201 137 393), lower := (rows 35 70 164 56 336 33 64 128 256), losses := [] }

theorem u2198 : Upper (D 8) (R 8) [34,68,160,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2198 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2199 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 70 164 56 336 40 193 129 385), lower := (rows 35 70 164 56 336 40 64 128 256), losses := [] }

theorem u2199 : Upper (D 8) (R 8) [34,68,160,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2199 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2200 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 56 336 160 73 137 265), lower := (rows 35 70 164 56 336 160 64 128 256), losses := [] }

theorem u2200 : Upper (D 8) (R 8) [34,68,160,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2200 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2201 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 56 400 33 73 201 329), lower := (rows 35 70 164 56 400 33 64 128 256), losses := [] }

theorem u2201 : Upper (D 8) (R 8) [34,68,160,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2201 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2202 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 35 70 164 56 400 40 65 193 321), lower := (rows 35 70 164 56 400 40 64 128 256), losses := [] }

theorem u2202 : Upper (D 8) (R 8) [34,68,160,48,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2202 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2203 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 56 400 96 73 137 265), lower := (rows 35 70 164 56 400 96 64 128 256), losses := [] }

theorem u2203 : Upper (D 8) (R 8) [34,68,160,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2203 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2204 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 88 273 33 232 168 424), lower := (rows 35 70 164 88 273 33 64 128 256), losses := [] }

theorem u2204 : Upper (D 8) (R 8) [34,68,160,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2204 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2205 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 70 164 88 273 40 225 161 417), lower := (rows 35 70 164 88 273 40 64 128 256), losses := [] }

theorem u2205 : Upper (D 8) (R 8) [34,68,160,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2205 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2206 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 88 273 160 105 169 297), lower := (rows 35 70 164 88 273 160 64 128 256), losses := [] }

theorem u2206 : Upper (D 8) (R 8) [34,68,160,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2206 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2207 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 88 304 33 201 137 393), lower := (rows 35 70 164 88 304 33 64 128 256), losses := [] }

theorem u2207 : Upper (D 8) (R 8) [34,68,160,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2207 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2208 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 70 164 88 304 40 193 129 385), lower := (rows 35 70 164 88 304 40 64 128 256), losses := [] }

theorem u2208 : Upper (D 8) (R 8) [34,68,160,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2208 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2209 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 88 304 160 73 137 265), lower := (rows 35 70 164 88 304 160 64 128 256), losses := [] }

theorem u2209 : Upper (D 8) (R 8) [34,68,160,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2209 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2210 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 88 400 33 105 169 297), lower := (rows 35 70 164 88 400 33 64 128 256), losses := [] }

theorem u2210 : Upper (D 8) (R 8) [34,68,160,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2210 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2211 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 70 164 88 400 40 97 161 289), lower := (rows 35 70 164 88 400 40 64 128 256), losses := [] }

theorem u2211 : Upper (D 8) (R 8) [34,68,160,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2211 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2212 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 104 152 33 337 401 273), lower := (rows 35 70 164 104 152 33 64 128 256), losses := [] }

theorem u2212 : Upper (D 8) (R 8) [34,68,160,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2212 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2213 : PairBound 9 := { available := 257, camps := [], pairs := [], upper := (rows 35 70 164 104 152 48 321 385 257), lower := (rows 35 70 164 104 152 48 64 128 256), losses := [] }

theorem u2213 : Upper (D 8) (R 8) [34,68,160,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2213 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2214 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 70 164 104 152 288 81 145 273), lower := (rows 35 70 164 104 152 288 64 128 256), losses := [] }

theorem u2214 : Upper (D 8) (R 8) [34,68,160,96,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2214 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2215 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 104 273 33 216 152 408), lower := (rows 35 70 164 104 273 33 64 128 256), losses := [] }

theorem u2215 : Upper (D 8) (R 8) [34,68,160,96,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2215 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2216 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 70 164 104 273 40 209 145 401), lower := (rows 35 70 164 104 273 40 64 128 256), losses := [] }

theorem u2216 : Upper (D 8) (R 8) [34,68,160,96,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2216 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2217 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 35 70 164 104 273 48 201 137 393), lower := (rows 35 70 164 104 273 48 64 128 256), losses := [] }

theorem u2217 : Upper (D 8) (R 8) [34,68,160,96,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2217 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2218 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 104 273 160 89 153 281), lower := (rows 35 70 164 104 273 160 64 128 256), losses := [] }

theorem u2218 : Upper (D 8) (R 8) [34,68,160,96,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2218 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2219 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 104 280 33 209 145 401), lower := (rows 35 70 164 104 280 33 64 128 256), losses := [] }

theorem u2219 : Upper (D 8) (R 8) [34,68,160,96,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2219 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u2219
end Delivery.IrregularNine14.P08
