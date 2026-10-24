import RegularNineSharp2x7Base
import RegularNineSharp2x7C002
import RegularNineSharp2x7C003
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x7
open Bounds BoundTreeRows Extremal
theorem node256 : UpperPrefix a [2,3,6,8,7,1] 30 :=
  branch_upper a [2,3,6,8,7,1] 30 (by decide) (fin9_cases _
  node253
  (invalid_upper a [2,3,6,8,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,1,3] 30 (by decide +kernel))
  node254
  node255
  (invalid_upper a [2,3,6,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,1,8] 30 (by decide +kernel)))

def cert257 : Leaf := ⟨⟨72,68,306,102,70,134,6,118,114⟩,[],[(3,1,0),(7,4,5)],⟨7,11,76,280,176,112,193,418,294⟩,⟨7,11,76,280,176,112,193,384,260⟩,[⟨0,1214839157535771271889920,⟨446,410,124,280,180,124,508,384,292⟩⟩,⟨8,1184058984512747478277,⟨39,11,127,59,240,112,241,241,39⟩⟩,⟨4,1210109871125761388190981,⟨7,11,79,267,224,96,193,449,263⟩⟩,⟨5,1210109870000960992976133,⟨7,11,79,283,208,80,193,449,263⟩⟩]⟩
theorem node257 : UpperPrefix a [2,3,6,8,7,4,0] 30 :=
  Boolean.leaf_sound a [2,3,6,8,7,4,0] 30 cert257 (by decide +kernel)

def cert258 : Leaf := ⟨⟨104,100,305,101,64,128,309,117,113⟩,[],[(3,1,0),(7,4,5)],⟨7,11,76,280,176,112,194,417,293⟩,⟨7,11,76,280,176,112,194,384,260⟩,[⟨1,1214839157535762673565697,⟨445,409,124,280,176,116,252,384,292⟩⟩,⟨8,1181748066157859970309,⟨39,11,127,27,176,112,242,129,39⟩⟩,⟨0,1210107567680787034670080,⟨38,10,124,280,176,112,242,384,292⟩⟩,⟨2,1210107567680787033621505,⟨35,11,120,280,176,112,242,384,288⟩⟩,⟨4,1210107565282752174497029,⟨7,11,79,267,160,96,194,385,263⟩⟩]⟩
theorem node258 : UpperPrefix a [2,3,6,8,7,4,1] 30 :=
  Boolean.leaf_sound a [2,3,6,8,7,4,1] 30 cert258 (by decide +kernel)

def cert259 : Local := ⟨⟨344,340,275,71,0,391,0,87,83⟩,[(4,6),(6,4)],[(3,1,0),(7,4,5),(5,6,5)]⟩
theorem node259 : UpperPrefix a [2,3,6,8,7,4,5] 30 :=
  local_sound a [2,3,6,8,7,4,5] 30 cert259 (by decide +kernel)

theorem node260 : UpperPrefix a [2,3,6,8,7,4] 30 :=
  branch_upper a [2,3,6,8,7,4] 30 (by decide) (fin9_cases _
  node257
  node258
  (invalid_upper a [2,3,6,8,7,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,4,4] 30 (by decide +kernel))
  node259
  (invalid_upper a [2,3,6,8,7,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,4,8] 30 (by decide +kernel)))

theorem node261 : UpperPrefix a [2,3,6,8,7] 30 :=
  branch_upper a [2,3,6,8,7] 30 (by decide) (fin9_cases _
  node252
  node256
  (invalid_upper a [2,3,6,8,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,3] 30 (by decide +kernel))
  node260
  (invalid_upper a [2,3,6,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,8] 30 (by decide +kernel)))

theorem node262 : UpperPrefix a [2,3,6,8] 30 :=
  branch_upper a [2,3,6,8] 30 (by decide) (fin9_cases _
  node239
  node248
  (invalid_upper a [2,3,6,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,6] 30 (by decide +kernel))
  node261
  (invalid_upper a [2,3,6,8,8] 30 (by decide +kernel)))

theorem node263 : UpperPrefix a [2,3,6] 30 :=
  branch_upper a [2,3,6] 30 (by decide) (fin9_cases _
  node171
  node181
  (invalid_upper a [2,3,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,4] 30 (by decide +kernel))
  node194
  (invalid_upper a [2,3,6,6] 30 (by decide +kernel))
  node228
  node262)

def cert264 : Leaf := ⟨⟨504,0,368,482,448,384,304,112,240⟩,[(1,3)],[(3,1,0),(0,3,1),(1,4,3)],⟨7,11,140,25,50,112,480,480,356⟩,⟨7,11,140,25,50,112,192,384,260⟩,[⟨2,1212475675202594891896321,⟨59,27,250,27,58,112,192,480,496⟩⟩]⟩
theorem node264 : UpperPrefix a [2,3,7,0,1,4] 30 :=
  Boolean.leaf_sound a [2,3,7,0,1,4] 30 cert264 (by decide +kernel)

def cert265 : Leaf := ⟨⟨504,0,368,482,448,144,304,112,240⟩,[(1,3)],[(3,1,0),(0,3,1),(1,4,3)],⟨7,11,140,25,50,352,240,496,372⟩,⟨7,11,140,25,50,352,192,384,260⟩,[⟨2,1212473445779972867233281,⟨91,11,250,27,50,480,224,480,496⟩⟩]⟩
theorem node265 : UpperPrefix a [2,3,7,0,1,8] 30 :=
  Boolean.leaf_sound a [2,3,7,0,1,8] 30 cert265 (by decide +kernel)

theorem node266 : UpperPrefix a [2,3,7,0,1] 30 :=
  branch_upper a [2,3,7,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,1,3] 30 (by decide +kernel))
  node264
  (invalid_upper a [2,3,7,0,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,1,7] 30 (by decide +kernel))
  node265)

def cert267 : Leaf := ⟨⟨392,0,306,422,0,406,310,54,178⟩,[(1,3),(4,5)],[(3,1,0),(0,3,1),(6,4,4)],⟨7,11,140,25,112,370,498,434,310⟩,⟨7,11,140,25,112,96,192,384,260⟩,[⟨4,1210107565282752174497029,⟨7,11,143,11,96,96,192,385,263⟩⟩,⟨5,1210107564157951779282181,⟨7,11,143,27,80,64,192,385,263⟩⟩]⟩
theorem node267 : UpperPrefix a [2,3,7,0,6] 30 :=
  Boolean.leaf_sound a [2,3,7,0,6] 30 cert267 (by decide +kernel)

def cert268 : Leaf := ⟨⟨408,0,368,390,194,400,304,112,242⟩,[(1,3)],[(3,1,0),(0,3,1)],⟨7,11,140,25,304,98,240,496,372⟩,⟨7,11,140,25,304,98,192,384,260⟩,[⟨2,1212621367019632234337281,⟨35,107,234,251,496,98,192,464,496⟩⟩,⟨1,1210255427466817516339201,⟨5,13,140,221,496,96,192,384,260⟩⟩,⟨5,1210107564157953926774021,⟨7,11,143,27,283,66,192,385,263⟩⟩,⟨6,1210106412362349226769669,⟨7,11,143,27,315,34,128,385,263⟩⟩]⟩
theorem node268 : UpperPrefix a [2,3,7,0,8,1] 30 :=
  Boolean.leaf_sound a [2,3,7,0,8,1] 30 cert268 (by decide +kernel)

def cert269 : Leaf := ⟨⟨24,0,370,6,194,386,306,118,242⟩,[(1,3)],[(3,1,0),(0,3,1)],⟨7,11,140,25,304,112,226,482,358⟩,⟨7,11,140,25,304,112,192,384,260⟩,[⟨2,1210107648767570558850049,⟨99,11,250,27,304,112,240,432,368⟩⟩,⟨5,1210107564157953926774021,⟨7,11,143,27,283,90,192,385,263⟩⟩,⟨6,1210106412362349226769669,⟨7,11,143,27,315,58,128,385,263⟩⟩,⟨7,1208926973663136422313221,⟨7,11,15,27,315,122,64,257,263⟩⟩,⟨8,1181745669224658910469,⟨7,11,143,27,59,122,192,129,7⟩⟩]⟩
theorem node269 : UpperPrefix a [2,3,7,0,8,4] 30 :=
  Boolean.leaf_sound a [2,3,7,0,8,4] 30 cert269 (by decide +kernel)

theorem node270 : UpperPrefix a [2,3,7,0,8] 30 :=
  branch_upper a [2,3,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,0,8,0] 30 (by decide +kernel))
  node268
  (invalid_upper a [2,3,7,0,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,8,3] 30 (by decide +kernel))
  node269
  (invalid_upper a [2,3,7,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,8,8] 30 (by decide +kernel)))

theorem node271 : UpperPrefix a [2,3,7,0] 30 :=
  branch_upper a [2,3,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,0,0] 30 (by decide +kernel))
  node266
  (invalid_upper a [2,3,7,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,5] 30 (by decide +kernel))
  node267
  (invalid_upper a [2,3,7,0,7] 30 (by decide +kernel))
  node270)

def cert272 : Leaf := ⟨⟨24,20,368,5,452,404,308,116,240⟩,[],[(3,1,0),(1,3,1),(0,4,3)],⟨7,11,140,26,49,368,496,496,372⟩,⟨7,11,140,26,49,96,192,384,260⟩,[⟨5,1210107564157953926769925,⟨7,11,143,26,27,64,192,385,263⟩⟩,⟨6,1210106412362349226765573,⟨7,11,143,26,59,32,128,385,263⟩⟩,⟨7,1208926973663136422309125,⟨7,11,15,26,59,96,64,257,263⟩⟩,⟨8,1181745669224658906373,⟨7,11,143,26,59,96,192,129,7⟩⟩]⟩
theorem node272 : UpperPrefix a [2,3,7,1,0] 30 :=
  Boolean.leaf_sound a [2,3,7,1,0] 30 cert272 (by decide +kernel)

def cert273 : Leaf := ⟨⟨8,4,305,421,0,405,309,53,177⟩,[(4,5)],[(3,1,0),(1,3,1),(6,4,4)],⟨7,11,140,26,112,369,497,433,309⟩,⟨7,11,140,26,112,96,192,384,260⟩,[⟨4,1210107565282752174492933,⟨7,11,143,10,96,96,192,385,263⟩⟩,⟨5,1210107564157951779278085,⟨7,11,143,26,80,64,192,385,263⟩⟩,⟨7,1208926973665333298072837,⟨7,11,15,26,112,112,64,257,263⟩⟩,⟨8,1181745671421534670085,⟨7,11,143,26,112,112,192,129,7⟩⟩]⟩
theorem node273 : UpperPrefix a [2,3,7,1,6] 30 :=
  Boolean.leaf_sound a [2,3,7,1,6] 30 cert273 (by decide +kernel)

def cert274 : Leaf := ⟨⟨24,20,368,5,197,400,304,112,241⟩,[],[(3,1,0),(1,3,1)],⟨7,11,140,26,304,97,240,496,372⟩,⟨7,11,140,26,304,97,192,384,260⟩,[⟨0,1210255427466817516340224,⟨6,14,140,222,496,96,192,384,260⟩⟩,⟨2,1210255571652374333228033,⟨35,107,200,250,496,97,192,384,256⟩⟩,⟨5,1210107564157953926769925,⟨7,11,143,26,283,65,192,385,263⟩⟩,⟨6,1210106412362349226765573,⟨7,11,143,26,315,33,128,385,263⟩⟩,⟨7,1208926973663136422309125,⟨7,11,15,26,315,97,64,257,263⟩⟩,⟨8,1181745669224658906373,⟨7,11,143,26,59,97,192,129,7⟩⟩]⟩
theorem node274 : UpperPrefix a [2,3,7,1,8,0] 30 :=
  Boolean.leaf_sound a [2,3,7,1,8,0] 30 cert274 (by decide +kernel)

def cert275 : Leaf := ⟨⟨8,4,353,5,197,389,293,101,241⟩,[],[(3,1,0),(1,3,1)],⟨7,11,140,26,304,112,225,481,357⟩,⟨7,11,140,26,304,112,192,384,260⟩,[⟨4,1210255427465718004718863,⟨7,15,143,207,481,224,192,385,263⟩⟩,⟨5,1210107564157958221737221,⟨7,11,143,26,283,90,192,385,263⟩⟩,⟨6,1210106412362353521732869,⟨7,11,143,26,315,58,128,385,263⟩⟩,⟨7,1208926973663140717276421,⟨7,11,15,26,315,122,64,257,263⟩⟩,⟨8,1181745669228953873669,⟨7,11,143,26,59,122,192,129,7⟩⟩]⟩
theorem node275 : UpperPrefix a [2,3,7,1,8,4] 30 :=
  Boolean.leaf_sound a [2,3,7,1,8,4] 30 cert275 (by decide +kernel)

theorem node276 : UpperPrefix a [2,3,7,1,8] 30 :=
  branch_upper a [2,3,7,1,8] 30 (by decide) (fin9_cases _
  node274
  (invalid_upper a [2,3,7,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,8,3] 30 (by decide +kernel))
  node275
  (invalid_upper a [2,3,7,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,8,8] 30 (by decide +kernel)))

theorem node277 : UpperPrefix a [2,3,7,1] 30 :=
  branch_upper a [2,3,7,1] 30 (by decide) (fin9_cases _
  node272
  (invalid_upper a [2,3,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,5] 30 (by decide +kernel))
  node273
  (invalid_upper a [2,3,7,1,7] 30 (by decide +kernel))
  node276)

def cert278 : Leaf := ⟨⟨216,212,80,0,198,148,276,84,208⟩,[(3,4)],[(3,1,0),(5,3,3),(1,5,4)],⟨7,11,140,56,49,98,464,464,340⟩,⟨7,11,140,56,49,98,192,384,260⟩,[⟨0,1323666154217542811911168,⟨38,494,460,508,508,102,192,384,260⟩⟩,⟨8,1181747928184199904613,⟨7,27,159,59,59,127,255,129,7⟩⟩]⟩
theorem node278 : UpperPrefix a [2,3,7,5,0,1] 30 :=
  Boolean.leaf_sound a [2,3,7,5,0,1] 30 cert278 (by decide +kernel)

def cert279 : Leaf := ⟨⟨456,452,322,0,454,390,262,70,194⟩,[(3,4)],[(3,1,0),(5,3,3),(4,5,3)],⟨7,11,140,56,49,112,450,450,326⟩,⟨7,11,140,56,49,112,192,384,260⟩,[⟨0,1224302389454723115123712,⟨454,462,140,60,508,124,192,384,260⟩⟩]⟩
theorem node279 : UpperPrefix a [2,3,7,5,0,4] 30 :=
  Boolean.leaf_sound a [2,3,7,5,0,4] 30 cert279 (by decide +kernel)

def cert280 : Leaf := ⟨⟨8,4,339,0,6,151,279,87,211⟩,[(3,4)],[(3,1,0),(5,3,3)],⟨7,11,140,56,49,352,210,466,342⟩,⟨7,11,140,56,49,352,192,384,260⟩,[⟨6,1210106412364552545004805,⟨7,11,143,58,59,315,128,385,263⟩⟩,⟨7,1208926973665339740548357,⟨7,11,15,58,59,379,64,257,263⟩⟩,⟨8,1181745671427977145605,⟨7,11,143,58,59,123,192,129,7⟩⟩,⟨4,1210107565282752174492933,⟨7,11,143,40,33,353,192,385,263⟩⟩]⟩
theorem node280 : UpperPrefix a [2,3,7,5,0,8] 30 :=
  Boolean.leaf_sound a [2,3,7,5,0,8] 30 cert280 (by decide +kernel)

theorem node281 : UpperPrefix a [2,3,7,5,0] 30 :=
  branch_upper a [2,3,7,5,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,5,0,0] 30 (by decide +kernel))
  node278
  (invalid_upper a [2,3,7,5,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,0,3] 30 (by decide +kernel))
  node279
  (invalid_upper a [2,3,7,5,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,0,7] 30 (by decide +kernel))
  node280)

def cert282 : Leaf := ⟨⟨216,212,80,0,197,148,276,84,208⟩,[(3,4)],[(3,1,0),(5,3,3),(0,5,4)],⟨7,11,140,56,50,97,464,464,340⟩,⟨7,11,140,56,50,97,192,384,260⟩,[⟨1,1323666154217542811910145,⟨37,493,460,508,508,97,192,384,260⟩⟩,⟨8,1181747928184199904613,⟨7,27,159,59,59,127,255,129,7⟩⟩]⟩
theorem node282 : UpperPrefix a [2,3,7,5,1,0] 30 :=
  Boolean.leaf_sound a [2,3,7,5,1,0] 30 cert282 (by decide +kernel)

def cert283 : Leaf := ⟨⟨456,452,321,0,453,389,261,69,193⟩,[(3,4)],[(3,1,0),(5,3,3),(4,5,3)],⟨7,11,140,56,50,112,449,449,325⟩,⟨7,11,140,56,50,112,192,384,260⟩,[⟨1,1224302389454723115122689,⟨453,461,140,60,508,124,192,384,260⟩⟩]⟩
theorem node283 : UpperPrefix a [2,3,7,5,1,4] 30 :=
  Boolean.leaf_sound a [2,3,7,5,1,4] 30 cert283 (by decide +kernel)

def cert284 : Leaf := ⟨⟨24,20,339,0,5,151,23,87,211⟩,[(3,4)],[(3,1,0),(5,3,3)],⟨7,11,140,56,50,352,209,465,341⟩,⟨7,11,140,56,50,352,192,384,260⟩,[⟨8,1181817729571770879237,⟨71,27,223,58,58,123,192,129,71⟩⟩,⟨6,1210106412365102300810501,⟨7,27,159,58,58,315,128,385,263⟩⟩,⟨7,1208926973665889496354053,⟨7,27,31,58,58,379,64,257,263⟩⟩]⟩
theorem node284 : UpperPrefix a [2,3,7,5,1,8] 30 :=
  Boolean.leaf_sound a [2,3,7,5,1,8] 30 cert284 (by decide +kernel)

theorem node285 : UpperPrefix a [2,3,7,5,1] 30 :=
  branch_upper a [2,3,7,5,1] 30 (by decide) (fin9_cases _
  node282
  (invalid_upper a [2,3,7,5,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,1,3] 30 (by decide +kernel))
  node283
  (invalid_upper a [2,3,7,5,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,1,7] 30 (by decide +kernel))
  node284)

def cert286 : Leaf := ⟨⟨392,388,275,0,0,407,279,23,147⟩,[(3,4),(4,5)],[(3,1,0),(5,3,3),(6,4,3),(6,4,4)],⟨7,11,140,56,112,371,467,403,279⟩,⟨7,11,140,56,112,96,192,384,260⟩,[⟨4,1210107565282752174492933,⟨7,11,143,40,96,96,192,385,263⟩⟩]⟩
theorem node286 : UpperPrefix a [2,3,7,5,6] 30 :=
  Boolean.leaf_sound a [2,3,7,5,6] 30 cert286 (by decide +kernel)

def cert287 : Leaf := ⟨⟨472,468,336,0,196,406,276,84,208⟩,[(3,4)],[(3,1,0),(5,3,3),(1,6,5)],⟨7,11,140,56,304,97,194,464,340⟩,⟨7,11,140,56,304,97,194,384,260⟩,[⟨0,1370981674396623450932224,⟨454,478,156,444,444,508,454,384,260⟩⟩]⟩
theorem node287 : UpperPrefix a [2,3,7,5,8,0,1] 30 :=
  Boolean.leaf_sound a [2,3,7,5,8,0,1] 30 cert287 (by decide +kernel)

def cert288 : Leaf := ⟨⟨136,132,19,0,199,150,263,87,211⟩,[(3,4)],[(3,1,0),(5,3,3),(8,4,6)],⟨7,11,140,56,304,97,208,450,326⟩,⟨7,11,140,56,304,97,208,384,260⟩,[⟨6,1210106412362349243579749,⟨7,11,143,59,315,39,159,385,263⟩⟩,⟨4,1210107565282752174492933,⟨7,11,143,40,289,97,192,385,263⟩⟩]⟩
theorem node288 : UpperPrefix a [2,3,7,5,8,0,4] 30 :=
  Boolean.leaf_sound a [2,3,7,5,8,0,4] 30 cert288 (by decide +kernel)

theorem node289 : UpperPrefix a [2,3,7,5,8,0] 30 :=
  branch_upper a [2,3,7,5,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,5,8,0,0] 30 (by decide +kernel))
  node287
  (invalid_upper a [2,3,7,5,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,8,0,3] 30 (by decide +kernel))
  node288
  (invalid_upper a [2,3,7,5,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,8,0,8] 30 (by decide +kernel)))

def cert290 : Leaf := ⟨⟨472,468,336,0,196,405,276,84,208⟩,[(3,4)],[(3,1,0),(5,3,3),(0,6,5)],⟨7,11,140,56,304,98,193,464,340⟩,⟨7,11,140,56,304,98,193,384,260⟩,[⟨1,1370981674396623450931201,⟨453,477,156,444,444,508,193,384,260⟩⟩]⟩
theorem node290 : UpperPrefix a [2,3,7,5,8,1,0] 30 :=
  Boolean.leaf_sound a [2,3,7,5,8,1,0] 30 cert290 (by decide +kernel)

def cert291 : Leaf := ⟨⟨24,20,19,0,199,21,263,87,211⟩,[(3,4)],[(3,1,0),(5,3,3),(8,4,6)],⟨7,11,140,56,304,98,208,449,325⟩,⟨7,11,140,56,304,98,208,384,260⟩,[⟨6,1210106412362349243579749,⟨7,11,143,59,315,39,159,385,263⟩⟩,⟨7,1208926975914944825928965,⟨7,11,15,58,315,106,122,257,263⟩⟩]⟩
theorem node291 : UpperPrefix a [2,3,7,5,8,1,4] 30 :=
  Boolean.leaf_sound a [2,3,7,5,8,1,4] 30 cert291 (by decide +kernel)

theorem node292 : UpperPrefix a [2,3,7,5,8,1] 30 :=
  branch_upper a [2,3,7,5,8,1] 30 (by decide) (fin9_cases _
  node290
  (invalid_upper a [2,3,7,5,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,8,1,3] 30 (by decide +kernel))
  node291
  (invalid_upper a [2,3,7,5,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,8,1,8] 30 (by decide +kernel)))

def cert293 : Leaf := ⟨⟨136,132,323,0,199,391,7,71,195⟩,[(3,4)],[(3,1,0),(5,3,3),(4,5,3)],⟨7,11,140,56,304,112,195,451,327⟩,⟨7,11,140,56,304,112,192,384,260⟩,[⟨8,1181817726822991801605,⟨71,11,207,58,59,122,192,129,71⟩⟩,⟨6,1210106412362353521732869,⟨7,11,143,58,315,58,128,385,263⟩⟩]⟩
theorem node293 : UpperPrefix a [2,3,7,5,8,4] 30 :=
  Boolean.leaf_sound a [2,3,7,5,8,4] 30 cert293 (by decide +kernel)

theorem node294 : UpperPrefix a [2,3,7,5,8] 30 :=
  branch_upper a [2,3,7,5,8] 30 (by decide) (fin9_cases _
  node289
  node292
  (invalid_upper a [2,3,7,5,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,8,3] 30 (by decide +kernel))
  node293
  (invalid_upper a [2,3,7,5,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,8,8] 30 (by decide +kernel)))

theorem node295 : UpperPrefix a [2,3,7,5] 30 :=
  branch_upper a [2,3,7,5] 30 (by decide) (fin9_cases _
  node281
  node285
  (invalid_upper a [2,3,7,5,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,5] 30 (by decide +kernel))
  node286
  (invalid_upper a [2,3,7,5,7] 30 (by decide +kernel))
  node294)

def cert296 : Leaf := ⟨⟨120,116,112,36,70,21,308,116,112⟩,[],[(3,1,0),(1,5,4)],⟨7,11,140,88,49,98,496,432,308⟩,⟨7,11,140,88,49,98,192,384,260⟩,[⟨7,1227816439876504444218629,⟨279,59,319,122,59,122,64,257,279⟩⟩,⟨8,1181748210069345992045,⟨23,59,191,127,59,127,255,129,23⟩⟩,⟨0,1285813291192733991437312,⟨6,14,140,476,508,98,192,384,260⟩⟩]⟩
theorem node296 : UpperPrefix a [2,3,7,6,0,1] 30 :=
  Boolean.leaf_sound a [2,3,7,6,0,1] 30 cert296 (by decide +kernel)

def cert297 : Leaf := ⟨⟨120,116,114,0,70,0,310,118,114⟩,[(3,5),(5,3)],[(3,1,0)],⟨7,11,140,88,49,112,482,418,294⟩,⟨7,11,140,88,49,112,192,384,260⟩,[⟨0,1219570781303940977263616,⟨454,494,172,120,56,120,192,384,260⟩⟩,⟨7,1227816439876504444218629,⟨279,59,319,122,59,122,64,257,279⟩⟩,⟨8,1181748210069345992045,⟨23,59,191,127,59,127,255,129,23⟩⟩]⟩
theorem node297 : UpperPrefix a [2,3,7,6,0,4] 30 :=
  Boolean.leaf_sound a [2,3,7,6,0,4] 30 cert297 (by decide +kernel)

def cert298 : Leaf := ⟨⟨168,164,368,165,132,132,36,52,240⟩,[],[(3,1,0)],⟨7,11,140,88,49,352,194,432,308⟩,⟨7,11,140,88,49,352,194,384,260⟩,[⟨1,1635950654758857532243969,⟨405,445,428,508,437,492,508,384,260⟩⟩,⟨0,1247960320503744428508160,⟨102,494,428,508,48,352,230,384,260⟩⟩,⟨8,1181817729019867589893,⟨71,11,207,90,59,123,194,129,71⟩⟩,⟨4,1210107646347545467161861,⟨71,11,207,72,33,353,194,417,359⟩⟩,⟨6,1210401560269725455355141,⟨7,11,143,24,177,433,130,385,263⟩⟩]⟩
theorem node298 : UpperPrefix a [2,3,7,6,0,8,1] 30 :=
  Boolean.leaf_sound a [2,3,7,6,0,8,1] 30 cert298 (by decide +kernel)

def cert299 : Leaf := ⟨⟨136,132,67,0,134,135,295,103,227⟩,[(3,6)],[(3,1,0),(4,6,3)],⟨7,11,140,88,49,352,208,418,294⟩,⟨7,11,140,88,49,352,208,384,260⟩,[⟨8,1181745671434436410733,⟨7,11,143,95,59,127,223,129,7⟩⟩,⟨5,1210107564157960386043245,⟨7,11,143,95,19,335,223,385,263⟩⟩,⟨6,1210106412364546102529285,⟨7,11,143,24,49,305,144,385,263⟩⟩]⟩
theorem node299 : UpperPrefix a [2,3,7,6,0,8,4] 30 :=
  Boolean.leaf_sound a [2,3,7,6,0,8,4] 30 cert299 (by decide +kernel)

def cert300 : Leaf := ⟨⟨8,4,19,39,6,135,263,23,147⟩,[],[(3,1,0),(8,5,6),(5,6,3)],⟨7,11,140,88,49,352,224,402,278⟩,⟨7,11,140,88,49,352,224,384,260⟩,[⟨6,1247959131203798105070863,⟨7,399,399,415,49,305,176,385,263⟩⟩,⟨4,1210109956694154308226309,⟨71,11,239,72,33,353,224,481,359⟩⟩,⟨7,1208926973665346182999301,⟨7,11,15,90,59,379,122,257,263⟩⟩]⟩
theorem node300 : UpperPrefix a [2,3,7,6,0,8,5] 30 :=
  Boolean.leaf_sound a [2,3,7,6,0,8,5] 30 cert300 (by decide +kernel)

theorem node301 : UpperPrefix a [2,3,7,6,0,8] 30 :=
  branch_upper a [2,3,7,6,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,6,0,8,0] 30 (by decide +kernel))
  node298
  (invalid_upper a [2,3,7,6,0,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,0,8,3] 30 (by decide +kernel))
  node299
  node300
  (invalid_upper a [2,3,7,6,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,0,8,8] 30 (by decide +kernel)))

theorem node302 : UpperPrefix a [2,3,7,6,0] 30 :=
  branch_upper a [2,3,7,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,6,0,0] 30 (by decide +kernel))
  node296
  (invalid_upper a [2,3,7,6,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,0,3] 30 (by decide +kernel))
  node297
  (invalid_upper a [2,3,7,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,0,7] 30 (by decide +kernel))
  node301)

def cert303 : Leaf := ⟨⟨120,112,112,32,65,150,308,116,240⟩,[],[(3,1,0),(0,5,4)],⟨7,11,140,88,50,97,496,432,308⟩,⟨7,11,140,88,50,97,192,384,260⟩,[⟨8,1181748210069345992045,⟨23,59,191,127,59,127,255,129,23⟩⟩,⟨1,1285813291192733991436289,⟨5,13,140,476,508,97,192,384,260⟩⟩,⟨7,1208926973665337593056517,⟨7,11,15,88,58,123,64,257,263⟩⟩,⟨2,1210107565286055003309057,⟨3,11,136,88,58,123,192,384,256⟩⟩]⟩
theorem node303 : UpperPrefix a [2,3,7,6,1,0] 30 :=
  Boolean.leaf_sound a [2,3,7,6,1,0] 30 cert303 (by decide +kernel)

def cert304 : Leaf := ⟨⟨120,116,113,0,69,0,309,117,113⟩,[(3,5),(5,3)],[(3,1,0)],⟨7,11,140,88,50,112,481,417,293⟩,⟨7,11,140,88,50,112,192,384,260⟩,[⟨1,1219570781866893082361857,⟨453,493,172,124,508,124,192,384,260⟩⟩,⟨7,1227816439876504444210437,⟨279,59,319,120,58,120,64,257,279⟩⟩,⟨8,1181748210069345992045,⟨23,59,191,127,59,127,255,129,23⟩⟩]⟩
theorem node304 : UpperPrefix a [2,3,7,6,1,4] 30 :=
  Boolean.leaf_sound a [2,3,7,6,1,4] 30 cert304 (by decide +kernel)

def cert305 : Leaf := ⟨⟨104,100,368,37,68,132,36,116,240⟩,[],[(3,1,0)],⟨7,11,140,88,50,352,193,432,308⟩,⟨7,11,140,88,50,352,193,384,260⟩,[⟨1,1323665758745200533438465,⟨101,493,428,508,508,352,193,384,260⟩⟩,⟨0,1333128901793033104131072,⟨406,446,428,508,438,352,192,384,260⟩⟩,⟨8,1184123572029081275653,⟨71,11,207,88,58,123,193,193,71⟩⟩,⟨4,1210109956694154308226309,⟨71,11,239,72,34,353,225,481,359⟩⟩,⟨7,1208926973665337593056517,⟨7,11,15,88,58,379,65,257,263⟩⟩]⟩
theorem node305 : UpperPrefix a [2,3,7,6,1,8,0] 30 :=
  Boolean.leaf_sound a [2,3,7,6,1,8,0] 30 cert305 (by decide +kernel)

def cert306 : Leaf := ⟨⟨136,132,67,0,197,135,295,39,227⟩,[(3,6)],[(3,1,0),(4,6,3)],⟨7,11,140,88,50,352,208,417,293⟩,⟨7,11,140,88,50,352,208,384,260⟩,[⟨8,1181745671434436410733,⟨7,11,143,95,59,127,223,129,7⟩⟩,⟨5,1210107564157960386043245,⟨7,11,143,95,19,335,223,385,263⟩⟩,⟨6,1210401560267526432099589,⟨7,11,143,24,178,417,144,385,263⟩⟩]⟩
theorem node306 : UpperPrefix a [2,3,7,6,1,8,4] 30 :=
  Boolean.leaf_sound a [2,3,7,6,1,8,4] 30 cert306 (by decide +kernel)

def cert307 : Leaf := ⟨⟨8,4,19,39,69,135,263,23,147⟩,[],[(3,1,0),(8,5,6),(5,6,3)],⟨7,11,140,88,50,352,224,401,277⟩,⟨7,11,140,88,50,352,224,384,260⟩,[⟨6,1323664568880103081647391,⟨7,399,399,415,439,289,160,385,263⟩⟩,⟨4,1210109956694154308226309,⟨71,11,239,72,34,353,224,481,359⟩⟩,⟨7,1208926973669744229502213,⟨7,11,15,88,58,379,122,257,263⟩⟩]⟩
theorem node307 : UpperPrefix a [2,3,7,6,1,8,5] 30 :=
  Boolean.leaf_sound a [2,3,7,6,1,8,5] 30 cert307 (by decide +kernel)

theorem node308 : UpperPrefix a [2,3,7,6,1,8] 30 :=
  branch_upper a [2,3,7,6,1,8] 30 (by decide) (fin9_cases _
  node305
  (invalid_upper a [2,3,7,6,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,1,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,1,8,3] 30 (by decide +kernel))
  node306
  node307
  (invalid_upper a [2,3,7,6,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,1,8,8] 30 (by decide +kernel)))

theorem node309 : UpperPrefix a [2,3,7,6,1] 30 :=
  branch_upper a [2,3,7,6,1] 30 (by decide) (fin9_cases _
  node303
  (invalid_upper a [2,3,7,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,1,3] 30 (by decide +kernel))
  node304
  (invalid_upper a [2,3,7,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,1,7] 30 (by decide +kernel))
  node308)

def cert310 : Leaf := ⟨⟨168,164,304,420,196,134,37,52,240⟩,[],[(3,1,0),(1,6,5)],⟨7,11,140,88,304,97,194,432,308⟩,⟨7,11,140,88,304,97,194,384,260⟩,[⟨0,1437223878321567018517504,⟨6,14,140,476,444,508,194,384,260⟩⟩,⟨4,1210107646523467327606021,⟨103,43,239,72,289,97,194,417,359⟩⟩,⟨6,1210253986314936757787919,⟨7,15,143,159,433,33,131,385,263⟩⟩,⟨8,1181826909937664527621,⟨103,43,239,88,49,97,194,161,103⟩⟩]⟩
theorem node310 : UpperPrefix a [2,3,7,6,8,0,1] 30 :=
  Boolean.leaf_sound a [2,3,7,6,8,0,1] 30 cert310 (by decide +kernel)

def cert311 : Leaf := ⟨⟨200,192,67,0,199,130,291,99,227⟩,[(3,6)],[(3,1,0),(8,4,6),(4,6,3)],⟨7,11,140,88,304,97,208,418,294⟩,⟨7,11,140,88,304,97,208,384,260⟩,[⟨2,1210255571652385070662657,⟨35,107,200,216,506,107,216,384,256⟩⟩,⟨5,1210107564157960386043245,⟨7,11,143,95,275,79,223,385,263⟩⟩]⟩
theorem node311 : UpperPrefix a [2,3,7,6,8,0,4] 30 :=
  Boolean.leaf_sound a [2,3,7,6,8,0,4] 30 cert311 (by decide +kernel)

def cert312 : Leaf := ⟨⟨392,388,274,422,198,390,263,4,146⟩,[],[(3,1,0),(5,6,3)],⟨7,11,140,88,304,97,224,386,276⟩,⟨7,11,140,88,304,97,224,386,260⟩,[⟨0,1701252126252978469864448,⟨134,398,396,348,312,380,508,390,260⟩⟩,⟨4,1212476040590855523798277,⟨103,43,239,104,481,97,224,483,487⟩⟩,⟨6,1250375654675255033077135,⟨135,399,399,415,433,33,161,391,391⟩⟩]⟩
theorem node312 : UpperPrefix a [2,3,7,6,8,0,5,1] 30 :=
  Boolean.leaf_sound a [2,3,7,6,8,0,5,1] 30 cert312 (by decide +kernel)

def cert313 : Local := ⟨⟨200,196,83,167,199,134,7,0,195⟩,[(7,4)],[(3,1,0),(8,4,7),(5,6,3),(4,7,2)]⟩
theorem node313 : UpperPrefix a [2,3,7,6,8,0,5,4] 30 :=
  local_sound a [2,3,7,6,8,0,5,4] 30 cert313 (by decide +kernel)

theorem node314 : UpperPrefix a [2,3,7,6,8,0,5] 30 :=
  branch_upper a [2,3,7,6,8,0,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,6,8,0,5,0] 30 (by decide +kernel))
  node312
  (invalid_upper a [2,3,7,6,8,0,5,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,8,0,5,3] 30 (by decide +kernel))
  node313
  (invalid_upper a [2,3,7,6,8,0,5,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,8,0,5,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,8,0,5,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,8,0,5,8] 30 (by decide +kernel)))

theorem node315 : UpperPrefix a [2,3,7,6,8,0] 30 :=
  branch_upper a [2,3,7,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,6,8,0,0] 30 (by decide +kernel))
  node310
  (invalid_upper a [2,3,7,6,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,8,0,3] 30 (by decide +kernel))
  node311
  node314
  (invalid_upper a [2,3,7,6,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,8,0,8] 30 (by decide +kernel)))

def cert316 : Leaf := ⟨⟨168,164,304,420,196,133,38,52,240⟩,[],[(3,1,0),(0,6,5)],⟨7,11,140,88,304,98,193,432,308⟩,⟨7,11,140,88,304,98,193,384,260⟩,[⟨1,1437223878321567018516481,⟨5,13,140,476,444,508,193,384,260⟩⟩,⟨4,1210109952366476541299973,⟨103,43,239,72,289,98,225,481,359⟩⟩,⟨6,1210253986314936757787919,⟨7,15,143,159,433,35,129,385,263⟩⟩,⟨8,1184132752946878221573,⟨103,43,239,88,49,98,225,225,103⟩⟩]⟩
theorem node316 : UpperPrefix a [2,3,7,6,8,1,0] 30 :=
  Boolean.leaf_sound a [2,3,7,6,8,1,0] 30 cert316 (by decide +kernel)

def cert317 : Leaf := ⟨⟨136,132,3,0,199,133,295,39,227⟩,[(3,6)],[(3,1,0),(8,4,6),(4,6,3)],⟨7,11,140,88,304,98,208,417,293⟩,⟨7,11,140,88,304,98,208,384,260⟩,[⟨6,1210253986314936757787919,⟨7,15,143,159,433,35,144,385,263⟩⟩,⟨5,1210107564157960386043245,⟨7,11,143,95,275,79,223,385,263⟩⟩]⟩
theorem node317 : UpperPrefix a [2,3,7,6,8,1,4] 30 :=
  Boolean.leaf_sound a [2,3,7,6,8,1,4] 30 cert317 (by decide +kernel)

def cert318 : Leaf := ⟨⟨264,260,275,295,7,261,263,23,19⟩,[],[(3,1,0),(5,6,3)],⟨7,11,140,88,304,98,224,401,277⟩,⟨7,11,140,88,304,98,224,384,260⟩,[⟨6,1400107876328152533310767,⟨7,399,399,415,433,439,433,385,263⟩⟩,⟨7,1232538806359374089432325,⟨279,315,319,122,315,122,104,257,279⟩⟩,⟨4,1210109952366476541299973,⟨103,43,239,72,289,98,224,481,359⟩⟩]⟩
theorem node318 : UpperPrefix a [2,3,7,6,8,1,5] 30 :=
  Boolean.leaf_sound a [2,3,7,6,8,1,5] 30 cert318 (by decide +kernel)

theorem node319 : UpperPrefix a [2,3,7,6,8,1] 30 :=
  branch_upper a [2,3,7,6,8,1] 30 (by decide) (fin9_cases _
  node316
  (invalid_upper a [2,3,7,6,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,8,1,3] 30 (by decide +kernel))
  node317
  node318
  (invalid_upper a [2,3,7,6,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,8,1,8] 30 (by decide +kernel)))

#print axioms node319
end Delivery.FiniteExclusion.Sharp2x7
