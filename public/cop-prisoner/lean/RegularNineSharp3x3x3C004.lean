import RegularNineSharp3x3x3Base
import RegularNineSharp3x3x3C000
import RegularNineSharp3x3x3C002
import RegularNineSharp3x3x3C003
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x3x3
open Bounds BoundTreeRows Extremal
def cert256 : Leaf := ⟨⟨240,0,170,353,201,193,41,105,169⟩,[(1,4)],[(4,1,0),(2,4,1),(1,6,2)],⟨11,22,69,152,52,296,194,417,353⟩,⟨11,22,69,152,52,296,194,384,320⟩,[⟨8,1181889786609621300265,⟨79,22,69,223,55,127,194,128,64⟩⟩]⟩
theorem node256 : UpperPrefix a [3,4,6,7,2,8,1] 30 :=
  Boolean.leaf_sound a [3,4,6,7,2,8,1] 30 cert256 (by decide +kernel)

def cert257 : Leaf := ⟨⟨80,0,42,99,75,195,267,107,43⟩,[(1,4)],[(4,1,0),(2,4,1),(8,5,6)],⟨11,22,69,152,52,296,224,387,323⟩,⟨11,22,69,152,52,296,224,384,320⟩,[⟨7,1530047894502668212808745,⟨11,278,343,27,311,299,375,258,342⟩⟩,⟨5,1210107564157951779283977,⟨11,22,69,155,22,265,192,384,320⟩⟩]⟩
theorem node257 : UpperPrefix a [3,4,6,7,2,8,5] 30 :=
  Boolean.leaf_sound a [3,4,6,7,2,8,5] 30 cert257 (by decide +kernel)

theorem node258 : UpperPrefix a [3,4,6,7,2,8] 30 :=
  branch_upper a [3,4,6,7,2,8] 30 (by decide) (fin9_cases _
  node255
  node256
  (invalid_upper a [3,4,6,7,2,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,8,4] 30 (by decide +kernel))
  node257
  (invalid_upper a [3,4,6,7,2,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,8,8] 30 (by decide +kernel)))

theorem node259 : UpperPrefix a [3,4,6,7,2] 30 :=
  branch_upper a [3,4,6,7,2] 30 (by decide) (fin9_cases _
  node253
  node254
  (invalid_upper a [3,4,6,7,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,7] 30 (by decide +kernel))
  node258)

def cert260 : Leaf := ⟨⟨212,193,130,357,197,0,5,101,165⟩,[(5,0)],[(3,0,5),(4,1,0),(8,4,3),(1,6,2)],⟨11,22,69,152,304,41,194,420,356⟩,⟨11,22,69,152,304,41,194,384,320⟩,[⟨5,1210107708273139865891881,⟨79,22,69,223,279,79,194,384,320⟩⟩]⟩
theorem node260 : UpperPrefix a [3,4,6,7,8,0,1] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,0,1] 30 cert260 (by decide +kernel)

def cert261 : Leaf := ⟨⟨148,129,130,295,135,0,3,39,167⟩,[(5,0)],[(3,0,5),(4,1,0),(8,4,3)],⟨11,22,69,152,304,41,196,418,354⟩,⟨11,22,69,152,304,41,196,384,320⟩,[⟨6,1212467612202071711843655,⟨43,63,47,184,441,41,191,441,443⟩⟩,⟨5,1210107708273139865891881,⟨79,22,69,223,279,79,196,384,320⟩⟩]⟩
theorem node261 : UpperPrefix a [3,4,6,7,8,0,2] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,0,2] 30 cert261 (by decide +kernel)

def cert262 : Leaf := ⟨⟨212,225,130,327,199,0,7,69,135⟩,[(5,0)],[(3,0,5),(4,1,0),(8,4,3)],⟨11,22,69,152,304,41,224,386,324⟩,⟨11,22,69,152,304,41,224,386,320⟩,[⟨5,1531246931737161648571523,⟨139,415,325,153,272,9,453,395,324⟩⟩]⟩
theorem node262 : UpperPrefix a [3,4,6,7,8,0,5,1] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,0,5,1] 30 cert262 (by decide +kernel)

def cert263 : Leaf := ⟨⟨52,33,162,295,7,0,7,99,39⟩,[(5,0)],[(3,0,5),(4,1,0),(6,2,7),(8,4,3)],⟨11,22,69,152,304,41,224,388,322⟩,⟨11,22,69,152,304,41,224,388,320⟩,[⟨7,1530047894819602422631433,⟨43,278,375,59,304,41,370,278,336⟩⟩]⟩
theorem node263 : UpperPrefix a [3,4,6,7,8,0,5,2] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,0,5,2] 30 cert263 (by decide +kernel)

theorem node264 : UpperPrefix a [3,4,6,7,8,0,5] 30 :=
  branch_upper a [3,4,6,7,8,0,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,7,8,0,5,0] 30 (by decide +kernel))
  node262
  node263
  (invalid_upper a [3,4,6,7,8,0,5,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,0,5,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,0,5,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,0,5,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,0,5,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,0,5,8] 30 (by decide +kernel)))

theorem node265 : UpperPrefix a [3,4,6,7,8,0] 30 :=
  branch_upper a [3,4,6,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,7,8,0,0] 30 (by decide +kernel))
  node260
  node261
  (invalid_upper a [3,4,6,7,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,0,4] 30 (by decide +kernel))
  node264
  (invalid_upper a [3,4,6,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,0,8] 30 (by decide +kernel)))

def cert266 : Local := ⟨⟨0,232,0,358,206,0,46,110,174⟩,[(0,5),(2,6),(5,0)],[(4,1,0),(4,1,5),(8,4,3),(0,6,2)]⟩
theorem node266 : UpperPrefix a [3,4,6,7,8,1,0] 30 :=
  local_sound a [3,4,6,7,8,1,0] 30 cert266 (by decide +kernel)

def cert267 : Leaf := ⟨⟨0,169,170,291,139,0,43,43,171⟩,[(0,5),(5,0)],[(4,1,0),(4,1,5),(8,4,3)],⟨11,22,69,152,304,42,196,417,353⟩,⟨11,22,69,152,304,42,196,384,320⟩,[⟨2,1229199945506122476028963,⟨187,443,505,152,441,187,472,384,328⟩⟩,⟨6,1212615181088112075900263,⟨43,191,47,152,441,43,191,441,443⟩⟩]⟩
theorem node267 : UpperPrefix a [3,4,6,7,8,1,2] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,1,2] 30 cert267 (by decide +kernel)

def cert268 : Leaf := ⟨⟨0,105,10,327,79,0,15,79,15⟩,[(0,5),(5,0)],[(4,1,0),(4,1,5),(8,4,3)],⟨11,22,69,152,304,42,224,389,325⟩,⟨11,22,69,152,304,42,224,384,320⟩,[⟨5,1531874121035667773326371,⟨139,415,453,152,273,139,453,384,452⟩⟩,⟨7,1530047894538127462796321,⟨43,278,375,24,307,43,375,258,342⟩⟩]⟩
theorem node268 : UpperPrefix a [3,4,6,7,8,1,5] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,1,5] 30 cert268 (by decide +kernel)

theorem node269 : UpperPrefix a [3,4,6,7,8,1] 30 :=
  branch_upper a [3,4,6,7,8,1] 30 (by decide) (fin9_cases _
  node266
  (invalid_upper a [3,4,6,7,8,1,1] 30 (by decide +kernel))
  node267
  (invalid_upper a [3,4,6,7,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,1,4] 30 (by decide +kernel))
  node268
  (invalid_upper a [3,4,6,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,1,8] 30 (by decide +kernel)))

def cert270 : Leaf := ⟨⟨212,200,0,356,204,192,14,110,174⟩,[(2,6)],[(4,1,0),(8,4,3),(0,6,2)],⟨11,22,69,152,304,44,193,418,354⟩,⟨11,22,69,152,304,44,193,384,320⟩,[⟨1,1210107576710002308546561,⟨9,52,109,152,304,44,253,440,380⟩⟩,⟨5,1210107708273139882669097,⟨79,22,69,223,279,79,197,384,324⟩⟩]⟩
theorem node270 : UpperPrefix a [3,4,6,7,8,2,0] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,2,0] 30 cert270 (by decide +kernel)

def cert271 : Leaf := ⟨⟨212,200,138,324,204,192,13,76,172⟩,[],[(4,1,0),(8,4,3),(1,6,2)],⟨11,22,69,152,304,44,194,385,352⟩,⟨11,22,69,152,304,44,194,385,320⟩,[⟨5,1212616789726340040111227,⟨79,223,69,223,479,79,207,389,453⟩⟩,⟨0,1228997031358687685397504,⟨26,310,382,152,306,318,218,384,328⟩⟩]⟩
theorem node271 : UpperPrefix a [3,4,6,7,8,2,1,0] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,2,1,0] 30 cert271 (by decide +kernel)

def cert272 : Local := ⟨⟨212,201,138,357,0,193,13,0,141⟩,[(4,7),(7,4)],[(4,1,0),(8,4,3),(1,6,2),(5,7,3)]⟩
theorem node272 : UpperPrefix a [3,4,6,7,8,2,1,5] 30 :=
  local_sound a [3,4,6,7,8,2,1,5] 30 cert272 (by decide +kernel)

theorem node273 : UpperPrefix a [3,4,6,7,8,2,1] 30 :=
  branch_upper a [3,4,6,7,8,2,1] 30 (by decide) (fin9_cases _
  node271
  (invalid_upper a [3,4,6,7,8,2,1,1] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,2,1,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,2,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,2,1,4] 30 (by decide +kernel))
  node272
  (invalid_upper a [3,4,6,7,8,2,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,2,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,2,1,8] 30 (by decide +kernel)))

def cert274 : Leaf := ⟨⟨244,224,168,356,196,192,5,102,166⟩,[],[(4,1,0),(8,4,3)],⟨11,22,69,152,304,44,224,385,322⟩,⟨11,22,69,152,304,44,224,385,320⟩,[⟨0,1531228486266743025585152,⟨26,310,382,152,306,318,506,384,344⟩⟩,⟨1,1210110022481259336564737,⟨109,52,109,252,304,108,252,509,376⟩⟩,⟨3,1757939547252226249477121,⟨3,406,471,400,370,502,498,385,336⟩⟩]⟩
theorem node274 : UpperPrefix a [3,4,6,7,8,2,5,0] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,2,5,0] 30 cert274 (by decide +kernel)

def cert275 : Leaf := ⟨⟨208,225,138,323,195,195,7,65,131⟩,[],[(4,1,0),(8,4,3)],⟨11,22,69,152,304,44,224,386,321⟩,⟨11,22,69,152,304,44,224,386,320⟩,[⟨2,1531246932869667197289603,⟨139,411,345,153,304,312,505,395,344⟩⟩,⟨3,1229459064510499410428929,⟨131,470,325,208,498,502,242,386,320⟩⟩,⟨5,1531246931737161648571523,⟨139,415,325,153,272,268,453,395,324⟩⟩]⟩
theorem node275 : UpperPrefix a [3,4,6,7,8,2,5,1] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,2,5,1] 30 cert275 (by decide +kernel)

theorem node276 : UpperPrefix a [3,4,6,7,8,2,5] 30 :=
  branch_upper a [3,4,6,7,8,2,5] 30 (by decide) (fin9_cases _
  node274
  node275
  (invalid_upper a [3,4,6,7,8,2,5,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,2,5,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,2,5,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,2,5,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,2,5,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,2,5,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,2,5,8] 30 (by decide +kernel)))

theorem node277 : UpperPrefix a [3,4,6,7,8,2] 30 :=
  branch_upper a [3,4,6,7,8,2] 30 (by decide) (fin9_cases _
  node270
  node273
  (invalid_upper a [3,4,6,7,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,2,4] 30 (by decide +kernel))
  node276
  (invalid_upper a [3,4,6,7,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,2,8] 30 (by decide +kernel)))

theorem node278 : UpperPrefix a [3,4,6,7,8] 30 :=
  branch_upper a [3,4,6,7,8] 30 (by decide) (fin9_cases _
  node265
  node269
  node277
  (invalid_upper a [3,4,6,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,8] 30 (by decide +kernel)))

theorem node279 : UpperPrefix a [3,4,6,7] 30 :=
  branch_upper a [3,4,6,7] 30 (by decide) (fin9_cases _
  node246
  node252
  node259
  (invalid_upper a [3,4,6,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,7] 30 (by decide +kernel))
  node278)

def cert280 : Local := ⟨⟨500,0,418,0,458,322,290,98,162⟩,[(1,3),(3,1)],[(3,0,4),(4,1,0),(2,3,0),(0,4,1),(0,4,3)]⟩
theorem node280 : UpperPrefix a [3,4,6,2,0,7] 30 :=
  local_sound a [3,4,6,2,0,7] 30 cert280 (by decide +kernel)

def cert281 : Leaf := ⟨⟨52,33,290,102,14,322,294,102,166⟩,[],[(3,0,4),(4,1,0),(0,4,1)],⟨11,22,69,280,49,44,226,418,482⟩,⟨11,22,69,280,49,44,192,384,320⟩,[⟨7,1208926989741138273099241,⟨59,22,119,319,51,63,127,319,383⟩⟩,⟨6,1210106412364546102543393,⟨11,22,5,280,51,63,128,384,256⟩⟩,⟨8,1181745671421534684193,⟨11,22,69,24,51,63,192,128,64⟩⟩]⟩
theorem node281 : UpperPrefix a [3,4,6,8,0,2] 30 :=
  Boolean.leaf_sound a [3,4,6,8,0,2] 30 cert281 (by decide +kernel)

def cert282 : Leaf := ⟨⟨180,161,162,164,140,260,36,100,164⟩,[],[(3,0,4),(4,1,0),(8,3,5),(0,4,1),(1,6,2)],⟨11,22,69,280,49,168,194,420,356⟩,⟨11,22,69,280,49,168,194,384,320⟩,[⟨6,1210106419140063170399297,⟨11,22,55,280,49,168,187,440,313⟩⟩]⟩
theorem node282 : UpperPrefix a [3,4,6,8,0,7,1] 30 :=
  Boolean.leaf_sound a [3,4,6,8,0,7,1] 30 cert282 (by decide +kernel)

def cert283 : Leaf := ⟨⟨180,161,162,166,142,262,34,38,166⟩,[],[(3,0,4),(4,1,0),(8,3,5),(0,4,1)],⟨11,22,69,280,49,168,196,418,354⟩,⟨11,22,69,280,49,168,196,384,320⟩,[⟨6,1212467611679586792803649,⟨59,22,55,441,49,184,191,441,443⟩⟩]⟩
theorem node283 : UpperPrefix a [3,4,6,8,0,7,2] 30 :=
  Boolean.leaf_sound a [3,4,6,8,0,7,2] 30 cert283 (by decide +kernel)

def cert284 : Local := ⟨⟨116,97,34,102,78,326,0,102,38⟩,[(6,5)],[(3,0,4),(4,1,0),(8,3,5),(0,4,1),(7,5,6)]⟩
theorem node284 : UpperPrefix a [3,4,6,8,0,7,5] 30 :=
  local_sound a [3,4,6,8,0,7,5] 30 cert284 (by decide +kernel)

theorem node285 : UpperPrefix a [3,4,6,8,0,7] 30 :=
  branch_upper a [3,4,6,8,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,8,0,7,0] 30 (by decide +kernel))
  node282
  node283
  (invalid_upper a [3,4,6,8,0,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,0,7,4] 30 (by decide +kernel))
  node284
  (invalid_upper a [3,4,6,8,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,0,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,0,7,8] 30 (by decide +kernel)))

theorem node286 : UpperPrefix a [3,4,6,8,0] 30 :=
  branch_upper a [3,4,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,8,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut61 [3,4,6,8,0,1] [3,4,6,2,0,7] 30 (by decide +kernel) node280)
  node281
  (invalid_upper a [3,4,6,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,0,6] 30 (by decide +kernel))
  node285
  (invalid_upper a [3,4,6,8,0,8] 30 (by decide +kernel)))

def cert287 : Leaf := ⟨⟨372,289,288,101,261,0,293,101,165⟩,[(5,0)],[(3,0,5),(4,1,0)],⟨11,22,69,280,50,41,228,420,484⟩,⟨11,22,69,280,50,41,192,384,320⟩,[⟨1,1460882782392203984764929,⟨493,476,485,472,508,493,192,384,320⟩⟩,⟨7,1208926989776322645171689,⟨59,22,119,319,51,59,127,319,383⟩⟩,⟨6,1210106412397875048745985,⟨59,22,55,280,50,57,128,384,256⟩⟩]⟩
theorem node287 : UpperPrefix a [3,4,6,8,1,0] 30 :=
  Boolean.leaf_sound a [3,4,6,8,1,0] 30 cert287 (by decide +kernel)

def cert288 : Leaf := ⟨⟨212,200,0,228,204,324,12,108,172⟩,[(2,6)],[(4,1,0),(8,3,5),(0,6,2)],⟨11,22,69,280,50,168,193,420,356⟩,⟨11,22,69,280,50,168,193,384,320⟩,[⟨1,1546050535722711235428353,⟨493,508,485,312,440,168,485,384,452⟩⟩,⟨5,1210108140618704112071721,⟨11,22,69,287,87,207,197,384,324⟩⟩]⟩
theorem node288 : UpperPrefix a [3,4,6,8,1,7,0] 30 :=
  Boolean.leaf_sound a [3,4,6,8,1,7,0] 30 cert288 (by decide +kernel)

def cert289 : Leaf := ⟨⟨176,169,168,161,137,257,41,41,169⟩,[],[(4,1,0),(8,3,5)],⟨11,22,69,280,50,168,196,417,353⟩,⟨11,22,69,280,50,168,196,384,320⟩,[⟨1,1233765640764727137402881,⟨493,508,485,280,120,168,452,384,320⟩⟩,⟨2,1229126161766568544961555,⟨187,443,505,441,187,168,488,384,352⟩⟩,⟨6,1212541398681720154262849,⟨187,22,55,441,50,168,191,441,443⟩⟩]⟩
theorem node289 : UpperPrefix a [3,4,6,8,1,7,2] 30 :=
  Boolean.leaf_sound a [3,4,6,8,1,7,2] 30 cert289 (by decide +kernel)

def cert290 : Leaf := ⟨⟨84,105,40,69,77,325,0,77,13⟩,[(6,5)],[(4,1,0),(8,3,5),(7,5,6)],⟨11,22,69,280,50,168,224,389,325⟩,⟨11,22,69,280,50,168,224,384,320⟩,[⟨1,1233766217225479440826369,⟨493,508,485,280,120,232,224,384,320⟩⟩,⟨5,1229052370321651757220883,⟨139,415,453,281,155,136,192,384,320⟩⟩]⟩
theorem node290 : UpperPrefix a [3,4,6,8,1,7,5] 30 :=
  Boolean.leaf_sound a [3,4,6,8,1,7,5] 30 cert290 (by decide +kernel)

theorem node291 : UpperPrefix a [3,4,6,8,1,7] 30 :=
  branch_upper a [3,4,6,8,1,7] 30 (by decide) (fin9_cases _
  node288
  (invalid_upper a [3,4,6,8,1,7,1] 30 (by decide +kernel))
  node289
  (invalid_upper a [3,4,6,8,1,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,1,7,4] 30 (by decide +kernel))
  node290
  (invalid_upper a [3,4,6,8,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,1,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,1,7,8] 30 (by decide +kernel)))

theorem node292 : UpperPrefix a [3,4,6,8,1] 30 :=
  branch_upper a [3,4,6,8,1] 30 (by decide) (fin9_cases _
  node287
  (invalid_upper a [3,4,6,8,1,1] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut97 [3,4,6,8,1,2] [3,4,6,0,7,2] 30 (by decide +kernel) node183)
  (invalid_upper a [3,4,6,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,1,6] 30 (by decide +kernel))
  node291
  (invalid_upper a [3,4,6,8,1,8] 30 (by decide +kernel)))

def cert293 : Leaf := ⟨⟨0,0,298,99,331,0,299,107,171⟩,[(0,5),(1,4),(5,0)],[(4,1,0),(4,1,5),(2,4,1)],⟨11,22,69,280,52,42,225,417,481⟩,⟨11,22,69,280,52,42,192,384,320⟩,[⟨7,1208926989774054902447593,⟨59,22,119,319,55,59,127,319,383⟩⟩]⟩
theorem node293 : UpperPrefix a [3,4,6,8,2,1] 30 :=
  Boolean.leaf_sound a [3,4,6,8,2,1] 30 cert293 (by decide +kernel)

def cert294 : Leaf := ⟨⟨16,0,170,227,139,259,43,43,171⟩,[(1,4)],[(4,1,0),(8,3,5),(2,4,1)],⟨11,22,69,280,52,168,227,419,355⟩,⟨11,22,69,280,52,168,192,384,320⟩,[⟨6,1210180199655576144194569,⟨171,22,55,443,54,169,128,384,256⟩⟩,⟨5,1210107564157951779283977,⟨11,22,69,283,22,137,192,384,320⟩⟩,⟨7,1208926973663134274823177,⟨11,22,69,283,54,41,64,256,320⟩⟩]⟩
theorem node294 : UpperPrefix a [3,4,6,8,2,7] 30 :=
  Boolean.leaf_sound a [3,4,6,8,2,7] 30 cert294 (by decide +kernel)

theorem node295 : UpperPrefix a [3,4,6,8,2] 30 :=
  branch_upper a [3,4,6,8,2] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut79 [3,4,6,8,2,0] [3,4,6,7,2,0] 30 (by decide +kernel) node253)
  node293
  (invalid_upper a [3,4,6,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,2,6] 30 (by decide +kernel))
  node294
  (invalid_upper a [3,4,6,8,2,8] 30 (by decide +kernel)))

def cert296 : Leaf := ⟨⟨340,321,258,101,325,0,261,101,37⟩,[(5,0)],[(3,0,5),(4,1,0),(1,6,2)],⟨11,22,69,280,176,41,194,420,356⟩,⟨11,22,69,280,176,41,194,384,320⟩,[⟨7,1530047897137098408334443,⟨43,319,357,319,49,43,367,260,357⟩⟩,⟨5,1210107852388327937291305,⟨15,86,69,351,215,15,194,384,320⟩⟩]⟩
theorem node296 : UpperPrefix a [3,4,6,8,7,0,1] 30 :=
  Boolean.leaf_sound a [3,4,6,8,7,0,1] 30 cert296 (by decide +kernel)

def cert297 : Leaf := ⟨⟨148,129,130,167,263,0,3,39,167⟩,[(5,0)],[(3,0,5),(4,1,0)],⟨11,22,69,280,176,41,196,418,354⟩,⟨11,22,69,280,176,41,196,384,320⟩,[⟨6,1212467611714427567508801,⟨59,22,55,441,184,57,191,441,443⟩⟩,⟨5,1210107852388327937291305,⟨15,86,69,351,215,15,196,384,320⟩⟩,⟨8,1182034216258018227241,⟨47,86,101,127,247,47,196,128,64⟩⟩]⟩
theorem node297 : UpperPrefix a [3,4,6,8,7,0,2] 30 :=
  Boolean.leaf_sound a [3,4,6,8,7,0,2] 30 cert297 (by decide +kernel)

def cert298 : Leaf := ⟨⟨500,480,418,230,0,0,0,102,166⟩,[(4,6),(5,0),(6,4)],[(3,0,5),(4,1,0)],⟨11,22,69,280,176,41,224,390,326⟩,⟨11,22,69,280,176,41,224,384,320⟩,[⟨0,1238497392648100049325056,⟨394,478,478,344,240,40,240,392,344⟩⟩]⟩
theorem node298 : UpperPrefix a [3,4,6,8,7,0,5] 30 :=
  Boolean.leaf_sound a [3,4,6,8,7,0,5] 30 cert298 (by decide +kernel)

theorem node299 : UpperPrefix a [3,4,6,8,7,0] 30 :=
  branch_upper a [3,4,6,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,8,7,0,0] 30 (by decide +kernel))
  node296
  node297
  (invalid_upper a [3,4,6,8,7,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,0,4] 30 (by decide +kernel))
  node298
  (invalid_upper a [3,4,6,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,0,8] 30 (by decide +kernel)))

def cert300 : Local := ⟨⟨0,488,0,230,334,0,302,110,174⟩,[(0,5),(2,6),(5,0)],[(4,1,0),(4,1,5),(0,6,2)]⟩
theorem node300 : UpperPrefix a [3,4,6,8,7,1,0] 30 :=
  local_sound a [3,4,6,8,7,1,0] 30 cert300 (by decide +kernel)

def cert301 : Leaf := ⟨⟨0,424,426,162,266,0,299,43,171⟩,[(0,5),(5,0)],[(4,1,0),(4,1,5)],⟨11,22,69,280,176,42,196,417,353⟩,⟨11,22,69,280,176,42,196,384,320⟩,[⟨2,1229052371555793965679651,⟨187,443,505,280,177,187,472,384,328⟩⟩,⟨6,1212541393907915544366433,⟨187,22,55,441,185,187,191,441,443⟩⟩,⟨0,1210107576591280805809152,⟨42,22,118,312,184,42,254,440,378⟩⟩]⟩
theorem node301 : UpperPrefix a [3,4,6,8,7,1,2] 30 :=
  Boolean.leaf_sound a [3,4,6,8,7,1,2] 30 cert301 (by decide +kernel)

def cert302 : Local := ⟨⟨0,489,426,231,0,0,0,111,175⟩,[(0,5),(4,6),(5,0),(6,4)],[(4,1,0),(4,1,5)]⟩
theorem node302 : UpperPrefix a [3,4,6,8,7,1,5] 30 :=
  local_sound a [3,4,6,8,7,1,5] 30 cert302 (by decide +kernel)

theorem node303 : UpperPrefix a [3,4,6,8,7,1] 30 :=
  branch_upper a [3,4,6,8,7,1] 30 (by decide) (fin9_cases _
  node300
  (invalid_upper a [3,4,6,8,7,1,1] 30 (by decide +kernel))
  node301
  (invalid_upper a [3,4,6,8,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,1,4] 30 (by decide +kernel))
  node302
  (invalid_upper a [3,4,6,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,1,8] 30 (by decide +kernel)))

def cert304 : Leaf := ⟨⟨212,200,0,228,76,192,14,110,174⟩,[(2,6)],[(4,1,0),(0,6,2)],⟨11,22,69,280,176,44,193,418,354⟩,⟨11,22,69,280,176,44,193,384,320⟩,[⟨8,1182034220656081681449,⟨47,86,119,127,247,47,247,130,86⟩⟩,⟨1,1210107576556096450461697,⟨9,20,117,312,184,44,253,440,380⟩⟩,⟨5,1210107852388327954068521,⟨15,86,69,351,215,15,197,384,324⟩⟩]⟩
theorem node304 : UpperPrefix a [3,4,6,8,7,2,0] 30 :=
  Boolean.leaf_sound a [3,4,6,8,7,2,0] 30 cert304 (by decide +kernel)

def cert305 : Leaf := ⟨⟨116,104,42,100,76,64,45,108,44⟩,[],[(4,1,0),(1,6,2)],⟨11,22,69,280,176,44,194,385,352⟩,⟨11,22,69,280,176,44,194,385,320⟩,[⟨7,1530047897101914036245611,⟨43,319,357,319,49,303,367,261,357⟩⟩,⟨8,1184340068063358596137,⟨47,86,103,127,247,47,214,247,66⟩⟩,⟨0,1531228486334535594675200,⟨42,318,382,280,176,302,506,392,344⟩⟩]⟩
theorem node305 : UpperPrefix a [3,4,6,8,7,2,1,0] 30 :=
  Boolean.leaf_sound a [3,4,6,8,7,2,1,0] 30 cert305 (by decide +kernel)

def cert306 : Leaf := ⟨⟨340,329,266,69,0,321,269,77,13⟩,[(4,7)],[(4,1,0),(1,6,2),(5,7,4)],⟨11,22,69,280,176,44,194,416,321⟩,⟨11,22,69,280,176,44,194,416,320⟩,[⟨7,1530047897101914036245611,⟨43,319,357,319,49,303,367,293,357⟩⟩]⟩
theorem node306 : UpperPrefix a [3,4,6,8,7,2,1,5] 30 :=
  Boolean.leaf_sound a [3,4,6,8,7,2,1,5] 30 cert306 (by decide +kernel)

theorem node307 : UpperPrefix a [3,4,6,8,7,2,1] 30 :=
  branch_upper a [3,4,6,8,7,2,1] 30 (by decide) (fin9_cases _
  node305
  (invalid_upper a [3,4,6,8,7,2,1,1] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,2,1,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,2,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,2,1,4] 30 (by decide +kernel))
  node306
  (invalid_upper a [3,4,6,8,7,2,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,2,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,2,1,8] 30 (by decide +kernel)))

def cert308 : Leaf := ⟨⟨240,225,170,227,0,195,0,99,163⟩,[(4,6),(6,4)],[(4,1,0)],⟨11,22,69,280,176,44,224,387,323⟩,⟨11,22,69,280,176,44,224,384,320⟩,[⟨2,1219580256600510366221315,⟨395,475,209,344,240,40,240,392,344⟩⟩,⟨8,1182034220656081681449,⟨47,86,119,127,247,47,247,130,86⟩⟩,⟨3,1229034789401202137254913,⟨3,470,471,336,242,502,242,384,336⟩⟩]⟩
theorem node308 : UpperPrefix a [3,4,6,8,7,2,5] 30 :=
  Boolean.leaf_sound a [3,4,6,8,7,2,5] 30 cert308 (by decide +kernel)

theorem node309 : UpperPrefix a [3,4,6,8,7,2] 30 :=
  branch_upper a [3,4,6,8,7,2] 30 (by decide) (fin9_cases _
  node304
  node307
  (invalid_upper a [3,4,6,8,7,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,2,4] 30 (by decide +kernel))
  node308
  (invalid_upper a [3,4,6,8,7,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,2,8] 30 (by decide +kernel)))

theorem node310 : UpperPrefix a [3,4,6,8,7] 30 :=
  branch_upper a [3,4,6,8,7] 30 (by decide) (fin9_cases _
  node299
  node303
  node309
  (invalid_upper a [3,4,6,8,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,8] 30 (by decide +kernel)))

theorem node311 : UpperPrefix a [3,4,6,8] 30 :=
  branch_upper a [3,4,6,8] 30 (by decide) (fin9_cases _
  node286
  node292
  node295
  (invalid_upper a [3,4,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,6] 30 (by decide +kernel))
  node310
  (invalid_upper a [3,4,6,8,8] 30 (by decide +kernel)))

theorem node312 : UpperPrefix a [3,4,6] 30 :=
  branch_upper a [3,4,6] 30 (by decide) (fin9_cases _
  node196
  node213
  node223
  (invalid_upper a [3,4,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,4] 30 (by decide +kernel))
  node237
  (invalid_upper a [3,4,6,6] 30 (by decide +kernel))
  node279
  node311)

theorem node313 : UpperPrefix a [3,4] 30 :=
  branch_upper a [3,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut18 [3,4,1] [2,3,4] 30 (by decide +kernel) node20)
  (invalid_upper a [3,4,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,4] 30 (by decide +kernel))
  node174
  node312
  (PrefixConjugacy.upper aut2 [3,4,7] [3,4,6] 30 (by decide +kernel) node312)
  (PrefixConjugacy.upper aut1 [3,4,8] [3,4,6] 30 (by decide +kernel) node312))

def cert314 : Leaf := ⟨⟨404,401,0,0,454,471,262,70,134⟩,[(2,3),(3,2)],[],⟨11,38,21,25,502,494,454,454,454⟩,⟨11,38,21,25,48,40,192,384,320⟩,[⟨3,1375713840711862408463361,⟨471,502,469,469,498,502,192,384,320⟩⟩,⟨0,1219570781022599144014848,⟨474,502,20,24,48,40,192,384,320⟩⟩,⟨5,1224302387765867346658307,⟨463,463,477,477,16,12,192,384,320⟩⟩,⟨4,1219570781021362193433601,⟨459,486,5,9,32,40,192,384,320⟩⟩,⟨6,1210106412362349769942079,⟨15,47,31,31,63,47,128,384,256⟩⟩]⟩
theorem node314 : UpperPrefix a [3,5,4,0] 30 :=
  Boolean.leaf_sound a [3,5,4,0] 30 cert314 (by decide +kernel)

def cert315 : Leaf := ⟨⟨0,25,8,37,461,469,261,69,133⟩,[(0,3)],[(5,1,3),(1,3,0)],⟨11,38,21,26,501,493,453,453,453⟩,⟨11,38,21,26,48,40,192,384,320⟩,[⟨3,1229033996761070650262529,⟨3,486,469,18,48,32,192,384,320⟩⟩,⟨4,1229033996759972212376585,⟨11,486,453,11,32,41,192,384,320⟩⟩,⟨6,1210106412362349769942079,⟨15,47,31,31,63,47,128,384,256⟩⟩,⟨7,1208926973663136965485631,⟨15,47,31,31,63,47,64,256,320⟩⟩,⟨8,1181745669225202082879,⟨15,47,31,31,63,47,192,128,64⟩⟩]⟩
theorem node315 : UpperPrefix a [3,5,4,1] 30 :=
  Boolean.leaf_sound a [3,5,4,1] 30 cert315 (by decide +kernel)

def cert316 : Leaf := ⟨⟨260,265,298,0,459,451,259,67,131⟩,[(3,2)],[(4,2,3),(2,3,0)],⟨11,38,21,28,499,491,451,451,451⟩,⟨11,38,21,28,48,40,192,384,320⟩,[⟨5,1224302387765867344561155,⟨459,463,477,28,16,8,192,384,320⟩⟩,⟨3,1214839173153155621848065,⟨451,38,469,20,48,32,192,384,320⟩⟩,⟨6,1210106412362349769942079,⟨15,47,31,31,63,47,128,384,256⟩⟩,⟨7,1208926973663136965485631,⟨15,47,31,31,63,47,64,256,320⟩⟩]⟩
theorem node316 : UpperPrefix a [3,5,4,2] 30 :=
  Boolean.leaf_sound a [3,5,4,2] 30 cert316 (by decide +kernel)

def cert317 : Leaf := ⟨⟨308,272,0,422,270,470,262,70,134⟩,[(2,4)],[(3,0,4),(0,4,2)],⟨11,38,21,88,49,430,454,390,454⟩,⟨11,38,21,88,49,40,192,384,320⟩,[⟨4,1219570781021362193433601,⟨459,486,5,72,33,40,192,384,320⟩⟩,⟨5,1219570779896561802413057,⟨459,454,21,92,21,8,192,384,320⟩⟩,⟨6,1210106412364683556971561,⟨31,55,23,31,55,63,128,384,256⟩⟩,⟨7,1208926973665470752515113,⟨31,55,23,95,55,63,64,256,320⟩⟩]⟩
theorem node317 : UpperPrefix a [3,5,4,6,0] 30 :=
  Boolean.leaf_sound a [3,5,4,6,0] 30 cert317 (by decide +kernel)

def cert318 : Leaf := ⟨⟨276,281,258,389,0,469,261,69,133⟩,[(4,1)],[(5,1,4),(1,4,2)],⟨11,38,21,88,50,429,453,389,453⟩,⟨11,38,21,88,50,40,192,384,320⟩,[⟨3,1233765604630513098949633,⟨471,502,469,80,50,32,192,384,320⟩⟩,⟨4,1229033996759972212376577,⟨11,486,453,72,34,40,192,384,320⟩⟩,⟨6,1210106412364683556971561,⟨31,55,23,31,55,63,128,384,256⟩⟩,⟨7,1208926973665470752515113,⟨31,55,23,95,55,63,64,256,320⟩⟩]⟩
theorem node318 : UpperPrefix a [3,5,4,6,1] 30 :=
  Boolean.leaf_sound a [3,5,4,6,1] 30 cert318 (by decide +kernel)

def cert319 : Leaf := ⟨⟨448,0,490,387,0,451,267,75,139⟩,[(1,4),(4,1)],[],⟨11,38,21,88,52,427,451,387,451⟩,⟨11,38,21,88,52,40,192,384,320⟩,[⟨2,1224302388997320366621699,⟨491,491,505,88,56,40,192,384,320⟩⟩,⟨4,1271618467900376646429705,⟨491,486,487,491,486,489,192,384,320⟩⟩,⟨5,1224302387765867344561155,⟨459,463,477,88,28,8,192,384,320⟩⟩]⟩
theorem node319 : UpperPrefix a [3,5,4,6,2] 30 :=
  Boolean.leaf_sound a [3,5,4,6,2] 30 cert319 (by decide +kernel)

#print axioms node319
end Delivery.FiniteExclusion.Sharp3x3x3
