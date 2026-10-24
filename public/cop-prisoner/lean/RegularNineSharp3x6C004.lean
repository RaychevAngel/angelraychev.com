import RegularNineSharp3x6Base
import RegularNineSharp3x6C003
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
def cert256 : Local := ⟨⟨0,433,314,417,0,0,315,59,179⟩,[(0,1),(4,5),(5,4)],[(2,0,0),(6,4,4),(6,4,5)]⟩
theorem node256 : UpperPrefix a [2,3,7,1,6,4] 30 :=
  local_sound a [2,3,7,1,6,4] 30 cert256 (by decide +kernel)

def cert257 : Local := ⟨⟨0,433,0,417,0,155,0,59,179⟩,[(0,1),(2,6),(4,5),(6,2)],[(2,0,0),(6,4,4)]⟩
theorem node257 : UpperPrefix a [2,3,7,1,6,8,0] 30 :=
  local_sound a [2,3,7,1,6,8,0] 30 cert257 (by decide +kernel)

def cert258 : Leaf := ⟨⟨0,432,314,416,0,154,298,59,179⟩,[(0,1),(4,5)],[(2,0,0),(6,4,4)],⟨7,14,133,26,112,352,208,417,297⟩,⟨7,14,133,26,112,352,208,384,264⟩,[⟨0,1210109947703723545333248,⟨94,94,254,26,112,368,240,496,264⟩⟩]⟩
theorem node258 : UpperPrefix a [2,3,7,1,6,8,4] 30 :=
  Boolean.leaf_sound a [2,3,7,1,6,8,4] 30 cert258 (by decide +kernel)

def cert259 : Local := ⟨⟨0,145,26,129,0,155,283,27,147⟩,[(0,1),(4,5)],[(2,0,0),(6,4,4),(8,5,6),(5,6,4)]⟩
theorem node259 : UpperPrefix a [2,3,7,1,6,8,5] 30 :=
  local_sound a [2,3,7,1,6,8,5] 30 cert259 (by decide +kernel)

theorem node260 : UpperPrefix a [2,3,7,1,6,8] 30 :=
  branch_upper a [2,3,7,1,6,8] 30 (by decide) (fin9_cases _
  node257
  (invalid_upper a [2,3,7,1,6,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,6,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,6,8,3] 30 (by decide +kernel))
  node258
  node259
  (invalid_upper a [2,3,7,1,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,6,8,8] 30 (by decide +kernel)))

theorem node261 : UpperPrefix a [2,3,7,1,6] 30 :=
  branch_upper a [2,3,7,1,6] 30 (by decide) (fin9_cases _
  node255
  (invalid_upper a [2,3,7,1,6,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,6,3] 30 (by decide +kernel))
  node256
  (invalid_upper a [2,3,7,1,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,6,7] 30 (by decide +kernel))
  node260)

def cert262 : Leaf := ⟨⟨0,241,112,225,193,144,289,113,241⟩,[(0,1)],[(2,0,0),(8,4,6)],⟨7,14,133,26,304,97,208,480,360⟩,⟨7,14,133,26,304,97,208,384,264⟩,[⟨1,1219728677401525342175233,⟨501,508,245,472,500,245,208,384,328⟩⟩,⟨3,1212623753971414202319883,⟨103,103,245,247,500,97,208,500,501⟩⟩]⟩
theorem node262 : UpperPrefix a [2,3,7,1,8,0,4] 30 :=
  Boolean.leaf_sound a [2,3,7,1,8,0,4] 30 cert262 (by decide +kernel)

def cert263 : Leaf := ⟨⟨0,497,368,481,193,400,272,112,240⟩,[(0,1)],[(2,0,0)],⟨7,14,133,26,304,97,224,464,344⟩,⟨7,14,133,26,304,97,224,384,264⟩,[⟨1,1257581252125589266235393,⟨501,508,245,472,500,245,228,384,392⟩⟩,⟨3,1212623753971414202319883,⟨103,103,245,247,500,97,240,500,501⟩⟩,⟨0,1248108146306069514159104,⟨6,398,132,474,496,96,224,384,392⟩⟩]⟩
theorem node263 : UpperPrefix a [2,3,7,1,8,0,5] 30 :=
  Boolean.leaf_sound a [2,3,7,1,8,0,5] 30 cert263 (by decide +kernel)

theorem node264 : UpperPrefix a [2,3,7,1,8,0] 30 :=
  branch_upper a [2,3,7,1,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,1,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,8,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,8,0,3] 30 (by decide +kernel))
  node262
  node263
  (invalid_upper a [2,3,7,1,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,8,0,8] 30 (by decide +kernel)))

def cert265 : Leaf := ⟨⟨0,497,0,481,201,393,0,121,241⟩,[(0,1),(2,6),(6,2)],[(2,0,0)],⟨7,14,133,26,304,112,193,480,360⟩,⟨7,14,133,26,304,112,193,384,264⟩,[⟨1,1219580060936540437872641,⟨501,508,245,440,304,116,245,384,280⟩⟩]⟩
theorem node265 : UpperPrefix a [2,3,7,1,8,4,0] 30 :=
  Boolean.leaf_sound a [2,3,7,1,8,4,0] 30 cert265 (by decide +kernel)

def cert266 : Leaf := ⟨⟨0,448,330,448,202,394,266,75,195⟩,[(0,1)],[(2,0,0),(5,6,5)],⟨7,14,133,26,304,112,224,449,329⟩,⟨7,14,133,26,304,112,224,384,264⟩,[⟨0,1210109950089388497047040,⟨110,110,254,26,304,112,240,496,264⟩⟩,⟨4,1248108722765722438735259,⟨7,399,133,463,487,229,229,391,399⟩⟩]⟩
theorem node266 : UpperPrefix a [2,3,7,1,8,4,5] 30 :=
  Boolean.leaf_sound a [2,3,7,1,8,4,5] 30 cert266 (by decide +kernel)

theorem node267 : UpperPrefix a [2,3,7,1,8,4] 30 :=
  branch_upper a [2,3,7,1,8,4] 30 (by decide) (fin9_cases _
  node265
  (invalid_upper a [2,3,7,1,8,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,8,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,8,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,8,4,4] 30 (by decide +kernel))
  node266
  (invalid_upper a [2,3,7,1,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,8,4,8] 30 (by decide +kernel)))

theorem node268 : UpperPrefix a [2,3,7,1,8] 30 :=
  branch_upper a [2,3,7,1,8] 30 (by decide) (fin9_cases _
  node264
  (invalid_upper a [2,3,7,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,8,3] 30 (by decide +kernel))
  node267
  (invalid_upper a [2,3,7,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,8,8] 30 (by decide +kernel)))

theorem node269 : UpperPrefix a [2,3,7,1] 30 :=
  branch_upper a [2,3,7,1] 30 (by decide) (fin9_cases _
  node254
  (invalid_upper a [2,3,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,5] 30 (by decide +kernel))
  node261
  (invalid_upper a [2,3,7,1,7] 30 (by decide +kernel))
  node268)

def cert270 : Leaf := ⟨⟨0,465,344,0,458,408,280,88,208⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3),(1,5,4)],⟨7,14,133,56,49,98,464,464,344⟩,⟨7,14,133,56,49,98,192,384,264⟩,[⟨0,1323666154217542805095424,⟨38,494,132,504,504,98,192,384,456⟩⟩]⟩
theorem node270 : UpperPrefix a [2,3,7,5,0,1] 30 :=
  Boolean.leaf_sound a [2,3,7,5,0,1] 30 cert270 (by decide +kernel)

def cert271 : Local := ⟨⟨0,449,330,0,458,395,267,75,195⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3),(4,5,3)]⟩
theorem node271 : UpperPrefix a [2,3,7,5,0,4] 30 :=
  local_sound a [2,3,7,5,0,4] 30 cert271 (by decide +kernel)

def cert272 : Leaf := ⟨⟨0,401,274,0,386,155,281,83,211⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3)],⟨7,14,133,56,49,352,194,464,344⟩,⟨7,14,133,56,49,352,194,384,264⟩,[⟨3,1210402713191229017818179,⟨7,7,133,180,181,501,199,384,256⟩⟩,⟨6,1210106412365102317585507,⟨7,31,133,59,59,319,135,384,280⟩⟩]⟩
theorem node272 : UpperPrefix a [2,3,7,5,0,8,1] 30 :=
  Boolean.leaf_sound a [2,3,7,5,0,8,1] 30 cert272 (by decide +kernel)

def cert273 : Leaf := ⟨⟨0,385,266,0,394,155,267,75,211⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3)],⟨7,14,133,56,49,352,208,450,330⟩,⟨7,14,133,56,49,352,208,384,264⟩,[⟨4,1210402713187931592463787,⟨7,15,133,175,165,487,197,391,271⟩⟩,⟨6,1210106412365102317618275,⟨7,31,133,59,59,319,159,384,280⟩⟩]⟩
theorem node273 : UpperPrefix a [2,3,7,5,0,8,4] 30 :=
  Boolean.leaf_sound a [2,3,7,5,0,8,4] 30 cert273 (by decide +kernel)

theorem node274 : UpperPrefix a [2,3,7,5,0,8] 30 :=
  branch_upper a [2,3,7,5,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,5,0,8,0] 30 (by decide +kernel))
  node272
  (invalid_upper a [2,3,7,5,0,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,0,8,3] 30 (by decide +kernel))
  node273
  (invalid_upper a [2,3,7,5,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,0,8,8] 30 (by decide +kernel)))

theorem node275 : UpperPrefix a [2,3,7,5,0] 30 :=
  branch_upper a [2,3,7,5,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,5,0,0] 30 (by decide +kernel))
  node270
  (invalid_upper a [2,3,7,5,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,0,3] 30 (by decide +kernel))
  node271
  (invalid_upper a [2,3,7,5,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,0,7] 30 (by decide +kernel))
  node274)

def cert276 : Leaf := ⟨⟨0,209,90,0,201,154,282,90,210⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3)],⟨7,14,133,56,50,97,464,464,344⟩,⟨7,14,133,56,50,97,192,384,264⟩,[⟨8,1181747928184199890019,⟨7,31,133,59,59,127,255,128,24⟩⟩,⟨0,1323666154147174060917760,⟨6,462,132,504,506,96,192,384,456⟩⟩]⟩
theorem node276 : UpperPrefix a [2,3,7,5,1,0] 30 :=
  Boolean.leaf_sound a [2,3,7,5,1,0] 30 cert276 (by decide +kernel)

def cert277 : Local := ⟨⟨0,449,330,0,457,395,267,75,195⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3),(4,5,3)]⟩
theorem node277 : UpperPrefix a [2,3,7,5,1,4] 30 :=
  local_sound a [2,3,7,5,1,4] 30 cert277 (by decide +kernel)

def cert278 : Local := ⟨⟨0,465,0,0,457,155,0,91,211⟩,[(0,1),(2,6),(3,4),(6,2)],[(2,0,0),(5,3,3)]⟩
theorem node278 : UpperPrefix a [2,3,7,5,1,8,0] 30 :=
  local_sound a [2,3,7,5,1,8,0] 30 cert278 (by decide +kernel)

def cert279 : Leaf := ⟨⟨0,385,266,0,393,155,267,75,211⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3)],⟨7,14,133,56,50,352,208,449,329⟩,⟨7,14,133,56,50,352,208,384,264⟩,[⟨4,1210402713187931592463803,⟨7,15,133,175,167,487,197,391,271⟩⟩,⟨6,1210106412365102317618275,⟨7,31,133,59,59,319,159,384,280⟩⟩]⟩
theorem node279 : UpperPrefix a [2,3,7,5,1,8,4] 30 :=
  Boolean.leaf_sound a [2,3,7,5,1,8,4] 30 cert279 (by decide +kernel)

theorem node280 : UpperPrefix a [2,3,7,5,1,8] 30 :=
  branch_upper a [2,3,7,5,1,8] 30 (by decide) (fin9_cases _
  node278
  (invalid_upper a [2,3,7,5,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,1,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,1,8,3] 30 (by decide +kernel))
  node279
  (invalid_upper a [2,3,7,5,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,1,8,8] 30 (by decide +kernel)))

theorem node281 : UpperPrefix a [2,3,7,5,1] 30 :=
  branch_upper a [2,3,7,5,1] 30 (by decide) (fin9_cases _
  node276
  (invalid_upper a [2,3,7,5,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,1,3] 30 (by decide +kernel))
  node277
  (invalid_upper a [2,3,7,5,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,1,7] 30 (by decide +kernel))
  node280)

def cert282 : Local := ⟨⟨0,401,282,0,0,411,283,27,147⟩,[(0,1),(3,4),(4,5)],[(2,0,0),(5,3,3),(6,4,3),(6,4,4)]⟩
theorem node282 : UpperPrefix a [2,3,7,5,6] 30 :=
  local_sound a [2,3,7,5,6] 30 cert282 (by decide +kernel)

def cert283 : Local := ⟨⟨0,465,344,0,201,410,281,89,209⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3),(1,6,5)]⟩
theorem node283 : UpperPrefix a [2,3,7,5,8,0,1] 30 :=
  local_sound a [2,3,7,5,8,0,1] 30 cert283 (by decide +kernel)

def cert284 : Leaf := ⟨⟨0,145,26,0,203,154,267,91,211⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3),(8,4,6)],⟨7,14,133,56,304,97,208,450,330⟩,⟨7,14,133,56,304,97,208,384,264⟩,[⟨6,1210106412362349243565155,⟨7,15,133,57,313,39,159,384,264⟩⟩]⟩
theorem node284 : UpperPrefix a [2,3,7,5,8,0,4] 30 :=
  Boolean.leaf_sound a [2,3,7,5,8,0,4] 30 cert284 (by decide +kernel)

theorem node285 : UpperPrefix a [2,3,7,5,8,0] 30 :=
  branch_upper a [2,3,7,5,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,5,8,0,0] 30 (by decide +kernel))
  node283
  (invalid_upper a [2,3,7,5,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,8,0,3] 30 (by decide +kernel))
  node284
  (invalid_upper a [2,3,7,5,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,8,0,8] 30 (by decide +kernel)))

def cert286 : Local := ⟨⟨0,465,0,0,203,409,0,91,211⟩,[(0,1),(2,6),(3,4),(6,2)],[(2,0,0),(5,3,3)]⟩
theorem node286 : UpperPrefix a [2,3,7,5,8,1,0] 30 :=
  local_sound a [2,3,7,5,8,1,0] 30 cert286 (by decide +kernel)

def cert287 : Leaf := ⟨⟨0,145,26,0,203,153,267,91,211⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3),(8,4,6)],⟨7,14,133,56,304,98,208,449,329⟩,⟨7,14,133,56,304,98,208,384,264⟩,[⟨6,1210106412362349243565155,⟨7,15,133,57,313,39,159,384,264⟩⟩]⟩
theorem node287 : UpperPrefix a [2,3,7,5,8,1,4] 30 :=
  Boolean.leaf_sound a [2,3,7,5,8,1,4] 30 cert287 (by decide +kernel)

theorem node288 : UpperPrefix a [2,3,7,5,8,1] 30 :=
  branch_upper a [2,3,7,5,8,1] 30 (by decide) (fin9_cases _
  node286
  (invalid_upper a [2,3,7,5,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,8,1,3] 30 (by decide +kernel))
  node287
  (invalid_upper a [2,3,7,5,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,8,1,8] 30 (by decide +kernel)))

def cert289 : Local := ⟨⟨0,449,330,0,203,395,267,75,195⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3),(4,5,3)]⟩
theorem node289 : UpperPrefix a [2,3,7,5,8,4] 30 :=
  local_sound a [2,3,7,5,8,4] 30 cert289 (by decide +kernel)

theorem node290 : UpperPrefix a [2,3,7,5,8] 30 :=
  branch_upper a [2,3,7,5,8] 30 (by decide) (fin9_cases _
  node285
  node288
  (invalid_upper a [2,3,7,5,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,8,3] 30 (by decide +kernel))
  node289
  (invalid_upper a [2,3,7,5,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,8,8] 30 (by decide +kernel)))

theorem node291 : UpperPrefix a [2,3,7,5] 30 :=
  branch_upper a [2,3,7,5] 30 (by decide) (fin9_cases _
  node275
  node281
  (invalid_upper a [2,3,7,5,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,5,5] 30 (by decide +kernel))
  node282
  (invalid_upper a [2,3,7,5,7] 30 (by decide +kernel))
  node290)

def cert292 : Leaf := ⟨⟨0,241,120,32,74,153,312,120,112⟩,[(0,1)],[(2,0,0),(1,5,4)],⟨7,14,133,88,49,98,496,432,312⟩,⟨7,14,133,88,49,98,192,384,264⟩,[⟨8,1181748227386654119019,⟨23,63,133,127,59,127,255,144,59⟩⟩,⟨0,1285813291192733985145856,⟨6,14,132,472,504,98,192,384,264⟩⟩,⟨7,1435600564843080563295235,⟨7,15,5,344,313,379,64,256,264⟩⟩]⟩
theorem node292 : UpperPrefix a [2,3,7,6,0,1] 30 :=
  Boolean.leaf_sound a [2,3,7,6,0,1] 30 cert292 (by decide +kernel)

def cert293 : Leaf := ⟨⟨0,241,122,0,202,0,314,122,242⟩,[(0,1),(3,5),(5,3)],[(2,0,0)],⟨7,14,133,88,49,112,482,418,298⟩,⟨7,14,133,88,49,112,192,384,264⟩,[⟨0,1219570781303940976739328,⟨454,494,132,120,56,120,192,384,296⟩⟩,⟨8,1181748227386654119019,⟨23,63,133,127,59,127,255,144,59⟩⟩]⟩
theorem node293 : UpperPrefix a [2,3,7,6,0,4] 30 :=
  Boolean.leaf_sound a [2,3,7,6,0,4] 30 cert293 (by decide +kernel)

def cert294 : Leaf := ⟨⟨0,177,58,35,10,26,312,58,114⟩,[(0,1)],[(2,0,0)],⟨7,14,133,88,49,352,194,432,312⟩,⟨7,14,133,88,49,352,194,384,264⟩,[⟨0,1247960320503744425886720,⟨102,494,132,504,48,352,226,384,424⟩⟩,⟨6,1210401560269725484717131,⟨7,15,133,31,181,437,135,384,267⟩⟩,⟨7,1785055687111054151648259,⟨279,319,5,376,313,376,379,256,296⟩⟩,⟨8,1181745671425846432875,⟨7,15,133,95,59,127,199,128,11⟩⟩]⟩
theorem node294 : UpperPrefix a [2,3,7,6,0,8,1] 30 :=
  Boolean.leaf_sound a [2,3,7,6,0,8,1] 30 cert294 (by decide +kernel)

def cert295 : Leaf := ⟨⟨0,193,74,0,202,139,299,107,227⟩,[(0,1),(3,6)],[(2,0,0),(4,6,3)],⟨7,14,133,88,49,352,208,418,298⟩,⟨7,14,133,88,49,352,208,384,264⟩,[⟨8,1181745671434436400235,⟨7,15,133,95,59,127,223,128,11⟩⟩,⟨5,1210107564157960386040939,⟨7,15,133,95,19,335,223,384,267⟩⟩]⟩
theorem node295 : UpperPrefix a [2,3,7,6,0,8,4] 30 :=
  Boolean.leaf_sound a [2,3,7,6,0,8,4] 30 cert295 (by decide +kernel)

def cert296 : Leaf := ⟨⟨0,145,26,161,136,153,281,27,147⟩,[(0,1)],[(2,0,0),(8,5,6),(5,6,3)],⟨7,14,133,88,49,352,224,402,282⟩,⟨7,14,133,88,49,352,224,384,264⟩,[⟨6,1248254279113375634560427,⟨7,399,133,415,181,439,181,391,399⟩⟩,⟨1,1210109947688330382540801,⟨93,92,253,88,57,352,224,480,264⟩⟩]⟩
theorem node296 : UpperPrefix a [2,3,7,6,0,8,5] 30 :=
  Boolean.leaf_sound a [2,3,7,6,0,8,5] 30 cert296 (by decide +kernel)

theorem node297 : UpperPrefix a [2,3,7,6,0,8] 30 :=
  branch_upper a [2,3,7,6,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,6,0,8,0] 30 (by decide +kernel))
  node294
  (invalid_upper a [2,3,7,6,0,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,0,8,3] 30 (by decide +kernel))
  node295
  node296
  (invalid_upper a [2,3,7,6,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,0,8,8] 30 (by decide +kernel)))

theorem node298 : UpperPrefix a [2,3,7,6,0] 30 :=
  branch_upper a [2,3,7,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,6,0,0] 30 (by decide +kernel))
  node292
  (invalid_upper a [2,3,7,6,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,0,3] 30 (by decide +kernel))
  node293
  (invalid_upper a [2,3,7,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,0,7] 30 (by decide +kernel))
  node297)

def cert299 : Leaf := ⟨⟨0,225,106,0,201,138,43,107,227⟩,[(0,1),(3,6)],[(2,0,0),(4,6,3)],⟨7,14,133,88,50,97,208,416,296⟩,⟨7,14,133,88,50,97,208,384,264⟩,[⟨8,1184130887037981155055,⟨127,127,255,127,59,127,255,255,59⟩⟩]⟩
theorem node299 : UpperPrefix a [2,3,7,6,1,0,4] 30 :=
  Boolean.leaf_sound a [2,3,7,6,1,0,4] 30 cert299 (by decide +kernel)

def cert300 : Leaf := ⟨⟨0,209,90,161,201,152,25,89,209⟩,[(0,1)],[(2,0,0),(5,6,3)],⟨7,14,133,88,50,97,224,400,280⟩,⟨7,14,133,88,50,97,224,384,264⟩,[⟨8,1184130887037981155055,⟨127,127,255,127,59,127,255,255,59⟩⟩,⟨1,1323666118294298902396929,⟨101,492,229,472,504,97,224,384,392⟩⟩]⟩
theorem node300 : UpperPrefix a [2,3,7,6,1,0,5] 30 :=
  Boolean.leaf_sound a [2,3,7,6,1,0,5] 30 cert300 (by decide +kernel)

def cert301 : Leaf := ⟨⟨0,241,122,161,201,152,0,121,241⟩,[(0,1),(6,7)],[(2,0,0),(8,6,6)],⟨7,14,133,88,50,97,448,432,312⟩,⟨7,14,133,88,50,97,448,384,264⟩,[⟨1,1285815741291668763049985,⟨37,108,229,472,504,97,448,448,328⟩⟩]⟩
theorem node301 : UpperPrefix a [2,3,7,6,1,0,8] 30 :=
  Boolean.leaf_sound a [2,3,7,6,1,0,8] 30 cert301 (by decide +kernel)

theorem node302 : UpperPrefix a [2,3,7,6,1,0] 30 :=
  branch_upper a [2,3,7,6,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,6,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,1,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,1,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,1,0,3] 30 (by decide +kernel))
  node299
  node300
  (invalid_upper a [2,3,7,6,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,1,0,7] 30 (by decide +kernel))
  node301)

def cert303 : Leaf := ⟨⟨0,241,122,0,73,0,315,123,115⟩,[(0,1),(3,5),(5,3)],[(2,0,0)],⟨7,14,133,88,50,112,481,417,297⟩,⟨7,14,133,88,50,112,192,384,264⟩,[⟨8,1181748227386654119019,⟨23,63,133,127,59,127,255,144,59⟩⟩,⟨7,1293929570636404599292931,⟨279,319,5,376,315,376,64,256,296⟩⟩]⟩
theorem node303 : UpperPrefix a [2,3,7,6,1,4] 30 :=
  Boolean.leaf_sound a [2,3,7,6,1,4] 30 cert303 (by decide +kernel)

def cert304 : Leaf := ⟨⟨0,497,0,419,456,154,0,122,242⟩,[(0,1),(2,6),(6,2)],[(2,0,0)],⟨7,14,133,88,50,352,193,432,312⟩,⟨7,14,133,88,50,352,193,384,264⟩,[⟨0,1257571038067118778090496,⟨406,446,132,504,434,352,192,384,424⟩⟩]⟩
theorem node304 : UpperPrefix a [2,3,7,6,1,8,0] 30 :=
  Boolean.leaf_sound a [2,3,7,6,1,8,0] 30 cert304 (by decide +kernel)

def cert305 : Leaf := ⟨⟨0,193,74,0,201,139,299,107,227⟩,[(0,1),(3,6)],[(2,0,0),(4,6,3)],⟨7,14,133,88,50,352,208,417,297⟩,⟨7,14,133,88,50,352,208,384,264⟩,[⟨8,1181745671434436400235,⟨7,15,133,95,59,127,223,128,11⟩⟩,⟨5,1210107564157960386040939,⟨7,15,133,95,19,335,223,384,267⟩⟩]⟩
theorem node305 : UpperPrefix a [2,3,7,6,1,8,4] 30 :=
  Boolean.leaf_sound a [2,3,7,6,1,8,4] 30 cert305 (by decide +kernel)

def cert306 : Leaf := ⟨⟨0,144,26,162,136,154,282,27,147⟩,[(0,1)],[(2,0,0),(8,5,6),(5,6,3)],⟨7,14,133,88,50,352,224,401,281⟩,⟨7,14,133,88,50,352,224,384,264⟩,[⟨0,1210109947688330382544384,⟨94,94,254,88,58,352,224,480,264⟩⟩,⟨6,1248254279108977588049339,⟨7,399,133,415,183,439,181,391,399⟩⟩]⟩
theorem node306 : UpperPrefix a [2,3,7,6,1,8,5] 30 :=
  Boolean.leaf_sound a [2,3,7,6,1,8,5] 30 cert306 (by decide +kernel)

theorem node307 : UpperPrefix a [2,3,7,6,1,8] 30 :=
  branch_upper a [2,3,7,6,1,8] 30 (by decide) (fin9_cases _
  node304
  (invalid_upper a [2,3,7,6,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,1,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,1,8,3] 30 (by decide +kernel))
  node305
  node306
  (invalid_upper a [2,3,7,6,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,1,8,8] 30 (by decide +kernel)))

theorem node308 : UpperPrefix a [2,3,7,6,1] 30 :=
  branch_upper a [2,3,7,6,1] 30 (by decide) (fin9_cases _
  node302
  (invalid_upper a [2,3,7,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,1,3] 30 (by decide +kernel))
  node303
  (invalid_upper a [2,3,7,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,1,7] 30 (by decide +kernel))
  node307)

def cert309 : Leaf := ⟨⟨0,497,368,288,64,274,313,112,112⟩,[(0,1)],[(2,0,0),(1,6,5)],⟨7,14,133,88,304,97,194,432,312⟩,⟨7,14,133,88,304,97,194,384,264⟩,[⟨0,1437223878321567003837440,⟨6,14,132,472,440,504,194,384,264⟩⟩,⟨3,1212616325028742106711107,⟨7,39,133,245,432,101,231,400,436⟩⟩,⟨7,1775610953866451224626179,⟨7,287,5,376,312,377,379,256,280⟩⟩]⟩
theorem node309 : UpperPrefix a [2,3,7,6,8,0,1] 30 :=
  Boolean.leaf_sound a [2,3,7,6,8,0,1] 30 cert309 (by decide +kernel)

def cert310 : Leaf := ⟨⟨0,161,42,0,203,138,299,43,227⟩,[(0,1),(3,6)],[(2,0,0),(8,4,6),(4,6,3)],⟨7,14,133,88,304,97,208,418,298⟩,⟨7,14,133,88,304,97,208,384,264⟩,[⟨6,1210253986314936812443035,⟨7,15,133,159,439,37,149,391,271⟩⟩]⟩
theorem node310 : UpperPrefix a [2,3,7,6,8,0,4] 30 :=
  Boolean.leaf_sound a [2,3,7,6,8,0,4] 30 cert310 (by decide +kernel)

def cert311 : Leaf := ⟨⟨0,401,282,419,203,384,257,27,147⟩,[(0,1)],[(2,0,0),(5,6,3)],⟨7,14,133,88,304,97,224,402,282⟩,⟨7,14,133,88,304,97,224,384,264⟩,[⟨6,1248106705154188879992219,⟨7,399,133,415,439,37,165,391,399⟩⟩,⟨1,1210107637517367584489473,⟨101,108,229,88,304,97,224,384,264⟩⟩,⟨3,1210107637587735254926339,⟨103,103,229,80,304,97,224,384,256⟩⟩,⟨4,1210107637586636817040387,⟨103,111,229,72,288,97,224,384,264⟩⟩]⟩
theorem node311 : UpperPrefix a [2,3,7,6,8,0,5] 30 :=
  Boolean.leaf_sound a [2,3,7,6,8,0,5] 30 cert311 (by decide +kernel)

theorem node312 : UpperPrefix a [2,3,7,6,8,0] 30 :=
  branch_upper a [2,3,7,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,6,8,0,0] 30 (by decide +kernel))
  node309
  (invalid_upper a [2,3,7,6,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,8,0,3] 30 (by decide +kernel))
  node310
  node311
  (invalid_upper a [2,3,7,6,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,8,0,8] 30 (by decide +kernel)))

def cert313 : Leaf := ⟨⟨0,497,0,418,202,409,0,122,242⟩,[(0,1),(2,6),(6,2)],[(2,0,0)],⟨7,14,133,88,304,98,193,432,312⟩,⟨7,14,133,88,304,98,193,384,264⟩,[⟨0,1437223878321567003837440,⟨6,14,132,472,440,506,192,384,264⟩⟩]⟩
theorem node313 : UpperPrefix a [2,3,7,6,8,1,0] 30 :=
  Boolean.leaf_sound a [2,3,7,6,8,1,0] 30 cert313 (by decide +kernel)

def cert314 : Leaf := ⟨⟨0,161,42,0,203,137,299,43,227⟩,[(0,1),(3,6)],[(2,0,0),(8,4,6),(4,6,3)],⟨7,14,133,88,304,98,208,417,297⟩,⟨7,14,133,88,304,98,208,384,264⟩,[⟨6,1210253986314936812443067,⟨7,15,133,159,439,39,149,391,271⟩⟩]⟩
theorem node314 : UpperPrefix a [2,3,7,6,8,1,4] 30 :=
  Boolean.leaf_sound a [2,3,7,6,8,1,4] 30 cert314 (by decide +kernel)

def cert315 : Leaf := ⟨⟨0,385,258,419,203,385,259,19,147⟩,[(0,1)],[(2,0,0),(5,6,3)],⟨7,14,133,88,304,98,224,401,281⟩,⟨7,14,133,88,304,98,224,384,264⟩,[⟨3,1210255499629963615667235,⟨103,103,229,212,501,103,229,384,256⟩⟩,⟨4,1210107637727374322177067,⟨103,111,229,111,289,103,229,384,299⟩⟩,⟨6,1248106705154188879992251,⟨7,399,133,415,439,39,165,391,399⟩⟩]⟩
theorem node315 : UpperPrefix a [2,3,7,6,8,1,5] 30 :=
  Boolean.leaf_sound a [2,3,7,6,8,1,5] 30 cert315 (by decide +kernel)

theorem node316 : UpperPrefix a [2,3,7,6,8,1] 30 :=
  branch_upper a [2,3,7,6,8,1] 30 (by decide) (fin9_cases _
  node313
  (invalid_upper a [2,3,7,6,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,8,1,3] 30 (by decide +kernel))
  node314
  node315
  (invalid_upper a [2,3,7,6,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,8,1,8] 30 (by decide +kernel)))

def cert317 : Leaf := ⟨⟨0,417,298,0,203,0,299,43,243⟩,[(0,1),(3,5),(5,3)],[(2,0,0)],⟨7,14,133,88,304,112,227,419,299⟩,⟨7,14,133,88,304,112,192,384,264⟩,[⟨4,1210255427465718067762587,⟨7,15,133,207,487,229,197,391,271⟩⟩,⟨6,1210253986314936820831643,⟨7,15,133,159,439,181,133,391,271⟩⟩]⟩
theorem node317 : UpperPrefix a [2,3,7,6,8,4] 30 :=
  Boolean.leaf_sound a [2,3,7,6,8,4] 30 cert317 (by decide +kernel)

theorem node318 : UpperPrefix a [2,3,7,6,8] 30 :=
  branch_upper a [2,3,7,6,8] 30 (by decide) (fin9_cases _
  node312
  node316
  (invalid_upper a [2,3,7,6,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,8,3] 30 (by decide +kernel))
  node317
  (invalid_upper a [2,3,7,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,8,8] 30 (by decide +kernel)))

theorem node319 : UpperPrefix a [2,3,7,6] 30 :=
  branch_upper a [2,3,7,6] 30 (by decide) (fin9_cases _
  node298
  node308
  (invalid_upper a [2,3,7,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,6,7] 30 (by decide +kernel))
  node318)

#print axioms node319
end Delivery.FiniteExclusion.Sharp3x6
