import RegularNineSharp3x6Base
import RegularNineSharp3x6C002
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
def cert192 : Leaf := ⟨⟨0,433,442,0,457,153,0,57,177⟩,[(0,1),(3,6),(6,3)],[(2,0,0)],⟨7,14,69,152,50,352,208,417,297⟩,⟨7,14,69,152,50,352,208,384,264⟩,[⟨1,1229043301409016693915649,⟨421,492,493,216,48,360,216,416,360⟩⟩,⟨6,1285811850040861816523783,⟨7,15,15,408,443,296,408,384,264⟩⟩]⟩
theorem node192 : UpperPrefix a [2,3,6,7,1,8,4] 30 :=
  Boolean.leaf_sound a [2,3,6,7,1,8,4] 30 cert192 (by decide +kernel)

def cert193 : Leaf := ⟨⟨0,225,162,67,201,131,259,91,211⟩,[(0,1)],[(2,0,0),(8,5,6)],⟨7,14,69,152,50,352,224,401,281⟩,⟨7,14,69,152,50,352,224,384,264⟩,[⟨4,1210110028751748474738107,⟨7,79,69,239,39,359,229,487,367⟩⟩,⟨3,1210110028752846786659347,⟨7,71,69,245,55,352,224,480,356⟩⟩,⟨5,1285813001836457926591491,⟨7,15,69,408,411,320,192,384,264⟩⟩]⟩
theorem node193 : UpperPrefix a [2,3,6,7,1,8,5] 30 :=
  Boolean.leaf_sound a [2,3,6,7,1,8,5] 30 cert193 (by decide +kernel)

theorem node194 : UpperPrefix a [2,3,6,7,1,8] 30 :=
  branch_upper a [2,3,6,7,1,8] 30 (by decide) (fin9_cases _
  node191
  (invalid_upper a [2,3,6,7,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,8,3] 30 (by decide +kernel))
  node192
  node193
  (invalid_upper a [2,3,6,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,8,8] 30 (by decide +kernel)))

theorem node195 : UpperPrefix a [2,3,6,7,1] 30 :=
  branch_upper a [2,3,6,7,1] 30 (by decide) (fin9_cases _
  node189
  (invalid_upper a [2,3,6,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,3] 30 (by decide +kernel))
  node190
  (invalid_upper a [2,3,6,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,7] 30 (by decide +kernel))
  node194)

def cert196 : Leaf := ⟨⟨0,241,0,355,75,0,59,123,115⟩,[(0,1),(2,5),(5,2)],[(2,0,0),(8,4,3)],⟨7,14,69,152,304,97,242,434,314⟩,⟨7,14,69,152,304,97,192,384,264⟩,[⟨7,1218371706769817220416515,⟨311,319,117,24,308,117,64,256,264⟩⟩]⟩
theorem node196 : UpperPrefix a [2,3,6,7,8,0] 30 :=
  Boolean.leaf_sound a [2,3,6,7,8,0] 30 cert196 (by decide +kernel)

def cert197 : Local := ⟨⟨0,240,0,354,202,152,58,122,242⟩,[(0,1),(2,6)],[(2,0,0),(8,4,3),(0,6,2)]⟩
theorem node197 : UpperPrefix a [2,3,6,7,8,1,0] 30 :=
  local_sound a [2,3,6,7,8,1,0] 30 cert197 (by decide +kernel)

def cert198 : Leaf := ⟨⟨0,177,186,0,139,153,0,59,179⟩,[(0,1),(3,6),(6,3)],[(2,0,0),(8,4,3),(8,4,6)],⟨7,14,69,152,304,98,208,417,297⟩,⟨7,14,69,152,304,98,208,384,264⟩,[⟨6,1361517287721569134578695,⟨7,15,15,152,440,443,152,384,264⟩⟩]⟩
theorem node198 : UpperPrefix a [2,3,6,7,8,1,4] 30 :=
  Boolean.leaf_sound a [2,3,6,7,8,1,4] 30 cert198 (by decide +kernel)

def cert199 : Leaf := ⟨⟨0,145,154,259,139,153,27,27,147⟩,[(0,1)],[(2,0,0),(8,4,3)],⟨7,14,69,152,304,98,224,401,281⟩,⟨7,14,69,152,304,98,224,384,264⟩,[⟨5,1323665720675709951681587,⟨7,399,69,411,415,71,197,384,392⟩⟩,⟨6,1380443647145593717919239,⟨399,399,415,152,440,443,440,384,264⟩⟩]⟩
theorem node199 : UpperPrefix a [2,3,6,7,8,1,5] 30 :=
  Boolean.leaf_sound a [2,3,6,7,8,1,5] 30 cert199 (by decide +kernel)

theorem node200 : UpperPrefix a [2,3,6,7,8,1] 30 :=
  branch_upper a [2,3,6,7,8,1] 30 (by decide) (fin9_cases _
  node197
  (invalid_upper a [2,3,6,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,1,3] 30 (by decide +kernel))
  node198
  node199
  (invalid_upper a [2,3,6,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,1,8] 30 (by decide +kernel)))

def cert201 : Local := ⟨⟨0,240,0,354,202,138,58,122,242⟩,[(0,1),(2,6)],[(2,0,0),(8,4,3),(0,6,2)]⟩
theorem node201 : UpperPrefix a [2,3,6,7,8,4,0] 30 :=
  local_sound a [2,3,6,7,8,4,0] 30 cert201 (by decide +kernel)

def cert202 : Leaf := ⟨⟨0,225,42,353,73,9,41,105,113⟩,[(0,1)],[(2,0,0),(8,4,3),(1,6,2)],⟨7,14,69,152,304,112,194,417,297⟩,⟨7,14,69,152,304,112,194,384,264⟩,[⟨4,1210257877423915424945627,⟨7,79,69,207,487,229,199,455,335⟩⟩,⟨7,1218371709026015097390147,⟨311,319,117,24,308,117,375,256,264⟩⟩]⟩
theorem node202 : UpperPrefix a [2,3,6,7,8,4,1] 30 :=
  Boolean.leaf_sound a [2,3,6,7,8,4,1] 30 cert202 (by decide +kernel)

def cert203 : Leaf := ⟨⟨0,208,154,322,202,138,26,91,211⟩,[(0,1)],[(2,0,0),(8,4,3),(5,6,5)],⟨7,14,69,152,304,112,224,387,267⟩,⟨7,14,69,152,304,112,224,384,264⟩,[⟨0,1210110031312536697048064,⟨6,110,110,248,304,120,248,504,376⟩⟩]⟩
theorem node203 : UpperPrefix a [2,3,6,7,8,4,5] 30 :=
  Boolean.leaf_sound a [2,3,6,7,8,4,5] 30 cert203 (by decide +kernel)

theorem node204 : UpperPrefix a [2,3,6,7,8,4] 30 :=
  branch_upper a [2,3,6,7,8,4] 30 (by decide) (fin9_cases _
  node201
  node202
  (invalid_upper a [2,3,6,7,8,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,4,4] 30 (by decide +kernel))
  node203
  (invalid_upper a [2,3,6,7,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,4,8] 30 (by decide +kernel)))

theorem node205 : UpperPrefix a [2,3,6,7,8] 30 :=
  branch_upper a [2,3,6,7,8] 30 (by decide) (fin9_cases _
  node196
  node200
  (invalid_upper a [2,3,6,7,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,3] 30 (by decide +kernel))
  node204
  (invalid_upper a [2,3,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,8] 30 (by decide +kernel)))

theorem node206 : UpperPrefix a [2,3,6,7] 30 :=
  branch_upper a [2,3,6,7] 30 (by decide) (fin9_cases _
  node188
  node195
  (invalid_upper a [2,3,6,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,7] 30 (by decide +kernel))
  node205)

def cert207 : Leaf := ⟨⟨0,497,432,160,386,409,312,56,176⟩,[(0,1)],[(2,0,0),(1,5,4)],⟨7,14,69,280,49,98,240,432,440⟩,⟨7,14,69,280,49,98,192,384,264⟩,[⟨0,1285813291192733985145856,⟨6,14,68,472,504,98,192,384,264⟩⟩,⟨6,1437222725400064544474115,⟨7,15,5,408,441,443,128,384,264⟩⟩,⟨3,1210107565286049644020771,⟨7,7,69,272,53,119,192,384,256⟩⟩]⟩
theorem node207 : UpperPrefix a [2,3,6,8,0,1] 30 :=
  Boolean.leaf_sound a [2,3,6,8,0,1] 30 cert207 (by decide +kernel)

def cert208 : Leaf := ⟨⟨0,497,434,160,448,385,313,56,176⟩,[(0,1)],[(2,0,0),(1,6,2)],⟨7,14,69,280,49,112,194,416,424⟩,⟨7,14,69,280,49,112,194,384,264⟩,[⟨0,1437223878319370128065536,⟨6,14,68,408,440,504,194,384,264⟩⟩,⟨3,1210107567683466045686851,⟨55,55,117,272,53,117,247,384,256⟩⟩,⟨6,1437222725397865521218563,⟨7,15,5,408,441,440,131,384,264⟩⟩]⟩
theorem node208 : UpperPrefix a [2,3,6,8,0,4,1] 30 :=
  Boolean.leaf_sound a [2,3,6,8,0,4,1] 30 cert208 (by decide +kernel)

def cert209 : Leaf := ⟨⟨0,449,394,195,458,394,266,74,194⟩,[(0,1)],[(2,0,0),(5,6,5)],⟨7,14,69,280,49,112,224,386,394⟩,⟨7,14,69,280,49,112,224,384,264⟩,[⟨4,1259794158675665009906955,⟨391,399,197,463,229,100,224,387,399⟩⟩,⟨0,1219580293469299641680896,⟨454,494,196,376,240,112,224,384,296⟩⟩]⟩
theorem node209 : UpperPrefix a [2,3,6,8,0,4,5] 30 :=
  Boolean.leaf_sound a [2,3,6,8,0,4,5] 30 cert209 (by decide +kernel)

theorem node210 : UpperPrefix a [2,3,6,8,0,4] 30 :=
  branch_upper a [2,3,6,8,0,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,8,0,4,0] 30 (by decide +kernel))
  node208
  (invalid_upper a [2,3,6,8,0,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,4,4] 30 (by decide +kernel))
  node209
  (invalid_upper a [2,3,6,8,0,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,4,8] 30 (by decide +kernel)))

def cert211 : Local := ⟨⟨0,369,314,97,328,0,313,121,113⟩,[(0,1),(5,6)],[(2,0,0),(7,5,5),(1,6,2)]⟩
theorem node211 : UpperPrefix a [2,3,6,8,0,7,1] 30 :=
  local_sound a [2,3,6,8,0,7,1] 30 cert211 (by decide +kernel)

def cert212 : Leaf := ⟨⟨0,369,314,99,330,0,298,106,98⟩,[(0,1),(5,6)],[(2,0,0),(7,5,5)],⟨7,14,69,280,49,224,208,418,298⟩,⟨7,14,69,280,49,224,208,384,264⟩,[⟨0,1219580259551564948046848,⟨422,430,228,376,240,224,240,384,264⟩⟩,⟨4,1219579970757139331286019,⟨423,431,229,264,161,224,224,384,264⟩⟩]⟩
theorem node212 : UpperPrefix a [2,3,6,8,0,7,4] 30 :=
  Boolean.leaf_sound a [2,3,6,8,0,7,4] 30 cert212 (by decide +kernel)

def cert213 : Local := ⟨⟨0,369,314,99,330,0,0,123,115⟩,[(0,1),(5,6),(6,5)],[(2,0,0),(7,5,5),(7,5,6)]⟩
theorem node213 : UpperPrefix a [2,3,6,8,0,7,5] 30 :=
  local_sound a [2,3,6,8,0,7,5] 30 cert213 (by decide +kernel)

theorem node214 : UpperPrefix a [2,3,6,8,0,7] 30 :=
  branch_upper a [2,3,6,8,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,8,0,7,0] 30 (by decide +kernel))
  node211
  (invalid_upper a [2,3,6,8,0,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,7,3] 30 (by decide +kernel))
  node212
  node213
  (invalid_upper a [2,3,6,8,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,7,8] 30 (by decide +kernel)))

theorem node215 : UpperPrefix a [2,3,6,8,0] 30 :=
  branch_upper a [2,3,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,8,0,0] 30 (by decide +kernel))
  node207
  (invalid_upper a [2,3,6,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,3] 30 (by decide +kernel))
  node210
  (invalid_upper a [2,3,6,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,6] 30 (by decide +kernel))
  node214
  (invalid_upper a [2,3,6,8,0,8] 30 (by decide +kernel)))

def cert216 : Leaf := ⟨⟨0,497,0,226,457,0,314,122,242⟩,[(0,1),(2,5),(5,2)],[(2,0,0)],⟨7,14,69,280,50,97,240,432,440⟩,⟨7,14,69,280,50,97,192,384,264⟩,[⟨0,1285813291192733985145856,⟨6,14,68,472,506,96,192,384,264⟩⟩]⟩
theorem node216 : UpperPrefix a [2,3,6,8,1,0] 30 :=
  Boolean.leaf_sound a [2,3,6,8,1,0] 30 cert216 (by decide +kernel)

def cert217 : Leaf := ⟨⟨0,497,50,163,64,2,307,51,179⟩,[(0,1)],[(2,0,0)],⟨7,14,69,280,50,112,225,417,425⟩,⟨7,14,69,280,50,112,192,384,264⟩,[⟨3,1210181533495052254053395,⟨119,247,117,501,119,117,192,384,484⟩⟩,⟨6,1285811850040857521554435,⟨7,15,5,408,443,440,128,384,264⟩⟩,⟨7,1208926973804077929989139,⟨55,63,117,281,55,117,64,256,264⟩⟩,⟨8,1181745810166166586387,⟨55,63,117,25,55,117,192,128,8⟩⟩,⟨0,1210107565424795332903936,⟨54,62,116,280,50,112,192,384,264⟩⟩]⟩
theorem node217 : UpperPrefix a [2,3,6,8,1,4] 30 :=
  Boolean.leaf_sound a [2,3,6,8,1,4] 30 cert217 (by decide +kernel)

def cert218 : Leaf := ⟨⟨0,369,306,35,321,0,307,51,51⟩,[(0,1),(5,6)],[(2,0,0),(7,5,5)],⟨7,14,69,280,50,224,241,433,313⟩,⟨7,14,69,280,50,224,192,384,264⟩,[⟨3,1210181544015179500225555,⟨119,247,117,501,119,224,224,416,484⟩⟩,⟨6,1285811850040853226587139,⟨7,15,5,408,443,160,128,384,264⟩⟩]⟩
theorem node218 : UpperPrefix a [2,3,6,8,1,7] 30 :=
  Boolean.leaf_sound a [2,3,6,8,1,7] 30 cert218 (by decide +kernel)

theorem node219 : UpperPrefix a [2,3,6,8,1] 30 :=
  branch_upper a [2,3,6,8,1] 30 (by decide) (fin9_cases _
  node216
  (invalid_upper a [2,3,6,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,3] 30 (by decide +kernel))
  node217
  (invalid_upper a [2,3,6,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,6] 30 (by decide +kernel))
  node218
  (invalid_upper a [2,3,6,8,1,8] 30 (by decide +kernel)))

def cert220 : Local := ⟨⟨0,497,0,225,329,0,313,121,241⟩,[(0,1),(2,5),(5,2)],[(2,0,0),(1,6,2),(1,6,5)]⟩
theorem node220 : UpperPrefix a [2,3,6,8,7,0,1] 30 :=
  local_sound a [2,3,6,8,7,0,1] 30 cert220 (by decide +kernel)

def cert221 : Local := ⟨⟨0,369,0,99,331,0,0,123,115⟩,[(0,1),(2,5),(5,2),(6,4)],[(2,0,0),(7,4,6)]⟩
theorem node221 : UpperPrefix a [2,3,6,8,7,0,4] 30 :=
  local_sound a [2,3,6,8,7,0,4] 30 cert221 (by decide +kernel)

def cert222 : Local := ⟨⟨0,497,0,227,0,0,0,123,243⟩,[(0,1),(2,5),(4,6),(5,2),(6,4)],[(2,0,0)]⟩
theorem node222 : UpperPrefix a [2,3,6,8,7,0,5] 30 :=
  local_sound a [2,3,6,8,7,0,5] 30 cert222 (by decide +kernel)

theorem node223 : UpperPrefix a [2,3,6,8,7,0] 30 :=
  branch_upper a [2,3,6,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,8,7,0,0] 30 (by decide +kernel))
  node220
  (invalid_upper a [2,3,6,8,7,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,0,3] 30 (by decide +kernel))
  node221
  node222
  (invalid_upper a [2,3,6,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,0,8] 30 (by decide +kernel)))

def cert224 : Leaf := ⟨⟨0,113,50,35,11,153,51,59,51⟩,[(0,1)],[(2,0,0)],⟨7,14,69,280,176,98,241,433,313⟩,⟨7,14,69,280,176,98,192,384,264⟩,[⟨8,1184344540876685579691,⟨7,47,85,127,245,119,245,247,47⟩⟩,⟨6,1361517287721560544642051,⟨7,15,5,280,440,443,128,384,264⟩⟩,⟨7,1284484837389050754114611,⟨7,15,69,283,319,103,64,256,264⟩⟩,⟨3,1210107853514226776671267,⟨7,7,69,340,245,103,192,384,256⟩⟩]⟩
theorem node224 : UpperPrefix a [2,3,6,8,7,1] 30 :=
  Boolean.leaf_sound a [2,3,6,8,7,1] 30 cert224 (by decide +kernel)

def cert225 : Local := ⟨⟨0,368,0,98,330,394,314,122,114⟩,[(0,1),(2,6)],[(2,0,0),(7,4,5),(0,6,2)]⟩
theorem node225 : UpperPrefix a [2,3,6,8,7,4,0] 30 :=
  local_sound a [2,3,6,8,7,4,0] 30 cert225 (by decide +kernel)

def cert226 : Leaf := ⟨⟨0,369,50,97,65,129,313,121,113⟩,[(0,1)],[(2,0,0),(7,4,5),(1,6,2)],⟨7,14,69,280,176,112,194,417,297⟩,⟨7,14,69,280,176,112,194,384,264⟩,[⟨3,1210107567680785986094147,⟨39,39,117,272,180,117,247,384,256⟩⟩,⟨8,1181748066157885129795,⟨39,47,117,24,180,117,247,128,8⟩⟩]⟩
theorem node226 : UpperPrefix a [2,3,6,8,7,4,1] 30 :=
  Boolean.leaf_sound a [2,3,6,8,7,4,1] 30 cert226 (by decide +kernel)

def cert227 : Local := ⟨⟨0,337,282,67,0,395,0,91,83⟩,[(0,1),(4,6),(6,4)],[(2,0,0),(7,4,5),(5,6,5)]⟩
theorem node227 : UpperPrefix a [2,3,6,8,7,4,5] 30 :=
  local_sound a [2,3,6,8,7,4,5] 30 cert227 (by decide +kernel)

theorem node228 : UpperPrefix a [2,3,6,8,7,4] 30 :=
  branch_upper a [2,3,6,8,7,4] 30 (by decide) (fin9_cases _
  node225
  node226
  (invalid_upper a [2,3,6,8,7,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,4,4] 30 (by decide +kernel))
  node227
  (invalid_upper a [2,3,6,8,7,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,4,8] 30 (by decide +kernel)))

theorem node229 : UpperPrefix a [2,3,6,8,7] 30 :=
  branch_upper a [2,3,6,8,7] 30 (by decide) (fin9_cases _
  node223
  node224
  (invalid_upper a [2,3,6,8,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,3] 30 (by decide +kernel))
  node228
  (invalid_upper a [2,3,6,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,8] 30 (by decide +kernel)))

theorem node230 : UpperPrefix a [2,3,6,8] 30 :=
  branch_upper a [2,3,6,8] 30 (by decide) (fin9_cases _
  node215
  node219
  (invalid_upper a [2,3,6,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,6] 30 (by decide +kernel))
  node229
  (invalid_upper a [2,3,6,8,8] 30 (by decide +kernel)))

theorem node231 : UpperPrefix a [2,3,6] 30 :=
  branch_upper a [2,3,6] 30 (by decide) (fin9_cases _
  node144
  node162
  (invalid_upper a [2,3,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,4] 30 (by decide +kernel))
  node178
  (invalid_upper a [2,3,6,6] 30 (by decide +kernel))
  node206
  node230)

def cert232 : Leaf := ⟨⟨0,241,120,226,200,136,312,120,240⟩,[(0,1)],[(2,0,0),(0,3,1),(1,4,3)],⟨7,14,133,25,50,112,480,480,360⟩,⟨7,14,133,25,50,112,192,384,264⟩,[⟨8,1181747927634444076131,⟨7,15,133,25,59,127,255,128,8⟩⟩]⟩
theorem node232 : UpperPrefix a [2,3,7,0,1,4] 30 :=
  Boolean.leaf_sound a [2,3,7,0,1,4] 30 cert232 (by decide +kernel)

def cert233 : Leaf := ⟨⟨0,433,312,418,392,152,296,120,240⟩,[(0,1)],[(2,0,0),(0,3,1),(1,4,3)],⟨7,14,133,25,50,352,208,480,360⟩,⟨7,14,133,25,50,352,208,384,264⟩,[⟨6,1210106412364561151738979,⟨7,15,133,25,59,319,159,384,264⟩⟩]⟩
theorem node233 : UpperPrefix a [2,3,7,0,1,8,4] 30 :=
  Boolean.leaf_sound a [2,3,7,0,1,8,4] 30 cert233 (by decide +kernel)

def cert234 : Local := ⟨⟨0,241,120,226,200,152,280,120,240⟩,[(0,1)],[(2,0,0),(0,3,1),(1,4,3),(8,5,6)]⟩
theorem node234 : UpperPrefix a [2,3,7,0,1,8,5] 30 :=
  local_sound a [2,3,7,0,1,8,5] 30 cert234 (by decide +kernel)

theorem node235 : UpperPrefix a [2,3,7,0,1,8] 30 :=
  branch_upper a [2,3,7,0,1,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,0,1,8,0] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,1,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,1,8,3] 30 (by decide +kernel))
  node233
  node234
  (invalid_upper a [2,3,7,0,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,1,8,8] 30 (by decide +kernel)))

theorem node236 : UpperPrefix a [2,3,7,0,1] 30 :=
  branch_upper a [2,3,7,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,1,3] 30 (by decide +kernel))
  node232
  (invalid_upper a [2,3,7,0,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,1,7] 30 (by decide +kernel))
  node235)

def cert237 : Leaf := ⟨⟨0,177,58,162,0,152,314,58,178⟩,[(0,1),(4,5)],[(2,0,0),(0,3,1),(6,4,4)],⟨7,14,133,25,112,98,496,432,312⟩,⟨7,14,133,25,112,98,192,384,264⟩,[⟨8,1181748490584397505651,⟨7,15,133,59,127,127,255,128,8⟩⟩]⟩
theorem node237 : UpperPrefix a [2,3,7,0,6,1] 30 :=
  Boolean.leaf_sound a [2,3,7,0,6,1] 30 cert237 (by decide +kernel)

def cert238 : Local := ⟨⟨0,433,314,418,0,0,314,58,178⟩,[(0,1),(4,5),(5,4)],[(2,0,0),(0,3,1),(6,4,4),(6,4,5)]⟩
theorem node238 : UpperPrefix a [2,3,7,0,6,4] 30 :=
  local_sound a [2,3,7,0,6,4] 30 cert238 (by decide +kernel)

def cert239 : Local := ⟨⟨0,433,314,418,0,154,312,58,178⟩,[(0,1),(4,5)],[(2,0,0),(0,3,1),(6,4,4)]⟩
theorem node239 : UpperPrefix a [2,3,7,0,6,8,1] 30 :=
  local_sound a [2,3,7,0,6,8,1] 30 cert239 (by decide +kernel)

def cert240 : Local := ⟨⟨0,433,314,418,0,154,298,58,178⟩,[(0,1),(4,5)],[(2,0,0),(0,3,1),(6,4,4)]⟩
theorem node240 : UpperPrefix a [2,3,7,0,6,8,4] 30 :=
  local_sound a [2,3,7,0,6,8,4] 30 cert240 (by decide +kernel)

def cert241 : Local := ⟨⟨0,145,26,130,0,154,282,26,146⟩,[(0,1),(4,5)],[(2,0,0),(0,3,1),(6,4,4),(8,5,6),(5,6,4)]⟩
theorem node241 : UpperPrefix a [2,3,7,0,6,8,5] 30 :=
  local_sound a [2,3,7,0,6,8,5] 30 cert241 (by decide +kernel)

theorem node242 : UpperPrefix a [2,3,7,0,6,8] 30 :=
  branch_upper a [2,3,7,0,6,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,0,6,8,0] 30 (by decide +kernel))
  node239
  (invalid_upper a [2,3,7,0,6,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,6,8,3] 30 (by decide +kernel))
  node240
  node241
  (invalid_upper a [2,3,7,0,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,6,8,8] 30 (by decide +kernel)))

theorem node243 : UpperPrefix a [2,3,7,0,6] 30 :=
  branch_upper a [2,3,7,0,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,0,6,0] 30 (by decide +kernel))
  node237
  (invalid_upper a [2,3,7,0,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,6,3] 30 (by decide +kernel))
  node238
  (invalid_upper a [2,3,7,0,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,6,7] 30 (by decide +kernel))
  node242)

def cert244 : Leaf := ⟨⟨0,241,112,226,202,144,288,112,242⟩,[(0,1)],[(2,0,0),(0,3,1),(8,4,6)],⟨7,14,133,25,304,98,208,480,360⟩,⟨7,14,133,25,304,98,208,384,264⟩,[⟨3,1210255571652373262631939,⟨39,103,133,213,496,99,208,384,324⟩⟩,⟨1,1210255571582005592195073,⟨5,76,133,221,496,96,208,384,332⟩⟩]⟩
theorem node244 : UpperPrefix a [2,3,7,0,8,1,4] 30 :=
  Boolean.leaf_sound a [2,3,7,0,8,1,4] 30 cert244 (by decide +kernel)

def cert245 : Leaf := ⟨⟨0,497,112,226,202,144,16,112,240⟩,[(0,1)],[(2,0,0),(0,3,1)],⟨7,14,133,25,304,98,224,464,344⟩,⟨7,14,133,25,304,98,224,384,264⟩,[⟨1,1248108146306069516255233,⟨5,396,133,477,496,96,224,384,396⟩⟩,⟨3,1210255643745151693620259,⟨103,103,229,245,501,103,229,384,324⟩⟩,⟨8,1181817832371829867555,⟨103,111,229,57,57,103,229,128,8⟩⟩]⟩
theorem node245 : UpperPrefix a [2,3,7,0,8,1,5] 30 :=
  Boolean.leaf_sound a [2,3,7,0,8,1,5] 30 cert245 (by decide +kernel)

theorem node246 : UpperPrefix a [2,3,7,0,8,1] 30 :=
  branch_upper a [2,3,7,0,8,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,0,8,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,8,1,3] 30 (by decide +kernel))
  node244
  node245
  (invalid_upper a [2,3,7,0,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,8,1,8] 30 (by decide +kernel)))

def cert247 : Leaf := ⟨⟨0,449,330,322,74,266,296,106,114⟩,[(0,1)],[(2,0,0),(0,3,1)],⟨7,14,133,25,304,112,194,480,360⟩,⟨7,14,133,25,304,112,194,384,264⟩,[⟨4,1210257877423915357312475,⟨7,79,197,207,487,229,199,455,335⟩⟩,⟨7,1662274158277025688716291,⟨7,15,5,25,304,376,379,256,264⟩⟩,⟨5,1210107564157958238520419,⟨7,15,133,25,283,95,199,384,264⟩⟩]⟩
theorem node247 : UpperPrefix a [2,3,7,0,8,4,1] 30 :=
  Boolean.leaf_sound a [2,3,7,0,8,4,1] 30 cert247 (by decide +kernel)

def cert248 : Leaf := ⟨⟨0,449,330,450,202,394,266,74,194⟩,[(0,1)],[(2,0,0),(0,3,1),(5,6,5)],⟨7,14,133,25,304,112,224,450,330⟩,⟨7,14,133,25,304,112,224,384,264⟩,[⟨4,1248108722765722438735259,⟨7,399,133,463,487,229,229,391,399⟩⟩]⟩
theorem node248 : UpperPrefix a [2,3,7,0,8,4,5] 30 :=
  Boolean.leaf_sound a [2,3,7,0,8,4,5] 30 cert248 (by decide +kernel)

theorem node249 : UpperPrefix a [2,3,7,0,8,4] 30 :=
  branch_upper a [2,3,7,0,8,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,0,8,4,0] 30 (by decide +kernel))
  node247
  (invalid_upper a [2,3,7,0,8,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,8,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,8,4,4] 30 (by decide +kernel))
  node248
  (invalid_upper a [2,3,7,0,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,8,4,8] 30 (by decide +kernel)))

theorem node250 : UpperPrefix a [2,3,7,0,8] 30 :=
  branch_upper a [2,3,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,0,8,0] 30 (by decide +kernel))
  node246
  (invalid_upper a [2,3,7,0,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,8,3] 30 (by decide +kernel))
  node249
  (invalid_upper a [2,3,7,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,8,8] 30 (by decide +kernel)))

theorem node251 : UpperPrefix a [2,3,7,0] 30 :=
  branch_upper a [2,3,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,0,0] 30 (by decide +kernel))
  node236
  (invalid_upper a [2,3,7,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,0,5] 30 (by decide +kernel))
  node243
  (invalid_upper a [2,3,7,0,7] 30 (by decide +kernel))
  node250)

def cert252 : Leaf := ⟨⟨0,241,120,225,200,136,312,120,240⟩,[(0,1)],[(2,0,0)],⟨7,14,133,26,49,112,480,480,360⟩,⟨7,14,133,26,49,112,192,384,264⟩,[⟨1,1259798681381849531678721,⟨501,508,245,508,245,116,192,448,488⟩⟩,⟨8,1181747927634444076131,⟨7,15,133,27,59,127,255,128,8⟩⟩,⟨0,1259789439185830007538688,⟨454,494,132,506,48,112,192,448,488⟩⟩]⟩
theorem node252 : UpperPrefix a [2,3,7,1,0,4] 30 :=
  Boolean.leaf_sound a [2,3,7,1,0,4] 30 cert252 (by decide +kernel)

def cert253 : Leaf := ⟨⟨0,497,368,481,448,144,304,112,240⟩,[(0,1)],[(2,0,0)],⟨7,14,133,26,49,352,240,496,376⟩,⟨7,14,133,26,49,352,192,384,264⟩,[⟨1,1257433255045878284288001,⟨501,508,245,508,245,352,192,416,488⟩⟩,⟨3,1212771764236880939320331,⟨87,87,245,87,245,500,224,500,501⟩⟩,⟨0,1247960437597334737519616,⟨38,494,132,506,48,352,192,416,488⟩⟩]⟩
theorem node253 : UpperPrefix a [2,3,7,1,0,8] 30 :=
  Boolean.leaf_sound a [2,3,7,1,0,8] 30 cert253 (by decide +kernel)

theorem node254 : UpperPrefix a [2,3,7,1,0] 30 :=
  branch_upper a [2,3,7,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,7,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,0,3] 30 (by decide +kernel))
  node252
  (invalid_upper a [2,3,7,1,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,7,1,0,7] 30 (by decide +kernel))
  node253)

def cert255 : Leaf := ⟨⟨0,433,312,417,0,408,313,57,177⟩,[(0,1),(4,5)],[(2,0,0),(6,4,4)],⟨7,14,133,26,112,97,496,432,312⟩,⟨7,14,133,26,112,97,192,384,264⟩,[⟨1,1219580022587498998005761,⟨501,508,245,472,116,245,192,384,264⟩⟩]⟩
theorem node255 : UpperPrefix a [2,3,7,1,6,0] 30 :=
  Boolean.leaf_sound a [2,3,7,1,6,0] 30 cert255 (by decide +kernel)

#print axioms node255
end Delivery.FiniteExclusion.Sharp3x6
