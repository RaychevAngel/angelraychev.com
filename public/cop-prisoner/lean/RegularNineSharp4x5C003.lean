import RegularNineSharp4x5Base
import RegularNineSharp4x5C002
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp4x5
open Bounds BoundTreeRows Extremal
theorem node192 : UpperPrefix a [2,4,6,5,1] 30 :=
  branch_upper a [2,4,6,5,1] 30 (by decide) (fin9_cases _
  node188
  (invalid_upper a [2,4,6,5,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,1,2] 30 (by decide +kernel))
  node189
  (invalid_upper a [2,4,6,5,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,1,6] 30 (by decide +kernel))
  node190
  node191)

def cert193 : Leaf := ⟨⟨0,393,403,466,0,403,275,19,131⟩,[(0,1),(4,3)],[(2,0,0),(5,3,4),(3,4,1)],⟨7,22,76,41,56,483,451,387,403⟩,⟨7,22,76,41,56,96,192,384,272⟩,[⟨6,1238505174864372689800199,⟨391,407,415,185,56,32,128,384,272⟩⟩]⟩
theorem node193 : UpperPrefix a [2,4,6,5,3] 30 :=
  Boolean.leaf_sound a [2,4,6,5,3] 30 cert193 (by decide +kernel)

def cert194 : Leaf := ⟨⟨0,232,178,0,74,154,314,122,234⟩,[(0,1),(3,5)],[(2,0,0),(0,5,3)],⟨7,22,76,41,176,97,458,394,282⟩,⟨7,22,76,41,176,97,192,384,272⟩,[⟨8,1181748066173857098879,⟨47,63,127,47,191,127,255,128,27⟩⟩]⟩
theorem node194 : UpperPrefix a [2,4,6,5,7,0] 30 :=
  Boolean.leaf_sound a [2,4,6,5,7,0] 30 cert194 (by decide +kernel)

def cert195 : Leaf := ⟨⟨0,169,177,146,9,153,313,57,169⟩,[(0,1)],[(2,0,0),(1,5,3)],⟨7,22,76,41,176,98,457,393,281⟩,⟨7,22,76,41,176,98,192,384,272⟩,[⟨6,1418296365980986152848391,⟨391,407,415,441,440,443,128,384,272⟩⟩,⟨8,1181748066173857098879,⟨47,63,127,47,191,127,255,128,27⟩⟩]⟩
theorem node195 : UpperPrefix a [2,4,6,5,7,1] 30 :=
  Boolean.leaf_sound a [2,4,6,5,7,1] 30 cert195 (by decide +kernel)

def cert196 : Leaf := ⟨⟨0,481,0,466,323,0,307,115,227⟩,[(0,1),(2,5),(5,2)],[(2,0,0)],⟨7,22,76,41,176,104,451,387,275⟩,⟨7,22,76,41,176,104,192,384,272⟩,[⟨3,1238506453886665789279239,⟨455,471,471,241,176,112,192,384,272⟩⟩]⟩
theorem node196 : UpperPrefix a [2,4,6,5,7,3] 30 :=
  Boolean.leaf_sound a [2,4,6,5,7,3] 30 cert196 (by decide +kernel)

def cert197 : Local := ⟨⟨0,232,161,192,328,136,42,120,232⟩,[(0,1)],[(2,0,0),(4,1,7),(8,5,4),(0,6,2),(1,7,6)]⟩
theorem node197 : UpperPrefix a [2,4,6,5,7,8,0,1] 30 :=
  local_sound a [2,4,6,5,7,8,0,1] 30 cert197 (by decide +kernel)

def cert198 : Leaf := ⟨⟨0,232,177,208,328,152,56,112,234⟩,[(0,1)],[(2,0,0),(8,5,4),(0,6,2)],⟨7,22,76,41,176,352,193,392,274⟩,⟨7,22,76,41,176,352,193,392,272⟩,[⟨1,1210402861823770311524353,⟨5,20,92,253,180,508,253,508,272⟩⟩]⟩
theorem node198 : UpperPrefix a [2,4,6,5,7,8,0,3] 30 :=
  Boolean.leaf_sound a [2,4,6,5,7,8,0,3] 30 cert198 (by decide +kernel)

theorem node199 : UpperPrefix a [2,4,6,5,7,8,0] 30 :=
  branch_upper a [2,4,6,5,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,5,7,8,0,0] 30 (by decide +kernel))
  node197
  (invalid_upper a [2,4,6,5,7,8,0,2] 30 (by decide +kernel))
  node198
  (invalid_upper a [2,4,6,5,7,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,8,0,8] 30 (by decide +kernel)))

def cert200 : Leaf := ⟨⟨0,105,51,80,329,25,57,121,105⟩,[(0,1)],[(2,0,0),(8,5,4)],⟨7,22,76,41,176,352,194,393,281⟩,⟨7,22,76,41,176,352,194,384,272⟩,[⟨1,1252691874119641161793537,⟨445,52,508,441,176,352,192,384,272⟩⟩,⟨7,1293929572606603296777299,⟨271,287,109,45,319,365,367,256,283⟩⟩]⟩
theorem node200 : UpperPrefix a [2,4,6,5,7,8,1] 30 :=
  Boolean.leaf_sound a [2,4,6,5,7,8,1] 30 cert200 (by decide +kernel)

def cert201 : Local := ⟨⟨0,225,0,210,323,147,51,115,227⟩,[(0,1),(2,6)],[(2,0,0),(8,5,4),(3,6,2)]⟩
theorem node201 : UpperPrefix a [2,4,6,5,7,8,3] 30 :=
  local_sound a [2,4,6,5,7,8,3] 30 cert201 (by decide +kernel)

theorem node202 : UpperPrefix a [2,4,6,5,7,8] 30 :=
  branch_upper a [2,4,6,5,7,8] 30 (by decide) (fin9_cases _
  node199
  node200
  (invalid_upper a [2,4,6,5,7,8,2] 30 (by decide +kernel))
  node201
  (invalid_upper a [2,4,6,5,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,8,8] 30 (by decide +kernel)))

theorem node203 : UpperPrefix a [2,4,6,5,7] 30 :=
  branch_upper a [2,4,6,5,7] 30 (by decide) (fin9_cases _
  node194
  node195
  (invalid_upper a [2,4,6,5,7,2] 30 (by decide +kernel))
  node196
  (invalid_upper a [2,4,6,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,7] 30 (by decide +kernel))
  node202)

def cert204 : Leaf := ⟨⟨0,104,50,0,202,410,314,122,234⟩,[(0,1),(3,5)],[(2,0,0),(0,5,3)],⟨7,22,76,41,304,97,202,394,410⟩,⟨7,22,76,41,304,97,192,384,272⟩,[⟨7,1208926973663140725662739,⟨7,31,76,45,319,109,64,256,283⟩⟩,⟨8,1181745669228962259987,⟨7,31,76,45,63,109,192,128,27⟩⟩]⟩
theorem node204 : UpperPrefix a [2,4,6,5,8,0] 30 :=
  Boolean.leaf_sound a [2,4,6,5,8,0] 30 cert204 (by decide +kernel)

def cert205 : Leaf := ⟨⟨0,425,417,386,137,393,297,41,169⟩,[(0,1)],[(2,0,0),(1,5,3)],⟨7,22,76,41,304,98,201,393,409⟩,⟨7,22,76,41,304,98,192,384,272⟩,[⟨4,1210255463600075063428131,⟨111,239,76,45,493,111,192,388,460⟩⟩,⟨6,1418296365980986152848391,⟨391,407,415,441,440,443,128,384,272⟩⟩]⟩
theorem node205 : UpperPrefix a [2,4,6,5,8,1] 30 :=
  Boolean.leaf_sound a [2,4,6,5,8,1] 30 cert205 (by decide +kernel)

def cert206 : Leaf := ⟨⟨0,457,0,466,203,0,283,91,203⟩,[(0,1),(2,5),(5,2)],[(2,0,0)],⟨7,22,76,41,304,104,195,387,403⟩,⟨7,22,76,41,304,104,192,384,272⟩,[⟨5,1297651542119330574509075,⟨455,471,76,205,471,76,192,448,467⟩⟩]⟩
theorem node206 : UpperPrefix a [2,4,6,5,8,3] 30 :=
  Boolean.leaf_sound a [2,4,6,5,8,3] 30 cert206 (by decide +kernel)

def cert207 : Local := ⟨⟨0,360,307,338,74,0,314,122,106⟩,[(0,1),(5,6)],[(2,0,0),(7,5,5),(0,6,2)]⟩
theorem node207 : UpperPrefix a [2,4,6,5,8,7,0] 30 :=
  local_sound a [2,4,6,5,8,7,0] 30 cert207 (by decide +kernel)

def cert208 : Leaf := ⟨⟨0,361,307,336,73,0,313,121,105⟩,[(0,1),(5,6)],[(2,0,0),(7,5,5)],⟨7,22,76,41,304,224,194,393,281⟩,⟨7,22,76,41,304,224,194,384,272⟩,[⟨1,1252691876371440975478785,⟨445,52,508,441,304,224,224,384,272⟩⟩]⟩
theorem node208 : UpperPrefix a [2,4,6,5,8,7,1] 30 :=
  Boolean.leaf_sound a [2,4,6,5,8,7,1] 30 cert208 (by decide +kernel)

def cert209 : Local := ⟨⟨0,353,0,338,67,0,307,115,99⟩,[(0,1),(2,6),(5,6)],[(2,0,0),(7,5,5),(3,6,2)]⟩
theorem node209 : UpperPrefix a [2,4,6,5,8,7,3] 30 :=
  local_sound a [2,4,6,5,8,7,3] 30 cert209 (by decide +kernel)

theorem node210 : UpperPrefix a [2,4,6,5,8,7] 30 :=
  branch_upper a [2,4,6,5,8,7] 30 (by decide) (fin9_cases _
  node207
  node208
  (invalid_upper a [2,4,6,5,8,7,2] 30 (by decide +kernel))
  node209
  (invalid_upper a [2,4,6,5,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,7,8] 30 (by decide +kernel)))

theorem node211 : UpperPrefix a [2,4,6,5,8] 30 :=
  branch_upper a [2,4,6,5,8] 30 (by decide) (fin9_cases _
  node204
  node205
  (invalid_upper a [2,4,6,5,8,2] 30 (by decide +kernel))
  node206
  (invalid_upper a [2,4,6,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,6] 30 (by decide +kernel))
  node210
  (invalid_upper a [2,4,6,5,8,8] 30 (by decide +kernel)))

theorem node212 : UpperPrefix a [2,4,6,5] 30 :=
  branch_upper a [2,4,6,5] 30 (by decide) (fin9_cases _
  node187
  node192
  (invalid_upper a [2,4,6,5,2] 30 (by decide +kernel))
  node193
  (invalid_upper a [2,4,6,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,6] 30 (by decide +kernel))
  node203
  node211)

def cert213 : Leaf := ⟨⟨0,105,177,48,10,25,313,57,41⟩,[(0,1)],[(2,0,0),(7,3,2),(1,5,4)],⟨7,22,76,137,49,98,488,424,312⟩,⟨7,22,76,137,49,98,192,384,272⟩,[⟨8,1181748068846534717047,⟨55,55,127,155,55,127,255,128,19⟩⟩,⟨6,1437222725400064812909571,⟨15,415,12,137,441,443,128,384,408⟩⟩]⟩
theorem node213 : UpperPrefix a [2,4,6,7,0,1] 30 :=
  Boolean.leaf_sound a [2,4,6,7,0,1] 30 cert213 (by decide +kernel)

def cert214 : Leaf := ⟨⟨0,360,0,370,330,0,314,122,106⟩,[(0,1),(2,5),(5,2)],[(2,0,0),(7,3,2),(7,3,5)],⟨7,22,76,137,49,104,482,418,306⟩,⟨7,22,76,137,49,104,192,384,272⟩,[⟨0,1295285748739989696422912,⟨486,502,108,236,502,108,192,384,466⟩⟩]⟩
theorem node214 : UpperPrefix a [2,4,6,7,0,3] 30 :=
  Boolean.leaf_sound a [2,4,6,7,0,3] 30 cert214 (by decide +kernel)

def cert215 : Leaf := ⟨⟨0,105,163,96,74,27,313,105,105⟩,[(0,1)],[(2,0,0),(7,3,2)],⟨7,22,76,137,49,352,194,424,312⟩,⟨7,22,76,137,49,352,194,384,272⟩,[⟨8,1181745671430149792883,⟨7,23,77,137,55,127,207,128,19⟩⟩,⟨1,1285813002962357833433089,⟨5,412,76,137,441,352,192,384,408⟩⟩,⟨4,1210402713187946584867907,⟨7,15,77,137,173,493,207,384,264⟩⟩]⟩
theorem node215 : UpperPrefix a [2,4,6,7,0,8,1] 30 :=
  Boolean.leaf_sound a [2,4,6,7,0,8,1] 30 cert215 (by decide +kernel)

def cert216 : Local := ⟨⟨0,353,0,370,322,19,0,115,99⟩,[(0,1),(2,6),(6,3)],[(2,0,0),(7,3,2),(7,3,6),(3,6,2)]⟩
theorem node216 : UpperPrefix a [2,4,6,7,0,8,3] 30 :=
  local_sound a [2,4,6,7,0,8,3] 30 cert216 (by decide +kernel)

def cert217 : Leaf := ⟨⟨0,73,145,82,72,25,281,91,75⟩,[(0,1)],[(2,0,0),(7,3,2),(8,5,6)],⟨7,22,76,137,49,352,224,394,282⟩,⟨7,22,76,137,49,352,224,384,272⟩,[⟨5,1297646588159777374741523,⟨399,415,76,137,415,460,196,392,411⟩⟩,⟨1,1210110019746198360948737,⟨5,20,92,253,49,352,224,480,272⟩⟩]⟩
theorem node217 : UpperPrefix a [2,4,6,7,0,8,5] 30 :=
  Boolean.leaf_sound a [2,4,6,7,0,8,5] 30 cert217 (by decide +kernel)

theorem node218 : UpperPrefix a [2,4,6,7,0,8] 30 :=
  branch_upper a [2,4,6,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,7,0,8,0] 30 (by decide +kernel))
  node215
  (invalid_upper a [2,4,6,7,0,8,2] 30 (by decide +kernel))
  node216
  (invalid_upper a [2,4,6,7,0,8,4] 30 (by decide +kernel))
  node217
  (invalid_upper a [2,4,6,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,0,8,8] 30 (by decide +kernel)))

theorem node219 : UpperPrefix a [2,4,6,7,0] 30 :=
  branch_upper a [2,4,6,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,7,0,0] 30 (by decide +kernel))
  node213
  (invalid_upper a [2,4,6,7,0,2] 30 (by decide +kernel))
  node214
  (invalid_upper a [2,4,6,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,0,7] 30 (by decide +kernel))
  node218)

def cert220 : Leaf := ⟨⟨0,97,179,50,65,18,315,59,43⟩,[(0,1)],[(2,0,0),(7,3,2)],⟨7,22,76,137,50,97,488,424,312⟩,⟨7,22,76,137,50,97,192,384,272⟩,[⟨8,1181748068846534717047,⟨55,55,127,155,55,127,255,128,19⟩⟩,⟨3,1210107565427268160327175,⟨55,55,119,147,51,115,192,384,272⟩⟩,⟨6,1285811850040853495022595,⟨15,415,12,137,443,33,128,384,408⟩⟩]⟩
theorem node220 : UpperPrefix a [2,4,6,7,1,0] 30 :=
  Boolean.leaf_sound a [2,4,6,7,1,0] 30 cert220 (by decide +kernel)

def cert221 : Leaf := ⟨⟨0,361,0,370,329,0,307,115,99⟩,[(0,1),(2,5),(5,2)],[(2,0,0),(7,3,2),(7,3,5)],⟨7,22,76,137,50,104,481,417,305⟩,⟨7,22,76,137,50,104,192,384,272⟩,[⟨3,1285813291192730763920387,⟨7,471,68,129,499,96,192,384,464⟩⟩]⟩
theorem node221 : UpperPrefix a [2,4,6,7,1,3] 30 :=
  Boolean.leaf_sound a [2,4,6,7,1,3] 30 cert221 (by decide +kernel)

def cert222 : Local := ⟨⟨0,360,435,0,328,26,0,122,106⟩,[(0,1),(3,6),(6,3)],[(2,0,0),(7,3,2),(0,6,2)]⟩
theorem node222 : UpperPrefix a [2,4,6,7,1,8,0] 30 :=
  local_sound a [2,4,6,7,1,8,0] 30 cert222 (by decide +kernel)

def cert223 : Local := ⟨⟨0,353,0,370,321,19,0,115,99⟩,[(0,1),(2,6),(6,3)],[(2,0,0),(7,3,2),(7,3,6),(3,6,2)]⟩
theorem node223 : UpperPrefix a [2,4,6,7,1,8,3] 30 :=
  local_sound a [2,4,6,7,1,8,3] 30 cert223 (by decide +kernel)

def cert224 : Leaf := ⟨⟨0,104,162,98,72,10,266,107,107⟩,[(0,1)],[(2,0,0),(7,3,2),(8,5,6)],⟨7,22,76,137,50,352,224,393,281⟩,⟨7,22,76,137,50,352,224,384,272⟩,[⟨0,1210110019746198360955904,⟨6,22,94,254,50,352,224,480,272⟩⟩,⟨4,1212476400139988370457619,⟨7,7,76,237,103,492,228,492,493⟩⟩]⟩
theorem node224 : UpperPrefix a [2,4,6,7,1,8,5] 30 :=
  Boolean.leaf_sound a [2,4,6,7,1,8,5] 30 cert224 (by decide +kernel)

theorem node225 : UpperPrefix a [2,4,6,7,1,8] 30 :=
  branch_upper a [2,4,6,7,1,8] 30 (by decide) (fin9_cases _
  node222
  (invalid_upper a [2,4,6,7,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,1,8,2] 30 (by decide +kernel))
  node223
  (invalid_upper a [2,4,6,7,1,8,4] 30 (by decide +kernel))
  node224
  (invalid_upper a [2,4,6,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,1,8,8] 30 (by decide +kernel)))

theorem node226 : UpperPrefix a [2,4,6,7,1] 30 :=
  branch_upper a [2,4,6,7,1] 30 (by decide) (fin9_cases _
  node220
  (invalid_upper a [2,4,6,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,1,2] 30 (by decide +kernel))
  node221
  (invalid_upper a [2,4,6,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,1,7] 30 (by decide +kernel))
  node225)

def cert227 : Leaf := ⟨⟨0,104,178,114,67,18,306,114,98⟩,[(0,1)],[(2,0,0),(7,3,2),(3,4,1),(0,5,4)],⟨7,22,76,137,56,97,482,418,306⟩,⟨7,22,76,137,56,97,192,384,272⟩,[⟨8,1181748068640376286839,⟨55,55,127,139,63,127,255,128,19⟩⟩]⟩
theorem node227 : UpperPrefix a [2,4,6,7,3,0] 30 :=
  Boolean.leaf_sound a [2,4,6,7,3,0] 30 cert227 (by decide +kernel)

def cert228 : Leaf := ⟨⟨0,105,179,50,3,17,307,51,35⟩,[(0,1)],[(2,0,0),(7,3,2),(3,4,1)],⟨7,22,76,137,56,98,481,417,305⟩,⟨7,22,76,137,56,98,192,384,272⟩,[⟨8,1181748068640376286839,⟨55,55,127,139,63,127,255,128,19⟩⟩,⟨6,1361517287721558397158403,⟨7,23,12,137,440,443,128,384,272⟩⟩]⟩
theorem node228 : UpperPrefix a [2,4,6,7,3,1] 30 :=
  Boolean.leaf_sound a [2,4,6,7,3,1] 30 cert228 (by decide +kernel)

def cert229 : Local := ⟨⟨0,360,435,0,322,18,0,114,98⟩,[(0,1),(3,6),(6,3)],[(2,0,0),(7,3,2),(3,4,1),(0,6,2)]⟩
theorem node229 : UpperPrefix a [2,4,6,7,3,8,0] 30 :=
  local_sound a [2,4,6,7,3,8,0] 30 cert229 (by decide +kernel)

def cert230 : Leaf := ⟨⟨0,104,178,114,66,18,304,115,99⟩,[(0,1)],[(2,0,0),(7,3,2),(3,4,1)],⟨7,22,76,137,56,352,194,417,305⟩,⟨7,22,76,137,56,352,194,384,272⟩,[⟨0,1210110019746198365289472,⟨6,22,94,254,126,354,226,482,278⟩⟩,⟨8,1181745671430149792883,⟨7,23,77,137,63,127,207,128,19⟩⟩]⟩
theorem node230 : UpperPrefix a [2,4,6,7,3,8,1] 30 :=
  Boolean.leaf_sound a [2,4,6,7,3,8,1] 30 cert230 (by decide +kernel)

def cert231 : Leaf := ⟨⟨0,104,178,114,66,18,274,115,99⟩,[(0,1)],[(2,0,0),(7,3,2),(3,4,1),(8,5,6)],⟨7,22,76,137,56,352,224,387,275⟩,⟨7,22,76,137,56,352,224,384,272⟩,[⟨0,1210110019746198365289472,⟨6,22,94,254,126,354,224,482,278⟩⟩]⟩
theorem node231 : UpperPrefix a [2,4,6,7,3,8,5] 30 :=
  Boolean.leaf_sound a [2,4,6,7,3,8,5] 30 cert231 (by decide +kernel)

theorem node232 : UpperPrefix a [2,4,6,7,3,8] 30 :=
  branch_upper a [2,4,6,7,3,8] 30 (by decide) (fin9_cases _
  node229
  node230
  (invalid_upper a [2,4,6,7,3,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,8,4] 30 (by decide +kernel))
  node231
  (invalid_upper a [2,4,6,7,3,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,8,8] 30 (by decide +kernel)))

theorem node233 : UpperPrefix a [2,4,6,7,3] 30 :=
  branch_upper a [2,4,6,7,3] 30 (by decide) (fin9_cases _
  node227
  node228
  (invalid_upper a [2,4,6,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,7] 30 (by decide +kernel))
  node232)

def cert234 : Leaf := ⟨⟨0,105,177,48,9,26,313,57,41⟩,[(0,1)],[(2,0,0),(7,3,2),(1,6,5)],⟨7,22,76,137,304,97,194,424,312⟩,⟨7,22,76,137,304,97,194,384,272⟩,[⟨6,1437222725400071255360515,⟨15,415,12,137,440,441,139,384,400⟩⟩,⟨8,1181748061768428561491,⟨39,55,109,137,55,109,239,128,19⟩⟩]⟩
theorem node234 : UpperPrefix a [2,4,6,7,8,0,1] 30 :=
  Boolean.leaf_sound a [2,4,6,7,8,0,1] 30 cert234 (by decide +kernel)

def cert235 : Local := ⟨⟨0,353,0,370,67,274,0,115,99⟩,[(0,1),(2,6),(6,3)],[(2,0,0),(7,3,2),(7,3,6),(3,6,2)]⟩
theorem node235 : UpperPrefix a [2,4,6,7,8,0,3] 30 :=
  local_sound a [2,4,6,7,8,0,3] 30 cert235 (by decide +kernel)

def cert236 : Leaf := ⟨⟨0,329,385,338,75,264,265,91,75⟩,[(0,1)],[(2,0,0),(7,3,2)],⟨7,22,76,137,304,97,224,394,282⟩,⟨7,22,76,137,304,97,224,384,272⟩,[⟨5,1297646588159781686486035,⟨399,415,76,137,415,205,204,392,411⟩⟩,⟨1,1210107709680514740781057,⟨5,20,108,237,304,97,224,384,272⟩⟩,⟨4,1210107709679415229154307,⟨7,7,108,237,288,97,224,384,256⟩⟩]⟩
theorem node236 : UpperPrefix a [2,4,6,7,8,0,5] 30 :=
  Boolean.leaf_sound a [2,4,6,7,8,0,5] 30 cert236 (by decide +kernel)

theorem node237 : UpperPrefix a [2,4,6,7,8,0] 30 :=
  branch_upper a [2,4,6,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,7,8,0,0] 30 (by decide +kernel))
  node234
  (invalid_upper a [2,4,6,7,8,0,2] 30 (by decide +kernel))
  node235
  (invalid_upper a [2,4,6,7,8,0,4] 30 (by decide +kernel))
  node236
  (invalid_upper a [2,4,6,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,0,8] 30 (by decide +kernel)))

def cert238 : Local := ⟨⟨0,360,435,0,74,280,0,122,106⟩,[(0,1),(3,6),(6,3)],[(2,0,0),(7,3,2),(0,6,2)]⟩
theorem node238 : UpperPrefix a [2,4,6,7,8,1,0] 30 :=
  local_sound a [2,4,6,7,8,1,0] 30 cert238 (by decide +kernel)

def cert239 : Local := ⟨⟨0,353,0,370,67,273,0,115,99⟩,[(0,1),(2,6),(6,3)],[(2,0,0),(7,3,2),(7,3,6),(3,6,2)]⟩
theorem node239 : UpperPrefix a [2,4,6,7,8,1,3] 30 :=
  local_sound a [2,4,6,7,8,1,3] 30 cert239 (by decide +kernel)

def cert240 : Leaf := ⟨⟨0,329,387,322,75,265,267,75,75⟩,[(0,1)],[(2,0,0),(7,3,2)],⟨7,22,76,137,304,98,224,393,281⟩,⟨7,22,76,137,304,98,224,384,272⟩,[⟨4,1210255607715267318907939,⟨111,239,76,237,493,111,237,388,460⟩⟩,⟨5,1297941736064969629246515,⟨399,415,76,137,415,463,205,392,411⟩⟩]⟩
theorem node240 : UpperPrefix a [2,4,6,7,8,1,5] 30 :=
  Boolean.leaf_sound a [2,4,6,7,8,1,5] 30 cert240 (by decide +kernel)

theorem node241 : UpperPrefix a [2,4,6,7,8,1] 30 :=
  branch_upper a [2,4,6,7,8,1] 30 (by decide) (fin9_cases _
  node238
  (invalid_upper a [2,4,6,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,1,2] 30 (by decide +kernel))
  node239
  (invalid_upper a [2,4,6,7,8,1,4] 30 (by decide +kernel))
  node240
  (invalid_upper a [2,4,6,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,1,8] 30 (by decide +kernel)))

def cert242 : Leaf := ⟨⟨0,360,0,370,75,0,315,123,107⟩,[(0,1),(2,5),(5,2)],[(2,0,0),(7,3,2),(7,3,5)],⟨7,22,76,137,304,104,227,419,307⟩,⟨7,22,76,137,304,104,192,384,272⟩,[⟨0,1210107565424589182870528,⟨38,54,108,136,310,108,192,384,274⟩⟩]⟩
theorem node242 : UpperPrefix a [2,4,6,7,8,3] 30 :=
  Boolean.leaf_sound a [2,4,6,7,8,3] 30 cert242 (by decide +kernel)

theorem node243 : UpperPrefix a [2,4,6,7,8] 30 :=
  branch_upper a [2,4,6,7,8] 30 (by decide) (fin9_cases _
  node237
  node241
  (invalid_upper a [2,4,6,7,8,2] 30 (by decide +kernel))
  node242
  (invalid_upper a [2,4,6,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,8] 30 (by decide +kernel)))

theorem node244 : UpperPrefix a [2,4,6,7] 30 :=
  branch_upper a [2,4,6,7] 30 (by decide) (fin9_cases _
  node219
  node226
  (invalid_upper a [2,4,6,7,2] 30 (by decide +kernel))
  node233
  (invalid_upper a [2,4,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,7] 30 (by decide +kernel))
  node243)

def cert245 : Leaf := ⟨⟨0,353,433,176,258,273,313,57,169⟩,[(0,1)],[(2,0,0),(1,5,4)],⟨7,22,76,265,49,98,232,424,440⟩,⟨7,22,76,265,49,98,192,384,272⟩,[⟨6,1437222725400064812909571,⟨15,415,12,265,441,443,128,384,408⟩⟩,⟨3,1210107565427268160327175,⟨55,55,119,275,51,115,192,384,272⟩⟩,⟨7,1208926973806551822765575,⟨55,55,127,283,51,115,64,256,272⟩⟩]⟩
theorem node245 : UpperPrefix a [2,4,6,8,0,1] 30 :=
  Boolean.leaf_sound a [2,4,6,8,0,1] 30 cert245 (by decide +kernel)

def cert246 : Leaf := ⟨⟨0,488,0,242,458,0,314,122,234⟩,[(0,1),(2,5),(5,2)],[(2,0,0)],⟨7,22,76,265,49,104,226,418,434⟩,⟨7,22,76,265,49,104,192,384,272⟩,[⟨0,1295285748739989696422912,⟨486,502,108,492,502,108,192,384,466⟩⟩]⟩
theorem node246 : UpperPrefix a [2,4,6,8,0,3] 30 :=
  Boolean.leaf_sound a [2,4,6,8,0,3] 30 cert246 (by decide +kernel)

def cert247 : Leaf := ⟨⟨0,361,307,48,330,0,313,57,41⟩,[(0,1),(5,6)],[(2,0,0),(7,5,5)],⟨7,22,76,265,49,224,194,424,312⟩,⟨7,22,76,265,49,224,194,384,272⟩,[⟨1,1285813005214157647118337,⟨5,412,108,265,441,224,224,384,408⟩⟩,⟨6,1285811850040853495022595,⟨15,415,12,265,441,160,139,384,408⟩⟩]⟩
theorem node247 : UpperPrefix a [2,4,6,8,0,7,1] 30 :=
  Boolean.leaf_sound a [2,4,6,8,0,7,1] 30 cert247 (by decide +kernel)

def cert248 : Local := ⟨⟨0,97,0,114,66,0,307,115,99⟩,[(0,1),(2,6),(5,6)],[(2,0,0),(8,3,6),(7,5,5),(3,6,2)]⟩
theorem node248 : UpperPrefix a [2,4,6,8,0,7,3] 30 :=
  local_sound a [2,4,6,8,0,7,3] 30 cert248 (by decide +kernel)

def cert249 : Local := ⟨⟨0,361,307,114,330,0,0,123,107⟩,[(0,1),(5,6),(6,5)],[(2,0,0),(7,5,5),(7,5,6)]⟩
theorem node249 : UpperPrefix a [2,4,6,8,0,7,5] 30 :=
  local_sound a [2,4,6,8,0,7,5] 30 cert249 (by decide +kernel)

theorem node250 : UpperPrefix a [2,4,6,8,0,7] 30 :=
  branch_upper a [2,4,6,8,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,8,0,7,0] 30 (by decide +kernel))
  node247
  (invalid_upper a [2,4,6,8,0,7,2] 30 (by decide +kernel))
  node248
  (invalid_upper a [2,4,6,8,0,7,4] 30 (by decide +kernel))
  node249
  (invalid_upper a [2,4,6,8,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,0,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,0,7,8] 30 (by decide +kernel)))

theorem node251 : UpperPrefix a [2,4,6,8,0] 30 :=
  branch_upper a [2,4,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,8,0,0] 30 (by decide +kernel))
  node245
  (invalid_upper a [2,4,6,8,0,2] 30 (by decide +kernel))
  node246
  (invalid_upper a [2,4,6,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,0,6] 30 (by decide +kernel))
  node250
  (invalid_upper a [2,4,6,8,0,8] 30 (by decide +kernel)))

def cert252 : Leaf := ⟨⟨0,353,417,178,321,256,297,41,171⟩,[(0,1)],[(2,0,0)],⟨7,22,76,265,50,97,232,424,440⟩,⟨7,22,76,265,50,97,192,384,272⟩,[⟨1,1210181568749587989004289,⟨101,84,236,493,48,97,192,384,272⟩⟩,⟨4,1210181568818857221555203,⟨103,103,236,493,35,97,192,384,256⟩⟩,⟨3,1210107565427268160327175,⟨55,55,119,275,51,115,192,384,272⟩⟩,⟨6,1285811850040853495022595,⟨15,415,12,265,443,33,128,384,408⟩⟩,⟨7,1208926973806551822765575,⟨55,55,127,283,51,115,64,256,272⟩⟩]⟩
theorem node252 : UpperPrefix a [2,4,6,8,1,0] 30 :=
  Boolean.leaf_sound a [2,4,6,8,1,0] 30 cert252 (by decide +kernel)

def cert253 : Leaf := ⟨⟨0,489,0,226,457,0,291,99,227⟩,[(0,1),(2,5),(5,2)],[(2,0,0)],⟨7,22,76,265,50,104,225,417,433⟩,⟨7,22,76,265,50,104,192,384,272⟩,[⟨3,1285813291192730763920387,⟨7,471,68,257,499,96,192,384,464⟩⟩,⟨4,1212547305234734156612627,⟨39,39,236,493,39,236,228,492,493⟩⟩]⟩
theorem node253 : UpperPrefix a [2,4,6,8,1,3] 30 :=
  Boolean.leaf_sound a [2,4,6,8,1,3] 30 cert253 (by decide +kernel)

def cert254 : Leaf := ⟨⟨0,361,289,114,329,0,297,105,107⟩,[(0,1),(5,6)],[(2,0,0),(7,5,5)],⟨7,22,76,265,50,224,233,425,313⟩,⟨7,22,76,265,50,224,192,384,272⟩,[⟨1,1210181499049346881028097,⟨37,52,236,493,48,224,224,384,272⟩⟩,⟨4,1210181499048247369401347,⟨39,39,236,493,35,224,224,384,256⟩⟩]⟩
theorem node254 : UpperPrefix a [2,4,6,8,1,7] 30 :=
  Boolean.leaf_sound a [2,4,6,8,1,7] 30 cert254 (by decide +kernel)

theorem node255 : UpperPrefix a [2,4,6,8,1] 30 :=
  branch_upper a [2,4,6,8,1] 30 (by decide) (fin9_cases _
  node252
  (invalid_upper a [2,4,6,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,1,2] 30 (by decide +kernel))
  node253
  (invalid_upper a [2,4,6,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,1,6] 30 (by decide +kernel))
  node254
  (invalid_upper a [2,4,6,8,1,8] 30 (by decide +kernel)))

#print axioms node255
end Delivery.FiniteExclusion.Sharp4x5
