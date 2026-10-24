import RegularNineSharp2x7Base
import RegularNineSharp2x7C002
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x7
open Bounds BoundTreeRows Extremal
def cert192 : Local := ⟨⟨344,340,275,0,71,0,279,87,83⟩,[(3,4),(5,6)],[(3,1,0),(5,3,3),(7,5,5)]⟩
theorem node192 : UpperPrefix a [2,3,6,5,8,7] 30 :=
  local_sound a [2,3,6,5,8,7] 30 cert192 (by decide +kernel)

theorem node193 : UpperPrefix a [2,3,6,5,8] 30 :=
  branch_upper a [2,3,6,5,8] 30 (by decide) (fin9_cases _
  node189
  node190
  (invalid_upper a [2,3,6,5,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,8,3] 30 (by decide +kernel))
  node191
  (invalid_upper a [2,3,6,5,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,8,6] 30 (by decide +kernel))
  node192
  (invalid_upper a [2,3,6,5,8,8] 30 (by decide +kernel)))

theorem node194 : UpperPrefix a [2,3,6,5] 30 :=
  branch_upper a [2,3,6,5] 30 (by decide) (fin9_cases _
  node182
  node183
  (invalid_upper a [2,3,6,5,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,6] 30 (by decide +kernel))
  node188
  node193)

def cert195 : Leaf := ⟨⟨104,100,176,100,70,5,308,116,112⟩,[],[(3,1,0),(7,3,2),(1,5,4)],⟨7,11,76,152,49,98,496,432,308⟩,⟨7,11,76,152,49,98,192,384,260⟩,[⟨8,1181748086318461738357,⟨55,27,127,155,55,127,255,155,55⟩⟩,⟨0,1285813291192733991437312,⟨6,14,76,476,508,98,192,384,260⟩⟩,⟨4,1210107565423489662848261,⟨39,11,111,136,33,98,192,385,295⟩⟩]⟩
theorem node195 : UpperPrefix a [2,3,6,7,0,1] 30 :=
  Boolean.leaf_sound a [2,3,6,7,0,1] 30 cert195 (by decide +kernel)

def cert196 : Leaf := ⟨⟨104,100,160,100,70,7,37,116,112⟩,[],[(3,1,0),(7,3,2)],⟨7,11,76,152,49,112,194,416,292⟩,⟨7,11,76,152,49,112,194,384,260⟩,[⟨8,1184202909442423512575,⟨55,127,127,255,55,127,255,255,55⟩⟩,⟨0,1437223878319370136454144,⟨6,10,76,408,444,508,194,384,260⟩⟩,⟨1,1437223878319370136453121,⟨5,9,76,408,445,508,192,384,260⟩⟩,⟨4,1210107709397940252974415,⟨7,79,79,207,33,97,199,385,263⟩⟩]⟩
theorem node196 : UpperPrefix a [2,3,6,7,0,4,1] 30 :=
  Boolean.leaf_sound a [2,3,6,7,0,4,1] 30 cert196 (by decide +kernel)

def cert197 : Leaf := ⟨⟨88,84,146,70,70,6,22,86,82⟩,[],[(3,1,0),(7,3,2),(5,6,5)],⟨7,11,76,152,49,112,224,386,262⟩,⟨7,11,76,152,49,112,224,384,260⟩,[⟨8,1184202909442423512575,⟨55,127,127,255,55,127,255,255,55⟩⟩,⟨0,1224302804067359525438464,⟨454,494,108,252,508,124,228,384,260⟩⟩]⟩
theorem node197 : UpperPrefix a [2,3,6,7,0,4,5] 30 :=
  Boolean.leaf_sound a [2,3,6,7,0,4,5] 30 cert197 (by decide +kernel)

def cert198 : Leaf := ⟨⟨120,116,176,103,68,4,0,118,114⟩,[(6,7)],[(3,1,0),(7,3,2),(8,6,6)],⟨7,11,76,152,49,112,448,418,294⟩,⟨7,11,76,152,49,112,448,384,260⟩,[⟨0,1219573105724294360990720,⟨454,494,108,252,112,112,448,448,260⟩⟩,⟨1,1210109871408473317572609,⟨21,61,108,252,49,112,448,448,260⟩⟩]⟩
theorem node198 : UpperPrefix a [2,3,6,7,0,4,8] 30 :=
  Boolean.leaf_sound a [2,3,6,7,0,4,8] 30 cert198 (by decide +kernel)

theorem node199 : UpperPrefix a [2,3,6,7,0,4] 30 :=
  branch_upper a [2,3,6,7,0,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,7,0,4,0] 30 (by decide +kernel))
  node196
  (invalid_upper a [2,3,6,7,0,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,4,4] 30 (by decide +kernel))
  node197
  (invalid_upper a [2,3,6,7,0,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,4,7] 30 (by decide +kernel))
  node198)

def cert200 : Leaf := ⟨⟨8,4,131,295,6,23,5,55,115⟩,[],[(3,1,0),(7,3,2)],⟨7,11,76,152,49,352,194,432,308⟩,⟨7,11,76,152,49,352,194,384,260⟩,[⟨6,1210401560269731897830661,⟨7,11,15,154,187,443,130,385,263⟩⟩,⟨8,1181889786609613151567,⟨7,79,79,223,49,113,199,129,7⟩⟩,⟨4,1210107709397940252974415,⟨7,79,79,207,33,353,199,385,263⟩⟩,⟨5,1210107708273139857759567,⟨7,79,79,223,17,321,199,385,263⟩⟩]⟩
theorem node200 : UpperPrefix a [2,3,6,7,0,8,1] 30 :=
  Boolean.leaf_sound a [2,3,6,7,0,8,1] 30 cert200 (by decide +kernel)

def cert201 : Local := ⟨⟨360,356,435,0,326,7,0,103,99⟩,[(3,6),(6,3)],[(3,1,0),(7,3,2),(4,6,2)]⟩
theorem node201 : UpperPrefix a [2,3,6,7,0,8,4] 30 :=
  local_sound a [2,3,6,7,0,8,4] 30 cert201 (by decide +kernel)

def cert202 : Leaf := ⟨⟨40,36,162,39,6,6,262,55,115⟩,[],[(3,1,0),(7,3,2),(8,5,6)],⟨7,11,76,152,49,352,224,402,278⟩,⟨7,11,76,152,49,352,224,384,260⟩,[⟨4,1210110019744549094038799,⟨7,79,79,239,33,353,224,481,263⟩⟩,⟨6,1210401560269740487765253,⟨7,11,15,154,187,443,186,385,263⟩⟩,⟨0,1210110019745648605660160,⟨6,78,76,252,48,352,224,480,260⟩⟩]⟩
theorem node202 : UpperPrefix a [2,3,6,7,0,8,5] 30 :=
  Boolean.leaf_sound a [2,3,6,7,0,8,5] 30 cert202 (by decide +kernel)

theorem node203 : UpperPrefix a [2,3,6,7,0,8] 30 :=
  branch_upper a [2,3,6,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,7,0,8,0] 30 (by decide +kernel))
  node200
  (invalid_upper a [2,3,6,7,0,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,8,3] 30 (by decide +kernel))
  node201
  node202
  (invalid_upper a [2,3,6,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,8,8] 30 (by decide +kernel)))

theorem node204 : UpperPrefix a [2,3,6,7,0] 30 :=
  branch_upper a [2,3,6,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,7,0,0] 30 (by decide +kernel))
  node195
  (invalid_upper a [2,3,6,7,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,3] 30 (by decide +kernel))
  node199
  (invalid_upper a [2,3,6,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,7] 30 (by decide +kernel))
  node203)

def cert205 : Leaf := ⟨⟨104,100,176,100,69,6,308,116,112⟩,[],[(3,1,0),(7,3,2),(0,5,4)],⟨7,11,76,152,50,97,496,432,308⟩,⟨7,11,76,152,50,97,192,384,260⟩,[⟨8,1181748086318461738357,⟨55,27,127,155,55,127,255,155,55⟩⟩,⟨1,1285813291192733991436289,⟨5,13,76,476,508,97,192,384,260⟩⟩,⟨4,1210107565423489662848261,⟨39,11,111,136,34,97,192,385,295⟩⟩]⟩
theorem node205 : UpperPrefix a [2,3,6,7,1,0] 30 :=
  Boolean.leaf_sound a [2,3,6,7,1,0] 30 cert205 (by decide +kernel)

def cert206 : Leaf := ⟨⟨104,100,161,101,69,5,36,101,97⟩,[],[(3,1,0),(7,3,2)],⟨7,11,76,152,50,112,193,416,292⟩,⟨7,11,76,152,50,112,193,384,260⟩,[⟨8,1184202909442423512575,⟨55,127,127,255,55,127,255,255,55⟩⟩,⟨1,1475076633750369113473025,⟨69,461,460,444,508,508,193,384,260⟩⟩,⟨4,1286111465515761274461471,⟨7,79,79,463,487,481,193,449,263⟩⟩]⟩
theorem node206 : UpperPrefix a [2,3,6,7,1,4,0] 30 :=
  Boolean.leaf_sound a [2,3,6,7,1,4,0] 30 cert206 (by decide +kernel)

def cert207 : Leaf := ⟨⟨88,84,145,69,69,5,21,85,81⟩,[],[(3,1,0),(7,3,2),(5,6,5)],⟨7,11,76,152,50,112,224,385,261⟩,⟨7,11,76,152,50,112,224,384,260⟩,[⟨8,1184202909442423512575,⟨55,127,127,255,55,127,255,255,55⟩⟩,⟨1,1224302804067359525437441,⟨453,493,108,252,508,124,228,384,260⟩⟩]⟩
theorem node207 : UpperPrefix a [2,3,6,7,1,4,5] 30 :=
  Boolean.leaf_sound a [2,3,6,7,1,4,5] 30 cert207 (by decide +kernel)

def cert208 : Leaf := ⟨⟨120,116,177,101,69,5,0,117,113⟩,[(6,7)],[(3,1,0),(7,3,2),(8,6,6)],⟨7,11,76,152,50,112,448,417,293⟩,⟨7,11,76,152,50,112,448,384,260⟩,[⟨1,1219573393954672672768001,⟨453,493,108,252,508,124,448,448,260⟩⟩]⟩
theorem node208 : UpperPrefix a [2,3,6,7,1,4,8] 30 :=
  Boolean.leaf_sound a [2,3,6,7,1,4,8] 30 cert208 (by decide +kernel)

theorem node209 : UpperPrefix a [2,3,6,7,1,4] 30 :=
  branch_upper a [2,3,6,7,1,4] 30 (by decide) (fin9_cases _
  node206
  (invalid_upper a [2,3,6,7,1,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,4,4] 30 (by decide +kernel))
  node207
  (invalid_upper a [2,3,6,7,1,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,4,7] 30 (by decide +kernel))
  node208)

def cert210 : Leaf := ⟨⟨360,356,416,356,324,4,292,116,112⟩,[],[(3,1,0),(7,3,2)],⟨7,11,76,152,50,352,193,432,308⟩,⟨7,11,76,152,50,352,193,384,260⟩,[⟨0,1593366345923895372022784,⟨446,410,492,408,446,492,508,384,292⟩⟩,⟨1,1323665758604463042985985,⟨101,493,492,444,508,352,193,384,292⟩⟩,⟨4,1210110019744549094038815,⟨7,79,79,239,39,353,225,481,263⟩⟩]⟩
theorem node210 : UpperPrefix a [2,3,6,7,1,8,0] 30 :=
  Boolean.leaf_sound a [2,3,6,7,1,8,0] 30 cert210 (by decide +kernel)

def cert211 : Local := ⟨⟨360,356,435,0,325,7,0,103,99⟩,[(3,6),(6,3)],[(3,1,0),(7,3,2),(4,6,2)]⟩
theorem node211 : UpperPrefix a [2,3,6,7,1,8,4] 30 :=
  local_sound a [2,3,6,7,1,8,4] 30 cert211 (by decide +kernel)

def cert212 : Leaf := ⟨⟨40,36,163,39,5,7,263,55,51⟩,[],[(3,1,0),(7,3,2),(8,5,6)],⟨7,11,76,152,50,352,224,401,277⟩,⟨7,11,76,152,50,352,224,384,260⟩,[⟨6,1229327919693765071228677,⟨399,11,415,152,186,443,186,387,399⟩⟩,⟨4,1210110019744549094038815,⟨7,79,79,239,39,353,224,481,263⟩⟩]⟩
theorem node212 : UpperPrefix a [2,3,6,7,1,8,5] 30 :=
  Boolean.leaf_sound a [2,3,6,7,1,8,5] 30 cert212 (by decide +kernel)

theorem node213 : UpperPrefix a [2,3,6,7,1,8] 30 :=
  branch_upper a [2,3,6,7,1,8] 30 (by decide) (fin9_cases _
  node210
  (invalid_upper a [2,3,6,7,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,8,3] 30 (by decide +kernel))
  node211
  node212
  (invalid_upper a [2,3,6,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,8,8] 30 (by decide +kernel)))

theorem node214 : UpperPrefix a [2,3,6,7,1] 30 :=
  branch_upper a [2,3,6,7,1] 30 (by decide) (fin9_cases _
  node205
  (invalid_upper a [2,3,6,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,3] 30 (by decide +kernel))
  node209
  (invalid_upper a [2,3,6,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,7] 30 (by decide +kernel))
  node213)

def cert215 : Leaf := ⟨⟨104,100,160,356,68,6,37,116,112⟩,[],[(3,1,0),(7,3,2),(8,4,3),(1,6,5)],⟨7,11,76,152,304,97,194,432,308⟩,⟨7,11,76,152,304,97,194,384,260⟩,[⟨0,1437223878321569159709696,⟨6,10,76,408,444,508,194,384,260⟩⟩,⟨4,1210107712142321275903311,⟨39,111,111,239,289,97,231,385,295⟩⟩]⟩
theorem node215 : UpperPrefix a [2,3,6,7,8,0,1] 30 :=
  Boolean.leaf_sound a [2,3,6,7,8,0,1] 30 cert215 (by decide +kernel)

def cert216 : Local := ⟨⟨104,100,179,0,71,6,0,103,99⟩,[(3,6),(6,3)],[(3,1,0),(7,3,2),(8,4,3),(8,4,6),(4,6,2)]⟩
theorem node216 : UpperPrefix a [2,3,6,7,8,0,4] 30 :=
  local_sound a [2,3,6,7,8,0,4] 30 cert216 (by decide +kernel)

def cert217 : Leaf := ⟨⟨8,4,163,263,71,6,7,23,115⟩,[],[(3,1,0),(7,3,2),(8,4,3)],⟨7,11,76,152,304,97,224,402,278⟩,⟨7,11,76,152,304,97,224,384,260⟩,[⟨4,1210110020237130303282447,⟨39,111,111,239,289,97,224,481,295⟩⟩,⟨5,1210255138110543603182853,⟨7,11,79,154,411,65,192,385,263⟩⟩,⟨6,1210253986314938903178501,⟨7,11,15,154,443,33,160,385,263⟩⟩]⟩
theorem node217 : UpperPrefix a [2,3,6,7,8,0,5] 30 :=
  Boolean.leaf_sound a [2,3,6,7,8,0,5] 30 cert217 (by decide +kernel)

theorem node218 : UpperPrefix a [2,3,6,7,8,0] 30 :=
  branch_upper a [2,3,6,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,7,8,0,0] 30 (by decide +kernel))
  node215
  (invalid_upper a [2,3,6,7,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,0,3] 30 (by decide +kernel))
  node216
  node217
  (invalid_upper a [2,3,6,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,0,8] 30 (by decide +kernel)))

def cert219 : Leaf := ⟨⟨120,112,176,352,64,17,54,112,112⟩,[],[(3,1,0),(7,3,2),(8,4,3),(0,6,5)],⟨7,11,76,152,304,98,193,432,308⟩,⟨7,11,76,152,304,98,193,384,260⟩,[⟨1,1437223878321569159708673,⟨5,9,76,408,444,508,193,384,260⟩⟩,⟨2,1212616324888059359298561,⟨35,11,106,152,440,98,235,408,440⟩⟩]⟩
theorem node219 : UpperPrefix a [2,3,6,7,8,1,0] 30 :=
  Boolean.leaf_sound a [2,3,6,7,8,1,0] 30 cert219 (by decide +kernel)

def cert220 : Local := ⟨⟨104,100,179,0,71,5,0,103,99⟩,[(3,6),(6,3)],[(3,1,0),(7,3,2),(8,4,3),(8,4,6),(4,6,2)]⟩
theorem node220 : UpperPrefix a [2,3,6,7,8,1,4] 30 :=
  local_sound a [2,3,6,7,8,1,4] 30 cert220 (by decide +kernel)

def cert221 : Leaf := ⟨⟨8,4,163,263,71,5,7,23,115⟩,[],[(3,1,0),(7,3,2),(8,4,3)],⟨7,11,76,152,304,98,224,401,277⟩,⟨7,11,76,152,304,98,224,384,260⟩,[⟨4,1210107709890521462218031,⟨39,111,111,239,289,103,225,385,295⟩⟩,⟨5,1210255138110543603182853,⟨7,11,79,154,411,66,192,385,263⟩⟩,⟨6,1210253986314938903178501,⟨7,11,15,154,443,34,160,385,263⟩⟩]⟩
theorem node221 : UpperPrefix a [2,3,6,7,8,1,5] 30 :=
  Boolean.leaf_sound a [2,3,6,7,8,1,5] 30 cert221 (by decide +kernel)

theorem node222 : UpperPrefix a [2,3,6,7,8,1] 30 :=
  branch_upper a [2,3,6,7,8,1] 30 (by decide) (fin9_cases _
  node219
  (invalid_upper a [2,3,6,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,1,3] 30 (by decide +kernel))
  node220
  node221
  (invalid_upper a [2,3,6,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,1,8] 30 (by decide +kernel)))

def cert223 : Leaf := ⟨⟨72,68,130,358,70,6,6,118,114⟩,[],[(3,1,0),(7,3,2),(8,4,3)],⟨7,11,76,152,304,112,193,418,294⟩,⟨7,11,76,152,304,112,193,384,260⟩,[⟨0,1214839157553380637803520,⟨446,410,124,152,308,124,508,408,308⟩⟩,⟨4,1210110015240949466668303,⟨7,79,79,207,289,96,193,449,263⟩⟩,⟨5,1210110014116149071453455,⟨7,79,79,223,273,80,193,449,263⟩⟩]⟩
theorem node223 : UpperPrefix a [2,3,6,7,8,4,0] 30 :=
  Boolean.leaf_sound a [2,3,6,7,8,4,0] 30 cert223 (by decide +kernel)

def cert224 : Leaf := ⟨⟨8,4,131,295,71,7,5,39,115⟩,[],[(3,1,0),(7,3,2),(8,4,3)],⟨7,11,76,152,304,112,194,417,293⟩,⟨7,11,76,152,304,112,194,384,260⟩,[⟨4,1210255283350529929387343,⟨7,79,79,207,417,225,199,385,263⟩⟩,⟨5,1210107708273139857759567,⟨7,79,79,223,273,81,199,385,263⟩⟩,⟨6,1210253986314943198145797,⟨7,11,15,154,443,186,130,385,263⟩⟩]⟩
theorem node224 : UpperPrefix a [2,3,6,7,8,4,1] 30 :=
  Boolean.leaf_sound a [2,3,6,7,8,4,1] 30 cert224 (by decide +kernel)

def cert225 : Leaf := ⟨⟨72,68,131,327,71,7,7,71,67⟩,[],[(3,1,0),(7,3,2),(8,4,3),(5,6,5)],⟨7,11,76,152,304,112,224,387,263⟩,⟨7,11,76,152,304,112,224,384,260⟩,[⟨4,1283442884578160650755343,⟨391,399,463,463,481,96,224,385,391⟩⟩]⟩
theorem node225 : UpperPrefix a [2,3,6,7,8,4,5] 30 :=
  Boolean.leaf_sound a [2,3,6,7,8,4,5] 30 cert225 (by decide +kernel)

theorem node226 : UpperPrefix a [2,3,6,7,8,4] 30 :=
  branch_upper a [2,3,6,7,8,4] 30 (by decide) (fin9_cases _
  node223
  node224
  (invalid_upper a [2,3,6,7,8,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,4,4] 30 (by decide +kernel))
  node225
  (invalid_upper a [2,3,6,7,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,4,8] 30 (by decide +kernel)))

theorem node227 : UpperPrefix a [2,3,6,7,8] 30 :=
  branch_upper a [2,3,6,7,8] 30 (by decide) (fin9_cases _
  node218
  node222
  (invalid_upper a [2,3,6,7,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,3] 30 (by decide +kernel))
  node226
  (invalid_upper a [2,3,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,8] 30 (by decide +kernel)))

theorem node228 : UpperPrefix a [2,3,6,7] 30 :=
  branch_upper a [2,3,6,7] 30 (by decide) (fin9_cases _
  node204
  node214
  (invalid_upper a [2,3,6,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,7] 30 (by decide +kernel))
  node227)

def cert229 : Leaf := ⟨⟨104,100,304,100,70,5,308,116,240⟩,[],[(3,1,0),(1,5,4)],⟨7,11,76,280,49,98,240,432,436⟩,⟨7,11,76,280,49,98,192,384,260⟩,[⟨7,1208926976080255986670949,⟨55,27,127,283,49,119,127,283,319⟩⟩,⟨0,1285813291192733991437312,⟨6,14,76,476,508,98,192,384,260⟩⟩,⟨8,1181745827895783202053,⟨55,27,127,27,49,98,192,145,55⟩⟩,⟨4,1210107565423489662852357,⟨39,11,111,267,33,98,192,385,295⟩⟩]⟩
theorem node229 : UpperPrefix a [2,3,6,8,0,1] 30 :=
  Boolean.leaf_sound a [2,3,6,8,0,1] 30 cert229 (by decide +kernel)

def cert230 : Leaf := ⟨⟨72,68,304,100,70,7,309,116,240⟩,[],[(3,1,0)],⟨7,11,76,280,49,112,194,416,420⟩,⟨7,11,76,280,49,112,194,384,260⟩,[⟨7,1208926976080255986670949,⟨55,27,127,283,49,119,127,283,319⟩⟩,⟨0,1437223878319370136454144,⟨6,10,76,408,444,508,194,384,260⟩⟩,⟨1,1437223878319370136453121,⟨5,9,76,408,445,508,192,384,260⟩⟩,⟨8,1181745827895783202053,⟨55,27,127,27,49,112,194,145,55⟩⟩,⟨4,1210107565282752174497029,⟨7,11,79,267,33,96,194,385,263⟩⟩,⟨5,1210107564157951779282181,⟨7,11,79,283,17,80,194,385,263⟩⟩]⟩
theorem node230 : UpperPrefix a [2,3,6,8,0,4,1] 30 :=
  Boolean.leaf_sound a [2,3,6,8,0,4,1] 30 cert230 (by decide +kernel)

def cert231 : Leaf := ⟨⟨328,324,258,70,326,262,262,70,194⟩,[],[(3,1,0),(5,6,5)],⟨7,11,76,280,49,112,224,386,390⟩,⟨7,11,76,280,49,112,224,384,260⟩,[⟨0,1224302659952171449582592,⟨454,494,108,380,508,124,228,384,260⟩⟩,⟨4,1283442884578160650755343,⟨391,399,463,463,481,96,224,385,391⟩⟩,⟨7,1208926976080255986670949,⟨55,27,127,283,49,119,127,283,319⟩⟩]⟩
theorem node231 : UpperPrefix a [2,3,6,8,0,4,5] 30 :=
  Boolean.leaf_sound a [2,3,6,8,0,4,5] 30 cert231 (by decide +kernel)

theorem node232 : UpperPrefix a [2,3,6,8,0,4] 30 :=
  branch_upper a [2,3,6,8,0,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,8,0,4,0] 30 (by decide +kernel))
  node230
  (invalid_upper a [2,3,6,8,0,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,4,4] 30 (by decide +kernel))
  node231
  (invalid_upper a [2,3,6,8,0,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,4,8] 30 (by decide +kernel)))

def cert233 : Local := ⟨⟨376,372,307,0,326,0,309,0,115⟩,[(3,7),(5,6),(7,3)],[(3,1,0),(7,5,5)]⟩
theorem node233 : UpperPrefix a [2,3,6,8,0,7,1,4] 30 :=
  local_sound a [2,3,6,8,0,7,1,4] 30 cert233 (by decide +kernel)

def cert234 : Leaf := ⟨⟨360,356,290,102,326,0,292,70,114⟩,[(5,6)],[(3,1,0),(7,5,5)],⟨7,11,76,280,49,224,194,416,276⟩,⟨7,11,76,280,49,224,194,416,260⟩,[⟨0,1326082302379501689504768,⟨230,494,492,444,508,224,230,416,420⟩⟩,⟨4,1212547415643259303107919,⟨103,239,239,495,33,225,231,481,487⟩⟩]⟩
theorem node234 : UpperPrefix a [2,3,6,8,0,7,1,5] 30 :=
  Boolean.leaf_sound a [2,3,6,8,0,7,1,5] 30 cert234 (by decide +kernel)

theorem node235 : UpperPrefix a [2,3,6,8,0,7,1] 30 :=
  branch_upper a [2,3,6,8,0,7,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,8,0,7,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,7,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,7,1,3] 30 (by decide +kernel))
  node233
  node234
  (invalid_upper a [2,3,6,8,0,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,7,1,8] 30 (by decide +kernel)))

def cert236 : Leaf := ⟨⟨72,68,307,103,70,0,39,103,99⟩,[(5,6)],[(3,1,0),(7,5,5),(4,6,2)],⟨7,11,76,280,49,224,208,418,294⟩,⟨7,11,76,280,49,224,208,384,260⟩,[⟨8,1184634737454440520965,⟨23,11,127,27,113,240,240,241,23⟩⟩,⟨5,1210107564157951779282181,⟨7,11,79,283,17,192,208,385,263⟩⟩]⟩
theorem node236 : UpperPrefix a [2,3,6,8,0,7,4] 30 :=
  Boolean.leaf_sound a [2,3,6,8,0,7,4] 30 cert236 (by decide +kernel)

def cert237 : Leaf := ⟨⟨280,276,307,103,326,0,0,23,115⟩,[(5,6),(6,5)],[(3,1,0),(7,5,5),(7,5,6)],⟨7,11,76,280,49,224,224,402,278⟩,⟨7,11,76,280,49,224,224,384,260⟩,[⟨5,1210181351134246617488645,⟨7,139,207,411,17,192,192,385,263⟩⟩,⟨6,1210180199338641917484293,⟨7,139,143,411,49,160,160,385,263⟩⟩]⟩
theorem node237 : UpperPrefix a [2,3,6,8,0,7,5] 30 :=
  Boolean.leaf_sound a [2,3,6,8,0,7,5] 30 cert237 (by decide +kernel)

theorem node238 : UpperPrefix a [2,3,6,8,0,7] 30 :=
  branch_upper a [2,3,6,8,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,8,0,7,0] 30 (by decide +kernel))
  node235
  (invalid_upper a [2,3,6,8,0,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,7,3] 30 (by decide +kernel))
  node236
  node237
  (invalid_upper a [2,3,6,8,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,7,8] 30 (by decide +kernel)))

theorem node239 : UpperPrefix a [2,3,6,8,0] 30 :=
  branch_upper a [2,3,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,8,0,0] 30 (by decide +kernel))
  node229
  (invalid_upper a [2,3,6,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,3] 30 (by decide +kernel))
  node232
  (invalid_upper a [2,3,6,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,6] 30 (by decide +kernel))
  node238
  (invalid_upper a [2,3,6,8,0,8] 30 (by decide +kernel)))

def cert240 : Leaf := ⟨⟨104,100,304,100,69,6,52,116,240⟩,[],[(3,1,0),(0,5,4)],⟨7,11,76,280,50,97,240,432,436⟩,⟨7,11,76,280,50,97,192,384,260⟩,[⟨7,1208926976080255986670949,⟨55,27,127,283,51,119,127,283,319⟩⟩,⟨1,1285813291192733991436289,⟨5,13,76,476,508,97,192,384,260⟩⟩,⟨8,1184056174504624266501,⟨55,27,127,27,50,113,224,241,55⟩⟩,⟨4,1210107565423489662852357,⟨39,11,111,267,34,97,192,385,295⟩⟩]⟩
theorem node240 : UpperPrefix a [2,3,6,8,1,0] 30 :=
  Boolean.leaf_sound a [2,3,6,8,1,0] 30 cert240 (by decide +kernel)

def cert241 : Leaf := ⟨⟨104,100,289,101,69,5,36,101,225⟩,[],[(3,1,0)],⟨7,11,76,280,50,112,193,416,420⟩,⟨7,11,76,280,50,112,193,384,260⟩,[⟨1,1475076633750369113473025,⟨69,461,460,444,508,508,193,384,260⟩⟩,⟨4,1286111465515761274461471,⟨7,79,79,463,487,481,193,449,263⟩⟩,⟨7,1208926976080255986670949,⟨55,27,127,283,51,119,127,283,319⟩⟩,⟨8,1184058426304437951749,⟨55,27,127,27,50,112,241,241,55⟩⟩]⟩
theorem node241 : UpperPrefix a [2,3,6,8,1,4,0] 30 :=
  Boolean.leaf_sound a [2,3,6,8,1,4,0] 30 cert241 (by decide +kernel)

def cert242 : Leaf := ⟨⟨328,324,257,69,325,261,261,69,193⟩,[],[(3,1,0),(5,6,5)],⟨7,11,76,280,50,112,224,385,389⟩,⟨7,11,76,280,50,112,224,384,260⟩,[⟨1,1224302659952171449581569,⟨453,493,108,380,508,124,228,384,260⟩⟩,⟨4,1283591034991502630591759,⟨391,399,463,463,483,224,224,385,391⟩⟩,⟨7,1208926976080255986670949,⟨55,27,127,283,51,119,127,283,319⟩⟩]⟩
theorem node242 : UpperPrefix a [2,3,6,8,1,4,5] 30 :=
  Boolean.leaf_sound a [2,3,6,8,1,4,5] 30 cert242 (by decide +kernel)

theorem node243 : UpperPrefix a [2,3,6,8,1,4] 30 :=
  branch_upper a [2,3,6,8,1,4] 30 (by decide) (fin9_cases _
  node241
  (invalid_upper a [2,3,6,8,1,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,4,4] 30 (by decide +kernel))
  node242
  (invalid_upper a [2,3,6,8,1,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,4,8] 30 (by decide +kernel)))

def cert244 : Leaf := ⟨⟨376,372,304,100,324,0,308,116,112⟩,[(5,6)],[(3,1,0),(7,5,5)],⟨7,11,76,280,50,224,193,432,308⟩,⟨7,11,76,280,50,224,193,384,260⟩,[⟨0,1593366345923895372022784,⟨446,410,492,408,446,492,508,384,292⟩⟩,⟨1,1323665760856262856671233,⟨101,493,492,444,508,224,225,384,292⟩⟩]⟩
theorem node244 : UpperPrefix a [2,3,6,8,1,7,0] 30 :=
  Boolean.leaf_sound a [2,3,6,8,1,7,0] 30 cert244 (by decide +kernel)

def cert245 : Leaf := ⟨⟨8,4,307,103,69,0,295,103,99⟩,[(5,6)],[(3,1,0),(7,5,5),(4,6,2)],⟨7,11,76,280,50,224,208,417,293⟩,⟨7,11,76,280,50,224,208,384,260⟩,[⟨8,1181747921297203010821,⟨23,11,127,27,50,224,240,129,23⟩⟩,⟨5,1210107564157951779282181,⟨7,11,79,283,18,192,208,385,263⟩⟩,⟨6,1210106412362347079277829,⟨7,11,15,283,50,160,144,385,263⟩⟩]⟩
theorem node245 : UpperPrefix a [2,3,6,8,1,7,4] 30 :=
  Boolean.leaf_sound a [2,3,6,8,1,7,4] 30 cert245 (by decide +kernel)

def cert246 : Leaf := ⟨⟨280,276,307,103,325,0,0,23,115⟩,[(5,6),(6,5)],[(3,1,0),(7,5,5),(7,5,6)],⟨7,11,76,280,50,224,224,401,277⟩,⟨7,11,76,280,50,224,224,384,260⟩,[⟨5,1210181351134246617488645,⟨7,139,207,411,18,192,192,385,263⟩⟩,⟨6,1210180199338641917484293,⟨7,139,143,411,50,160,160,385,263⟩⟩]⟩
theorem node246 : UpperPrefix a [2,3,6,8,1,7,5] 30 :=
  Boolean.leaf_sound a [2,3,6,8,1,7,5] 30 cert246 (by decide +kernel)

theorem node247 : UpperPrefix a [2,3,6,8,1,7] 30 :=
  branch_upper a [2,3,6,8,1,7] 30 (by decide) (fin9_cases _
  node244
  (invalid_upper a [2,3,6,8,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,7,3] 30 (by decide +kernel))
  node245
  node246
  (invalid_upper a [2,3,6,8,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,7,8] 30 (by decide +kernel)))

theorem node248 : UpperPrefix a [2,3,6,8,1] 30 :=
  branch_upper a [2,3,6,8,1] 30 (by decide) (fin9_cases _
  node240
  (invalid_upper a [2,3,6,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,3] 30 (by decide +kernel))
  node243
  (invalid_upper a [2,3,6,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,6] 30 (by decide +kernel))
  node247
  (invalid_upper a [2,3,6,8,1,8] 30 (by decide +kernel)))

def cert249 : Leaf := ⟨⟨72,68,432,228,324,6,309,116,240⟩,[],[(3,1,0),(1,6,5)],⟨7,11,76,280,176,97,194,432,308⟩,⟨7,11,76,280,176,97,194,384,260⟩,[⟨0,1437223878321569159709696,⟨6,10,76,408,444,508,194,384,260⟩⟩,⟨4,1210107565423489662852357,⟨39,11,111,267,160,97,194,385,295⟩⟩,⟨7,1208926973803871763176709,⟨39,11,111,283,48,97,66,257,295⟩⟩,⟨8,1181745809959999773957,⟨39,11,111,27,176,97,194,129,39⟩⟩,⟨5,1210107564157951779282181,⟨7,11,79,283,144,65,194,385,263⟩⟩]⟩
theorem node249 : UpperPrefix a [2,3,6,8,7,0,1] 30 :=
  Boolean.leaf_sound a [2,3,6,8,7,0,1] 30 cert249 (by decide +kernel)

def cert250 : Leaf := ⟨⟨104,100,51,103,71,6,0,103,99⟩,[(6,4)],[(3,1,0),(7,4,6),(4,6,2)],⟨7,11,76,280,176,97,208,418,294⟩,⟨7,11,76,280,176,97,208,384,260⟩,[⟨8,1184344681614110891279,⟨39,47,127,127,240,113,240,241,39⟩⟩]⟩
theorem node250 : UpperPrefix a [2,3,6,8,7,0,4] 30 :=
  Boolean.leaf_sound a [2,3,6,8,7,0,4] 30 cert250 (by decide +kernel)

def cert251 : Leaf := ⟨⟨168,164,163,167,0,134,0,55,179⟩,[(4,6),(6,4)],[(3,1,0)],⟨7,11,76,280,176,97,224,402,278⟩,⟨7,11,76,280,176,97,224,384,260⟩,[⟨6,1229106558762666500955909,⟨399,139,415,411,176,51,176,387,399⟩⟩,⟨4,1210110164281949634436367,⟨39,47,111,367,224,97,224,481,295⟩⟩,⟨8,1184344681614110891279,⟨39,47,127,127,240,113,240,241,39⟩⟩]⟩
theorem node251 : UpperPrefix a [2,3,6,8,7,0,5] 30 :=
  Boolean.leaf_sound a [2,3,6,8,7,0,5] 30 cert251 (by decide +kernel)

theorem node252 : UpperPrefix a [2,3,6,8,7,0] 30 :=
  branch_upper a [2,3,6,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,8,7,0,0] 30 (by decide +kernel))
  node249
  (invalid_upper a [2,3,6,8,7,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,0,3] 30 (by decide +kernel))
  node250
  node251
  (invalid_upper a [2,3,6,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,0,8] 30 (by decide +kernel)))

def cert253 : Leaf := ⟨⟨232,224,432,224,320,129,38,112,240⟩,[],[(3,1,0),(0,6,5)],⟨7,11,76,280,176,98,193,432,308⟩,⟨7,11,76,280,176,98,193,384,260⟩,[⟨1,1437223878321569159708673,⟨5,9,76,408,444,508,193,384,260⟩⟩,⟨2,1212468750939865581913089,⟨35,11,122,408,184,114,251,408,440⟩⟩,⟨4,1210109871266498876546309,⟨39,11,111,267,224,98,193,449,295⟩⟩,⟨8,1184051652969213467909,⟨39,11,111,27,240,98,193,193,39⟩⟩]⟩
theorem node253 : UpperPrefix a [2,3,6,8,7,1,0] 30 :=
  Boolean.leaf_sound a [2,3,6,8,7,1,0] 30 cert253 (by decide +kernel)

def cert254 : Leaf := ⟨⟨72,68,19,103,327,5,0,103,99⟩,[(6,4)],[(3,1,0),(7,4,6),(4,6,2)],⟨7,11,76,280,176,98,208,417,293⟩,⟨7,11,76,280,176,98,208,384,260⟩,[⟨8,1182034321811130293519,⟨39,47,111,127,240,99,208,129,39⟩⟩,⟨5,1210107852388327933091087,⟨7,15,79,351,208,67,208,385,263⟩⟩]⟩
theorem node254 : UpperPrefix a [2,3,6,8,7,1,4] 30 :=
  Boolean.leaf_sound a [2,3,6,8,7,1,4] 30 cert254 (by decide +kernel)

def cert255 : Leaf := ⟨⟨168,164,163,167,0,133,0,55,179⟩,[(4,6),(6,4)],[(3,1,0)],⟨7,11,76,280,176,98,224,401,277⟩,⟨7,11,76,280,176,98,224,384,260⟩,[⟨6,1229106558762666500955909,⟨399,139,415,411,176,50,176,387,399⟩⟩,⟨4,1210107853935340793371919,⟨39,47,111,367,224,99,224,385,295⟩⟩,⟨8,1182034326209176804623,⟨39,47,127,127,240,115,240,129,39⟩⟩]⟩
theorem node255 : UpperPrefix a [2,3,6,8,7,1,5] 30 :=
  Boolean.leaf_sound a [2,3,6,8,7,1,5] 30 cert255 (by decide +kernel)

#print axioms node255
end Delivery.FiniteExclusion.Sharp2x7
