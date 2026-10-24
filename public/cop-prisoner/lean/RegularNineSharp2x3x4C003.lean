import RegularNineSharp2x3x4Base
import RegularNineSharp2x3x4C002
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x3x4
open Bounds BoundTreeRows Extremal
def cert192 : Leaf := ⟨⟨0,332,353,261,105,0,285,93,93⟩,[(0,2),(5,6)],[(1,2,0),(7,5,5)],⟨7,35,14,88,276,224,217,409,313⟩,⟨7,35,14,88,276,224,192,384,288⟩,[⟨5,1210255426340919754884101,⟨7,3,15,216,477,192,192,384,256⟩⟩,⟨4,1210107567534551990277133,⟨7,35,15,111,261,224,224,384,288⟩⟩]⟩
theorem node192 : UpperPrefix a [2,5,1,6,8,7] 30 :=
  Boolean.leaf_sound a [2,5,1,6,8,7] 30 cert192 (by decide +kernel)

theorem node193 : UpperPrefix a [2,5,1,6,8] 30 :=
  branch_upper a [2,5,1,6,8] 30 (by decide) (fin9_cases _
  node189
  (invalid_upper a [2,5,1,6,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,6,8,2] 30 (by decide +kernel))
  node190
  node191
  (invalid_upper a [2,5,1,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,6,8,6] 30 (by decide +kernel))
  node192
  (invalid_upper a [2,5,1,6,8,8] 30 (by decide +kernel)))

theorem node194 : UpperPrefix a [2,5,1,6] 30 :=
  branch_upper a [2,5,1,6] 30 (by decide) (fin9_cases _
  node179
  (invalid_upper a [2,5,1,6,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,6,2] 30 (by decide +kernel))
  node180
  (invalid_upper a [2,5,1,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,6,6] 30 (by decide +kernel))
  node188
  node193)

def cert195 : Leaf := ⟨⟨0,472,497,352,0,408,312,120,216⟩,[(0,2),(4,0)],[(2,0,4),(1,2,0),(1,2,4)],⟨7,35,14,152,21,376,472,472,376⟩,⟨7,35,14,152,21,96,192,384,288⟩,[⟨0,1323666154991598991049728,⟨6,34,494,504,508,96,192,384,288⟩⟩]⟩
theorem node195 : UpperPrefix a [2,5,1,7,0] 30 :=
  Boolean.leaf_sound a [2,5,1,7,0] 30 cert195 (by decide +kernel)

def cert196 : Leaf := ⟨⟨0,148,177,37,0,405,309,117,213⟩,[(0,2),(4,2)],[(1,2,0),(3,4,4)],⟨7,35,14,152,28,369,465,465,369⟩,⟨7,35,14,152,28,96,192,384,288⟩,[⟨6,1210106412378590687675815,⟨23,55,31,157,29,63,157,415,311⟩⟩,⟨8,1181745685466119816615,⟨23,55,31,157,29,127,221,159,55⟩⟩]⟩
theorem node196 : UpperPrefix a [2,5,1,7,3] 30 :=
  Boolean.leaf_sound a [2,5,1,7,3] 30 cert196 (by decide +kernel)

def cert197 : Leaf := ⟨⟨0,0,240,100,168,156,316,124,220⟩,[(0,2),(1,5)],[(1,2,0),(0,5,1)],⟨7,35,14,152,84,97,472,408,312⟩,⟨7,35,14,152,84,97,192,384,288⟩,[⟨8,1181748490577969870207,⟨7,55,15,191,127,127,255,131,55⟩⟩]⟩
theorem node197 : UpperPrefix a [2,5,1,7,6,0] 30 :=
  Boolean.leaf_sound a [2,5,1,7,6,0] 30 cert197 (by decide +kernel)

def cert198 : Leaf := ⟨⟨0,76,97,101,33,149,309,117,85⟩,[(0,2)],[(1,2,0),(7,3,5)],⟨7,35,14,152,84,104,465,401,305⟩,⟨7,35,14,152,84,104,192,384,288⟩,[⟨8,1181748490577969870207,⟨7,55,15,191,127,127,255,131,55⟩⟩,⟨3,1219616987954981049992197,⟨471,499,471,144,213,96,192,384,288⟩⟩,⟨4,1210107565282752183026983,⟨7,39,15,136,69,111,192,387,295⟩⟩]⟩
theorem node198 : UpperPrefix a [2,5,1,7,6,3] 30 :=
  Boolean.leaf_sound a [2,5,1,7,6,3] 30 cert198 (by decide +kernel)

def cert199 : Leaf := ⟨⟨0,28,49,37,169,0,317,61,29⟩,[(0,2),(5,4)],[(1,2,0),(6,4,5)],⟨7,35,14,152,84,112,457,393,297⟩,⟨7,35,14,152,84,112,192,384,288⟩,[⟨8,1181748490577969870207,⟨7,55,15,191,127,127,255,131,55⟩⟩,⟨7,1246705906089041392071709,⟨7,35,271,319,119,115,64,256,290⟩⟩]⟩
theorem node199 : UpperPrefix a [2,5,1,7,6,4] 30 :=
  Boolean.leaf_sound a [2,5,1,7,6,4] 30 cert199 (by decide +kernel)

def cert200 : Leaf := ⟨⟨0,220,209,68,137,156,28,92,220⟩,[(0,2)],[(1,2,0)],⟨7,35,14,152,84,352,193,408,312⟩,⟨7,35,14,152,84,352,193,384,288⟩,[⟨5,1210402748096820388037639,⟨95,223,95,152,93,472,221,384,392⟩⟩,⟨8,1184195643663409366439,⟨23,55,95,221,93,127,221,223,55⟩⟩,⟨0,1323665722364559786771456,⟨6,34,398,440,508,352,192,384,288⟩⟩]⟩
theorem node200 : UpperPrefix a [2,5,1,7,6,8,0] 30 :=
  Boolean.leaf_sound a [2,5,1,7,6,8,0] 30 cert200 (by decide +kernel)

def cert201 : Local := ⟨⟨0,340,369,357,297,21,0,117,85⟩,[(0,2),(6,3)],[(1,2,0),(7,3,6),(3,6,4)]⟩
theorem node201 : UpperPrefix a [2,5,1,7,6,8,3] 30 :=
  local_sound a [2,5,1,7,6,8,3] 30 cert201 (by decide +kernel)

def cert202 : Leaf := ⟨⟨0,412,433,0,425,157,0,61,157⟩,[(0,2),(3,6),(6,3)],[(1,2,0)],⟨7,35,14,152,84,352,208,393,297⟩,⟨7,35,14,152,84,352,208,384,288⟩,[⟨6,1361517287719363677406503,⟨7,423,15,152,29,431,152,387,423⟩⟩]⟩
theorem node202 : UpperPrefix a [2,5,1,7,6,8,4] 30 :=
  Boolean.leaf_sound a [2,5,1,7,6,8,4] 30 cert202 (by decide +kernel)

theorem node203 : UpperPrefix a [2,5,1,7,6,8] 30 :=
  branch_upper a [2,5,1,7,6,8] 30 (by decide) (fin9_cases _
  node200
  (invalid_upper a [2,5,1,7,6,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,6,8,2] 30 (by decide +kernel))
  node201
  node202
  (invalid_upper a [2,5,1,7,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,6,8,8] 30 (by decide +kernel)))

theorem node204 : UpperPrefix a [2,5,1,7,6] 30 :=
  branch_upper a [2,5,1,7,6] 30 (by decide) (fin9_cases _
  node197
  (invalid_upper a [2,5,1,7,6,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,6,2] 30 (by decide +kernel))
  node198
  node199
  (invalid_upper a [2,5,1,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,6,7] 30 (by decide +kernel))
  node203)

def cert205 : Local := ⟨⟨0,0,240,356,232,156,60,124,220⟩,[(0,2),(1,5)],[(1,2,0),(8,4,3),(0,5,1)]⟩
theorem node205 : UpperPrefix a [2,5,1,7,8,0] 30 :=
  local_sound a [2,5,1,7,8,0] 30 cert205 (by decide +kernel)

def cert206 : Leaf := ⟨⟨0,28,49,293,33,149,53,117,85⟩,[(0,2)],[(1,2,0),(7,3,5),(8,4,3)],⟨7,35,14,152,276,104,209,465,369⟩,⟨7,35,14,152,276,104,192,384,288⟩,[⟨3,1219764850137946878116869,⟨471,499,471,208,469,96,192,384,288⟩⟩,⟨6,1210106412388761170232759,⟨7,39,15,157,279,47,157,415,311⟩⟩]⟩
theorem node206 : UpperPrefix a [2,5,1,7,8,3] 30 :=
  Boolean.leaf_sound a [2,5,1,7,8,3] 30 cert206 (by decide +kernel)

def cert207 : Leaf := ⟨⟨0,220,240,352,232,140,56,120,216⟩,[(0,2)],[(1,2,0),(8,4,3)],⟨7,35,14,152,276,112,193,456,360⟩,⟨7,35,14,152,276,112,193,384,288⟩,[⟨0,1664340193611224138384384,⟨30,446,30,152,276,504,508,384,424⟩⟩,⟨2,1371018567882022074713089,⟨451,491,458,152,408,504,193,384,424⟩⟩]⟩
theorem node207 : UpperPrefix a [2,5,1,7,8,4,0] 30 :=
  Boolean.leaf_sound a [2,5,1,7,8,4,0] 30 cert207 (by decide +kernel)

def cert208 : Leaf := ⟨⟨0,28,49,293,41,13,0,125,93⟩,[(0,2),(6,3)],[(1,2,0),(7,3,6),(8,4,3)],⟨7,35,14,152,276,112,200,449,353⟩,⟨7,35,14,152,276,112,200,384,288⟩,[⟨6,1210106412388761170232759,⟨7,39,15,157,279,63,157,415,311⟩⟩]⟩
theorem node208 : UpperPrefix a [2,5,1,7,8,4,3] 30 :=
  Boolean.leaf_sound a [2,5,1,7,8,4,3] 30 cert208 (by decide +kernel)

theorem node209 : UpperPrefix a [2,5,1,7,8,4] 30 :=
  branch_upper a [2,5,1,7,8,4] 30 (by decide) (fin9_cases _
  node207
  (invalid_upper a [2,5,1,7,8,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,8,4,2] 30 (by decide +kernel))
  node208
  (invalid_upper a [2,5,1,7,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,8,4,8] 30 (by decide +kernel)))

theorem node210 : UpperPrefix a [2,5,1,7,8] 30 :=
  branch_upper a [2,5,1,7,8] 30 (by decide) (fin9_cases _
  node205
  (invalid_upper a [2,5,1,7,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,8,2] 30 (by decide +kernel))
  node206
  node209
  (invalid_upper a [2,5,1,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,8,8] 30 (by decide +kernel)))

theorem node211 : UpperPrefix a [2,5,1,7] 30 :=
  branch_upper a [2,5,1,7] 30 (by decide) (fin9_cases _
  node195
  (invalid_upper a [2,5,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,2] 30 (by decide +kernel))
  node196
  (invalid_upper a [2,5,1,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,5] 30 (by decide +kernel))
  node204
  (invalid_upper a [2,5,1,7,7] 30 (by decide +kernel))
  node210)

def cert212 : Leaf := ⟨⟨0,472,497,224,0,408,312,120,216⟩,[(0,2),(4,0)],[(2,0,4),(1,2,0),(1,2,4)],⟨7,35,14,280,21,248,216,472,504⟩,⟨7,35,14,280,21,96,192,384,288⟩,[⟨0,1323666154991598991049728,⟨6,34,494,504,508,96,192,384,288⟩⟩]⟩
theorem node212 : UpperPrefix a [2,5,1,8,0] 30 :=
  Boolean.leaf_sound a [2,5,1,8,0] 30 cert212 (by decide +kernel)

def cert213 : Leaf := ⟨⟨0,276,305,37,0,405,309,117,213⟩,[(0,2),(4,2)],[(1,2,0),(3,4,4)],⟨7,35,14,280,28,241,209,465,497⟩,⟨7,35,14,280,28,96,192,384,288⟩,[⟨6,1210106412394009681069453,⟨23,35,31,287,29,48,157,415,319⟩⟩,⟨7,1208926973694796876613005,⟨23,35,31,287,29,112,93,287,319⟩⟩]⟩
theorem node213 : UpperPrefix a [2,5,1,8,3] 30 :=
  Boolean.leaf_sound a [2,5,1,8,3] 30 cert213 (by decide +kernel)

def cert214 : Leaf := ⟨⟨0,0,496,228,392,412,284,92,220⟩,[(0,2),(1,5)],[(1,2,0),(0,5,1)],⟨7,35,14,280,84,97,216,408,440⟩,⟨7,35,14,280,84,97,192,384,288⟩,[⟨5,1210181567307372328649733,⟨87,19,223,472,85,81,192,384,256⟩⟩]⟩
theorem node214 : UpperPrefix a [2,5,1,8,6,0] 30 :=
  Boolean.leaf_sound a [2,5,1,8,6,0] 30 cert214 (by decide +kernel)

def cert215 : Leaf := ⟨⟨0,12,33,101,33,405,309,53,213⟩,[(0,2)],[(1,2,0)],⟨7,35,14,280,84,104,209,401,433⟩,⟨7,35,14,280,84,104,192,384,288⟩,[⟨3,1219617276185357201703941,⟨471,499,471,336,213,96,192,384,288⟩⟩,⟨7,1208926973669765815616943,⟨7,55,15,287,85,127,85,271,319⟩⟩,⟨6,1210180199338641928111407,⟨7,39,143,415,21,175,128,387,295⟩⟩,⟨8,1181745671421545301295,⟨7,55,15,31,85,127,192,131,55⟩⟩,⟨4,1210107565282752185124143,⟨7,39,15,271,69,111,192,387,295⟩⟩]⟩
theorem node215 : UpperPrefix a [2,5,1,8,6,3] 30 :=
  Boolean.leaf_sound a [2,5,1,8,6,3] 30 cert215 (by decide +kernel)

def cert216 : Leaf := ⟨⟨0,20,49,165,425,0,317,61,157⟩,[(0,2),(5,4)],[(1,2,0),(6,4,5)],⟨7,35,14,280,84,112,201,393,425⟩,⟨7,35,14,280,84,112,192,384,288⟩,[⟨7,1208926974226084230362141,⟨7,35,15,319,119,115,64,256,290⟩⟩,⟨8,1181746232172466959389,⟨7,35,15,63,119,115,192,128,34⟩⟩,⟨3,1210107565846800565826581,⟨7,35,7,307,119,115,192,384,290⟩⟩]⟩
theorem node216 : UpperPrefix a [2,5,1,8,6,4] 30 :=
  Boolean.leaf_sound a [2,5,1,8,6,4] 30 cert216 (by decide +kernel)

def cert217 : Leaf := ⟨⟨0,68,97,101,297,0,317,125,93⟩,[(0,2),(5,6)],[(1,2,0),(7,5,5)],⟨7,35,14,280,84,224,217,409,313⟩,⟨7,35,14,280,84,224,192,384,288⟩,[⟨4,1210107567534551990281245,⟨7,35,15,271,103,224,224,384,288⟩⟩,⟨8,1181747921022327202845,⟨7,35,15,31,119,224,224,128,32⟩⟩,⟨3,1210107567535650426070037,⟨7,35,7,275,119,224,224,384,288⟩⟩]⟩
theorem node217 : UpperPrefix a [2,5,1,8,6,7] 30 :=
  Boolean.leaf_sound a [2,5,1,8,6,7] 30 cert217 (by decide +kernel)

theorem node218 : UpperPrefix a [2,5,1,8,6] 30 :=
  branch_upper a [2,5,1,8,6] 30 (by decide) (fin9_cases _
  node214
  (invalid_upper a [2,5,1,8,6,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,6,2] 30 (by decide +kernel))
  node215
  node216
  (invalid_upper a [2,5,1,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,6,6] 30 (by decide +kernel))
  node217
  (invalid_upper a [2,5,1,8,6,8] 30 (by decide +kernel)))

def cert219 : Leaf := ⟨⟨0,0,496,228,328,412,284,92,220⟩,[(0,2),(1,5)],[(1,2,0),(0,5,1)],⟨7,35,14,280,148,97,216,472,376⟩,⟨7,35,14,280,148,97,192,384,288⟩,[⟨5,1210181567307303609172997,⟨87,3,223,472,213,65,192,384,256⟩⟩]⟩
theorem node219 : UpperPrefix a [2,5,1,8,7,0] 30 :=
  Boolean.leaf_sound a [2,5,1,8,7,0] 30 cert219 (by decide +kernel)

def cert220 : Leaf := ⟨⟨0,12,33,165,289,149,53,117,213⟩,[(0,2)],[(1,2,0)],⟨7,35,14,280,148,104,209,465,369⟩,⟨7,35,14,280,148,104,192,384,288⟩,[⟨3,1219617276185357201703941,⟨471,499,471,336,213,96,192,384,288⟩⟩,⟨6,1210106412375558442861999,⟨7,39,15,287,157,63,157,415,295⟩⟩,⟨8,1182034181073650474303,⟨7,39,47,127,215,111,192,131,39⟩⟩,⟨4,1210107565282752185124143,⟨7,39,15,271,133,111,192,387,295⟩⟩,⟨7,1208926973663134285448495,⟨7,39,15,287,21,111,64,259,295⟩⟩]⟩
theorem node220 : UpperPrefix a [2,5,1,8,7,3] 30 :=
  Boolean.leaf_sound a [2,5,1,8,7,3] 30 cert220 (by decide +kernel)

def cert221 : Leaf := ⟨⟨0,348,368,96,360,396,312,120,88⟩,[(0,2)],[(1,2,0),(7,4,5)],⟨7,35,14,280,148,112,193,456,360⟩,⟨7,35,14,280,148,112,193,384,288⟩,[⟨0,1664340193611224138384384,⟨30,446,30,280,148,504,508,384,424⟩⟩,⟨2,1371018567882019927229441,⟨451,491,458,280,144,504,193,384,424⟩⟩]⟩
theorem node221 : UpperPrefix a [2,5,1,8,7,4,0] 30 :=
  Boolean.leaf_sound a [2,5,1,8,7,4,0] 30 cert221 (by decide +kernel)

def cert222 : Leaf := ⟨⟨0,92,112,100,105,140,308,124,92⟩,[(0,2)],[(1,2,0),(8,3,6),(7,4,5)],⟨7,35,14,280,148,112,200,385,352⟩,⟨7,35,14,280,148,112,200,385,288⟩,[⟨0,1776791832303016636580864,⟨6,302,302,376,508,376,488,384,296⟩⟩]⟩
theorem node222 : UpperPrefix a [2,5,1,8,7,4,3,0] 30 :=
  Boolean.leaf_sound a [2,5,1,8,7,4,3,0] 30 cert222 (by decide +kernel)

def cert223 : Leaf := ⟨⟨0,28,49,37,41,141,309,61,29⟩,[(0,2)],[(1,2,0),(8,3,6),(7,4,5)],⟨7,35,14,280,148,112,200,448,289⟩,⟨7,35,14,280,148,112,200,448,288⟩,[⟨6,1370666872793130742728111,⟨263,303,271,287,157,319,157,415,303⟩⟩]⟩
theorem node223 : UpperPrefix a [2,5,1,8,7,4,3,6] 30 :=
  Boolean.leaf_sound a [2,5,1,8,7,4,3,6] 30 cert223 (by decide +kernel)

theorem node224 : UpperPrefix a [2,5,1,8,7,4,3] 30 :=
  branch_upper a [2,5,1,8,7,4,3] 30 (by decide) (fin9_cases _
  node222
  (invalid_upper a [2,5,1,8,7,4,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,7,4,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,7,4,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,7,4,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,7,4,3,5] 30 (by decide +kernel))
  node223
  (invalid_upper a [2,5,1,8,7,4,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,7,4,3,8] 30 (by decide +kernel)))

theorem node225 : UpperPrefix a [2,5,1,8,7,4] 30 :=
  branch_upper a [2,5,1,8,7,4] 30 (by decide) (fin9_cases _
  node221
  (invalid_upper a [2,5,1,8,7,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,7,4,2] 30 (by decide +kernel))
  node224
  (invalid_upper a [2,5,1,8,7,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,7,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,7,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,7,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,7,4,8] 30 (by decide +kernel)))

theorem node226 : UpperPrefix a [2,5,1,8,7] 30 :=
  branch_upper a [2,5,1,8,7] 30 (by decide) (fin9_cases _
  node219
  (invalid_upper a [2,5,1,8,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,7,2] 30 (by decide +kernel))
  node220
  node225
  (invalid_upper a [2,5,1,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,7,8] 30 (by decide +kernel)))

theorem node227 : UpperPrefix a [2,5,1,8] 30 :=
  branch_upper a [2,5,1,8] 30 (by decide) (fin9_cases _
  node212
  (invalid_upper a [2,5,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,2] 30 (by decide +kernel))
  node213
  (invalid_upper a [2,5,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,5] 30 (by decide +kernel))
  node218
  node226
  (invalid_upper a [2,5,1,8,8] 30 (by decide +kernel)))

theorem node228 : UpperPrefix a [2,5,1] 30 :=
  branch_upper a [2,5,1] 30 (by decide) (fin9_cases _
  node178
  (invalid_upper a [2,5,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,5] 30 (by decide +kernel))
  node194
  node211
  node227)

def cert229 : Local := ⟨⟨0,456,0,486,0,393,297,105,201⟩,[(0,4),(2,3),(4,0)],[(2,0,3),(4,2,2),(1,4,3)]⟩
theorem node229 : UpperPrefix a [2,5,4,0,1] 30 :=
  local_sound a [2,5,4,0,1] 30 cert229 (by decide +kernel)

def cert230 : Local := ⟨⟨480,448,0,486,0,387,291,99,195⟩,[(2,3),(4,2)],[(2,0,3),(4,2,2),(4,2,4),(3,4,2),(3,4,4)]⟩
theorem node230 : UpperPrefix a [2,5,4,0,3] 30 :=
  local_sound a [2,5,4,0,3] 30 cert230 (by decide +kernel)

def cert231 : Leaf := ⟨⟨488,456,0,484,424,392,296,104,200⟩,[(2,3)],[(2,0,3),(4,2,2),(1,5,1)],⟨7,35,28,25,84,98,456,392,424⟩,⟨7,35,28,25,84,98,192,384,288⟩,[⟨0,1247997393820110946305024,⟨246,50,476,508,212,98,192,384,288⟩⟩]⟩
theorem node231 : UpperPrefix a [2,5,4,0,6,1] 30 :=
  Boolean.leaf_sound a [2,5,4,0,6,1] 30 cert231 (by decide +kernel)

def cert232 : Leaf := ⟨⟨360,328,0,358,298,258,298,106,202⟩,[(2,3)],[(2,0,3),(4,2,2)],⟨7,35,28,25,84,104,450,386,418⟩,⟨7,35,28,25,84,104,192,384,288⟩,[⟨0,1219580022693326994015232,⟨470,502,60,252,84,124,192,384,308⟩⟩,⟨7,1208926976484531408403967,⟨15,63,63,63,127,127,127,271,319⟩⟩]⟩
theorem node232 : UpperPrefix a [2,5,4,0,6,3] 30 :=
  Boolean.leaf_sound a [2,5,4,0,6,3] 30 cert232 (by decide +kernel)

def cert233 : Leaf := ⟨⟨104,72,0,102,43,0,299,107,75⟩,[(2,3),(5,6)],[(2,0,3),(4,2,2),(7,5,5)],⟨7,35,28,25,84,224,458,394,298⟩,⟨7,35,28,25,84,224,192,384,288⟩,[⟨8,1181747927669691573759,⟨15,63,31,31,127,255,255,143,63⟩⟩]⟩
theorem node233 : UpperPrefix a [2,5,4,0,6,7] 30 :=
  Boolean.leaf_sound a [2,5,4,0,6,7] 30 cert233 (by decide +kernel)

def cert234 : Leaf := ⟨⟨488,456,0,484,424,136,296,104,200⟩,[(2,3)],[(2,0,3),(4,2,2)],⟨7,35,28,25,84,352,194,392,424⟩,⟨7,35,28,25,84,352,194,384,288⟩,[⟨0,1266886662437355975083008,⟨502,114,444,508,500,352,194,384,288⟩⟩,⟨1,1579180800159942664781825,⟨397,445,444,445,500,500,508,384,304⟩⟩]⟩
theorem node234 : UpperPrefix a [2,5,4,0,6,8,1] 30 :=
  Boolean.leaf_sound a [2,5,4,0,6,8,1] 30 cert234 (by decide +kernel)

def cert235 : Leaf := ⟨⟨224,192,0,230,171,131,35,99,195⟩,[(2,3)],[(2,0,3),(4,2,2),(3,6,4)],⟨7,35,28,25,84,352,200,386,418⟩,⟨7,35,28,25,84,352,200,384,288⟩,[⟨8,1184051527689713632675,⟨15,63,28,29,92,127,221,223,63⟩⟩]⟩
theorem node235 : UpperPrefix a [2,5,4,0,6,8,3] 30 :=
  Boolean.leaf_sound a [2,5,4,0,6,8,3] 30 cert235 (by decide +kernel)

theorem node236 : UpperPrefix a [2,5,4,0,6,8] 30 :=
  branch_upper a [2,5,4,0,6,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,4,0,6,8,0] 30 (by decide +kernel))
  node234
  (invalid_upper a [2,5,4,0,6,8,2] 30 (by decide +kernel))
  node235
  (invalid_upper a [2,5,4,0,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,6,8,8] 30 (by decide +kernel)))

theorem node237 : UpperPrefix a [2,5,4,0,6] 30 :=
  branch_upper a [2,5,4,0,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,4,0,6,0] 30 (by decide +kernel))
  node231
  (invalid_upper a [2,5,4,0,6,2] 30 (by decide +kernel))
  node232
  (invalid_upper a [2,5,4,0,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,6,6] 30 (by decide +kernel))
  node233
  node236)

def cert238 : Leaf := ⟨⟨488,456,0,484,360,392,296,104,200⟩,[(2,3)],[(2,0,3),(4,2,2),(1,5,1)],⟨7,35,28,25,148,98,456,456,360⟩,⟨7,35,28,25,148,98,192,384,288⟩,[⟨0,1247997393820110946305024,⟨246,50,476,508,212,98,192,384,288⟩⟩]⟩
theorem node238 : UpperPrefix a [2,5,4,0,7,1] 30 :=
  Boolean.leaf_sound a [2,5,4,0,7,1] 30 cert238 (by decide +kernel)

def cert239 : Leaf := ⟨⟨232,200,0,230,106,130,298,106,202⟩,[(2,3)],[(2,0,3),(4,2,2)],⟨7,35,28,25,148,104,450,450,354⟩,⟨7,35,28,25,148,104,192,384,288⟩,[⟨0,1219580022691127970759680,⟨470,502,60,252,148,124,192,384,292⟩⟩,⟨8,1181747934248742077923,⟨7,47,28,29,157,127,255,159,47⟩⟩]⟩
theorem node239 : UpperPrefix a [2,5,4,0,7,3] 30 :=
  Boolean.leaf_sound a [2,5,4,0,7,3] 30 cert239 (by decide +kernel)

def cert240 : Leaf := ⟨⟨456,456,0,452,329,137,265,73,201⟩,[(2,3)],[(2,0,3),(4,2,2)],⟨7,35,28,25,148,352,194,456,360⟩,⟨7,35,28,25,148,352,194,384,288⟩,[⟨1,1512929318256264856731649,⟨13,61,28,29,148,500,508,384,304⟩⟩,⟨5,1210402748125064321565763,⟨95,223,28,29,148,477,223,404,412⟩⟩]⟩
theorem node240 : UpperPrefix a [2,5,4,0,7,8,1] 30 :=
  Boolean.leaf_sound a [2,5,4,0,7,8,1] 30 cert240 (by decide +kernel)

def cert241 : Leaf := ⟨⟨168,136,0,166,43,139,35,107,203⟩,[(2,3)],[(2,0,3),(4,2,2)],⟨7,35,28,25,148,352,200,450,354⟩,⟨7,35,28,25,148,352,200,384,288⟩,[⟨8,1184339755834293765539,⟨7,47,92,93,221,127,221,223,47⟩⟩,⟨6,1210106412375573496219043,⟨7,47,28,29,157,319,157,415,303⟩⟩]⟩
theorem node241 : UpperPrefix a [2,5,4,0,7,8,3] 30 :=
  Boolean.leaf_sound a [2,5,4,0,7,8,3] 30 cert241 (by decide +kernel)

theorem node242 : UpperPrefix a [2,5,4,0,7,8] 30 :=
  branch_upper a [2,5,4,0,7,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,4,0,7,8,0] 30 (by decide +kernel))
  node240
  (invalid_upper a [2,5,4,0,7,8,2] 30 (by decide +kernel))
  node241
  (invalid_upper a [2,5,4,0,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,7,8,8] 30 (by decide +kernel)))

theorem node243 : UpperPrefix a [2,5,4,0,7] 30 :=
  branch_upper a [2,5,4,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,4,0,7,0] 30 (by decide +kernel))
  node238
  (invalid_upper a [2,5,4,0,7,2] 30 (by decide +kernel))
  node239
  (invalid_upper a [2,5,4,0,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,7,7] 30 (by decide +kernel))
  node242)

def cert244 : Leaf := ⟨⟨488,456,0,484,232,392,296,104,200⟩,[(2,3)],[(2,0,3),(4,2,2),(1,5,1)],⟨7,35,28,25,276,98,200,456,488⟩,⟨7,35,28,25,276,98,192,384,288⟩,[⟨0,1247997393820042226828288,⟨246,34,476,508,468,98,192,384,288⟩⟩]⟩
theorem node244 : UpperPrefix a [2,5,4,0,8,1] 30 :=
  Boolean.leaf_sound a [2,5,4,0,8,1] 30 cert244 (by decide +kernel)

def cert245 : Leaf := ⟨⟨360,328,0,358,106,258,298,106,202⟩,[(2,3)],[(2,0,3),(4,2,2)],⟨7,35,28,25,276,104,194,450,482⟩,⟨7,35,28,25,276,104,192,384,288⟩,[⟨0,1219580022690440767603712,⟨470,498,60,252,276,108,192,384,288⟩⟩,⟨7,1208926975941385305376241,⟨15,35,29,29,287,111,127,287,319⟩⟩]⟩
theorem node245 : UpperPrefix a [2,5,4,0,8,3] 30 :=
  Boolean.leaf_sound a [2,5,4,0,8,3] 30 cert245 (by decide +kernel)

def cert246 : Leaf := ⟨⟨296,264,0,294,43,0,299,107,75⟩,[(2,3),(5,6)],[(2,0,3),(4,2,2),(7,5,5)],⟨7,35,28,25,276,224,202,458,362⟩,⟨7,35,28,25,276,224,192,384,288⟩,[⟨6,1210106412388802599470515,⟨15,47,29,29,287,191,157,415,319⟩⟩]⟩
theorem node246 : UpperPrefix a [2,5,4,0,8,7] 30 :=
  Boolean.leaf_sound a [2,5,4,0,8,7] 30 cert246 (by decide +kernel)

theorem node247 : UpperPrefix a [2,5,4,0,8] 30 :=
  branch_upper a [2,5,4,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,4,0,8,0] 30 (by decide +kernel))
  node244
  (invalid_upper a [2,5,4,0,8,2] 30 (by decide +kernel))
  node245
  (invalid_upper a [2,5,4,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,8,6] 30 (by decide +kernel))
  node246
  (invalid_upper a [2,5,4,0,8,8] 30 (by decide +kernel)))

theorem node248 : UpperPrefix a [2,5,4,0] 30 :=
  branch_upper a [2,5,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,4,0,0] 30 (by decide +kernel))
  node229
  (invalid_upper a [2,5,4,0,2] 30 (by decide +kernel))
  node230
  (invalid_upper a [2,5,4,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,5] 30 (by decide +kernel))
  node237
  node243
  node247)

def cert249 : Local := ⟨⟨488,456,0,481,0,394,298,106,202⟩,[(2,3),(4,0)],[(2,0,4),(4,2,2),(0,4,3)]⟩
theorem node249 : UpperPrefix a [2,5,4,1,0] 30 :=
  local_sound a [2,5,4,1,0] 30 cert249 (by decide +kernel)

def cert250 : Leaf := ⟨⟨480,448,0,485,0,387,291,99,195⟩,[(2,3),(4,2)],[(4,2,2),(4,2,4),(3,4,2),(3,4,4)],⟨7,35,28,26,28,481,449,449,481⟩,⟨7,35,28,26,28,96,192,384,288⟩,[⟨2,1224302388997319829751297,⟨483,483,24,506,24,96,192,384,288⟩⟩]⟩
theorem node250 : UpperPrefix a [2,5,4,1,3] 30 :=
  Boolean.leaf_sound a [2,5,4,1,3] 30 cert250 (by decide +kernel)

def cert251 : Leaf := ⟨⟨104,0,0,100,42,14,302,110,206⟩,[(1,5),(2,3)],[(4,2,2),(0,5,1)],⟨7,35,28,26,84,97,456,392,424⟩,⟨7,35,28,26,84,97,192,384,288⟩,[⟨7,1208926976484531408403967,⟨15,63,63,63,127,127,127,271,319⟩⟩,⟨8,1181748490619645001215,⟨15,63,63,63,127,127,255,143,63⟩⟩]⟩
theorem node251 : UpperPrefix a [2,5,4,1,6,0] 30 :=
  Boolean.leaf_sound a [2,5,4,1,6,0] 30 cert251 (by decide +kernel)

def cert252 : Leaf := ⟨⟨104,76,0,101,41,5,301,109,205⟩,[(2,3)],[(4,2,2)],⟨7,35,28,26,84,104,449,385,417⟩,⟨7,35,28,26,84,104,192,384,288⟩,[⟨1,1219580022693326994014209,⟨469,501,60,508,84,124,192,384,308⟩⟩,⟨7,1208926976484531408403967,⟨15,63,63,63,127,127,127,271,319⟩⟩,⟨8,1181748490619645001215,⟨15,63,63,63,127,127,255,143,63⟩⟩]⟩
theorem node252 : UpperPrefix a [2,5,4,1,6,3] 30 :=
  Boolean.leaf_sound a [2,5,4,1,6,3] 30 cert252 (by decide +kernel)

def cert253 : Leaf := ⟨⟨96,68,0,101,43,0,303,111,79⟩,[(2,3),(5,6)],[(4,2,2),(7,5,5)],⟨7,35,28,26,84,224,457,393,297⟩,⟨7,35,28,26,84,224,192,384,288⟩,[⟨8,1181747927669691573759,⟨15,63,31,31,127,255,255,143,63⟩⟩,⟨3,1210107567535650426070037,⟨7,35,23,19,119,224,224,384,288⟩⟩]⟩
theorem node253 : UpperPrefix a [2,5,4,1,6,7] 30 :=
  Boolean.leaf_sound a [2,5,4,1,6,7] 30 cert253 (by decide +kernel)

def cert254 : Leaf := ⟨⟨232,200,0,225,169,137,40,105,201⟩,[(2,3)],[(4,2,2)],⟨7,35,28,26,84,352,193,392,424⟩,⟨7,35,28,26,84,352,193,384,288⟩,[⟨2,1342592099833768667284993,⟨483,99,440,442,506,354,227,384,288⟩⟩,⟨1,1266886662155331242557441,⟨501,113,444,444,500,352,241,384,288⟩⟩,⟨8,1184051527681119503787,⟨15,63,29,31,84,127,221,223,63⟩⟩]⟩
theorem node254 : UpperPrefix a [2,5,4,1,6,8,0] 30 :=
  Boolean.leaf_sound a [2,5,4,1,6,8,0] 30 cert254 (by decide +kernel)

def cert255 : Leaf := ⟨⟨224,196,0,229,169,133,37,101,197⟩,[(2,3)],[(4,2,2),(3,6,4)],⟨7,35,28,26,84,352,200,385,417⟩,⟨7,35,28,26,84,352,200,384,288⟩,[⟨1,1219580112769786315800577,⟨405,433,124,508,84,372,252,384,304⟩⟩,⟨8,1184051527681119503787,⟨15,63,29,31,84,127,221,223,63⟩⟩]⟩
theorem node255 : UpperPrefix a [2,5,4,1,6,8,3] 30 :=
  Boolean.leaf_sound a [2,5,4,1,6,8,3] 30 cert255 (by decide +kernel)

#print axioms node255
end Delivery.FiniteExclusion.Sharp2x3x4
