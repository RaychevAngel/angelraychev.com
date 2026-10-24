import RegularNineSharp3x3x3Base
import RegularNineSharp3x3x3C002
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x3x3
open Bounds BoundTreeRows Extremal
def cert192 : Leaf := ⟨⟨404,384,386,390,134,262,258,38,166⟩,[],[(4,1,0)],⟨11,22,69,25,304,168,196,418,354⟩,⟨11,22,69,25,304,168,196,384,320⟩,[⟨0,1233765622962327944989696,⟨506,470,502,440,304,184,470,384,322⟩⟩,⟨3,1437224634926299035751425,⟨71,470,69,471,498,502,196,384,320⟩⟩,⟨6,1212467611955781375657287,⟨11,63,47,57,441,184,191,441,443⟩⟩,⟨5,1210108140618706511213627,⟨11,31,69,31,351,207,196,384,320⟩⟩]⟩
theorem node192 : UpperPrefix a [3,4,6,0,8,7,2] 30 :=
  Boolean.leaf_sound a [3,4,6,0,8,7,2] 30 cert192 (by decide +kernel)

def cert193 : Leaf := ⟨⟨372,352,290,358,70,326,0,102,38⟩,[(6,5)],[(4,1,0),(7,5,6)],⟨11,22,69,25,304,168,224,390,326⟩,⟨11,22,69,25,304,168,224,384,320⟩,[⟨0,1238497770981563506363392,⟨506,470,502,120,368,232,224,384,320⟩⟩,⟨3,1427770786679311993691137,⟨391,470,471,471,498,502,498,384,336⟩⟩]⟩
theorem node193 : UpperPrefix a [3,4,6,0,8,7,5] 30 :=
  Boolean.leaf_sound a [3,4,6,0,8,7,5] 30 cert193 (by decide +kernel)

theorem node194 : UpperPrefix a [3,4,6,0,8,7] 30 :=
  branch_upper a [3,4,6,0,8,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,0,8,7,0] 30 (by decide +kernel))
  node191
  node192
  (invalid_upper a [3,4,6,0,8,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,8,7,4] 30 (by decide +kernel))
  node193
  (invalid_upper a [3,4,6,0,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,8,7,8] 30 (by decide +kernel)))

theorem node195 : UpperPrefix a [3,4,6,0,8] 30 :=
  branch_upper a [3,4,6,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,0,8,0] 30 (by decide +kernel))
  node189
  node190
  (invalid_upper a [3,4,6,0,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,8,6] 30 (by decide +kernel))
  node194
  (invalid_upper a [3,4,6,0,8,8] 30 (by decide +kernel)))

theorem node196 : UpperPrefix a [3,4,6,0] 30 :=
  branch_upper a [3,4,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,0,0] 30 (by decide +kernel))
  node180
  node181
  (invalid_upper a [3,4,6,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,6] 30 (by decide +kernel))
  node188
  node195)

def cert197 : Local := ⟨⟨0,481,416,0,460,452,292,100,164⟩,[(0,3),(3,1)],[(3,0,4),(4,1,0),(4,1,3),(1,3,0),(0,4,1)]⟩
theorem node197 : UpperPrefix a [3,4,6,1,0] 30 :=
  local_sound a [3,4,6,1,0] 30 cert197 (by decide +kernel)

def cert198 : Local := ⟨⟨0,0,424,0,457,449,297,105,169⟩,[(0,3),(1,4),(3,1)],[(4,1,0),(4,1,3),(1,3,0),(2,4,1),(2,4,3)]⟩
theorem node198 : UpperPrefix a [3,4,6,1,2] 30 :=
  local_sound a [3,4,6,1,2] 30 cert198 (by decide +kernel)

def cert199 : Local := ⟨⟨0,0,424,0,457,193,297,105,169⟩,[(0,3),(1,4),(3,1)],[(4,1,0),(4,1,3),(1,3,0),(2,4,1),(2,4,3)]⟩
theorem node199 : UpperPrefix a [3,4,6,1,2,8] 30 :=
  local_sound a [3,4,6,1,2,8] 30 cert199 (by decide +kernel)

def cert200 : Leaf := ⟨⟨0,489,424,0,329,449,297,105,169⟩,[(0,3),(3,1)],[(4,1,0),(4,1,3),(1,3,0)],⟨11,22,69,26,176,44,481,417,353⟩,⟨11,22,69,26,176,44,192,384,320⟩,[⟨2,1361519017103811279848459,⟨11,27,65,27,496,505,192,384,320⟩⟩]⟩
theorem node200 : UpperPrefix a [3,4,6,1,7,2] 30 :=
  Boolean.leaf_sound a [3,4,6,1,7,2] 30 cert200 (by decide +kernel)

def cert201 : Local := ⟨⟨0,232,0,0,332,196,44,108,172⟩,[(0,3),(2,6),(3,1)],[(4,1,0),(4,1,3),(1,3,0),(8,5,4),(0,6,2)]⟩
theorem node201 : UpperPrefix a [3,4,6,1,7,8,0] 30 :=
  local_sound a [3,4,6,1,7,8,0] 30 cert201 (by decide +kernel)

def cert202 : Local := ⟨⟨0,233,168,0,333,197,41,109,173⟩,[(0,3),(3,1)],[(4,1,0),(4,1,3),(1,3,0),(8,5,4)]⟩
theorem node202 : UpperPrefix a [3,4,6,1,7,8,2] 30 :=
  local_sound a [3,4,6,1,7,8,2] 30 cert202 (by decide +kernel)

def cert203 : Local := ⟨⟨0,233,168,0,0,197,0,109,173⟩,[(0,3),(3,1),(4,6),(6,4)],[(4,1,0),(4,1,3),(1,3,0),(8,5,4),(8,5,6)]⟩
theorem node203 : UpperPrefix a [3,4,6,1,7,8,5] 30 :=
  local_sound a [3,4,6,1,7,8,5] 30 cert203 (by decide +kernel)

theorem node204 : UpperPrefix a [3,4,6,1,7,8] 30 :=
  branch_upper a [3,4,6,1,7,8] 30 (by decide) (fin9_cases _
  node201
  (invalid_upper a [3,4,6,1,7,8,1] 30 (by decide +kernel))
  node202
  (invalid_upper a [3,4,6,1,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,7,8,4] 30 (by decide +kernel))
  node203
  (invalid_upper a [3,4,6,1,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,7,8,8] 30 (by decide +kernel)))

theorem node205 : UpperPrefix a [3,4,6,1,7] 30 :=
  branch_upper a [3,4,6,1,7] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut59 [3,4,6,1,7,0] [3,4,6,1,2,8] 30 (by decide +kernel) node199)
  (invalid_upper a [3,4,6,1,7,1] 30 (by decide +kernel))
  node200
  (invalid_upper a [3,4,6,1,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,7,7] 30 (by decide +kernel))
  node204)

def cert206 : Local := ⟨⟨0,0,424,0,457,321,297,105,169⟩,[(0,3),(1,4),(3,1)],[(4,1,0),(4,1,3),(1,3,0),(2,4,1),(2,4,3)]⟩
theorem node206 : UpperPrefix a [3,4,6,1,2,7] 30 :=
  local_sound a [3,4,6,1,2,7] 30 cert206 (by decide +kernel)

def cert207 : Leaf := ⟨⟨0,489,424,0,201,449,297,105,169⟩,[(0,3),(3,1)],[(4,1,0),(4,1,3),(1,3,0)],⟨11,22,69,26,304,44,225,417,481⟩,⟨11,22,69,26,304,44,192,384,320⟩,[⟨2,1361519017103811279848459,⟨11,27,65,27,496,505,192,384,320⟩⟩]⟩
theorem node207 : UpperPrefix a [3,4,6,1,8,2] 30 :=
  Boolean.leaf_sound a [3,4,6,1,8,2] 30 cert207 (by decide +kernel)

def cert208 : Local := ⟨⟨0,488,0,0,204,324,300,108,172⟩,[(0,3),(2,6),(3,1)],[(4,1,0),(4,1,3),(1,3,0),(0,6,2)]⟩
theorem node208 : UpperPrefix a [3,4,6,1,8,7,0] 30 :=
  local_sound a [3,4,6,1,8,7,0] 30 cert208 (by decide +kernel)

def cert209 : Leaf := ⟨⟨0,489,424,0,201,321,297,105,169⟩,[(0,3),(3,1)],[(4,1,0),(4,1,3),(1,3,0)],⟨11,22,69,26,304,168,196,417,353⟩,⟨11,22,69,26,304,168,196,384,320⟩,[⟨2,1229052371980127741936651,⟨187,443,505,187,304,169,496,384,336⟩⟩]⟩
theorem node209 : UpperPrefix a [3,4,6,1,8,7,2] 30 :=
  Boolean.leaf_sound a [3,4,6,1,8,7,2] 30 cert209 (by decide +kernel)

def cert210 : Local := ⟨⟨0,361,296,0,77,325,0,109,45⟩,[(0,3),(3,1),(6,5)],[(4,1,0),(4,1,3),(1,3,0),(7,5,6)]⟩
theorem node210 : UpperPrefix a [3,4,6,1,8,7,5] 30 :=
  local_sound a [3,4,6,1,8,7,5] 30 cert210 (by decide +kernel)

theorem node211 : UpperPrefix a [3,4,6,1,8,7] 30 :=
  branch_upper a [3,4,6,1,8,7] 30 (by decide) (fin9_cases _
  node208
  (invalid_upper a [3,4,6,1,8,7,1] 30 (by decide +kernel))
  node209
  (invalid_upper a [3,4,6,1,8,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,8,7,4] 30 (by decide +kernel))
  node210
  (invalid_upper a [3,4,6,1,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,8,7,8] 30 (by decide +kernel)))

theorem node212 : UpperPrefix a [3,4,6,1,8] 30 :=
  branch_upper a [3,4,6,1,8] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut58 [3,4,6,1,8,0] [3,4,6,1,2,7] 30 (by decide +kernel) node206)
  (invalid_upper a [3,4,6,1,8,1] 30 (by decide +kernel))
  node207
  (invalid_upper a [3,4,6,1,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,8,6] 30 (by decide +kernel))
  node211
  (invalid_upper a [3,4,6,1,8,8] 30 (by decide +kernel)))

theorem node213 : UpperPrefix a [3,4,6,1] 30 :=
  branch_upper a [3,4,6,1] 30 (by decide) (fin9_cases _
  node197
  (invalid_upper a [3,4,6,1,1] 30 (by decide +kernel))
  node198
  (invalid_upper a [3,4,6,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,6] 30 (by decide +kernel))
  node205
  node212)

def cert214 : Local := ⟨⟨500,0,418,0,458,450,290,98,162⟩,[(1,3),(3,1)],[(3,0,4),(4,1,0),(2,3,0),(0,4,1),(0,4,3)]⟩
theorem node214 : UpperPrefix a [3,4,6,2,0] 30 :=
  local_sound a [3,4,6,2,0] 30 cert214 (by decide +kernel)

def cert215 : Leaf := ⟨⟨436,0,424,0,393,449,297,105,169⟩,[(1,3),(3,1)],[(4,1,0),(2,3,0)],⟨11,22,69,28,50,425,481,417,481⟩,⟨11,22,69,28,50,40,192,384,320⟩,[⟨1,1233765604665561374261249,⟨493,476,485,476,56,40,192,384,320⟩⟩,⟨6,1210106412364546370966587,⟨11,31,5,31,59,59,128,384,256⟩⟩]⟩
theorem node215 : UpperPrefix a [3,4,6,2,1] 30 :=
  Boolean.leaf_sound a [3,4,6,2,1] 30 cert215 (by decide +kernel)

def cert216 : Local := ⟨⟨500,0,418,0,323,0,291,99,163⟩,[(1,3),(3,1),(5,0)],[(3,0,5),(4,1,0),(2,3,0)]⟩
theorem node216 : UpperPrefix a [3,4,6,2,7,0] 30 :=
  local_sound a [3,4,6,2,7,0] 30 cert216 (by decide +kernel)

def cert217 : Local := ⟨⟨0,0,426,0,331,0,299,107,171⟩,[(0,5),(1,3),(3,1),(5,0)],[(4,1,0),(4,1,5),(2,3,0),(2,3,5)]⟩
theorem node217 : UpperPrefix a [3,4,6,2,7,1] 30 :=
  local_sound a [3,4,6,2,7,1] 30 cert217 (by decide +kernel)

def cert218 : Leaf := ⟨⟨180,0,170,0,267,195,43,43,171⟩,[(1,3),(3,1)],[(4,1,0),(2,3,0),(8,5,4)],⟨11,22,69,28,176,296,227,419,355⟩,⟨11,22,69,28,176,296,192,384,320⟩,[⟨6,1210401560269725723792427,⟨11,31,5,31,177,443,128,384,256⟩⟩]⟩
theorem node218 : UpperPrefix a [3,4,6,2,7,8] 30 :=
  Boolean.leaf_sound a [3,4,6,2,7,8] 30 cert218 (by decide +kernel)

theorem node219 : UpperPrefix a [3,4,6,2,7] 30 :=
  branch_upper a [3,4,6,2,7] 30 (by decide) (fin9_cases _
  node216
  node217
  (invalid_upper a [3,4,6,2,7,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,2,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,2,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,2,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,2,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,2,7,7] 30 (by decide +kernel))
  node218)

def cert220 : Local := ⟨⟨500,0,418,0,195,0,291,99,163⟩,[(1,3),(3,1),(5,0)],[(3,0,5),(4,1,0),(2,3,0)]⟩
theorem node220 : UpperPrefix a [3,4,6,2,8,0] 30 :=
  local_sound a [3,4,6,2,8,0] 30 cert220 (by decide +kernel)

def cert221 : Leaf := ⟨⟨148,0,170,0,203,323,43,107,171⟩,[(1,3),(3,1)],[(4,1,0),(2,3,0)],⟨11,22,69,28,304,168,227,419,355⟩,⟨11,22,69,28,304,168,192,384,320⟩,[⟨8,1182322129977243350075,⟨11,31,69,31,127,239,192,128,64⟩⟩,⟨5,1210107564157952047715371,⟨11,31,69,31,273,139,192,384,320⟩⟩,⟨6,1210106412362347347711019,⟨11,31,5,31,305,171,128,384,256⟩⟩]⟩
theorem node221 : UpperPrefix a [3,4,6,2,8,7] 30 :=
  Boolean.leaf_sound a [3,4,6,2,8,7] 30 cert221 (by decide +kernel)

theorem node222 : UpperPrefix a [3,4,6,2,8] 30 :=
  branch_upper a [3,4,6,2,8] 30 (by decide) (fin9_cases _
  node220
  (PrefixConjugacy.upper aut94 [3,4,6,2,8,1] [3,4,6,2,7,1] 30 (by decide +kernel) node217)
  (invalid_upper a [3,4,6,2,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,2,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,2,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,2,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,2,8,6] 30 (by decide +kernel))
  node221
  (invalid_upper a [3,4,6,2,8,8] 30 (by decide +kernel)))

theorem node223 : UpperPrefix a [3,4,6,2] 30 :=
  branch_upper a [3,4,6,2] 30 (by decide) (fin9_cases _
  node214
  node215
  (invalid_upper a [3,4,6,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,2,6] 30 (by decide +kernel))
  node219
  node222)

def cert224 : Leaf := ⟨⟨400,449,386,0,462,454,262,70,134⟩,[(3,4)],[(3,0,4),(4,1,0),(5,3,3),(0,4,1)],⟨11,22,69,56,49,430,454,390,454⟩,⟨11,22,69,56,49,40,192,384,320⟩,[⟨2,1210107565283853832553475,⟨11,27,65,56,57,40,192,384,320⟩⟩,⟨6,1210106412362349226755075,⟨11,31,5,56,57,40,128,384,256⟩⟩]⟩
theorem node224 : UpperPrefix a [3,4,6,5,0] 30 :=
  Boolean.leaf_sound a [3,4,6,5,0] 30 cert224 (by decide +kernel)

def cert225 : Leaf := ⟨⟨400,457,384,0,461,453,261,69,133⟩,[(3,4)],[(4,1,0),(5,3,3)],⟨11,22,69,56,50,429,453,389,453⟩,⟨11,22,69,56,50,40,192,384,320⟩,[⟨1,1233765604665563253309441,⟨493,476,485,56,56,40,192,384,320⟩⟩,⟨3,1233765604630375659996161,⟨455,470,453,48,50,32,192,384,320⟩⟩,⟨2,1210107565283853832553491,⟨11,27,65,57,59,40,192,384,320⟩⟩,⟨6,1210106412362349226755091,⟨11,31,5,57,59,40,128,384,256⟩⟩]⟩
theorem node225 : UpperPrefix a [3,4,6,5,1] 30 :=
  Boolean.leaf_sound a [3,4,6,5,1] 30 cert225 (by decide +kernel)

def cert226 : Leaf := ⟨⟨464,0,386,0,459,451,259,67,131⟩,[(1,4),(3,4)],[(4,1,0),(5,3,3),(2,4,1)],⟨11,22,69,56,52,427,451,387,451⟩,⟨11,22,69,56,52,40,192,384,320⟩,[⟨3,1214839173153155622118401,⟨455,22,453,50,54,32,192,384,320⟩⟩]⟩
theorem node226 : UpperPrefix a [3,4,6,5,2] 30 :=
  Boolean.leaf_sound a [3,4,6,5,2] 30 cert226 (by decide +kernel)

def cert227 : Local := ⟨⟨0,440,0,482,456,208,312,120,184⟩,[(0,1),(2,3)],[(2,0,0),(0,3,2),(1,4,3)]⟩
theorem node227 : UpperPrefix a [2,6,3,0,1,8] 30 :=
  local_sound a [2,6,3,0,1,8] 30 cert227 (by decide +kernel)

def cert228 : Local := ⟨⟨0,441,0,481,201,0,313,121,185⟩,[(0,1),(2,5),(5,2)],[(2,0,0),(1,3,2),(1,3,5)]⟩
theorem node228 : UpperPrefix a [2,6,3,1,8,0] 30 :=
  local_sound a [2,6,3,1,8,0] 30 cert228 (by decide +kernel)

def cert229 : Leaf := ⟨⟨0,313,368,96,322,337,304,112,176⟩,[(0,1)],[(2,0,0),(1,5,4)],⟨7,70,13,280,49,42,240,432,496⟩,⟨7,70,13,280,49,42,192,384,320⟩,[⟨7,1208926989741207036528107,⟨23,119,61,319,53,63,127,319,383⟩⟩,⟨0,1285813291192733985145856,⟨6,70,12,472,504,42,192,384,320⟩⟩,⟨3,1437224743012690090263555,⟨7,71,5,464,497,499,192,384,320⟩⟩]⟩
theorem node229 : UpperPrefix a [2,6,3,8,0,1] 30 :=
  Boolean.leaf_sound a [2,6,3,8,0,1] 30 cert229 (by decide +kernel)

def cert230 : Leaf := ⟨⟨0,185,120,98,73,80,312,120,56⟩,[(0,1)],[(2,0,0),(7,2,1),(1,4,3)],⟨7,70,133,25,50,296,248,440,376⟩,⟨7,70,133,25,50,296,192,384,320⟩,[⟨0,1247960428519766738600960,⟨6,70,132,504,50,488,192,384,320⟩⟩,⟨8,1181745671428027614659,⟨7,71,133,25,59,59,199,135,71⟩⟩]⟩
theorem node230 : UpperPrefix a [2,6,7,0,1,8] 30 :=
  Boolean.leaf_sound a [2,6,7,0,1,8] 30 cert230 (by decide +kernel)

theorem node231 : UpperPrefix a [3,4,6,5,7] 30 :=
  branch_upper a [3,4,6,5,7] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut56 [3,4,6,5,7,0] [2,6,3,0,1,8] 30 (by decide +kernel) node227)
  (PrefixConjugacy.upper aut92 [3,4,6,5,7,1] [2,6,3,1,8,0] 30 (by decide +kernel) node228)
  (PrefixConjugacy.upper aut74 [3,4,6,5,7,2] [2,6,3,8,0,1] 30 (by decide +kernel) node229)
  (invalid_upper a [3,4,6,5,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut56 [3,4,6,5,7,8] [2,6,7,0,1,8] 30 (by decide +kernel) node230))

def cert232 : Local := ⟨⟨0,440,0,482,456,336,312,120,184⟩,[(0,1),(2,3)],[(2,0,0),(0,3,2),(1,4,3)]⟩
theorem node232 : UpperPrefix a [2,6,3,0,1,7] 30 :=
  local_sound a [2,6,3,0,1,7] 30 cert232 (by decide +kernel)

def cert233 : Local := ⟨⟨0,441,0,481,329,0,313,121,185⟩,[(0,1),(2,5),(5,2)],[(2,0,0),(1,3,2),(1,3,5)]⟩
theorem node233 : UpperPrefix a [2,6,3,1,7,0] 30 :=
  local_sound a [2,6,3,1,7,0] 30 cert233 (by decide +kernel)

def cert234 : Leaf := ⟨⟨0,185,240,96,194,209,304,112,176⟩,[(0,1)],[(2,0,0),(1,5,4)],⟨7,70,13,152,49,42,496,432,368⟩,⟨7,70,13,152,49,42,192,384,320⟩,[⟨8,1181761535957112882659,⟨55,127,29,189,53,63,255,191,127⟩⟩,⟨0,1285813291192733985145856,⟨6,70,12,472,504,42,192,384,320⟩⟩,⟨3,1437224743012690090263555,⟨7,71,5,464,497,499,192,384,320⟩⟩]⟩
theorem node234 : UpperPrefix a [2,6,3,7,0,1] 30 :=
  Boolean.leaf_sound a [2,6,3,7,0,1] 30 cert234 (by decide +kernel)

def cert235 : Leaf := ⟨⟨0,409,216,386,393,272,312,56,184⟩,[(0,1)],[(2,0,0),(1,4,3)],⟨7,70,261,25,50,168,248,440,376⟩,⟨7,70,261,25,50,168,192,384,320⟩,[⟨0,1247960428519766738600960,⟨6,70,260,504,50,488,192,384,320⟩⟩,⟨6,1210143306096994348434435,⟨191,191,445,57,59,168,128,384,256⟩⟩,⟨5,1210107564157954027587015,⟨7,71,263,25,27,141,199,391,327⟩⟩]⟩
theorem node235 : UpperPrefix a [2,6,8,0,1,7] 30 :=
  Boolean.leaf_sound a [2,6,8,0,1,7] 30 cert235 (by decide +kernel)

theorem node236 : UpperPrefix a [3,4,6,5,8] 30 :=
  branch_upper a [3,4,6,5,8] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut55 [3,4,6,5,8,0] [2,6,3,0,1,7] 30 (by decide +kernel) node232)
  (PrefixConjugacy.upper aut91 [3,4,6,5,8,1] [2,6,3,1,7,0] 30 (by decide +kernel) node233)
  (PrefixConjugacy.upper aut73 [3,4,6,5,8,2] [2,6,3,7,0,1] 30 (by decide +kernel) node234)
  (invalid_upper a [3,4,6,5,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,8,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut55 [3,4,6,5,8,7] [2,6,8,0,1,7] 30 (by decide +kernel) node235)
  (invalid_upper a [3,4,6,5,8,8] 30 (by decide +kernel)))

theorem node237 : UpperPrefix a [3,4,6,5] 30 :=
  branch_upper a [3,4,6,5] 30 (by decide) (fin9_cases _
  node224
  node225
  node226
  (invalid_upper a [3,4,6,5,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,6] 30 (by decide +kernel))
  node231
  node236)

def cert238 : Local := ⟨⟨500,0,418,0,458,194,290,98,162⟩,[(1,3),(3,1)],[(3,0,4),(4,1,0),(2,3,0),(0,4,1),(0,4,3)]⟩
theorem node238 : UpperPrefix a [3,4,6,2,0,8] 30 :=
  local_sound a [3,4,6,2,0,8] 30 cert238 (by decide +kernel)

def cert239 : Leaf := ⟨⟨52,33,162,102,14,194,294,102,166⟩,[],[(3,0,4),(4,1,0),(0,4,1)],⟨11,22,69,152,49,44,482,418,354⟩,⟨11,22,69,152,49,44,192,384,320⟩,[⟨8,1181761606531971010029,⟨27,55,127,187,51,63,255,191,127⟩⟩,⟨6,1210106412364546102543393,⟨11,22,5,152,51,63,128,384,256⟩⟩,⟨7,1208926973665333298086945,⟨11,22,69,24,51,63,64,256,320⟩⟩]⟩
theorem node239 : UpperPrefix a [3,4,6,7,0,2] 30 :=
  Boolean.leaf_sound a [3,4,6,7,0,2] 30 cert239 (by decide +kernel)

def cert240 : Leaf := ⟨⟨180,161,162,292,140,132,36,100,164⟩,[],[(3,0,4),(4,1,0),(0,4,1),(1,6,2)],⟨11,22,69,152,49,296,194,420,356⟩,⟨11,22,69,152,49,296,194,384,320⟩,[⟨6,1210106425895161963744325,⟨11,23,31,184,49,312,187,440,313⟩⟩,⟨8,1181889786609621300265,⟨79,22,69,223,55,127,194,128,64⟩⟩]⟩
theorem node240 : UpperPrefix a [3,4,6,7,0,8,1] 30 :=
  Boolean.leaf_sound a [3,4,6,7,0,8,1] 30 cert240 (by decide +kernel)

def cert241 : Leaf := ⟨⟨180,161,162,294,142,134,34,38,166⟩,[],[(3,0,4),(4,1,0),(0,4,1)],⟨11,22,69,152,49,296,196,418,354⟩,⟨11,22,69,152,49,296,196,384,320⟩,[⟨6,1212467609147630557367621,⟨11,23,31,184,57,441,191,441,443⟩⟩,⟨8,1181889786609621300265,⟨79,22,69,223,55,127,196,128,64⟩⟩]⟩
theorem node241 : UpperPrefix a [3,4,6,7,0,8,2] 30 :=
  Boolean.leaf_sound a [3,4,6,7,0,8,2] 30 cert241 (by decide +kernel)

def cert242 : Leaf := ⟨⟨240,225,162,98,202,194,258,100,166⟩,[],[(3,0,4),(4,1,0),(0,4,1),(8,5,6)],⟨11,22,69,152,49,296,224,386,324⟩,⟨11,22,69,152,49,296,224,386,320⟩,[⟨2,1210110028766617521882241,⟨91,18,89,249,49,376,249,507,376⟩⟩]⟩
theorem node242 : UpperPrefix a [3,4,6,7,0,8,5,1] 30 :=
  Boolean.leaf_sound a [3,4,6,7,0,8,5,1] 30 cert242 (by decide +kernel)

def cert243 : Local := ⟨⟨180,161,162,38,142,134,262,98,166⟩,[],[(3,0,4),(4,1,0),(6,2,7),(0,4,1),(8,5,6)]⟩
theorem node243 : UpperPrefix a [3,4,6,7,0,8,5,2] 30 :=
  local_sound a [3,4,6,7,0,8,5,2] 30 cert243 (by decide +kernel)

theorem node244 : UpperPrefix a [3,4,6,7,0,8,5] 30 :=
  branch_upper a [3,4,6,7,0,8,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,7,0,8,5,0] 30 (by decide +kernel))
  node242
  node243
  (invalid_upper a [3,4,6,7,0,8,5,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,8,5,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,8,5,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,8,5,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,8,5,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,8,5,8] 30 (by decide +kernel)))

theorem node245 : UpperPrefix a [3,4,6,7,0,8] 30 :=
  branch_upper a [3,4,6,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,7,0,8,0] 30 (by decide +kernel))
  node240
  node241
  (invalid_upper a [3,4,6,7,0,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,8,4] 30 (by decide +kernel))
  node244
  (invalid_upper a [3,4,6,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,8,8] 30 (by decide +kernel)))

theorem node246 : UpperPrefix a [3,4,6,7,0] 30 :=
  branch_upper a [3,4,6,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,7,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut62 [3,4,6,7,0,1] [3,4,6,2,0,8] 30 (by decide +kernel) node238)
  node239
  (invalid_upper a [3,4,6,7,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,7] 30 (by decide +kernel))
  node245)

def cert247 : Leaf := ⟨⟨244,97,160,101,69,0,293,101,37⟩,[(5,0)],[(3,0,5),(4,1,0)],⟨11,22,69,152,50,41,484,420,356⟩,⟨11,22,69,152,50,41,192,384,320⟩,[⟨1,1460882782392203984764929,⟨493,476,485,472,508,493,192,384,320⟩⟩,⟨8,1181761921061016014285,⟨59,55,127,187,50,57,255,191,127⟩⟩,⟨7,1227816439630140825144321,⟨59,278,375,24,50,57,64,256,320⟩⟩]⟩
theorem node247 : UpperPrefix a [3,4,6,7,1,0] 30 :=
  Boolean.leaf_sound a [3,4,6,7,1,0] 30 cert247 (by decide +kernel)

def cert248 : Leaf := ⟨⟨212,200,0,356,204,196,12,108,172⟩,[(2,6)],[(4,1,0),(0,6,2)],⟨11,22,69,152,50,296,193,420,356⟩,⟨11,22,69,152,50,296,193,384,320⟩,[⟨1,1546050535722711235428353,⟨493,508,485,184,440,296,485,384,452⟩⟩,⟨8,1181889786609638077481,⟨79,22,69,223,55,127,197,128,68⟩⟩,⟨5,1210107708273139882669097,⟨79,22,69,223,23,335,197,384,324⟩⟩]⟩
theorem node248 : UpperPrefix a [3,4,6,7,1,8,0] 30 :=
  Boolean.leaf_sound a [3,4,6,7,1,8,0] 30 cert248 (by decide +kernel)

def cert249 : Leaf := ⟨⟨176,169,168,289,137,129,41,41,169⟩,[],[(4,1,0)],⟨11,22,69,152,50,296,196,417,353⟩,⟨11,22,69,152,50,296,196,384,320⟩,[⟨1,1233765640764727137402881,⟨493,508,485,152,120,296,452,384,320⟩⟩,⟨2,1229052373910666686235667,⟨187,443,505,153,187,296,488,384,352⟩⟩,⟨6,1212762757041816941399383,⟨11,31,31,185,187,441,191,441,443⟩⟩,⟨8,1181889786609621300265,⟨79,22,69,223,55,127,196,128,64⟩⟩]⟩
theorem node249 : UpperPrefix a [3,4,6,7,1,8,2] 30 :=
  Boolean.leaf_sound a [3,4,6,7,1,8,2] 30 cert249 (by decide +kernel)

def cert250 : Leaf := ⟨⟨84,105,40,69,77,197,269,69,5⟩,[],[(4,1,0),(8,5,6)],⟨11,22,69,152,50,296,224,389,325⟩,⟨11,22,69,152,50,296,224,384,320⟩,[⟨1,1233765640764727137402881,⟨493,508,485,152,120,296,224,384,320⟩⟩,⟨7,1530047894504867236056097,⟨11,278,343,24,51,315,375,258,342⟩⟩,⟨5,1229052370321653904704531,⟨139,415,453,153,155,264,192,384,320⟩⟩,⟨3,1229033924703476612334593,⟨3,406,453,144,50,288,224,384,320⟩⟩]⟩
theorem node250 : UpperPrefix a [3,4,6,7,1,8,5] 30 :=
  Boolean.leaf_sound a [3,4,6,7,1,8,5] 30 cert250 (by decide +kernel)

theorem node251 : UpperPrefix a [3,4,6,7,1,8] 30 :=
  branch_upper a [3,4,6,7,1,8] 30 (by decide) (fin9_cases _
  node248
  (invalid_upper a [3,4,6,7,1,8,1] 30 (by decide +kernel))
  node249
  (invalid_upper a [3,4,6,7,1,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,8,4] 30 (by decide +kernel))
  node250
  (invalid_upper a [3,4,6,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,8,8] 30 (by decide +kernel)))

theorem node252 : UpperPrefix a [3,4,6,7,1] 30 :=
  branch_upper a [3,4,6,7,1] 30 (by decide) (fin9_cases _
  node247
  (invalid_upper a [3,4,6,7,1,1] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut98 [3,4,6,7,1,2] [3,4,6,0,8,2] 30 (by decide +kernel) node190)
  (invalid_upper a [3,4,6,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,7] 30 (by decide +kernel))
  node251)

def cert253 : Local := ⟨⟨496,0,418,354,451,0,290,98,162⟩,[(1,4),(5,0)],[(3,0,5),(4,1,0),(2,4,1),(0,5,4)]⟩
theorem node253 : UpperPrefix a [3,4,6,7,2,0] 30 :=
  local_sound a [3,4,6,7,2,0] 30 cert253 (by decide +kernel)

def cert254 : Leaf := ⟨⟨0,0,170,99,203,0,299,107,171⟩,[(0,5),(1,4),(5,0)],[(4,1,0),(4,1,5),(2,4,1)],⟨11,22,69,152,52,42,481,417,353⟩,⟨11,22,69,152,52,42,192,384,320⟩,[⟨8,1181761920442540731885,⟨59,55,127,187,55,59,255,191,127⟩⟩]⟩
theorem node254 : UpperPrefix a [3,4,6,7,2,1] 30 :=
  Boolean.leaf_sound a [3,4,6,7,2,1] 30 cert254 (by decide +kernel)

def cert255 : Local := ⟨⟨496,0,0,354,458,194,298,106,170⟩,[(1,4),(2,6)],[(4,1,0),(2,4,1),(0,6,2)]⟩
theorem node255 : UpperPrefix a [3,4,6,7,2,8,0] 30 :=
  local_sound a [3,4,6,7,2,8,0] 30 cert255 (by decide +kernel)

#print axioms node255
end Delivery.FiniteExclusion.Sharp3x3x3
