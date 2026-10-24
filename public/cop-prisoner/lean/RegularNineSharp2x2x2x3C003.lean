import RegularNineSharp2x2x2x3Base
import RegularNineSharp2x2x2x3C000
import RegularNineSharp2x2x2x3C001
import RegularNineSharp2x2x2x3C002
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x2x2x3
open Bounds BoundTreeRows Extremal
theorem node192 : UpperPrefix a [2,6,0,7] 30 :=
  branch_upper a [2,6,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,6,0,7,0] 30 (by decide +kernel))
  node185
  (invalid_upper a [2,6,0,7,2] 30 (by decide +kernel))
  node190
  (invalid_upper a [2,6,0,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,0,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,0,7,7] 30 (by decide +kernel))
  node191)

theorem node193 : UpperPrefix a [2,6,0] 30 :=
  branch_upper a [2,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,6,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut48 [2,6,0,1] [2,3,0,6] 30 (by decide +kernel) node2)
  (invalid_upper a [2,6,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,6,0,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut48 [2,6,0,4] [2,4,0,6] 30 (by decide +kernel) node60)
  (PrefixConjugacy.upper aut51 [2,6,0,5] [2,4,0,6] 30 (by decide +kernel) node60)
  (invalid_upper a [2,6,0,6] 30 (by decide +kernel))
  node192
  (PrefixConjugacy.upper aut49 [2,6,0,8] [2,6,0,7] 30 (by decide +kernel) node192))

def cert194 : Leaf := ⟨⟨0,136,193,65,200,201,313,121,185⟩,[(0,2)],[(1,2,0)],⟨7,67,14,140,49,304,248,440,376⟩,⟨7,67,14,140,49,304,192,384,320⟩,[⟨2,1229033996937199741830657,⟨499,115,506,488,51,304,192,384,320⟩⟩,⟨8,1181745671447422600679,⟨7,79,15,141,49,55,207,143,79⟩⟩,⟨4,1210107565282778062423527,⟨7,79,15,141,33,295,207,399,335⟩⟩,⟨5,1210107564157977667208679,⟨7,79,15,141,17,279,207,399,335⟩⟩]⟩
theorem node194 : UpperPrefix a [2,6,1,7,0,8] 30 :=
  Boolean.leaf_sound a [2,6,1,7,0,8] 30 cert194 (by decide +kernel)

theorem node195 : UpperPrefix a [2,6,1,7,0] 30 :=
  branch_upper a [2,6,1,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,6,1,7,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,0,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut66 [2,6,1,7,0,3] [2,4,5,6,7,3] 30 (by decide +kernel) node102)
  (invalid_upper a [2,6,1,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,0,7] 30 (by decide +kernel))
  node194)

def cert196 : Leaf := ⟨⟨0,0,496,368,448,200,312,120,184⟩,[(0,2),(1,6)],[(1,2,0),(0,6,1)],⟨7,67,14,140,56,304,193,432,368⟩,⟨7,67,14,140,56,304,193,384,320⟩,[⟨2,1234134503941275375404545,⟨499,483,506,440,184,432,483,384,322⟩⟩]⟩
theorem node196 : UpperPrefix a [2,6,1,7,3,8,0] 30 :=
  Boolean.leaf_sound a [2,6,1,7,3,8,0] 30 cert196 (by decide +kernel)

def cert197 : Leaf := ⟨⟨0,392,449,321,321,73,297,105,57⟩,[(0,2)],[(1,2,0)],⟨7,67,14,140,56,304,208,417,353⟩,⟨7,67,14,140,56,304,208,384,320⟩,[⟨2,1224302569212498302469633,⟨499,483,506,248,120,304,208,384,320⟩⟩,⟨4,1210402713187963866088935,⟨7,79,15,141,173,431,207,399,335⟩⟩,⟨5,1210107564157977667208679,⟨7,79,15,141,25,279,223,399,335⟩⟩,⟨7,1218371706805620059407365,⟨311,355,319,61,56,304,80,256,320⟩⟩]⟩
theorem node197 : UpperPrefix a [2,6,1,7,3,8,4] 30 :=
  Boolean.leaf_sound a [2,6,1,7,3,8,4] 30 cert197 (by decide +kernel)

def cert198 : Leaf := ⟨⟨0,168,225,97,193,201,265,104,185⟩,[(0,2)],[(1,2,0),(8,5,6)],⟨7,67,14,140,56,304,224,385,336⟩,⟨7,67,14,140,56,304,224,385,320⟩,[⟨2,1347086440483340240881153,⟨499,483,506,506,376,304,226,483,320⟩⟩,⟨4,1212764761120561507788279,⟨7,79,15,141,239,495,239,399,463⟩⟩]⟩
theorem node198 : UpperPrefix a [2,6,1,7,3,8,5,0] 30 :=
  Boolean.leaf_sound a [2,6,1,7,3,8,5,0] 30 cert198 (by decide +kernel)

def cert199 : Local := ⟨⟨0,172,225,97,197,0,285,0,173⟩,[(0,2),(5,7),(7,5)],[(1,2,0),(8,5,6),(4,7,6)]⟩
theorem node199 : UpperPrefix a [2,6,1,7,3,8,5,4] 30 :=
  local_sound a [2,6,1,7,3,8,5,4] 30 cert199 (by decide +kernel)

theorem node200 : UpperPrefix a [2,6,1,7,3,8,5] 30 :=
  branch_upper a [2,6,1,7,3,8,5] 30 (by decide) (fin9_cases _
  node198
  (invalid_upper a [2,6,1,7,3,8,5,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,3,8,5,2] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,3,8,5,3] 30 (by decide +kernel))
  node199
  (invalid_upper a [2,6,1,7,3,8,5,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,3,8,5,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,3,8,5,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,3,8,5,8] 30 (by decide +kernel)))

theorem node201 : UpperPrefix a [2,6,1,7,3,8] 30 :=
  branch_upper a [2,6,1,7,3,8] 30 (by decide) (fin9_cases _
  node196
  (invalid_upper a [2,6,1,7,3,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,3,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,3,8,3] 30 (by decide +kernel))
  node197
  node200
  (invalid_upper a [2,6,1,7,3,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,3,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,3,8,8] 30 (by decide +kernel)))

theorem node202 : UpperPrefix a [2,6,1,7,3] 30 :=
  branch_upper a [2,6,1,7,3] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut69 [2,6,1,7,3,0] [2,4,5,6,7,3] 30 (by decide +kernel) node102)
  (invalid_upper a [2,6,1,7,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,3,7] 30 (by decide +kernel))
  node201)

theorem node203 : UpperPrefix a [2,6,1,7,8] 30 :=
  branch_upper a [2,6,1,7,8] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut3 [2,6,1,7,8,0] [2,6,1,7,0,8] 30 (by decide +kernel) node194)
  (invalid_upper a [2,6,1,7,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,8,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut3 [2,6,1,7,8,3] [2,6,1,7,3,8] 30 (by decide +kernel) node201)
  (invalid_upper a [2,6,1,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,8,8] 30 (by decide +kernel)))

theorem node204 : UpperPrefix a [2,6,1,7] 30 :=
  branch_upper a [2,6,1,7] 30 (by decide) (fin9_cases _
  node195
  (invalid_upper a [2,6,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,2] 30 (by decide +kernel))
  node202
  (invalid_upper a [2,6,1,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,7,7] 30 (by decide +kernel))
  node203)

def cert205 : Leaf := ⟨⟨0,264,321,65,328,329,313,121,185⟩,[(0,2)],[(1,2,0)],⟨7,67,14,268,49,176,248,440,376⟩,⟨7,67,14,268,49,176,192,384,320⟩,[⟨2,1229033996937199741830657,⟨499,115,506,488,51,176,192,384,320⟩⟩,⟨7,1208926973665384957380047,⟨7,71,15,271,49,61,79,271,335⟩⟩,⟨4,1210107565282803833800143,⟨7,71,15,271,33,173,207,399,335⟩⟩,⟨5,1210107564158003438585295,⟨7,71,15,271,17,157,207,399,335⟩⟩]⟩
theorem node205 : UpperPrefix a [2,6,1,8,0,7] 30 :=
  Boolean.leaf_sound a [2,6,1,8,0,7] 30 cert205 (by decide +kernel)

theorem node206 : UpperPrefix a [2,6,1,8,0] 30 :=
  branch_upper a [2,6,1,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,6,1,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,8,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,8,0,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut66 [2,6,1,8,0,3] [2,4,5,6,8,3] 30 (by decide +kernel) node107)
  (invalid_upper a [2,6,1,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,8,0,6] 30 (by decide +kernel))
  node205
  (invalid_upper a [2,6,1,8,0,8] 30 (by decide +kernel)))

def cert207 : Leaf := ⟨⟨0,12,65,65,261,269,61,61,189⟩,[(0,2)],[(1,2,0)],⟨7,67,14,268,56,176,241,433,369⟩,⟨7,67,14,268,56,176,192,384,320⟩,[⟨7,1208926973665384957380047,⟨7,71,15,271,61,61,79,271,335⟩⟩,⟨4,1210107565282803833800143,⟨7,71,15,271,45,173,207,399,335⟩⟩,⟨5,1210107564158003438585295,⟨7,71,15,271,29,157,207,399,335⟩⟩,⟨6,1210180200324628969686021,⟨55,3,191,445,184,176,128,384,256⟩⟩,⟨8,1182322129974819054645,⟨7,67,15,13,127,247,192,128,64⟩⟩]⟩
theorem node207 : UpperPrefix a [2,6,1,8,3,7] 30 :=
  Boolean.leaf_sound a [2,6,1,8,3,7] 30 cert207 (by decide +kernel)

theorem node208 : UpperPrefix a [2,6,1,8,3] 30 :=
  branch_upper a [2,6,1,8,3] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut69 [2,6,1,8,3,0] [2,4,5,6,8,3] 30 (by decide +kernel) node107)
  (invalid_upper a [2,6,1,8,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,8,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,8,3,6] 30 (by decide +kernel))
  node207
  (invalid_upper a [2,6,1,8,3,8] 30 (by decide +kernel)))

theorem node209 : UpperPrefix a [2,6,1,8,7] 30 :=
  branch_upper a [2,6,1,8,7] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut3 [2,6,1,8,7,0] [2,6,1,8,0,7] 30 (by decide +kernel) node205)
  (invalid_upper a [2,6,1,8,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,8,7,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut3 [2,6,1,8,7,3] [2,6,1,8,3,7] 30 (by decide +kernel) node207)
  (invalid_upper a [2,6,1,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,8,7,8] 30 (by decide +kernel)))

theorem node210 : UpperPrefix a [2,6,1,8] 30 :=
  branch_upper a [2,6,1,8] 30 (by decide) (fin9_cases _
  node206
  (invalid_upper a [2,6,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,8,2] 30 (by decide +kernel))
  node208
  (invalid_upper a [2,6,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,8,6] 30 (by decide +kernel))
  node209
  (invalid_upper a [2,6,1,8,8] 30 (by decide +kernel)))

theorem node211 : UpperPrefix a [2,6,1] 30 :=
  branch_upper a [2,6,1] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut54 [2,6,1,0] [2,3,1,6] 30 (by decide +kernel) node6)
  (invalid_upper a [2,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,6,1,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut72 [2,6,1,4] [2,4,6,0] 30 (by decide +kernel) node133)
  (PrefixConjugacy.upper aut75 [2,6,1,5] [2,4,6,0] 30 (by decide +kernel) node133)
  (invalid_upper a [2,6,1,6] 30 (by decide +kernel))
  node204
  node210)

def cert212 : Local := ⟨⟨504,0,0,482,448,386,306,114,178⟩,[(1,2),(2,1)],[(2,0,1),(2,0,2),(3,1,0),(0,2,0)]⟩
theorem node212 : UpperPrefix a [2,3,0,4,1,6] 30 :=
  local_sound a [2,3,0,4,1,6] 30 cert212 (by decide +kernel)

theorem node213 : UpperPrefix a [2,6,4,5,0] 30 :=
  branch_upper a [2,6,4,5,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,6,4,5,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut96 [2,6,4,5,0,1] [2,3,4,5,0,6] 30 (by decide +kernel) node9)
  (invalid_upper a [2,6,4,5,0,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut105 [2,6,4,5,0,3] [2,3,0,4,1,6] 30 (by decide +kernel) node212)
  (invalid_upper a [2,6,4,5,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,5,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,5,0,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut98 [2,6,4,5,0,7] [2,3,4,6,0,8] 30 (by decide +kernel) node11)
  (PrefixConjugacy.upper aut97 [2,6,4,5,0,8] [2,3,4,6,0,7] 30 (by decide +kernel) node10))

theorem node214 : UpperPrefix a [2,6,4,5,1] 30 :=
  branch_upper a [2,6,4,5,1] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut105 [2,6,4,5,1,0] [2,3,4,5,1,6] 30 (by decide +kernel) node13)
  (invalid_upper a [2,6,4,5,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,5,1,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut129 [2,6,4,5,1,3] [2,3,0,4,6,1] 30 (by decide +kernel) node149)
  (invalid_upper a [2,6,4,5,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,5,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,5,1,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut122 [2,6,4,5,1,7] [2,3,4,6,8,0] 30 (by decide +kernel) node28)
  (PrefixConjugacy.upper aut121 [2,6,4,5,1,8] [2,3,4,6,7,0] 30 (by decide +kernel) node22))

def cert215 : Local := ⟨⟨448,388,0,467,0,455,263,71,135⟩,[(2,4),(4,3)],[(4,2,3),(5,3,2),(5,3,4),(3,4,2)]⟩
theorem node215 : UpperPrefix a [2,6,4,5,3] 30 :=
  local_sound a [2,6,4,5,3] 30 cert215 (by decide +kernel)

def cert216 : Local := ⟨⟨504,0,0,434,448,194,306,114,178⟩,[(1,2),(2,1)],[(2,0,1),(2,0,2),(3,1,0),(0,2,0)]⟩
theorem node216 : UpperPrefix a [2,3,0,6,1,8] 30 :=
  local_sound a [2,3,0,6,1,8] 30 cert216 (by decide +kernel)

def cert217 : Leaf := ⟨⟨72,68,131,67,66,67,307,115,51⟩,[],[(2,0,1),(3,1,0),(7,3,2)],⟨7,11,76,140,49,304,242,434,370⟩,⟨7,11,76,140,49,304,192,384,320⟩,[⟨8,1181745671447388593645,⟨7,11,79,143,49,55,207,143,79⟩⟩,⟨4,1210107565282778028416493,⟨7,11,79,143,33,295,207,399,335⟩⟩,⟨5,1210107564157977633201645,⟨7,11,79,143,17,279,207,399,335⟩⟩]⟩
theorem node217 : UpperPrefix a [2,3,6,7,0,8] 30 :=
  Boolean.leaf_sound a [2,3,6,7,0,8] 30 cert217 (by decide +kernel)

theorem node218 : UpperPrefix a [2,6,4,5,7] 30 :=
  branch_upper a [2,6,4,5,7] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut107 [2,6,4,5,7,0] [2,3,4,6,1,8] 30 (by decide +kernel) node20)
  (PrefixConjugacy.upper aut131 [2,6,4,5,7,1] [2,3,4,6,8,1] 30 (by decide +kernel) node31)
  (invalid_upper a [2,6,4,5,7,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut107 [2,6,4,5,7,3] [2,3,0,6,1,8] 30 (by decide +kernel) node216)
  (invalid_upper a [2,6,4,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,5,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,5,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,5,7,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut98 [2,6,4,5,7,8] [2,3,6,7,0,8] 30 (by decide +kernel) node217))

def cert219 : Local := ⟨⟨504,0,0,434,448,322,306,114,178⟩,[(1,2),(2,1)],[(2,0,1),(2,0,2),(3,1,0),(0,2,0)]⟩
theorem node219 : UpperPrefix a [2,3,0,6,1,7] 30 :=
  local_sound a [2,3,0,6,1,7] 30 cert219 (by decide +kernel)

def cert220 : Leaf := ⟨⟨72,68,131,67,65,67,307,115,51⟩,[],[(2,0,1),(3,1,0),(7,3,2)],⟨7,11,76,140,50,304,241,433,369⟩,⟨7,11,76,140,50,304,192,384,320⟩,[⟨8,1181745671447388593645,⟨7,11,79,143,51,55,207,143,79⟩⟩,⟨4,1210107565282778028416493,⟨7,11,79,143,35,295,207,399,335⟩⟩,⟨5,1210107564157977633201645,⟨7,11,79,143,19,279,207,399,335⟩⟩]⟩
theorem node220 : UpperPrefix a [2,3,6,7,1,8] 30 :=
  Boolean.leaf_sound a [2,3,6,7,1,8] 30 cert220 (by decide +kernel)

theorem node221 : UpperPrefix a [2,6,4,5,8] 30 :=
  branch_upper a [2,6,4,5,8] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut106 [2,6,4,5,8,0] [2,3,4,6,1,7] 30 (by decide +kernel) node17)
  (PrefixConjugacy.upper aut130 [2,6,4,5,8,1] [2,3,4,6,7,1] 30 (by decide +kernel) node23)
  (invalid_upper a [2,6,4,5,8,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut106 [2,6,4,5,8,3] [2,3,0,6,1,7] 30 (by decide +kernel) node219)
  (invalid_upper a [2,6,4,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,5,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,5,8,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut107 [2,6,4,5,8,7] [2,3,6,7,1,8] 30 (by decide +kernel) node220)
  (invalid_upper a [2,6,4,5,8,8] 30 (by decide +kernel)))

theorem node222 : UpperPrefix a [2,6,4,5] 30 :=
  branch_upper a [2,6,4,5] 30 (by decide) (fin9_cases _
  node213
  node214
  (invalid_upper a [2,6,4,5,2] 30 (by decide +kernel))
  node215
  (invalid_upper a [2,6,4,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,5,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,5,6] 30 (by decide +kernel))
  node218
  node221)

def cert223 : Leaf := ⟨⟨432,432,416,304,392,136,304,56,184⟩,[],[(1,6,1)],⟨7,67,28,140,49,304,194,424,360⟩,⟨7,67,28,140,49,304,194,384,320⟩,[⟨0,1290876688957479054214144,⟨494,458,444,172,508,444,194,384,320⟩⟩,⟨2,1266886733790850251236865,⟨499,115,506,488,115,306,210,384,320⟩⟩,⟨6,1212762757041817071912003,⟨7,31,28,172,189,444,191,444,445⟩⟩,⟨3,1210107709399038688238605,⟨7,67,87,199,49,304,194,384,320⟩⟩]⟩
theorem node223 : UpperPrefix a [2,6,4,7,0,8,1] 30 :=
  Boolean.leaf_sound a [2,6,4,7,0,8,1] 30 cert223 (by decide +kernel)

def cert224 : Leaf := ⟨⟨72,8,355,371,322,67,0,115,51⟩,[(6,3)],[(7,3,6)],⟨7,67,28,140,49,304,200,418,354⟩,⟨7,67,28,140,49,304,200,384,320⟩,[⟨2,1224450125642652203353601,⟨499,499,248,200,435,432,200,384,320⟩⟩,⟨3,1219579968471459741828097,⟨439,499,20,132,177,304,192,384,320⟩⟩,⟨4,1210107709397940250385421,⟨7,67,79,207,33,288,203,384,322⟩⟩,⟨5,1210107708273139855170573,⟨7,67,95,207,17,272,203,384,322⟩⟩,⟨8,1181889784410587307021,⟨7,67,95,207,49,48,203,128,66⟩⟩]⟩
theorem node224 : UpperPrefix a [2,6,4,7,0,8,3] 30 :=
  Boolean.leaf_sound a [2,6,4,7,0,8,3] 30 cert224 (by decide +kernel)

def cert225 : Leaf := ⟨⟨200,136,194,66,202,203,266,74,138⟩,[],[(8,5,6)],⟨7,67,28,140,49,304,224,394,330⟩,⟨7,67,28,140,49,304,224,384,320⟩,[⟨2,1229034159066786327176705,⟨499,115,506,488,115,306,224,384,320⟩⟩,⟨4,1314286417130155993476109,⟨399,459,463,399,491,482,224,384,320⟩⟩,⟨5,1525058049100446988141665,⟨399,459,28,140,157,415,463,386,459⟩⟩,⟨0,1219580256596088576803840,⟨398,458,92,140,252,380,236,384,328⟩⟩]⟩
theorem node225 : UpperPrefix a [2,6,4,7,0,8,5] 30 :=
  Boolean.leaf_sound a [2,6,4,7,0,8,5] 30 cert225 (by decide +kernel)

theorem node226 : UpperPrefix a [2,6,4,7,0,8] 30 :=
  branch_upper a [2,6,4,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,6,4,7,0,8,0] 30 (by decide +kernel))
  node223
  (invalid_upper a [2,6,4,7,0,8,2] 30 (by decide +kernel))
  node224
  (invalid_upper a [2,6,4,7,0,8,4] 30 (by decide +kernel))
  node225
  (invalid_upper a [2,6,4,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,0,8,8] 30 (by decide +kernel)))

theorem node227 : UpperPrefix a [2,6,4,7,0] 30 :=
  branch_upper a [2,6,4,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,6,4,7,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut60 [2,6,4,7,0,1] [2,3,4,6,0,7] 30 (by decide +kernel) node10)
  (invalid_upper a [2,6,4,7,0,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut66 [2,6,4,7,0,3] [2,4,5,6,7,0] 30 (by decide +kernel) node100)
  (invalid_upper a [2,6,4,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,0,7] 30 (by decide +kernel))
  node226)

def cert228 : Leaf := ⟨⟨432,0,416,304,452,196,308,60,188⟩,[(1,6)],[(0,6,1)],⟨7,67,28,140,50,304,193,424,360⟩,⟨7,67,28,140,50,304,193,384,320⟩,[⟨1,1290876688957479054213121,⟨493,457,444,172,508,444,457,384,320⟩⟩,⟨3,1210107722932377558752269,⟨7,83,87,247,50,304,243,432,370⟩⟩,⟨6,1210401560267532887131153,⟨7,3,29,140,191,445,129,384,256⟩⟩]⟩
theorem node228 : UpperPrefix a [2,6,4,7,1,8,0] 30 :=
  Boolean.leaf_sound a [2,6,4,7,1,8,0] 30 cert228 (by decide +kernel)

def cert229 : Leaf := ⟨⟨296,300,291,307,321,67,0,51,51⟩,[(6,3)],[(7,3,6)],⟨7,67,28,140,50,304,200,417,353⟩,⟨7,67,28,140,50,304,200,384,320⟩,[⟨2,1219580113149598843798529,⟨435,499,120,200,434,304,200,384,320⟩⟩,⟨3,1219579969034409695249409,⟨439,499,52,132,434,304,192,384,320⟩⟩,⟨6,1210401560267532887131153,⟨7,3,29,140,191,445,136,384,256⟩⟩,⟨4,1210107709397940250385421,⟨7,67,79,207,34,288,203,384,322⟩⟩]⟩
theorem node229 : UpperPrefix a [2,6,4,7,1,8,3] 30 :=
  Boolean.leaf_sound a [2,6,4,7,1,8,3] 30 cert229 (by decide +kernel)

def cert230 : Leaf := ⟨⟨136,140,129,1,205,205,269,13,141⟩,[],[(8,5,6)],⟨7,67,28,140,50,304,224,393,329⟩,⟨7,67,28,140,50,304,224,384,320⟩,[⟨1,1219580257159038530224129,⟨397,457,124,140,508,380,236,384,328⟩⟩,⟨4,1238580402990899690212365,⟨399,459,463,399,482,352,224,384,320⟩⟩,⟨5,1525205623053037201425521,⟨399,459,157,140,415,415,463,386,459⟩⟩,⟨6,1210401560267541477065745,⟨7,11,29,140,191,445,172,384,264⟩⟩]⟩
theorem node230 : UpperPrefix a [2,6,4,7,1,8,5] 30 :=
  Boolean.leaf_sound a [2,6,4,7,1,8,5] 30 cert230 (by decide +kernel)

theorem node231 : UpperPrefix a [2,6,4,7,1,8] 30 :=
  branch_upper a [2,6,4,7,1,8] 30 (by decide) (fin9_cases _
  node228
  (invalid_upper a [2,6,4,7,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,1,8,2] 30 (by decide +kernel))
  node229
  (invalid_upper a [2,6,4,7,1,8,4] 30 (by decide +kernel))
  node230
  (invalid_upper a [2,6,4,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,1,8,8] 30 (by decide +kernel)))

theorem node232 : UpperPrefix a [2,6,4,7,1] 30 :=
  branch_upper a [2,6,4,7,1] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut63 [2,6,4,7,1,0] [2,3,4,6,1,7] 30 (by decide +kernel) node17)
  (invalid_upper a [2,6,4,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,1,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut143 [2,6,4,7,1,3] [2,4,6,1,8,3] 30 (by decide +kernel) node140)
  (invalid_upper a [2,6,4,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,1,7] 30 (by decide +kernel))
  node231)

theorem node233 : UpperPrefix a [2,6,4,7,3] 30 :=
  branch_upper a [2,6,4,7,3] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut69 [2,6,4,7,3,0] [2,4,5,6,7,1] 30 (by decide +kernel) node101)
  (PrefixConjugacy.upper aut140 [2,6,4,7,3,1] [2,4,6,0,8,3] 30 (by decide +kernel) node127)
  (invalid_upper a [2,6,4,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,3,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut98 [2,6,4,7,3,8] [2,6,1,7,0,8] 30 (by decide +kernel) node194))

def cert234 : Leaf := ⟨⟨432,0,288,304,70,324,310,60,190⟩,[(1,6)],[(0,6,1)],⟨7,67,28,140,304,50,193,424,360⟩,⟨7,67,28,140,304,50,193,384,320⟩,[⟨3,1210107721106638500830221,⟨39,99,119,247,304,50,243,432,370⟩⟩,⟨6,1210253986314943747589153,⟨15,3,156,140,445,191,129,384,256⟩⟩,⟨1,1210255139236448354435073,⟨13,65,156,140,444,188,193,384,320⟩⟩,⟨7,1208926984948521624437761,⟨7,99,28,28,304,50,115,304,370⟩⟩]⟩
theorem node234 : UpperPrefix a [2,6,4,7,8,1,0] 30 :=
  Boolean.leaf_sound a [2,6,4,7,8,1,0] 30 cert234 (by decide +kernel)

def cert235 : Leaf := ⟨⟨56,60,291,307,67,65,0,51,51⟩,[(6,3)],[(7,3,6)],⟨7,67,28,140,304,50,200,417,353⟩,⟨7,67,28,140,304,50,200,384,320⟩,[⟨2,1219580112588847913632769,⟨435,499,88,200,304,434,200,384,320⟩⟩,⟨3,1219579968473658765083649,⟨439,499,20,132,304,434,192,384,320⟩⟩,⟨6,1210253986314943747589153,⟨15,3,156,140,445,191,136,384,256⟩⟩,⟨8,1181889925148075662349,⟨39,67,127,239,48,50,203,128,66⟩⟩]⟩
theorem node235 : UpperPrefix a [2,6,4,7,8,1,3] 30 :=
  Boolean.leaf_sound a [2,6,4,7,8,1,3] 30 cert235 (by decide +kernel)

def cert236 : Leaf := ⟨⟨144,148,385,257,205,197,5,13,141⟩,[],[],⟨7,67,28,140,304,50,224,393,329⟩,⟨7,67,28,140,304,50,224,384,320⟩,[⟨1,1219580544828666184466433,⟨397,461,28,140,380,508,252,384,332⟩⟩,⟨5,1525205623053037201425521,⟨399,459,157,140,415,415,463,386,459⟩⟩,⟨3,1210107709539776176593933,⟨39,67,119,231,304,50,224,384,320⟩⟩,⟨4,1219580544825354466886657,⟨399,459,12,140,352,482,224,384,320⟩⟩,⟨6,1210253986314952337523745,⟨15,11,156,140,445,191,173,384,264⟩⟩,⟨8,1181889925148075629581,⟨39,67,127,239,48,50,224,128,64⟩⟩]⟩
theorem node236 : UpperPrefix a [2,6,4,7,8,1,5] 30 :=
  Boolean.leaf_sound a [2,6,4,7,8,1,5] 30 cert236 (by decide +kernel)

theorem node237 : UpperPrefix a [2,6,4,7,8,1] 30 :=
  branch_upper a [2,6,4,7,8,1] 30 (by decide) (fin9_cases _
  node234
  (invalid_upper a [2,6,4,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,8,1,2] 30 (by decide +kernel))
  node235
  (invalid_upper a [2,6,4,7,8,1,4] 30 (by decide +kernel))
  node236
  (invalid_upper a [2,6,4,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,8,1,8] 30 (by decide +kernel)))

def cert238 : Leaf := ⟨⟨184,184,0,304,136,0,59,123,187⟩,[(2,5),(5,2)],[],⟨7,67,28,140,304,56,227,419,355⟩,⟨7,67,28,140,304,56,192,384,320⟩,[⟨2,1214839173293962902373889,⟨499,467,56,168,304,56,192,384,320⟩⟩,⟨6,1210106428573572416930819,⟨39,47,60,188,308,60,188,444,316⟩⟩,⟨8,1181889925148084034621,⟨39,67,127,239,55,127,192,128,64⟩⟩,⟨0,1210107581495077023777792,⟨38,110,60,188,308,60,252,444,380⟩⟩,⟨1,1210107581495077023776769,⟨37,109,60,188,308,60,252,444,380⟩⟩]⟩
theorem node238 : UpperPrefix a [2,6,4,7,8,3] 30 :=
  Boolean.leaf_sound a [2,6,4,7,8,3] 30 cert238 (by decide +kernel)

theorem node239 : UpperPrefix a [2,6,4,7,8] 30 :=
  branch_upper a [2,6,4,7,8] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut64 [2,6,4,7,8,0] [2,6,4,7,1,8] 30 (by decide +kernel) node231)
  node237
  (invalid_upper a [2,6,4,7,8,2] 30 (by decide +kernel))
  node238
  (invalid_upper a [2,6,4,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,8,8] 30 (by decide +kernel)))

theorem node240 : UpperPrefix a [2,6,4,7] 30 :=
  branch_upper a [2,6,4,7] 30 (by decide) (fin9_cases _
  node227
  node232
  (invalid_upper a [2,6,4,7,2] 30 (by decide +kernel))
  node233
  (invalid_upper a [2,6,4,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,7,7] 30 (by decide +kernel))
  node239)

def cert241 : Leaf := ⟨⟨432,432,416,176,384,256,304,56,184⟩,[],[(1,6,1)],⟨7,67,28,268,49,176,194,424,360⟩,⟨7,67,28,268,49,176,194,384,320⟩,[⟨0,1290950475933773892420608,⟨494,458,444,428,508,444,194,384,320⟩⟩,⟨2,1266887312503402368345601,⟨499,115,506,488,115,242,242,384,352⟩⟩,⟨6,1212541398787135959467075,⟨55,55,188,444,53,188,191,444,445⟩⟩,⟨3,1210108143996540168446981,⟨23,115,23,261,115,242,242,384,352⟩⟩]⟩
theorem node241 : UpperPrefix a [2,6,4,8,0,7,1] 30 :=
  Boolean.leaf_sound a [2,6,4,8,0,7,1] 30 cert241 (by decide +kernel)

def cert242 : Leaf := ⟨⟨168,168,162,162,138,10,290,104,170⟩,[],[(6,1,7),(8,3,6)],⟨7,67,28,268,49,176,200,386,352⟩,⟨7,67,28,268,49,176,200,386,320⟩,[⟨0,1455680765062391155131392,⟨462,202,380,268,508,508,200,450,320⟩⟩,⟨2,1583349838869894279464449,⟨499,499,504,360,435,176,488,434,320⟩⟩,⟨4,1288580248759493767249421,⟨207,67,463,463,483,418,203,386,450⟩⟩]⟩
theorem node242 : UpperPrefix a [2,6,4,8,0,7,3,1] 30 :=
  Boolean.leaf_sound a [2,6,4,8,0,7,3,1] 30 cert242 (by decide +kernel)

def cert243 : Leaf := ⟨⟨216,152,192,208,200,72,272,88,154⟩,[],[(8,3,6),(5,7,5)],⟨7,67,28,268,49,176,200,416,322⟩,⟨7,67,28,268,49,176,200,416,320⟩,[⟨0,1224508690487204218143744,⟨494,458,252,492,508,252,200,492,320⟩⟩,⟨1,1210184450877513551314945,⟨117,81,252,492,117,252,200,492,320⟩⟩,⟨2,1224523912759684529915393,⟨499,499,248,488,435,176,200,416,320⟩⟩]⟩
theorem node243 : UpperPrefix a [2,6,4,8,0,7,3,5] 30 :=
  Boolean.leaf_sound a [2,6,4,8,0,7,3,5] 30 cert243 (by decide +kernel)

theorem node244 : UpperPrefix a [2,6,4,8,0,7,3] 30 :=
  branch_upper a [2,6,4,8,0,7,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,6,4,8,0,7,3,0] 30 (by decide +kernel))
  node242
  (invalid_upper a [2,6,4,8,0,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,0,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,0,7,3,4] 30 (by decide +kernel))
  node243
  (invalid_upper a [2,6,4,8,0,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,0,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,0,7,3,8] 30 (by decide +kernel)))

def cert245 : Leaf := ⟨⟨360,296,354,98,330,330,0,106,42⟩,[(6,5)],[(7,5,6)],⟨7,67,28,268,49,176,224,394,330⟩,⟨7,67,28,268,49,176,224,384,320⟩,[⟨0,1219580833619780087841792,⟨398,458,124,268,252,244,224,384,320⟩⟩,⟨2,1229034735527538630600193,⟨499,115,506,488,115,242,224,384,320⟩⟩,⟨4,1314286417130155993476109,⟨399,459,463,399,491,482,224,384,320⟩⟩]⟩
theorem node245 : UpperPrefix a [2,6,4,8,0,7,5] 30 :=
  Boolean.leaf_sound a [2,6,4,8,0,7,5] 30 cert245 (by decide +kernel)

theorem node246 : UpperPrefix a [2,6,4,8,0,7] 30 :=
  branch_upper a [2,6,4,8,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,6,4,8,0,7,0] 30 (by decide +kernel))
  node241
  (invalid_upper a [2,6,4,8,0,7,2] 30 (by decide +kernel))
  node244
  (invalid_upper a [2,6,4,8,0,7,4] 30 (by decide +kernel))
  node245
  (invalid_upper a [2,6,4,8,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,0,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,0,7,8] 30 (by decide +kernel)))

theorem node247 : UpperPrefix a [2,6,4,8,0] 30 :=
  branch_upper a [2,6,4,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,6,4,8,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut60 [2,6,4,8,0,1] [2,3,4,6,0,8] 30 (by decide +kernel) node11)
  (invalid_upper a [2,6,4,8,0,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut66 [2,6,4,8,0,3] [2,4,5,6,8,0] 30 (by decide +kernel) node105)
  (invalid_upper a [2,6,4,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,0,6] 30 (by decide +kernel))
  node246
  (invalid_upper a [2,6,4,8,0,8] 30 (by decide +kernel)))

def cert248 : Leaf := ⟨⟨504,0,224,240,136,8,316,56,188⟩,[(1,6)],[(0,6,1)],⟨7,67,28,268,50,176,193,424,360⟩,⟨7,67,28,268,50,176,193,384,320⟩,[⟨1,1290950475933773892419585,⟨493,457,444,428,508,444,457,384,320⟩⟩,⟨2,1210181359459954820416513,⟨51,115,184,440,50,176,243,432,370⟩⟩,⟨6,1210180201731385377948673,⟨55,51,188,428,50,176,177,384,288⟩⟩,⟨8,1181752446749626106881,⟨23,115,28,28,50,176,243,176,114⟩⟩]⟩
theorem node248 : UpperPrefix a [2,6,4,8,1,7,0] 30 :=
  Boolean.leaf_sound a [2,6,4,8,1,7,0] 30 cert248 (by decide +kernel)

def cert249 : Leaf := ⟨⟨232,172,224,240,193,67,292,98,176⟩,[],[(8,3,6)],⟨7,67,28,268,50,176,200,385,352⟩,⟨7,67,28,268,50,176,200,385,320⟩,[⟨0,1436781732922353951704064,⟨14,66,284,268,382,508,200,384,320⟩⟩,⟨1,1436781732922353951703041,⟨13,65,284,268,380,508,200,385,320⟩⟩,⟨2,1521811428441667688989697,⟨435,499,56,264,434,176,488,433,320⟩⟩,⟨3,1521811428441666616296449,⟨439,499,52,260,434,176,480,433,320⟩⟩,⟨4,1210181568431829126520333,⟨71,67,207,463,34,160,203,387,322⟩⟩]⟩
theorem node249 : UpperPrefix a [2,6,4,8,1,7,3,0] 30 :=
  Boolean.leaf_sound a [2,6,4,8,1,7,3,0] 30 cert249 (by decide +kernel)

def cert250 : Leaf := ⟨⟨216,152,192,208,200,72,272,88,153⟩,[],[(8,3,6),(5,7,5)],⟨7,67,28,268,50,176,200,416,321⟩,⟨7,67,28,268,50,176,200,416,320⟩,[⟨0,1210184450877513551315968,⟨118,82,252,492,118,252,200,492,320⟩⟩,⟨1,1224508690487204218142721,⟨493,457,252,492,508,252,200,492,320⟩⟩,⟨2,1224523912759684529915393,⟨499,499,248,488,434,176,200,416,320⟩⟩]⟩
theorem node250 : UpperPrefix a [2,6,4,8,1,7,3,5] 30 :=
  Boolean.leaf_sound a [2,6,4,8,1,7,3,5] 30 cert250 (by decide +kernel)

theorem node251 : UpperPrefix a [2,6,4,8,1,7,3] 30 :=
  branch_upper a [2,6,4,8,1,7,3] 30 (by decide) (fin9_cases _
  node249
  (invalid_upper a [2,6,4,8,1,7,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,1,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,1,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,1,7,3,4] 30 (by decide +kernel))
  node250
  (invalid_upper a [2,6,4,8,1,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,1,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,1,7,3,8] 30 (by decide +kernel)))

def cert252 : Leaf := ⟨⟨328,268,321,65,333,333,0,77,13⟩,[(6,5)],[(7,5,6)],⟨7,67,28,268,50,176,224,393,329⟩,⟨7,67,28,268,50,176,224,384,320⟩,[⟨5,1524984262124147854967897,⟨399,459,157,399,415,157,463,386,459⟩⟩,⟨1,1219580833619782243713025,⟨397,457,124,268,508,252,228,384,320⟩⟩,⟨4,1238580979451651993635853,⟨399,459,463,399,482,224,224,384,320⟩⟩]⟩
theorem node252 : UpperPrefix a [2,6,4,8,1,7,5] 30 :=
  Boolean.leaf_sound a [2,6,4,8,1,7,5] 30 cert252 (by decide +kernel)

theorem node253 : UpperPrefix a [2,6,4,8,1,7] 30 :=
  branch_upper a [2,6,4,8,1,7] 30 (by decide) (fin9_cases _
  node248
  (invalid_upper a [2,6,4,8,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,1,7,2] 30 (by decide +kernel))
  node251
  (invalid_upper a [2,6,4,8,1,7,4] 30 (by decide +kernel))
  node252
  (invalid_upper a [2,6,4,8,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,1,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,1,7,8] 30 (by decide +kernel)))

theorem node254 : UpperPrefix a [2,6,4,8,1] 30 :=
  branch_upper a [2,6,4,8,1] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut63 [2,6,4,8,1,0] [2,3,4,6,1,8] 30 (by decide +kernel) node20)
  (invalid_upper a [2,6,4,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,1,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut142 [2,6,4,8,1,3] [2,4,6,1,7,3] 30 (by decide +kernel) node137)
  (invalid_upper a [2,6,4,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,1,6] 30 (by decide +kernel))
  node253
  (invalid_upper a [2,6,4,8,1,8] 30 (by decide +kernel)))

theorem node255 : UpperPrefix a [2,6,4,8,3] 30 :=
  branch_upper a [2,6,4,8,3] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut69 [2,6,4,8,3,0] [2,4,5,6,8,1] 30 (by decide +kernel) node106)
  (PrefixConjugacy.upper aut139 [2,6,4,8,3,1] [2,4,6,0,7,3] 30 (by decide +kernel) node122)
  (invalid_upper a [2,6,4,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,3,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut97 [2,6,4,8,3,7] [2,6,1,8,0,7] 30 (by decide +kernel) node205)
  (invalid_upper a [2,6,4,8,3,8] 30 (by decide +kernel)))

#print axioms node255
end Delivery.FiniteExclusion.Sharp2x2x2x3
