import RegularNineSharp3x6Base
import RegularNineSharp3x6C016
import RegularNineSharp3x6C017
import RegularNineSharp3x6C018
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
def cert1216 : Leaf := ⟨⟨180,176,162,166,0,150,0,62,182⟩,[(4,6),(6,4)],[],⟨11,70,21,280,176,97,224,390,270⟩,⟨11,70,21,280,176,97,224,384,264⟩,[⟨6,1224301181933668758193155,⟨399,415,413,280,188,445,188,384,264⟩⟩,⟨0,1238497392648065689586688,⟨394,478,478,344,240,112,240,384,264⟩⟩,⟨8,1184344681614152957193,⟨47,118,119,127,246,119,246,247,47⟩⟩,⟨3,1210107853659362307402753,⟨3,118,119,338,246,119,246,384,256⟩⟩]⟩
theorem node1216 : UpperPrefix a [3,6,4,8,7,0,5] 30 :=
  Boolean.leaf_sound a [3,6,4,8,7,0,5] 30 cert1216 (by decide +kernel)

theorem node1217 : UpperPrefix a [3,6,4,8,7,0] 30 :=
  branch_upper a [3,6,4,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,8,7,0,0] 30 (by decide +kernel))
  node1214
  node1215
  (invalid_upper a [3,6,4,8,7,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,7,0,4] 30 (by decide +kernel))
  node1216
  (invalid_upper a [3,6,4,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,7,0,8] 30 (by decide +kernel)))

def cert1218 : Leaf := ⟨⟨404,409,394,164,270,0,284,24,180⟩,[(5,1)],[(6,1,5),(0,6,1)],⟨11,70,21,280,176,98,193,388,296⟩,⟨11,70,21,280,176,98,193,388,264⟩,[⟨5,1212549614034295668809481,⟨207,70,87,479,210,66,195,455,463⟩⟩,⟨1,1285702394555510150922241,⟨9,204,477,280,440,96,193,460,264⟩⟩]⟩
theorem node1218 : UpperPrefix a [3,6,4,8,7,1,0,2] 30 :=
  Boolean.leaf_sound a [3,6,4,8,7,1,0,2] 30 cert1218 (by decide +kernel)

def cert1219 : Local := ⟨⟨404,409,394,134,0,0,286,30,150⟩,[(4,7),(5,1)],[(6,1,5),(0,6,1),(5,7,4)]⟩
theorem node1219 : UpperPrefix a [3,6,4,8,7,1,0,5] 30 :=
  local_sound a [3,6,4,8,7,1,0,5] 30 cert1219 (by decide +kernel)

theorem node1220 : UpperPrefix a [3,6,4,8,7,1,0] 30 :=
  branch_upper a [3,6,4,8,7,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,8,7,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,7,1,0,1] 30 (by decide +kernel))
  node1218
  (invalid_upper a [3,6,4,8,7,1,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,7,1,0,4] 30 (by decide +kernel))
  node1219
  (invalid_upper a [3,6,4,8,7,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,7,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,7,1,0,8] 30 (by decide +kernel)))

def cert1221 : Leaf := ⟨⟨176,0,170,163,11,0,59,59,179⟩,[(1,6),(5,1)],[(6,1,5),(2,6,1),(2,6,5)],⟨11,70,21,280,176,98,196,417,297⟩,⟨11,70,21,280,176,98,196,384,264⟩,[⟨8,1184347566732655836425,⟨47,118,119,127,246,114,246,247,47⟩⟩]⟩
theorem node1221 : UpperPrefix a [3,6,4,8,7,1,2] 30 :=
  Boolean.leaf_sound a [3,6,4,8,7,1,2] 30 cert1221 (by decide +kernel)

def cert1222 : Leaf := ⟨⟨404,441,426,135,0,0,0,31,151⟩,[(4,6),(5,1),(6,4)],[(6,1,5)],⟨11,70,21,280,176,98,224,389,269⟩,⟨11,70,21,280,176,98,224,384,264⟩,[⟨5,1238497103287391316083715,⟨395,463,413,280,144,451,192,384,264⟩⟩]⟩
theorem node1222 : UpperPrefix a [3,6,4,8,7,1,5] 30 :=
  Boolean.leaf_sound a [3,6,4,8,7,1,5] 30 cert1222 (by decide +kernel)

theorem node1223 : UpperPrefix a [3,6,4,8,7,1] 30 :=
  branch_upper a [3,6,4,8,7,1] 30 (by decide) (fin9_cases _
  node1220
  (invalid_upper a [3,6,4,8,7,1,1] 30 (by decide +kernel))
  node1221
  (invalid_upper a [3,6,4,8,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,7,1,4] 30 (by decide +kernel))
  node1222
  (invalid_upper a [3,6,4,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,7,1,8] 30 (by decide +kernel)))

def cert1224 : Leaf := ⟨⟨372,0,352,102,324,0,302,110,102⟩,[(1,5),(5,1)],[(0,6,1),(0,6,5)],⟨11,70,21,280,176,100,193,418,298⟩,⟨11,70,21,280,176,100,193,384,264⟩,[⟨7,1449767664359857615553587,⟨303,367,285,285,319,367,321,256,268⟩⟩,⟨4,1214876138908904873544705,⟨491,230,487,264,162,230,449,384,264⟩⟩,⟨1,1210107567610418307268609,⟨41,116,21,280,176,116,245,384,264⟩⟩,⟨3,1210107567610417233576961,⟨35,118,21,272,178,118,247,384,256⟩⟩]⟩
theorem node1224 : UpperPrefix a [3,6,4,8,7,2,0] 30 :=
  Boolean.leaf_sound a [3,6,4,8,7,2,0] 30 cert1224 (by decide +kernel)

def cert1225 : Leaf := ⟨⟨116,0,104,101,77,0,45,109,101⟩,[(1,5),(5,1)],[],⟨11,70,21,280,176,100,194,417,297⟩,⟨11,70,21,280,176,100,194,384,264⟩,[⟨1,1214839155213594367623169,⟨445,124,413,280,176,124,240,384,264⟩⟩,⟨7,1449767664359857615553587,⟨303,367,285,285,319,367,355,256,268⟩⟩,⟨8,1184347566732655852809,⟨47,118,119,127,246,118,246,247,47⟩⟩,⟨4,1214877039628830347643905,⟨491,230,487,328,226,230,226,384,264⟩⟩]⟩
theorem node1225 : UpperPrefix a [3,6,4,8,7,2,1] 30 :=
  Boolean.leaf_sound a [3,6,4,8,7,2,1] 30 cert1225 (by decide +kernel)

def cert1226 : Leaf := ⟨⟨468,0,458,199,0,0,0,95,215⟩,[(1,5),(4,6),(5,1),(6,4)],[],⟨11,70,21,280,176,100,224,387,267⟩,⟨11,70,21,280,176,100,224,384,264⟩,[⟨5,1452008942568544675054643,⟨399,463,413,413,415,463,451,384,268⟩⟩]⟩
theorem node1226 : UpperPrefix a [3,6,4,8,7,2,5] 30 :=
  Boolean.leaf_sound a [3,6,4,8,7,2,5] 30 cert1226 (by decide +kernel)

theorem node1227 : UpperPrefix a [3,6,4,8,7,2] 30 :=
  branch_upper a [3,6,4,8,7,2] 30 (by decide) (fin9_cases _
  node1224
  node1225
  (invalid_upper a [3,6,4,8,7,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,7,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,7,2,4] 30 (by decide +kernel))
  node1226
  (invalid_upper a [3,6,4,8,7,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,7,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,7,2,8] 30 (by decide +kernel)))

theorem node1228 : UpperPrefix a [3,6,4,8,7] 30 :=
  branch_upper a [3,6,4,8,7] 30 (by decide) (fin9_cases _
  node1217
  node1223
  node1227
  (invalid_upper a [3,6,4,8,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,7,8] 30 (by decide +kernel)))

theorem node1229 : UpperPrefix a [3,6,4,8] 30 :=
  branch_upper a [3,6,4,8] 30 (by decide) (fin9_cases _
  node1201
  node1207
  node1211
  (invalid_upper a [3,6,4,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,8,6] 30 (by decide +kernel))
  node1228
  (invalid_upper a [3,6,4,8,8] 30 (by decide +kernel)))

theorem node1230 : UpperPrefix a [3,6,4] 30 :=
  branch_upper a [3,6,4] 30 (by decide) (fin9_cases _
  node1072
  node1096
  node1112
  (invalid_upper a [3,6,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,4] 30 (by decide +kernel))
  node1146
  (invalid_upper a [3,6,4,6] 30 (by decide +kernel))
  node1194
  node1229)

def cert1231 : Leaf := ⟨⟨400,0,408,386,461,0,281,25,145⟩,[(1,5),(5,1)],[(6,1,4),(1,4,3),(2,5,4)],⟨11,70,37,25,50,100,464,400,408⟩,⟨11,70,37,25,50,100,192,384,264⟩,[⟨5,1323666153021274154091537,⟨459,70,7,473,475,70,192,384,456⟩⟩]⟩
theorem node1231 : UpperPrefix a [3,6,5,0,1,2] 30 :=
  Boolean.leaf_sound a [3,6,5,0,1,2] 30 cert1231 (by decide +kernel)

def cert1232 : Leaf := ⟨⟨20,25,24,6,77,13,285,29,149⟩,[],[(6,1,4),(1,4,3)],⟨11,70,37,25,50,112,452,388,396⟩,⟨11,70,37,25,50,112,192,384,264⟩,[⟨5,1229052478408048988130325,⟨203,455,463,25,219,89,192,384,264⟩⟩,⟨7,1208926975992396940887159,⟨63,127,63,29,63,127,127,256,264⟩⟩,⟨8,1181747998485177484407,⟨63,127,63,29,63,127,255,128,8⟩⟩]⟩
theorem node1232 : UpperPrefix a [3,6,5,0,1,4] 30 :=
  Boolean.leaf_sound a [3,6,5,0,1,4] 30 cert1232 (by decide +kernel)

def cert1233 : Leaf := ⟨⟨48,57,24,34,73,0,317,61,53⟩,[(5,6)],[(6,1,4),(1,4,3),(7,5,5)],⟨11,70,37,25,50,224,468,404,284⟩,⟨11,70,37,25,50,224,192,384,264⟩,[⟨8,1181747928047713567863,⟨31,127,63,29,63,255,255,128,8⟩⟩,⟨2,1210107567535791487845395,⟨27,123,41,25,59,224,224,384,264⟩⟩]⟩
theorem node1233 : UpperPrefix a [3,6,5,0,1,7] 30 :=
  Boolean.leaf_sound a [3,6,5,0,1,7] 30 cert1233 (by decide +kernel)

def cert1234 : Leaf := ⟨⟨432,0,408,418,456,152,312,56,176⟩,[(1,6)],[(6,1,4),(1,4,3),(2,6,1)],⟨11,70,37,25,50,352,196,400,408⟩,⟨11,70,37,25,50,352,196,384,264⟩,[⟨0,1253024023640727981427712,⟨506,246,502,440,242,498,246,384,392⟩⟩]⟩
theorem node1234 : UpperPrefix a [3,6,5,0,1,8,2] 30 :=
  Boolean.leaf_sound a [3,6,5,0,1,8,2] 30 cert1234 (by decide +kernel)

def cert1235 : Leaf := ⟨⟨16,57,24,2,77,157,269,29,149⟩,[],[(6,1,4),(1,4,3)],⟨11,70,37,25,50,352,208,388,396⟩,⟨11,70,37,25,50,352,208,384,264⟩,[⟨5,1219571032098151668384787,⟨395,463,5,89,475,328,217,384,264⟩⟩,⟨7,1208926973665624026301559,⟨11,95,63,29,63,383,95,256,264⟩⟩,⟨8,1181745671712262898807,⟨11,95,63,29,63,127,223,128,8⟩⟩,⟨2,1210107565283862422488083,⟨11,75,33,25,59,360,217,384,264⟩⟩]⟩
theorem node1235 : UpperPrefix a [3,6,5,0,1,8,4] 30 :=
  Boolean.leaf_sound a [3,6,5,0,1,8,4] 30 cert1235 (by decide +kernel)

theorem node1236 : UpperPrefix a [3,6,5,0,1,8] 30 :=
  branch_upper a [3,6,5,0,1,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,5,0,1,8,0] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,1,8,1] 30 (by decide +kernel))
  node1234
  (invalid_upper a [3,6,5,0,1,8,3] 30 (by decide +kernel))
  node1235
  (invalid_upper a [3,6,5,0,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,1,8,8] 30 (by decide +kernel)))

theorem node1237 : UpperPrefix a [3,6,5,0,1] 30 :=
  branch_upper a [3,6,5,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,5,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,1,1] 30 (by decide +kernel))
  node1231
  (invalid_upper a [3,6,5,0,1,3] 30 (by decide +kernel))
  node1232
  (invalid_upper a [3,6,5,0,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,1,6] 30 (by decide +kernel))
  node1233
  node1236)

def cert1238 : Leaf := ⟨⟨20,24,90,6,0,414,286,30,150⟩,[(4,2)],[(5,2,4)],⟨11,70,37,25,52,498,466,402,410⟩,⟨11,70,37,25,52,96,192,384,264⟩,[⟨0,1252729002111147382418432,⟨506,246,502,506,246,96,192,384,488⟩⟩,⟨6,1219569592072435762463747,⟨395,415,61,25,60,32,128,384,264⟩⟩,⟨7,1208926973665615436334135,⟨11,95,63,29,63,127,64,256,264⟩⟩,⟨8,1181745671703672931383,⟨11,95,63,29,63,127,192,128,8⟩⟩]⟩
theorem node1238 : UpperPrefix a [3,6,5,0,2] 30 :=
  Boolean.leaf_sound a [3,6,5,0,2] 30 cert1238 (by decide +kernel)

def cert1239 : Local := ⟨⟨432,0,410,416,265,0,313,57,177⟩,[(1,6),(5,1)],[(6,1,5),(1,5,2),(2,6,1),(2,6,5)]⟩
theorem node1239 : UpperPrefix a [3,6,5,0,7,1,2] 30 :=
  local_sound a [3,6,5,0,7,1,2] 30 cert1239 (by decide +kernel)

def cert1240 : Local := ⟨⟨308,313,282,292,269,0,0,61,53⟩,[(5,1),(6,4)],[(6,1,5),(7,4,6),(1,5,2)]⟩
theorem node1240 : UpperPrefix a [3,6,5,0,7,1,4] 30 :=
  local_sound a [3,6,5,0,7,1,4] 30 cert1240 (by decide +kernel)

def cert1241 : Local := ⟨⟨180,185,154,164,13,0,0,61,181⟩,[(5,1),(6,7)],[(6,1,5),(1,5,2),(8,6,6)]⟩
theorem node1241 : UpperPrefix a [3,6,5,0,7,1,8] 30 :=
  local_sound a [3,6,5,0,7,1,8] 30 cert1241 (by decide +kernel)

theorem node1242 : UpperPrefix a [3,6,5,0,7,1] 30 :=
  branch_upper a [3,6,5,0,7,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,5,0,7,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,7,1,1] 30 (by decide +kernel))
  node1239
  (invalid_upper a [3,6,5,0,7,1,3] 30 (by decide +kernel))
  node1240
  (invalid_upper a [3,6,5,0,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,7,1,7] 30 (by decide +kernel))
  node1241)

def cert1243 : Leaf := ⟨⟨84,0,90,70,78,0,286,94,86⟩,[(1,5),(5,1)],[],⟨11,70,37,25,176,100,466,402,282⟩,⟨11,70,37,25,176,100,192,384,264⟩,[⟨5,1285813290066834078319633,⟨11,70,7,473,475,70,192,384,264⟩⟩,⟨0,1214876138912684444765184,⟨506,246,502,472,178,246,192,384,264⟩⟩,⟨7,1284484837459419494368273,⟨47,102,39,285,319,102,64,256,264⟩⟩,⟨8,1181747995804446803063,⟨47,127,47,29,191,127,255,128,8⟩⟩]⟩
theorem node1243 : UpperPrefix a [3,6,5,0,7,2] 30 :=
  Boolean.leaf_sound a [3,6,5,0,7,2] 30 cert1243 (by decide +kernel)

def cert1244 : Leaf := ⟨⟨52,49,16,36,5,133,53,53,53⟩,[],[(7,4,5)],⟨11,70,37,25,176,112,194,388,268⟩,⟨11,70,37,25,176,112,194,384,264⟩,[⟨8,1184347426027745441279,⟨47,127,47,127,255,127,255,255,47⟩⟩,⟨1,1281081415434497498021889,⟨445,508,445,413,176,112,496,384,392⟩⟩,⟨3,1212475682481016797529089,⟨39,118,37,53,240,112,242,498,502⟩⟩,⟨6,1465612264529777088529475,⟨395,415,445,409,444,445,395,384,264⟩⟩]⟩
theorem node1244 : UpperPrefix a [3,6,5,0,7,4,1] 30 :=
  Boolean.leaf_sound a [3,6,5,0,7,4,1] 30 cert1244 (by decide +kernel)

def cert1245 : Leaf := ⟨⟨112,0,90,98,74,138,58,122,114⟩,[(1,6)],[(7,4,5),(2,6,1)],⟨11,70,37,25,176,112,196,386,266⟩,⟨11,70,37,25,176,112,196,384,264⟩,[⟨8,1184347426027745441279,⟨47,127,47,127,255,127,255,255,47⟩⟩,⟨0,1214876159216815919107072,⟨506,246,502,440,176,114,246,384,280⟩⟩]⟩
theorem node1245 : UpperPrefix a [3,6,5,0,7,4,2] 30 :=
  Boolean.leaf_sound a [3,6,5,0,7,4,2] 30 cert1245 (by decide +kernel)

def cert1246 : Leaf := ⟨⟨112,49,82,98,67,131,0,119,119⟩,[(6,7)],[(7,4,5),(8,6,6)],⟨11,70,37,25,176,112,448,390,270⟩,⟨11,70,37,25,176,112,448,384,264⟩,[⟨3,1212475682481016797529089,⟨39,118,37,53,240,112,498,498,502⟩⟩,⟨2,1210109878528773445387267,⟨43,123,33,57,240,112,496,496,264⟩⟩]⟩
theorem node1246 : UpperPrefix a [3,6,5,0,7,4,8] 30 :=
  Boolean.leaf_sound a [3,6,5,0,7,4,8] 30 cert1246 (by decide +kernel)

theorem node1247 : UpperPrefix a [3,6,5,0,7,4] 30 :=
  branch_upper a [3,6,5,0,7,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,5,0,7,4,0] 30 (by decide +kernel))
  node1244
  node1245
  (invalid_upper a [3,6,5,0,7,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,7,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,7,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,7,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,7,4,7] 30 (by decide +kernel))
  node1246)

def cert1248 : Leaf := ⟨⟨224,168,200,224,328,136,44,104,240⟩,[],[(8,5,4),(2,7,6)],⟨11,70,37,25,176,352,194,388,280⟩,⟨11,70,37,25,176,352,194,388,264⟩,[⟨0,1252648464252205255429120,⟨378,246,502,376,242,368,242,502,296⟩⟩,⟨1,1885544325241812085374977,⟨445,508,445,413,432,368,496,412,392⟩⟩,⟨4,1212771764217915475488009,⟨11,70,231,75,230,487,230,487,495⟩⟩]⟩
theorem node1248 : UpperPrefix a [3,6,5,0,7,8,1,2] 30 :=
  Boolean.leaf_sound a [3,6,5,0,7,8,1,2] 30 cert1248 (by decide +kernel)

def cert1249 : Leaf := ⟨⟨36,41,8,36,269,13,45,45,37⟩,[],[(8,5,4)],⟨11,70,37,25,176,352,194,400,268⟩,⟨11,70,37,25,176,352,194,400,264⟩,[⟨1,1281966859152234579755009,⟨445,508,445,413,176,496,496,400,392⟩⟩,⟨4,1252611462487039062439177,⟨303,70,295,367,230,359,230,487,303⟩⟩,⟨6,1465686051506071926735939,⟨395,415,445,409,444,445,395,400,392⟩⟩,⟨7,2233680502768035201598545,⟨303,359,295,285,319,359,367,285,264⟩⟩]⟩
theorem node1249 : UpperPrefix a [3,6,5,0,7,8,1,4] 30 :=
  Boolean.leaf_sound a [3,6,5,0,7,8,1,4] 30 cert1249 (by decide +kernel)

theorem node1250 : UpperPrefix a [3,6,5,0,7,8,1] 30 :=
  branch_upper a [3,6,5,0,7,8,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,5,0,7,8,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,7,8,1,1] 30 (by decide +kernel))
  node1248
  (invalid_upper a [3,6,5,0,7,8,1,3] 30 (by decide +kernel))
  node1249
  (invalid_upper a [3,6,5,0,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,7,8,1,8] 30 (by decide +kernel)))

def cert1251 : Leaf := ⟨⟨176,0,154,162,266,154,58,56,178⟩,[(1,6)],[(8,5,4),(2,6,1)],⟨11,70,37,25,176,352,196,386,280⟩,⟨11,70,37,25,176,352,196,386,264⟩,[⟨6,1654036531868490718512259,⟨395,415,445,413,445,296,413,395,264⟩⟩,⟨0,1252950241177378619427840,⟨506,246,502,440,176,498,246,498,280⟩⟩]⟩
theorem node1251 : UpperPrefix a [3,6,5,0,7,8,2,1] 30 :=
  Boolean.leaf_sound a [3,6,5,0,7,8,2,1] 30 cert1251 (by decide +kernel)

def cert1252 : Leaf := ⟨⟨224,0,202,226,330,138,42,106,226⟩,[(1,6)],[(8,5,4),(2,6,1)],⟨11,70,37,25,176,352,196,400,266⟩,⟨11,70,37,25,176,352,196,400,264⟩,[⟨0,1217606275019755398138880,⟨506,246,502,440,176,498,246,400,408⟩⟩,⟨4,1252611462487039062439177,⟨303,70,295,367,230,359,230,487,303⟩⟩]⟩
theorem node1252 : UpperPrefix a [3,6,5,0,7,8,2,4] 30 :=
  Boolean.leaf_sound a [3,6,5,0,7,8,2,4] 30 cert1252 (by decide +kernel)

theorem node1253 : UpperPrefix a [3,6,5,0,7,8,2] 30 :=
  branch_upper a [3,6,5,0,7,8,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,5,0,7,8,2,0] 30 (by decide +kernel))
  node1251
  (invalid_upper a [3,6,5,0,7,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,7,8,2,3] 30 (by decide +kernel))
  node1252
  (invalid_upper a [3,6,5,0,7,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,7,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,7,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,7,8,2,8] 30 (by decide +kernel)))

def cert1254 : Leaf := ⟨⟨112,57,90,98,320,16,0,127,119⟩,[(6,4)],[(7,4,6),(8,5,4)],⟨11,70,37,25,176,352,208,390,270⟩,⟨11,70,37,25,176,352,208,384,264⟩,[⟨2,1210110163874031085814787,⟨11,91,33,89,240,368,240,496,264⟩⟩,⟨0,1210110163874030818427904,⟨10,86,36,88,240,368,240,496,264⟩⟩,⟨1,1210110163874030818426881,⟨9,84,37,89,240,368,240,496,264⟩⟩,⟨3,1210110163874029744686081,⟨3,86,37,81,240,368,240,496,256⟩⟩]⟩
theorem node1254 : UpperPrefix a [3,6,5,0,7,8,4] 30 :=
  Boolean.leaf_sound a [3,6,5,0,7,8,4] 30 cert1254 (by decide +kernel)

theorem node1255 : UpperPrefix a [3,6,5,0,7,8] 30 :=
  branch_upper a [3,6,5,0,7,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,5,0,7,8,0] 30 (by decide +kernel))
  node1250
  node1253
  (invalid_upper a [3,6,5,0,7,8,3] 30 (by decide +kernel))
  node1254
  (invalid_upper a [3,6,5,0,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,7,8,8] 30 (by decide +kernel)))

theorem node1256 : UpperPrefix a [3,6,5,0,7] 30 :=
  branch_upper a [3,6,5,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,5,0,7,0] 30 (by decide +kernel))
  node1242
  node1243
  (invalid_upper a [3,6,5,0,7,3] 30 (by decide +kernel))
  node1247
  (invalid_upper a [3,6,5,0,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,7,7] 30 (by decide +kernel))
  node1255)

def cert1257 : Local := ⟨⟨432,0,410,416,137,0,313,57,177⟩,[(1,6),(5,1)],[(6,1,5),(1,5,2),(2,6,1),(2,6,5)]⟩
theorem node1257 : UpperPrefix a [3,6,5,0,8,1,2] 30 :=
  local_sound a [3,6,5,0,8,1,2] 30 cert1257 (by decide +kernel)

def cert1258 : Leaf := ⟨⟨180,177,146,164,133,0,293,53,181⟩,[(5,1)],[(6,1,5),(8,4,6),(1,5,2)],⟨11,70,37,25,304,98,208,388,396⟩,⟨11,70,37,25,304,98,208,384,264⟩,[⟨3,1212475968736670065759233,⟨39,102,37,119,498,98,240,498,502⟩⟩]⟩
theorem node1258 : UpperPrefix a [3,6,5,0,8,1,4] 30 :=
  Boolean.leaf_sound a [3,6,5,0,8,1,4] 30 cert1258 (by decide +kernel)

theorem node1259 : UpperPrefix a [3,6,5,0,8,1] 30 :=
  branch_upper a [3,6,5,0,8,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,5,0,8,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,8,1,1] 30 (by decide +kernel))
  node1257
  (invalid_upper a [3,6,5,0,8,1,3] 30 (by decide +kernel))
  node1258
  (invalid_upper a [3,6,5,0,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,8,1,8] 30 (by decide +kernel)))

def cert1260 : Leaf := ⟨⟨340,0,338,326,198,0,278,86,214⟩,[(1,5),(5,1)],[],⟨11,70,37,25,304,100,210,402,410⟩,⟨11,70,37,25,304,100,192,384,264⟩,[⟨5,1285813290066834078319633,⟨11,70,7,473,475,70,192,384,264⟩⟩,⟨0,1215024613582863133068288,⟨506,246,502,472,498,246,192,384,264⟩⟩,⟨3,1212623681773082609341953,⟨103,102,39,247,498,102,208,498,502⟩⟩,⟨7,1208926973733505170949137,⟨47,102,39,29,319,102,64,256,264⟩⟩]⟩
theorem node1260 : UpperPrefix a [3,6,5,0,8,2] 30 :=
  Boolean.leaf_sound a [3,6,5,0,8,2] 30 cert1260 (by decide +kernel)

def cert1261 : Leaf := ⟨⟨292,289,256,292,133,389,293,37,165⟩,[],[],⟨11,70,37,25,304,112,194,388,396⟩,⟨11,70,37,25,304,112,194,384,264⟩,[⟨1,1281081415434497498021889,⟨445,508,445,413,304,112,496,384,392⟩⟩,⟨3,1212475970918101135266817,⟨39,102,37,119,498,112,242,498,502⟩⟩,⟨4,1248113496581327322905865,⟨459,70,103,463,487,230,194,449,459⟩⟩,⟨6,1465612264529777088529475,⟨395,415,445,409,444,445,395,384,264⟩⟩,⟨7,1208926973663140729865269,⟨11,71,47,29,319,127,66,256,264⟩⟩]⟩
theorem node1261 : UpperPrefix a [3,6,5,0,8,4,1] 30 :=
  Boolean.leaf_sound a [3,6,5,0,8,4,1] 30 cert1261 (by decide +kernel)

def cert1262 : Leaf := ⟨⟨480,0,450,482,194,386,290,98,226⟩,[(1,6)],[(2,6,1)],⟨11,70,37,25,304,112,196,386,394⟩,⟨11,70,37,25,304,112,196,384,264⟩,[⟨0,1214876159212280433642496,⟨506,246,502,440,304,114,246,384,280⟩⟩,⟨3,1212621094912493522163201,⟨103,102,39,247,498,242,246,498,502⟩⟩,⟨4,1255238641551790184660233,⟨459,198,487,463,487,230,198,385,459⟩⟩]⟩
theorem node1262 : UpperPrefix a [3,6,5,0,8,4,2] 30 :=
  Boolean.leaf_sound a [3,6,5,0,8,4,2] 30 cert1262 (by decide +kernel)

theorem node1263 : UpperPrefix a [3,6,5,0,8,4] 30 :=
  branch_upper a [3,6,5,0,8,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,5,0,8,4,0] 30 (by decide +kernel))
  node1261
  node1262
  (invalid_upper a [3,6,5,0,8,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,8,4,8] 30 (by decide +kernel)))

def cert1264 : Leaf := ⟨⟨308,305,272,292,5,0,309,53,53⟩,[(5,6)],[(7,5,5)],⟨11,70,37,25,304,224,194,404,284⟩,⟨11,70,37,25,304,224,194,384,264⟩,[⟨6,1465612264529777088529475,⟨395,415,445,409,444,445,395,384,264⟩⟩,⟨1,1281081415434497498021889,⟨445,508,445,413,304,240,496,384,392⟩⟩,⟨3,1212475970636626158294017,⟨7,102,37,119,498,240,242,498,502⟩⟩]⟩
theorem node1264 : UpperPrefix a [3,6,5,0,8,7,1] 30 :=
  Boolean.leaf_sound a [3,6,5,0,8,7,1] 30 cert1264 (by decide +kernel)

def cert1265 : Leaf := ⟨⟨368,0,346,354,74,0,314,122,114⟩,[(1,6),(5,6)],[(7,5,5),(2,6,1)],⟨11,70,37,25,304,224,196,402,282⟩,⟨11,70,37,25,304,224,196,384,264⟩,[⟨0,1214876159212280433642496,⟨506,246,502,440,304,226,246,384,280⟩⟩]⟩
theorem node1265 : UpperPrefix a [3,6,5,0,8,7,2] 30 :=
  Boolean.leaf_sound a [3,6,5,0,8,7,2] 30 cert1265 (by decide +kernel)

def cert1266 : Leaf := ⟨⟨116,48,82,102,68,0,292,119,119⟩,[(5,6)],[(8,4,6),(7,5,5)],⟨11,70,37,25,304,224,208,390,270⟩,⟨11,70,37,25,304,224,208,384,264⟩,[⟨3,1212476547097378461719553,⟨7,102,103,119,498,240,240,498,502⟩⟩,⟨0,1210110454351808737315840,⟨10,102,102,24,368,240,240,496,264⟩⟩,⟨1,1210110454351808737312769,⟨9,100,101,25,368,240,240,496,264⟩⟩]⟩
theorem node1266 : UpperPrefix a [3,6,5,0,8,7,4] 30 :=
  Boolean.leaf_sound a [3,6,5,0,8,7,4] 30 cert1266 (by decide +kernel)

theorem node1267 : UpperPrefix a [3,6,5,0,8,7] 30 :=
  branch_upper a [3,6,5,0,8,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,5,0,8,7,0] 30 (by decide +kernel))
  node1264
  node1265
  (invalid_upper a [3,6,5,0,8,7,3] 30 (by decide +kernel))
  node1266
  (invalid_upper a [3,6,5,0,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,8,7,8] 30 (by decide +kernel)))

theorem node1268 : UpperPrefix a [3,6,5,0,8] 30 :=
  branch_upper a [3,6,5,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,5,0,8,0] 30 (by decide +kernel))
  node1259
  node1260
  (invalid_upper a [3,6,5,0,8,3] 30 (by decide +kernel))
  node1263
  (invalid_upper a [3,6,5,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,8,6] 30 (by decide +kernel))
  node1267
  (invalid_upper a [3,6,5,0,8,8] 30 (by decide +kernel)))

theorem node1269 : UpperPrefix a [3,6,5,0] 30 :=
  branch_upper a [3,6,5,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,5,0,0] 30 (by decide +kernel))
  node1237
  node1238
  (invalid_upper a [3,6,5,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,0,6] 30 (by decide +kernel))
  node1256
  node1268)

def cert1270 : Leaf := ⟨⟨0,57,0,37,0,413,317,61,181⟩,[(0,3),(2,4),(4,2)],[(1,3,0)],⟨11,70,37,26,49,500,468,404,412⟩,⟨11,70,37,26,49,96,192,384,264⟩,[⟨6,1257422310911687229703179,⟨395,415,53,415,53,32,128,384,393⟩⟩,⟨7,1208926973665615436334143,⟨11,95,63,31,63,127,64,256,265⟩⟩,⟨8,1181745671703672931391,⟨11,95,63,31,63,127,192,128,9⟩⟩]⟩
theorem node1270 : UpperPrefix a [3,6,5,1,0] 30 :=
  Boolean.leaf_sound a [3,6,5,1,0] 30 cert1270 (by decide +kernel)

def cert1271 : Leaf := ⟨⟨0,409,472,389,0,409,281,25,145⟩,[(0,3),(4,2)],[(5,2,4),(1,3,0),(2,4,3)],⟨11,70,37,26,52,497,465,401,409⟩,⟨11,70,37,26,52,96,192,384,264⟩,[⟨6,1257422310911687225508875,⟨395,415,53,411,52,32,128,384,393⟩⟩]⟩
theorem node1271 : UpperPrefix a [3,6,5,1,2] 30 :=
  Boolean.leaf_sound a [3,6,5,1,2] 30 cert1271 (by decide +kernel)

def cert1272 : Leaf := ⟨⟨0,184,0,228,76,156,316,124,244⟩,[(0,3),(2,5)],[(1,3,0),(0,5,2)],⟨11,70,37,26,176,97,468,404,284⟩,⟨11,70,37,26,176,97,192,384,264⟩,[⟨8,1181747995804448900223,⟨47,127,47,63,191,127,255,128,13⟩⟩]⟩
theorem node1272 : UpperPrefix a [3,6,5,1,7,0] 30 :=
  Boolean.leaf_sound a [3,6,5,1,7,0] 30 cert1272 (by decide +kernel)

def cert1273 : Leaf := ⟨⟨0,0,472,453,333,0,285,93,213⟩,[(0,3),(1,5),(5,1)],[(1,3,0)],⟨11,70,37,26,176,100,465,401,281⟩,⟨11,70,37,26,176,100,192,384,264⟩,[⟨5,1323666153021274154091545,⟨459,70,7,475,475,70,192,384,457⟩⟩]⟩
theorem node1273 : UpperPrefix a [3,6,5,1,7,2] 30 :=
  Boolean.leaf_sound a [3,6,5,1,7,2] 30 cert1273 (by decide +kernel)

def cert1274 : Leaf := ⟨⟨0,57,88,96,72,136,317,125,117⟩,[(0,3)],[(1,3,0),(7,4,5)],⟨11,70,37,26,176,112,453,389,269⟩,⟨11,70,37,26,176,112,192,384,264⟩,[⟨8,1181747995804448900223,⟨47,127,47,63,191,127,255,128,13⟩⟩,⟨0,1210107567610418558927872,⟨42,126,36,58,176,112,240,384,264⟩⟩,⟨2,1210107567610418557879307,⟨43,123,33,59,176,112,240,384,265⟩⟩]⟩
theorem node1274 : UpperPrefix a [3,6,5,1,7,4] 30 :=
  Boolean.leaf_sound a [3,6,5,1,7,4] 30 cert1274 (by decide +kernel)

def cert1275 : Leaf := ⟨⟨0,177,208,228,324,148,52,112,244⟩,[(0,3)],[(1,3,0),(8,5,4),(0,6,1)],⟨11,70,37,26,176,352,193,388,280⟩,⟨11,70,37,26,176,352,193,388,264⟩,[⟨3,1210402789765891688090625,⟨3,86,247,18,178,502,247,502,256⟩⟩]⟩
theorem node1275 : UpperPrefix a [3,6,5,1,7,8,0,2] 30 :=
  Boolean.leaf_sound a [3,6,5,1,7,8,0,2] 30 cert1275 (by decide +kernel)

def cert1276 : Leaf := ⟨⟨0,185,216,224,328,152,56,104,244⟩,[(0,3)],[(1,3,0),(8,5,4),(0,6,1)],⟨11,70,37,26,176,352,193,400,268⟩,⟨11,70,37,26,176,352,193,400,264⟩,[⟨2,1212768593718137703105547,⟨11,91,241,27,176,496,241,496,505⟩⟩]⟩
theorem node1276 : UpperPrefix a [3,6,5,1,7,8,0,4] 30 :=
  Boolean.leaf_sound a [3,6,5,1,7,8,0,4] 30 cert1276 (by decide +kernel)

theorem node1277 : UpperPrefix a [3,6,5,1,7,8,0] 30 :=
  branch_upper a [3,6,5,1,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,5,1,7,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,1,7,8,0,1] 30 (by decide +kernel))
  node1275
  (invalid_upper a [3,6,5,1,7,8,0,3] 30 (by decide +kernel))
  node1276
  (invalid_upper a [3,6,5,1,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,1,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,1,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,1,7,8,0,8] 30 (by decide +kernel)))

def cert1278 : Local := ⟨⟨0,0,216,225,329,153,57,121,241⟩,[(0,3),(1,6)],[(1,3,0),(8,5,4),(2,6,1)]⟩
theorem node1278 : UpperPrefix a [3,6,5,1,7,8,2] 30 :=
  local_sound a [3,6,5,1,7,8,2] 30 cert1278 (by decide +kernel)

def cert1279 : Leaf := ⟨⟨0,57,88,100,332,28,0,125,117⟩,[(0,3),(6,4)],[(1,3,0),(7,4,6),(8,5,4)],⟨11,70,37,26,176,352,208,389,269⟩,⟨11,70,37,26,176,352,208,384,264⟩,[⟨0,1210110163874031086863360,⟨10,94,36,90,240,368,240,496,264⟩⟩]⟩
theorem node1279 : UpperPrefix a [3,6,5,1,7,8,4] 30 :=
  Boolean.leaf_sound a [3,6,5,1,7,8,4] 30 cert1279 (by decide +kernel)

#print axioms node1279
end Delivery.FiniteExclusion.Sharp3x6
