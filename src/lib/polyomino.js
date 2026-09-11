/** Proved region capabilities for every nonnegative four-arm tuple. */
export function classifyArms(p) {
  if (p.length !== 4 || p.some(x => !Number.isSafeInteger(x) || x < 0)) throw new Error("Use four nonnegative integers.");
  const [a,b,c,d] = p;
  const regions = ["R", "HS", "BS", "Q", "S", "HP", "Plane"];
  const levels = {
    R: [true,true,true,true,true,true,true],
    BS: [false,false,true,true,true,true,true],
    S: [false,false,false,false,true,true,true],
    Plane: [false,false,false,false,false,false,true],
    None: [false,false,false,false,false,false,false],
  };
  const result = (level, family, reason) => ({ level, family, reason, reptile: level === "R", regions: Object.fromEntries(regions.map((r,i) => [r,levels[level][i]])) });
  const positive = p.filter(x => x > 0);
  if (positive.length <= 1 || (b === 0 && d === 0) || (a === 0 && c === 0)) return result("R", "Bar", "A bar is already a rectangle.");
  if (positive.length === 2) {
    const [short,long] = [...positive].sort((x,y) => x-y);
    if (short === 1) return result("R", "L shape", "Two copies tile a rectangle.");
    if (short === 2 || (short === 3 && long === 4)) return result("S", "L shape", "Raychev’s L classification: a strip tiling exists, but no quadrant tiling exists.");
    return result("Plane", "L shape", "Raychev’s L classification excludes a half-plane; a translation lattice tiles the plane.");
  }
  if (positive.length === 4) {
    if ((a === 1 && c === 1) || (b === 1 && d === 1)) return result("Plane", "Cross", "Two opposite unit arms give a periodic plane tiling. Every positive-arm cross fails at a half-plane boundary.");
    return result("None", "Cross", "The maximal-arm argument and the symbolic unit-arm obstructions exclude every plane tiling.");
  }
  const zero = p.indexOf(0);
  const stem = p[(zero+2)%4];
  const [short,long] = [p[(zero+1)%4],p[(zero+3)%4]].sort((x,y) => x-y);
  if (stem === 1) {
    if (short > 1) return result("S", "T shape", "A two-row strip tiling exists. The corner obstruction excludes quadrants.");
    if (long <= 3) return result("R", "T shape", "An exact rectangle witness is available.");
    return result("BS", "T shape", "Two jagged half-strips form a bent strip. Separate corner arguments exclude half-strips and enlarged copies.");
  }
  if (short === 1 || stem === 2 || (short === 2 && stem === long+3)) return result("Plane", "T shape", "An explicit periodic construction tiles the plane. The T boundary theorem excludes a half-plane.");
  if (short >= 3) return result("None", "T shape", "The two concave corners force a pair of opposed crossbars, followed by an impossible gap. This excludes a plane tiling whenever all three arms are at least three.");
  if (stem < long+3) return result("None", "T shape", "The symbolic corner obstruction covers every shorter stem in this family; each whole-tile alternative has been independently checked.");
  return result("None", "T shape", "The deep-wall gap and finite-boundary arguments exclude a plane tiling for every stem longer than the exceptional construction allows.");
}
