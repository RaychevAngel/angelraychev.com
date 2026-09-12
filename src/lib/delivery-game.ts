/** Least reachability fixed point: the budget counts messenger moves. */
export function solveDelivery(n: number, arcs: number[][], target: number) {
  const moves = Array.from({length:n}, (_,i)=>[i]);
  for (const [u,v] of arcs) if (!moves[u].includes(v)) moves[u].push(v);
  const rank = Array.from({length:n}, (_,r)=>Array.from({length:n}, ()=>r===target?0:Infinity));
  for (let k=1; k<=n*n; k++) {
    const updates: number[][]=[];
    for (let r=0;r<n;r++) for (let c=0;c<n;c++) {
      if (r===c || rank[r][c]<Infinity) continue;
      if (moves[r].some(v=>v===target || (v!==c && moves[c].every(d=>rank[v][d]<k)))) updates.push([r,c]);
    }
    if (!updates.length) break;
    for (const [r,c] of updates) rank[r][c]=k;
  }
  const cost=(v:number,c:number)=>v===target?0:v===c?Infinity:Math.max(...moves[c].map(d=>rank[v][d]));
  const messenger=(r:number,c:number)=>moves[r].reduce((best,v)=>cost(v,c)<cost(best,c)?v:best,moves[r][0]);
  const pursuer=(r:number,c:number)=>moves[c].reduce((best,d)=>rank[r][d]>rank[r][best]?d:best,moves[c][0]);
  return {moves,rank,messenger,pursuer};
}
