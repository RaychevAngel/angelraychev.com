// Exact two-count search, justified by the manuscript's all-odd-box nesting theorem.
// This module is also replayed independently outside the browser before publication.
export function oddBoxSearch(shape, budget) {
  if (!shape.length || shape.some(n => !Number.isInteger(n) || n < 1 || n % 2 === 0))
    throw new Error('Use positive odd side lengths, for example 3, 5, 7.');
  const volume = shape.reduce((a,b)=>a*b,1);
  if (volume > 343 || shape.length > 8) throw new Error('The interactive preview supports up to 343 rooms and eight dimensions. The theorem has no such restriction.');
  if (!Number.isInteger(budget) || budget < 1) throw new Error('Use a positive whole number of inspections per day.');
  const m = Math.min(volume,budget), axes = shape.map((_,i)=>i).sort((i,j)=>shape[i]-shape[j] || i-j);
  let vertices=[[]];
  for (const n of shape) vertices=vertices.flatMap(v=>Array.from({length:n},(_,i)=>[...v,i]));
  const key=v=>v.join(','), ix=new Map(vertices.map((v,i)=>[key(v),i]));
  const weight=v=>v.reduce((a,b)=>a+b,0);
  const neighbors=vertices.map(v=>{
    const out=[];
    for(let axis=0;axis<shape.length;axis++)for(const delta of [-1,1]) {
      const w=[...v];w[axis]+=delta;
      if(w[axis]>=0&&w[axis]<shape[axis])out.push(ix.get(key(w)));
    }
    return out;
  });
  const order=(i,j)=>{
    const a=vertices[i],b=vertices[j];let cmp=weight(a)-weight(b);
    for(const axis of axes)if(!cmp)cmp=b[axis]-a[axis];
    return cmp;
  };
  const parts=[0,1].map(p=>vertices.map((_,i)=>i).filter(i=>weight(vertices[i])%2===p).sort(order));
  const profiles=parts.map((part,p)=>{
    const seen=new Set(),g=[0];
    for(const v of part) {
      for(const u of neighbors[v])seen.add(u);
      if(parts[1-p].slice(0,seen.size).some(u=>!seen.has(u)))throw new Error('The neighborhood-prefix consistency check failed.');
      g.push(seen.size);
    }
    return g;
  });
  const [E,O]=parts.map(p=>p.length);
  const threshold=volume===1?1:1+Math.max(...profiles[0].map((v,k)=>v-k));
  const base={shape,volume,budget:m,threshold,vertices,neighbors,parts,profiles};
  if(m<threshold)return {...base,days:null,shots:[],frames:[]};
  const stride=O+1,total=(E+1)*stride,start=E*stride+O;
  const previous=new Int32Array(total).fill(-2),quota=new Uint16Array(total),queue=new Int32Array(total);
  previous[start]=-1;queue[0]=start;let read=0,write=1,goal=-1;
  while(read<write) {
    const state=queue[read++],a=Math.floor(state/stride),b=state%stride;
    if(a+b<=m){goal=state;break;}
    for(let p=Math.max(0,m-b);p<=Math.min(m,a);p++) {
      const next=profiles[1][b-(m-p)]*stride+profiles[0][a-p];
      if(previous[next]!==-2)continue;
      previous[next]=state;quota[next]=p;queue[write++]=next;
    }
  }
  if(goal<0)throw new Error('No strategy was found despite the feasibility criterion.');
  const transitions=[];
  for(let v=goal;previous[v]>=0;v=previous[v])transitions.push([previous[v],quota[v]]);
  transitions.reverse();
  const shots=transitions.map(([v,p])=>{
    const a=Math.floor(v/stride),b=v%stride;
    return parts[0].slice(a-p,a).concat(parts[1].slice(b-(m-p),b));
  });
  shots.push(parts[0].slice(0,Math.floor(goal/stride)).concat(parts[1].slice(0,goal%stride)));
  // Independently replay the resulting room sets through actual graph edges.
  let possible=new Set(vertices.map((_,i)=>i));const frames=[];
  for(const shot of shots) {
    if(shot.length>m)throw new Error('The daily budget was exceeded.');
    const inspected=new Set(shot),survivors=[...possible].filter(v=>!inspected.has(v));
    frames.push({possible:[...possible],shot,survivors});
    possible=new Set(survivors.flatMap(v=>neighbors[v]));
  }
  if(frames.at(-1).survivors.length)throw new Error('The room replay did not reach guaranteed capture.');
  return {...base,days:shots.length,shots,frames,visited:write};
}
