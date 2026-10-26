export const WIDTH = 660;
export const LEFT = 90, RIGHT = 642;
export const clock = (stamp,seconds=false) => new Date(stamp).toLocaleTimeString('en-GB', {timeZone:'America/Los_Angeles',hour:'2-digit',minute:'2-digit',...(seconds?{second:'2-digit'}:{}),hour12:false});
export const stageName = {'1':'Deep','2':'Light','3':'REM','4':'Awake'};
const stageY = {'4':34,'3':78,'2':122,'1':166};
const esc = x => String(x).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const X = (t,start,end) => LEFT+(RIGHT-LEFT)*(t-start)/(end-start);
export function stageSegments(timeline) {
  const start=Date.parse(timeline.start), end=Date.parse(timeline.end), step=timeline.stage_interval_seconds*1000;
  const result=[];
  for(let i=0;i<(timeline.stages||'').length;i++) {
    const a=start+i*step,b=Math.min(a+step,end),stage=timeline.stages[i];
    if(a>=end) break;
    const last=result.at(-1);
    if(last?.stage===stage && last.end===a) last.end=b;
    else result.push({start:a,end:b,stage});
  }
  return result;
}
export function samplePoints(sample,start,end) {
  if(!sample) return [];
  return sample.items.map((value,i)=>({t:Date.parse(sample.timestamp)+i*sample.interval*1000,value:Number.isFinite(value)&&value>0?value:null})).filter(p=>p.t>=start && p.t<=end);
}
export function linePaths(points,x,y) {
  const paths=[];let current='';
  for(const p of points) {
    if(!Number.isFinite(p.value)){if(current)paths.push(current);current='';continue;}
    current+=`${current?'L':'M'}${x(p.t).toFixed(2)},${y(p.value).toFixed(2)} `;
  }
  if(current) paths.push(current);
  return paths;
}
const axis=(start,end,y) => {
  const ticks=[start]; const hour=3600000;
  for(let t=Math.ceil(start/hour)*hour;t<end;t+=hour*2) if(t-start>Math.max(hour,(end-start)*.14)&&end-t>Math.max(hour,(end-start)*.14))ticks.push(t);
  ticks.push(end);
  return ticks.map(t=>`<text x="${X(t,start,end)}" y="${y}" text-anchor="${t===start?'start':t===end?'end':'middle'}">${clock(t)}</text>`).join('');
};
const svg=(label,desc,height,inner) => `<svg viewBox="0 0 660 ${height}" role="img" aria-label="${esc(label)}"><title>${esc(label)}</title><desc>${esc(desc)}</desc>${inner}</svg>`;
export function stageSVG(timeline) {
  const start=Date.parse(timeline.start),end=Date.parse(timeline.end),segments=stageSegments(timeline);
  const grid=Object.entries(stageY).map(([s,y])=>`<text x="0" y="${y+4}">${stageName[s]}</text><line class="grid" x1="90" x2="642" y1="${y}" y2="${y}"/>`).join('');
  let path='';
  for(const s of segments) path+=`${path?'L':'M'}${X(s.start,start,end)},${stageY[s.stage]} L${X(s.end,start,end)},${stageY[s.stage]} `;
  const fills=segments.map(s=>`<rect class="phase phase-${s.stage}" x="${X(s.start,start,end)}" y="${stageY[s.stage]-6}" width="${Math.max(.4,X(s.end,start,end)-X(s.start,start,end))}" height="12"/>`).join('');
  return svg(`Oura sleep stages, ${timeline.date}`,'Thirty-second estimated stages in chronological order. Awake at top, deep sleep at bottom. Uncovered time is blank.',210,grid+fills+`<path class="stage-line" d="${path}"/><line class="probe" x1="90" x2="90" y1="20" y2="181" hidden/>`+axis(start,end,202));
}
export function pulseSVG(timeline) {
  const start=Date.parse(timeline.start),end=Date.parse(timeline.end),points=samplePoints(timeline.heart_rate,start,end);
  const vals=points.filter(p=>p.value!=null).map(p=>p.value);
  if(!vals.length)return '<p>No pulse samples available.</p>';
  const min=Math.floor(Math.min(...vals)/10)*10-5,max=Math.ceil(Math.max(...vals)/10)*10+5;
  const y=v=>146-(v-min)/(max-min)*120;
  const ticks=[min,(min+max)/2,max];
  const grid=ticks.map(v=>`<text x="0" y="${y(v)+4}">${Math.round(v)}</text><line class="grid" x1="90" x2="642" y1="${y(v)}" y2="${y(v)}"/>`).join('');
  const paths=linePaths(points,t=>X(t,start,end),y).map(d=>`<path class="pulse-line" d="${d}"/>`).join('');
  const dots=points.filter(p=>p.value!=null).map(p=>`<circle class="pulse-dot" cx="${X(p.t,start,end)}" cy="${y(p.value)}" r="1.8"/>`).join('');
  return svg(`Oura sampled heart rate, ${timeline.date}`,'Pulse in beats per minute at provider timestamps. Missing samples break the line. The vertical scale adapts to this night.',180,grid+paths+dots+`<line class="probe" x1="90" x2="90" y1="20" y2="151" hidden/>`+axis(start,end,174));
}
export const metrics={score:{label:'Sleep score',unit:'/100',range:[0,100]},duration:{label:'Main sleep',unit:'hours',range:[0,12]},awake:{label:'Awake in episode',unit:'minutes',range:[0,100]},hrv:{label:'Overnight HRV',unit:'ms',range:[0,90]}};
export function trendValue(entry,metric,provider) {
  const p=entry[provider];if(!p)return null;
  if(provider==='oura' && p.score_eligible===false)return null;
  if(metric==='score')return provider==='oura'?p.score:p.sleep_score;
  if(metric==='duration')return provider==='oura'?p.sleep.total_sleep_duration/3600:p.main_sleep_minutes/60;
  if(metric==='awake')return provider==='oura'?p.sleep.awake_time/60:p.awake_minutes;
  return provider==='oura'?p.sleep.average_hrv:p.official_sleep_hrv_ms;
}
export function trendPoints(entries,metric,provider) {
  const points=[];
  for(const entry of entries) {
    const t=Date.parse(`${entry.wake_date}T00:00:00Z`),last=points.at(-1);
    if(last && t-last.t>86400000) points.push({t:last.t+86400000,value:null});
    points.push({t,date:entry.wake_date,value:trendValue(entry,metric,provider)});
  }
  return points;
}
export function trendSVG(entries,metric) {
  const m=metrics[metric],values=entries.flatMap(e=>['oura','coros'].map(p=>trendValue(e,metric,p))).filter(v=>v!=null);
  const step=metric==='duration'?2:10;
  const lo=m.range[0],hi=Math.max(m.range[1],Math.ceil(Math.max(...values)/step)*step);
  const dateTime=e=>Date.parse(`${e.wake_date}T00:00:00Z`),first=dateTime(entries[0]),last=dateTime(entries.at(-1));
  const x=t=>LEFT+(RIGHT-LEFT)*(t-first)/Math.max(86400000,last-first),y=v=>173-(v-lo)/(hi-lo)*145;
  const grid=[lo,(hi+lo)/2,hi].map(v=>`<text x="0" y="${y(v)+4}">${v}</text><line class="grid" x1="90" x2="642" y1="${y(v)}" y2="${y(v)}"/>`).join('');
  const paths=['oura','coros'].map(p=>{
    const points=trendPoints(entries,metric,p);
    return linePaths(points,x,y).map(d=>`<path class="trend-${p}" d="${d}"/>`).join('')+points.filter(v=>v.value!=null).map(v=>`<circle tabindex="0" role="button" data-date="${v.date}" data-provider="${p}" data-value="${v.value.toFixed(metric==='duration'?2:1)} ${m.unit}" aria-label="${v.date}, ${p}, ${v.value.toFixed(1)} ${m.unit}. Select this night." class="dot-${p}" cx="${x(v.t)}" cy="${y(v.value)}" r="4"><title>${v.date} · ${p==='oura'?'Oura':'COROS'} · ${v.value.toFixed(metric==='duration'?2:1)} ${m.unit}</title></circle>`).join('');
  }).join('');
  const stride=Math.max(1,Math.ceil(entries.length/7));
  const days=entries.filter((e,i)=>i%stride===0||i===entries.length-1).map(e=>`<text x="${x(dateTime(e))}" y="202" text-anchor="middle">${e.wake_date.slice(8)}</text>`).join('');
  return svg(`${m.label}, both providers`,`${m.unit}. One point per wake date; Oura's incomplete October 22 recording is omitted with a gap. Solid Oura, dashed COROS.`,214,grid+paths+days).replace('role="img"','role="group"');
}
