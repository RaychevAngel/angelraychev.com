import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {stageSegments,samplePoints,linePaths,trendValue,trendPoints,stageSVG,pulseSVG,trendSVG} from '../src/lib/sleep-charts.mjs';
const record=JSON.parse(readFileSync(new URL('../src/data/sleep/record.json',import.meta.url)));
const timelines=JSON.parse(readFileSync(new URL('../src/data/sleep/timelines.json',import.meta.url)));
test('stage runs preserve chronological labels and clip the final partial epoch',()=>{
 const t={start:'2026-10-26T00:00:00Z',end:'2026-10-26T00:01:10Z',stage_interval_seconds:30,stages:'4411'};
 const runs=stageSegments(t);assert.deepEqual(runs.map(x=>[x.stage,(x.end-x.start)/1000]),[['4',60],['1',10]]);
});
test('short stage sequence leaves missing tail uncovered',()=>{
 const t={start:'2026-10-26T00:00:00Z',end:'2026-10-26T00:02:00Z',stage_interval_seconds:30,stages:'12'};
 assert.equal(stageSegments(t).at(-1).end,Date.parse(t.start)+60000);
});
test('pulse uses its own timestamps; null and nonpositive samples break paths',()=>{
 const start=Date.parse('2026-10-26T00:00:00Z'),sample={timestamp:'2026-10-26T00:05:00Z',interval:300,items:[50,null,55,0,60]};
 const points=samplePoints(sample,start,start+3600000);
 assert.equal(points[0].t,start+300000);assert.deepEqual(points.map(x=>x.value),[50,null,55,null,60]);
 assert.equal(linePaths(points,x=>x,y=>y).length,3);
});
test('incomplete Oura never becomes a whole-night trend point; COROS remains available',()=>{
 const e=record.entries.find(e=>e.id==='2026-10-22');
 for(const metric of ['score','duration','awake','hrv']){assert.equal(trendValue(e,metric,'oura'),null);assert.ok(Number.isFinite(trendValue(e,metric,'coros')));}
});
test('missing provider is unknown, while a genuine zero is retained',()=>{
 assert.equal(trendValue({coros:{awake_minutes:0}},'awake','coros'),0);
 assert.equal(trendValue({},'score','oura'),null);
});
test('missing calendar nights break trend lines and retain real date spacing',()=>{
 const entries=[{wake_date:'2026-10-01',coros:{sleep_score:90}},{wake_date:'2026-10-04',coros:{sleep_score:80}}];
 const points=trendPoints(entries,'score','coros');assert.equal(points.length,3);assert.equal(points[1].value,null);assert.equal(points[2].t-points[0].t,3*86400000);assert.equal(linePaths(points,x=>x,y=>y).length,2);
});
test('every stored curve matches one canonical episode and valid sample cadence',()=>{
 assert.equal(new Set(timelines.entries.map(e=>e.date)).size,timelines.entries.length);
 for(const t of timelines.entries){const e=record.entries.find(e=>e.id===t.date);assert.ok(e);assert.equal(t.start,e.oura.sleep.bedtime_start);assert.equal(t.end,e.oura.sleep.bedtime_end);assert.equal(t.summary_matches_record,true);assert.match(t.stages,/^[1234]+$/);assert.equal(t.stage_interval_seconds,30);
   const elapsed=Date.parse(t.end)-Date.parse(t.start);assert.ok(Math.abs(t.stages.length*30000-elapsed)<30000);
   assert.equal(t.heart_rate.interval,300);assert.ok(stageSegments(t).every(s=>s.end<=Date.parse(t.end)));
   const sums={};for(const s of t.stages)sums[s]=(sums[s]||0)+30;
   for(const [stage,key] of [['1','deep_sleep_duration'],['2','light_sleep_duration'],['3','rem_sleep_duration'],['4','awake_time']])assert.ok(Math.abs((sums[stage]||0)-e.oura.sleep[key])<30,`${t.date} ${key}`);
 }
});
test('SVGs contain no NaN or undefined coordinates, including incomplete night',()=>{
 for(const t of timelines.entries) for(const svg of [stageSVG(t),pulseSVG(t)]){assert.ok(svg.includes('role="img"'));assert.doesNotMatch(svg,/NaN|undefined|Infinity/);}
 for(const metric of ['score','duration','awake','hrv'])assert.doesNotMatch(trendSVG(record.entries,metric),/NaN|undefined|Infinity/);
});
