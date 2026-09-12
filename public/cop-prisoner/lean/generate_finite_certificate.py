"""Generate an explicit small rank certificate; Lean checks every obligation.

The generator is outside the proof trust boundary: incorrect arrays fail the
closed Lean theorem `certificate_valid`, proved by kernel reduction (`decide`).
"""
import json
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'src'))
from game_solver import neighborhoods,recipient_fast,bits

N=12
item=next(x for x in json.loads((ROOT/'research/solver-two-regular-hillclimb.json').read_text()) if x['n']==N)
arcs=[tuple(x) for x in item['arcs']]
out,_=neighborhoods(N,arcs)
ranks=[];moves=[]
for t in range(N):
 wins,layers=recipient_fast(N,out,t,True)
 for r in range(N):
  for c in range(N):
   if r==t or r==c: ranks.append(0);moves.append(r);continue
   k=next(k for k,layer in enumerate(layers) if layer[r]>>c&1)
   opts=[z for z in bits(out[r]) if z==t or (z!=c and all(layers[k-1][z]>>cp&1 for cp in bits(out[c])))]
   assert opts
   ranks.append(k);moves.append(opts[0])
edgeclauses=' ∨\n  '.join(f'(r.val = {u} ∧ c.val = {v})' for u,v in arcs)
arr=lambda xs:'#[\n  '+',\n  '.join(','.join(map(str,xs[i:i+N])) for i in range(0,len(xs),N))+'\n]'
def nested(name, values):
 lines=[f'def {name} (t r c : Nat) : Nat :=', '  match t with']
 for t in range(N):
  lines += [f'  | {t} => match r with']
  for r in range(N):
   lines += [f'    | {r} => match c with']
   lines += [f'      | {c} => {values[t*N*N+r*N+c]}' for c in range(N)]
   lines += ['      | _ => 0']
  lines += ['    | _ => 0']
 lines += ['  | _ => 0']
 return '\n'.join(lines)
text=f'''import DeliveryGame

/-! Explicit 12-vertex graph and finite rank certificate.
Every rank decrease, chosen legal action, and possible pursuer reply is checked
by the Lean kernel. No external solver correctness assertion is assumed. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.TwelveVertex
abbrev Vertex := Fin {N}
def edge (r c : Vertex) : Prop :=
  {edgeclauses}
instance (r c : Vertex) : Decidable (edge r c) := inferInstanceAs (Decidable (_ ∨ _))
instance (r c : Vertex) : Decidable (Legal edge r c) :=
  inferInstanceAs (Decidable (r = c ∨ edge r c))

{nested("rankRaw",ranks)}
{nested("moveRaw",moves)}
def rank (t r c : Vertex) : Nat := rankRaw t.val r.val c.val
def move (t r c : Vertex) : Vertex :=
  ⟨moveRaw t.val r.val c.val % {N}, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 100000 in
theorem certificate_valid : ∀ t r c : Vertex, r ≠ t → r ≠ c →
    Legal edge r (move t r c) ∧ (move t r c = t ∨
      (move t r c ≠ c ∧ ∀ c', Legal edge c c' →
        move t r c ≠ c' ∧ rank t (move t r c) c' < rank t r c)) := by
  decide +kernel

def certificate (t : Vertex) : RankCertificate edge t where
  rank := rank t
  move := move t
  valid := certificate_valid t

theorem all_pairs_actual_delivery (t r c : Vertex) (hrc : r ≠ c)
    (cop : PursuerPolicy Vertex) (legal : LegalPursuer edge cop) (history : History Vertex) :
    play edge t cop (rank t r c + 1) history r c = .delivered :=
  rankCertificate_actual_delivery (certificate t) r c hrc cop legal history

def allPairs : List (Vertex × Vertex) :=
  (List.finRange {N}).flatMap (fun r => (List.finRange {N}).map (fun t => (r,t)))
def indirectCount : Nat :=
  (allPairs.filter (fun p => decide (p.1 ≠ p.2 ∧ ¬ edge p.1 p.2))).length

theorem arc_count : (allPairs.filter (fun p => decide (edge p.1 p.2))).length = {len(arcs)} := by decide
theorem indirect_count : indirectCount = {N*(N-3)} := by decide

#print axioms all_pairs_actual_delivery
#print axioms indirect_count
end Delivery.TwelveVertex
'''
(ROOT/'lean/TwelveVertexCertificate.lean').write_text(text)
print('Generated',N,'vertices; max rank',max(ranks),'and',len(arcs),'arcs.')
