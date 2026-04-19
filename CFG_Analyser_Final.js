// ═══════════════════════════════════════════════
// SPEED & TIMING
// ═══════════════════════════════════════════════
const SPEED_LABELS=['','Very Slow','Slow','Normal','Fast','Instant'];
let DELAY=900; // ms between steps
function updateSpeed(v){
  document.getElementById('speed-label').textContent=SPEED_LABELS[v];
  const map={1:900,2:500,3:280,4:100,5:0};
  DELAY=map[v];
}
const sleep=ms=>new Promise(r=>setTimeout(r,ms));
const tick=()=>sleep(DELAY);
const fastTick=()=>sleep(Math.max(DELAY*0.5, 120));

// ═══════════════════════════════════════════════
// STATE
// ═══════════════════════════════════════════════
let G=null,cnfG=null,cykRes=null;
let running=false;
let abortFlag=false;
const checkAbort=()=>{ if(abortFlag) throw new Error('__ABORTED__'); };

// ── NEXT BUTTON MACHINERY ──
let nextResolve=null;
function waitForNext(containerId, stepLabel){
  return new Promise(resolve=>{
    if(abortFlag){resolve();return;}
    nextResolve=resolve;
    const wrap=document.createElement('div');
    wrap.className='next-btn-wrap';
    wrap.id='next-btn-wrap-'+containerId;
    wrap.innerHTML=`<button class="next-btn" onclick="triggerNext('${containerId}')">Next → </button>
      <span class="next-hint">${stepLabel||'Click to advance to the next step'}</span>`;
    const container=document.getElementById(containerId);
    if(container) container.appendChild(wrap);
  });
}
function triggerNext(containerId){
  const wrap=document.getElementById('next-btn-wrap-'+containerId);
  if(wrap) wrap.remove();
  if(nextResolve){const r=nextResolve;nextResolve=null;r();}
}

const PRESETS=[
  "S -> AB | BC\nA -> BA | a\nB -> CC | b\nC -> AB | a",
  "S -> aSb | ab",
  "S -> aSa | bSb | a | b | e",
  "S -> SS | aSb | e",
  "E -> E+T | T\nT -> T*F | F\nF -> a"
];
const PSTRS=['ab','aabb','abba','aabb','a+a*a'];

// ═══════════════════════════════════════════════
// GRAMMAR PARSER
// ═══════════════════════════════════════════════
function parseGrammar(text){
  const lines=text.trim().split('\n').filter(l=>l.trim());
  if(!lines.length) throw new Error("Grammar is empty");
  const rules={},order=[];
  for(const line of lines){
    const m=line.match(/^([A-Z][A-Z0-9']*)\s*->\s*(.+)$/);
    if(!m) throw new Error(`Invalid rule: "${line.trim()}"\nFormat should be: S -> AB | a`);
    const lhs=m[1];
    if(!rules[lhs]){rules[lhs]=[];order.push(lhs);}
    for(const alt of m[2].split('|').map(a=>a.trim())){
      if(alt==='e'||alt==='ε'){rules[lhs].push(['ε']);continue;}
      const syms=alt.match(/[A-Z][0-9']*|[a-z+*()\[\]{}0-9]/g)||[];
      rules[lhs].push(syms.length?syms:['ε']);
    }
  }
  const start=order[0];
  const nts=new Set(order);
  const terms=new Set();
  for(const prods of Object.values(rules))
    for(const p of prods) for(const s of p) if(!nts.has(s)&&s!=='ε') terms.add(s);
  return{rules,start,nts:[...nts],terms:[...terms],order};
}

// ═══════════════════════════════════════════════
// CNF HELPERS
// ═══════════════════════════════════════════════
function deepCopy(r){const o={};for(const[k,v]of Object.entries(r))o[k]=v.map(p=>[...p]);return o;}
function arrEq(a,b){return a.length===b.length&&a.every((x,i)=>x===b[i]);}
function computeNullable(rules){
  const N=new Set();let ch=true;
  while(ch){ch=false;
    for(const[lhs,prods]of Object.entries(rules))
      if(!N.has(lhs)&&prods.some(p=>p.every(s=>s==='ε'||N.has(s)))){N.add(lhs);ch=true;}
  }return N;
}
function epsVariants(prod,nullable){
  let v=[[]];
  for(const s of prod){
    if(s==='ε') continue;
    const nv=[];
    for(const x of v){nv.push([...x,s]);if(nullable.has(s))nv.push([...x]);}
    v=nv;
  }
  return v.filter(x=>x.length>0);
}
function computeGen(rules,nts){
  const g=new Set();let ch=true;
  while(ch){ch=false;
    for(const[lhs,prods]of Object.entries(rules))
      if(!g.has(lhs)&&prods.some(p=>p.every(s=>s==='ε'||!nts.has(s)||g.has(s)))){g.add(lhs);ch=true;}
  }return g;
}
function computeReach(rules,start,nts){
  const r=new Set([start]);const q=[start];
  while(q.length){const s=q.shift();for(const p of(rules[s]||[]))for(const x of p)if(nts.has(x)&&!r.has(x)){r.add(x);q.push(x);}}
  return r;
}

// ═══════════════════════════════════════════════
// CYK
// ═══════════════════════════════════════════════
function runCYK(cnf,str){
  const n=str.length;
  if(n===0){const acc=(cnf.rules[cnf.start]||[]).some(p=>p.length===1&&p[0]==='ε');return{accepts:acc,table:[],n:0,str:[]};}
  const table=Array.from({length:n},()=>Array.from({length:n},()=>new Set()));
  const steps=[];
  for(let i=0;i<n;i++){
    const c=str[i];
    for(const[lhs,prods]of Object.entries(cnf.rules))
      for(const p of prods)
        if(p.length===1&&p[0]===c){table[i][i].add(lhs);steps.push({i,j:i,added:lhs,reason:`'${c}' matches rule ${lhs} → ${c}`,type:'base'});}
  }
  for(let len=2;len<=n;len++)
    for(let i=0;i<=n-len;i++){
      const j=i+len-1;
      for(let k=i;k<j;k++)
        for(const[lhs,prods]of Object.entries(cnf.rules))
          for(const p of prods)
            if(p.length===2&&table[i][k].has(p[0])&&table[k+1][j].has(p[1])){
              if(!table[i][j].has(lhs)){
                table[i][j].add(lhs);
                steps.push({i,j,added:lhs,k,B:p[0],C:p[1],reason:`table[${i}][${k}] has ${p[0]}, table[${k+1}][${j}] has ${p[1]} → rule ${lhs}→${p[0]}${p[1]} fires → add ${lhs} to table[${i}][${j}]`,type:'combine'});
              }
            }
    }
  return{accepts:table[0][n-1].has(cnf.start),table,n,str:str.split(''),steps};
}

// ═══════════════════════════════════════════════
// PARSE TREE
// ═══════════════════════════════════════════════
function buildTree(cnf,table,str,sym,i,j,memo={}){
  const key=`${sym},${i},${j}`;if(key in memo)return memo[key];memo[key]=null;
  if(i>j){
    for(const p of(cnf.rules[sym]||[]))
      if(p.length===1&&p[0]==='ε')
        return memo[key]={sym,children:[{sym:'ε',children:[],leaf:true}],i,j};
    return null;
  }
  if(i===j){for(const p of(cnf.rules[sym]||[]))if(p.length===1&&p[0]===str[i])return memo[key]={sym,children:[{sym:str[i],children:[],leaf:true}],i,j};return null;}
  for(const p of(cnf.rules[sym]||[])){
    if(p.length!==2)continue;const[B,C]=p;
    for(let k=i;k<j;k++){
      if(table[i][k].has(B)&&table[k+1][j].has(C)){
        const L=buildTree(cnf,table,str,B,i,k,memo);const R=buildTree(cnf,table,str,C,k+1,j,memo);
        if(L&&R)return memo[key]={sym,children:[L,R],i,j};
      }
    }
  }return null;
}
function treesEq(a,b){if(!a&&!b)return true;if(!a||!b)return false;if(a.sym!==b.sym||a.children.length!==b.children.length)return false;return a.children.every((c,i)=>treesEq(c,b.children[i]));}
function buildTreeVariants(cnf,table,str,sym,i,j,limit=2,memo=new Map()){
  const key=`${sym},${i},${j}`;
  if(memo.has(key)) return memo.get(key);
  const results=[];
  const addTree=tree=>{
    if(!tree||results.some(t=>treesEq(t,tree))) return;
    results.push(tree);
  };

  if(i>j){
    for(const p of(cnf.rules[sym]||[])){
      if(p.length===1&&p[0]==='ε'){
        addTree({sym,children:[{sym:'ε',children:[],leaf:true}],i,j});
        break;
      }
    }
    memo.set(key,results);
    return results;
  }

  if(i===j){
    for(const p of(cnf.rules[sym]||[])){
      if(p.length===1&&p[0]===str[i]) addTree({sym,children:[{sym:str[i],children:[],leaf:true}],i,j});
      if(results.length>=limit) break;
    }
    memo.set(key,results);
    return results;
  }

  for(const p of(cnf.rules[sym]||[])){
    if(p.length!==2) continue;
    const[B,C]=p;
    for(let k=i;k<j&&results.length<limit;k++){
      if(!table[i][k].has(B)||!table[k+1][j].has(C)) continue;
      const leftTrees=buildTreeVariants(cnf,table,str,B,i,k,limit,memo);
      const rightTrees=buildTreeVariants(cnf,table,str,C,k+1,j,limit,memo);
      for(const L of leftTrees){
        for(const R of rightTrees){
          addTree({sym,children:[L,R],i,j});
          if(results.length>=limit) break;
        }
        if(results.length>=limit) break;
      }
    }
  }

  memo.set(key,results);
  return results;
}

// ═══════════════════════════════════════════════
// FIRST & FOLLOW
// ═══════════════════════════════════════════════
function computeFirst(g){
  const first={};for(const nt of g.nts)first[nt]=new Set();let ch=true;
  while(ch){ch=false;
    for(const lhs of g.nts)for(const prod of(g.rules[lhs]||[])){
      if(prod[0]==='ε'){if(!first[lhs].has('ε')){first[lhs].add('ε');ch=true;}continue;}
      let allN=true;
      for(const sym of prod){
        if(!g.nts.includes(sym)){if(!first[lhs].has(sym)){first[lhs].add(sym);ch=true;}allN=false;break;}
        const prev=first[lhs].size;for(const t of first[sym])if(t!=='ε')first[lhs].add(t);
        if(first[lhs].size>prev)ch=true;
        if(!first[sym].has('ε')){allN=false;break;}
      }
      if(allN&&!first[lhs].has('ε')){first[lhs].add('ε');ch=true;}
    }
  }return first;
}
function firstSeq(seq,g,first){
  const r=new Set();if(!seq.length){r.add('ε');return r;}let allN=true;
  for(const sym of seq){
    if(!g.nts.includes(sym)){r.add(sym);allN=false;break;}
    for(const t of first[sym])if(t!=='ε')r.add(t);
    if(!first[sym].has('ε')){allN=false;break;}
  }
  if(allN)r.add('ε');return r;
}
function computeFollow(g,first){
  const follow={};for(const nt of g.nts)follow[nt]=new Set();follow[g.start].add('$');let ch=true;
  while(ch){ch=false;
    for(const lhs of g.nts)for(const prod of(g.rules[lhs]||[]))
      for(let i=0;i<prod.length;i++){
        const B=prod[i];if(!g.nts.includes(B))continue;
        const fb=firstSeq(prod.slice(i+1),g,first);const prev=follow[B].size;
        for(const t of fb)if(t!=='ε')follow[B].add(t);
        if(fb.has('ε')||i===prod.length-1)for(const t of follow[lhs])follow[B].add(t);
        if(follow[B].size>prev)ch=true;
      }
  }return follow;
}

// ═══════════════════════════════════════════════
// SVG TREE RENDERER
// ═══════════════════════════════════════════════
function makeSVGTree(tree,cnf){
  if(!tree) return null;
  const labels=[];
  (function collectLabels(node){
    labels.push(String(node.sym||''));
    for(const child of(node.children||[])) collectLabels(child);
  })(tree);
  const maxLabelLen=Math.max(1,...labels.map(s=>s.length));
  const NW=Math.max(56,maxLabelLen*11+18);
  const NH=38;
  const HG=Math.max(18,Math.round(NW*0.42));
  const VG=66;
  const pos={};let li=0;
  const treeId='tree-'+Date.now().toString(36)+'-'+Math.random().toString(36).slice(2,8);
  const nk=path=>path;
  function layL(node,path){
    const children=node.children||[];
    if(!children.length){pos[nk(path)]={x:li*(NW+HG),y:0};li++;return;}
    children.forEach((c,idx)=>layL(c,`${path}.${idx}`));
  }
  function layI(node,path,d){
    const children=node.children||[];
    if(!children.length){pos[nk(path)].y=d*VG;return;}
    children.forEach((c,idx)=>layI(c,`${path}.${idx}`,d+1));
    const xs=children.map((_,idx)=>pos[nk(`${path}.${idx}`)].x);
    pos[nk(path)]={x:(Math.min(...xs)+Math.max(...xs))/2,y:d*VG};
  }
  layL(tree,'0');layI(tree,'0',0);
  const allP=Object.values(pos);
  const W=Math.max(Math.max(...allP.map(p=>p.x))+NW+20,300);
  const H=Math.max(...allP.map(p=>p.y))+NH+30;
  const list=[];
  function collect(node,path='0',pk=null){
    const k=nk(path);
    list.push({k,node,p:pos[k],pk,nodeId:`${treeId}-node-${k}`,edgeId:`${treeId}-edge-${k}`});
    (node.children||[]).forEach((c,idx)=>collect(c,`${path}.${idx}`,k));
  }
  collect(tree,'0');
  return{list,W,H,NW,NH,cnfStart:cnf.start,nk,treeId};
}

function renderSVGTree(treeData,container,title){
  if(!treeData){container.innerHTML=`<div style="padding:20px;color:var(--text3);font-size:12px">No parse tree available</div>`;return;}
  const{list,W,H,NW,NH,cnfStart}=treeData;
  let edgesHTML='',nodesHTML='';
  list.forEach(({k,node,p,pk,edgeId,nodeId},idx)=>{
    if(!p)return;
    if(pk){const par=list.find(n=>n.k===pk);if(par&&par.p){edgesHTML+=`<line id="${edgeId}" class="ptree-edge" x1="${par.p.x+NW/2}" y1="${par.p.y+NH}" x2="${p.x+NW/2}" y2="${p.y}"/>\n`;}}
    const isNT=!node.leaf,isS=node.sym===cnfStart;
    const cx=p.x+NW/2,cy=p.y+NH/2,r=isS?18:14;
    const fill=isS?'#162a49':isNT?'#2b2250':'#123329';
    const stroke=isS?'#5ea2ff':isNT?'#b794f4':'#34d399';
    const tc=isS?'#d7e7ff':isNT?'#eadcff':'#c9ffe7';
    nodesHTML+=`<g id="${nodeId}" class="ptree-node">
      <circle cx="${cx}" cy="${cy}" r="${r}" fill="${fill}" stroke="${stroke}" stroke-width="1.5"/>
      <text x="${cx}" y="${cy}" text-anchor="middle" dominant-baseline="central" fill="${tc}" font-size="11" font-family="var(--mono)" font-weight="${isNT?'600':'400'}">${node.sym}</text>
    </g>\n`;
  });
  container.innerHTML=`${title?`<div style="font-family:var(--font);font-size:10px;font-weight:700;color:var(--text3);letter-spacing:.1em;text-transform:uppercase;margin-bottom:10px">${title}</div>`:''}
    <div style="overflow:auto">
    <svg class="ptree" width="${W}" height="${H}" style="min-width:${W}px">
      ${edgesHTML}${nodesHTML}
    </svg></div>`;
  return list.length;
}

async function animateTree(list, containerId){
  for(let idx=0;idx<list.length;idx++){
    if(abortFlag) throw new Error('__ABORTED__');
    const edge=document.getElementById(list[idx].edgeId);
    const node=document.getElementById(list[idx].nodeId);
    if(edge) edge.classList.add('show');
    if(node) node.classList.add('show');
    // show next button with info about what node just appeared
    const item=list[idx];
    if(item&&containerId){
      const isLeaf=item.node.leaf;
      const label=isLeaf
        ? `Terminal node <strong>${item.node.sym}</strong> — leaf of the derivation tree`
        : `Non-terminal <strong>${item.node.sym}</strong> — spans positions [${item.node.i}, ${item.node.j}]`;
      await waitForNext(containerId, label);
    } else {
      await fastTick();
    }
  }
}

// ═══════════════════════════════════════════════
// DERIVATION STEPS
// ═══════════════════════════════════════════════
function getDerivation(tree){
  const steps=[tree.sym];
  function step(node,sent){
    if(!node||node.leaf)return sent;
    const idx=sent.indexOf(node.sym);if(idx<0)return sent;
    const replacement=node.children.map(c=>c.sym);
    const next=[...sent.slice(0,idx),...replacement,...sent.slice(idx+1)];
    const nextStr=next.join(' ');
    if(steps[steps.length-1]!==nextStr)steps.push(nextStr);
    let cur=next;
    for(const c of node.children)cur=step(c,cur);
    return cur;
  }
  step(tree,[tree.sym]);
  const uniq=[];for(const s of steps)if(!uniq.length||uniq[uniq.length-1]!==s)uniq.push(s);
  return uniq;
}

// ═══════════════════════════════════════════════
// UI HELPERS
// ═══════════════════════════════════════════════
function showSection(id){const s=document.getElementById('sec-'+id);s.classList.add('visible');}
function setNum(id,state){
  const el=document.getElementById('num-'+id);
  el.className='section-num';
  if(state==='active')el.style.background='var(--accent)',el.style.color='#09142a',el.style.border='none';
  else if(state==='done'){el.style.background='var(--green)';el.style.color='#09142a';el.style.border='none';el.innerHTML='✓';}
  else{el.style.background='var(--bg3)';el.style.color='var(--text3)';el.style.border='1.5px solid var(--border)';}
}
function setStatus(text,type){const p=document.getElementById('status-pill');p.textContent=text;p.className='status-pill '+(type||'');}

function addLogLine(containerId,text,type,delay=0){
  return new Promise(res=>{
    setTimeout(()=>{
      const container=document.getElementById(containerId);
      if(!container){res();return;}
      const d=document.createElement('div');
      d.className=`log-line ${type||'info'}`;d.innerHTML=text;
      container.appendChild(d);
      requestAnimationFrame(()=>requestAnimationFrame(()=>d.classList.add('show')));
      res();
    },delay);
  });
}

function makeLogContainer(parentId){
  const el=document.getElementById(parentId);
  const log=document.createElement('div');log.className='log';
  const id='log-'+parentId+'-'+Date.now();log.id=id;
  el.appendChild(log);return id;
}

function makeComputing(parentId,text){
  const el=document.getElementById(parentId);
  const d=document.createElement('div');d.className='computing';d.id='computing-'+parentId;
  d.innerHTML=`<span style="color:var(--accent)">◆</span> ${text} <span class="dots"><span>.</span><span>.</span><span>.</span></span>`;
  el.appendChild(d);
}
function removeComputing(parentId){const d=document.getElementById('computing-'+parentId);if(d)d.remove();}

function makeStageCard(parentId,title,desc){
  const el=document.getElementById(parentId);
  const card=document.createElement('div');card.className='stage-card';
  const id='card-'+Date.now()+Math.random().toString(36).slice(2);card.id=id;
  card.innerHTML=`<div class="stage-title"><span class="stage-badge sb-pending" id="badge-${id}">PENDING</span>${title}</div><div class="stage-desc">${desc}</div><div id="changes-${id}" class="log"></div>`;
  el.appendChild(card);
  requestAnimationFrame(()=>requestAnimationFrame(()=>card.classList.add('show')));
  return{cardId:id,changesId:'changes-'+id,setBadge:(s)=>{const b=document.getElementById('badge-'+id);if(b){b.className='stage-badge '+(s==='running'?'sb-running':s==='done'?'sb-done':'sb-pending');b.textContent=s.toUpperCase();}},setActive:()=>card.classList.add('active'),setComplete:()=>{card.classList.remove('active');card.classList.add('complete');}};
}

function showError(msg){const e=document.getElementById('input-error');e.style.display='block';e.textContent='⚠ '+msg;}
function clearError(){document.getElementById('input-error').style.display='none';}

// ═══════════════════════════════════════════════
// MAIN ANALYSIS FLOW
// ═══════════════════════════════════════════════
async function runAnalysis(){
  if(running)return;
  clearError();
  const grammarText=document.getElementById('grammar-input').value.trim();
  const strInput=document.getElementById('string-input').value.trim();
  const str=(strInput===''||strInput==='e'||strInput==='ε')?'':strInput;

  // parse
  try{G=parseGrammar(grammarText);}catch(e){showError(e.message);return;}

  running=true;
  abortFlag=false;
  document.getElementById('run-btn').disabled=true;
  setStatus('Running...','running');

  // reset all sections
  ['grammar','cnf','cyk','tree','amb'].forEach(id=>{
    document.getElementById('sec-'+id).classList.remove('visible');
    setNum(id,'pending');
    document.getElementById(id==='grammar'?'grammar-body':id+'-body').innerHTML='';
  });

  try {

  // ─── SECTION 0: Grammar ───
  showSection('grammar');setNum('grammar','active');
  const gb=document.getElementById('grammar-body');
  makeComputing('grammar-body','Parsing grammar');
  await tick();
  removeComputing('grammar-body');
  gb.innerHTML=`<div class="grammar-strip">
    <div class="gs-item"><span class="gs-label">Start:</span><span class="gs-val a">${G.start}</span></div>
    <div class="gs-item"><span class="gs-label">Non-terminals:</span><span class="gs-val a">{${G.nts.join(', ')}}</span></div>
    <div class="gs-item"><span class="gs-label">Terminals:</span><span class="gs-val g">{${G.terms.join(', ')}}</span></div>
    <div class="gs-item"><span class="gs-label">Productions:</span><span class="gs-val">${Object.values(G.rules).reduce((a,b)=>a+b.length,0)}</span></div>
    <div class="gs-item"><span class="gs-label">Test string:</span><span class="gs-val">"${str||'ε'}"</span></div>
  </div>`;
  const logId=makeLogContainer('grammar-body');
  await addLogLine(logId,`✓ Found ${G.nts.length} non-terminals: {${G.nts.join(', ')}}`, 'result');await tick();
  await addLogLine(logId,`✓ Found ${G.terms.length} terminals: {${G.terms.join(', ')}}`, 'result');await tick();
  await addLogLine(logId,`✓ Grammar has ${Object.values(G.rules).reduce((a,b)=>a+b.length,0)} productions`, 'result');await tick();
  setNum('grammar','done');

  // ─── SECTION 1: CNF ───
  showSection('cnf');setNum('cnf','active');
  await tick();

  // We run CNF step by step, animating each stage
  try{ cnfG = await animateCNF(G); }
  catch(e){ if(e.message==='__ABORTED__') throw e; showError('CNF error: '+e.message); running=false; document.getElementById('run-btn').disabled=false; setStatus('Error'); return; }
  setNum('cnf','done');

  // ─── SECTION 2: CYK ───
  showSection('cyk');setNum('cyk','active');
  await tick();
  try{ cykRes = await animateCYK(cnfG,str); }
  catch(e){ if(e.message==='__ABORTED__') throw e; showError('CYK error: '+e.message); running=false; document.getElementById('run-btn').disabled=false; setStatus('Error'); return; }
  setNum('cyk','done');

  // ─── SECTION 3: Parse Tree ───
  showSection('tree');setNum('tree','active');
  await tick();
  await animateParseTree(cykRes,str);
  setNum('tree','done');

  // ─── SECTION 4: Ambiguity ───
  showSection('amb');setNum('amb','active');
  await tick();
  await animateAmbiguity(cykRes,str);
  setNum('amb','done');

  running=false;
  document.getElementById('run-btn').disabled=false;
  setStatus('Complete','done');
  } catch(e) {
    if(e.message!=='__ABORTED__') { showError(e.message); setStatus('Error'); }
    running=false;
    document.getElementById('run-btn').disabled=false;
  }
}

// ═══════════════════════════════════════════════
// ANIMATE CNF
// ═══════════════════════════════════════════════
async function animateCNF(g){
  const body='cnf-body';
  let rules=deepCopy(g.rules);
  const nts=new Set(g.nts);
  let order=[...g.order];
  const freshCounter={};
  const freshNT=(base)=>{
    let cand=base;
    if(!nts.has(cand)&&!rules[cand]) return cand;
    const key=base;
    freshCounter[key]=(freshCounter[key]||0)+1;
    cand=`${base}_${freshCounter[key]}`;
    while(nts.has(cand)||rules[cand]){
      freshCounter[key]++;
      cand=`${base}_${freshCounter[key]}`;
    }
    return cand;
  };
  let startSym='S0';

  // Stage 0: new start
  {
    startSym=freshNT('S0');
    const s=makeStageCard(body,'Step 1 — New start symbol',`Add ${startSym} → ${g.start} so the start symbol never appears on the right-hand side of any rule`);
    s.setActive();s.setBadge('running');await tick();
    rules[startSym]=[[g.start]];nts.add(startSym);order=[startSym,...order];
    await addLogLine(s.changesId,`<span style="color:var(--accent)">NEW RULE</span> &nbsp; ${startSym} → ${g.start}`,'added');await tick();
    await addLogLine(s.changesId,`${startSym} is now the new start symbol`,'info');await tick();
    s.setBadge('done');s.setComplete();
  }

  // Stage 1: remove epsilon
  {
    const nullable=computeNullable(rules);
    const s=makeStageCard(body,'Step 2 — Remove ε-productions',
      nullable.size?`Nullable variables found: {${[...nullable].join(', ')}}. For each rule containing nullable vars, add versions with those vars omitted.`:'No nullable variables found — nothing to remove.');
    s.setActive();s.setBadge('running');await tick();
    const newRules={};
    for(const lhs of Object.keys(rules)){
      newRules[lhs]=[];
      for(const prod of rules[lhs]){
        if(prod.length===1&&prod[0]==='ε'){
          await addLogLine(s.changesId,`<span style="color:var(--red)">REMOVE</span> &nbsp; ${lhs} → ε`,'removed');await tick();
          continue;
        }
        for(const v of epsVariants(prod,nullable))
          if(!newRules[lhs].some(p=>arrEq(p,v)))newRules[lhs].push(v);
      }
      // In CNF, only the start symbol may retain ε if language contains empty string.
      if(lhs===startSym&&nullable.has(startSym)&&!newRules[lhs].some(p=>p.length===1&&p[0]==='ε'))
        newRules[lhs].push(['ε']);
      if(!newRules[lhs].length) delete newRules[lhs];
    }
    // show added rules
    for(const lhs of Object.keys(newRules))
      for(const prod of newRules[lhs])
        if(!rules[lhs]||!rules[lhs].some(p=>arrEq(p,prod))){
          await addLogLine(s.changesId,`<span style="color:var(--green)">ADD</span> &nbsp; ${lhs} → ${prod.join(' ')}`,'added');await tick();
        }
    if(nullable.has(startSym))
      await addLogLine(s.changesId,`Retained ${startSym} → ε because start symbol is nullable`,'info');
    if(!nullable.size) await addLogLine(s.changesId,'No ε-productions found — grammar unchanged','info');
    order=order.filter(lhs=>newRules[lhs]);
    rules=newRules;s.setBadge('done');s.setComplete();
  }

  // Stage 2: unit productions
  {
    const s=makeStageCard(body,'Step 3 — Remove unit productions','A unit production is A → B where B is a single non-terminal. Replace each by copying B\'s rules directly into A.');
    s.setActive();s.setBadge('running');await tick();
    let anyChange=false;
    const keys=Object.keys(rules);
    const isUnit=p=>p.length===1&&nts.has(p[0]);
    const closure={};
    for(const lhs of keys){
      const seen=new Set([lhs]);
      const q=[lhs];
      while(q.length){
        const cur=q.shift();
        for(const p of(rules[cur]||[])){
          if(!isUnit(p)) continue;
          const tgt=p[0];
          if(!seen.has(tgt)){seen.add(tgt);q.push(tgt);}
        }
      }
      closure[lhs]=seen;
    }

    const newRules={};
    for(const lhs of keys){
      newRules[lhs]=[];
      const originalNonUnit=(rules[lhs]||[]).filter(p=>!isUnit(p));

      for(const p of(rules[lhs]||[])){
        if(isUnit(p)){
          anyChange=true;
          await addLogLine(s.changesId,`<span style="color:var(--red)">REMOVE</span> &nbsp; ${lhs} → ${p[0]} &nbsp; (unit production)`,'removed');
          await tick();
        }
      }

      for(const src of closure[lhs]){
        for(const p of(rules[src]||[])){
          if(isUnit(p)) continue;
          if(newRules[lhs].some(r=>arrEq(r,p))) continue;
          newRules[lhs].push(p);
          const existedOriginally=originalNonUnit.some(r=>arrEq(r,p));
          if(!existedOriginally){
            await addLogLine(s.changesId,`<span style="color:var(--green)">ADD</span> &nbsp; ${lhs} → ${p.join(' ')} &nbsp; (via unit-closure from ${src})`,'added');
            await tick();
          }
        }
      }
    }
    rules=newRules;
    if(!anyChange)await addLogLine(s.changesId,'No unit productions found — grammar unchanged','info');
    s.setBadge('done');s.setComplete();
  }

  // Stage 3: useless symbols
  {
    const gen=computeGen(rules,nts);
    const reach=computeReach(rules,startSym,nts);
    const useful=new Set([...gen].filter(x=>reach.has(x)));
    const s=makeStageCard(body,'Step 4 — Remove useless symbols',
      `Generating: {${[...gen].join(', ')}} &nbsp;|&nbsp; Reachable from ${startSym}: {${[...reach].join(', ')}}`);
    s.setActive();s.setBadge('running');await tick();
    let anyUseless=false;
    for(const lhs of Object.keys(rules)){
      if(!useful.has(lhs)){
        await addLogLine(s.changesId,`<span style="color:var(--red)">REMOVE</span> &nbsp; ${lhs} — not generating or not reachable`,'removed');await tick();
        delete rules[lhs];anyUseless=true;
      }else{
        rules[lhs]=rules[lhs].filter(p=>p.every(s=>s==='ε'||!nts.has(s)||useful.has(s)));
      }
    }
    order=order.filter(k=>rules[k]);
    if(!anyUseless)await addLogLine(s.changesId,'No useless symbols found — grammar unchanged','info');
    else await addLogLine(s.changesId,`✓ Remaining variables: {${order.join(', ')}}`,'result');
    s.setBadge('done');s.setComplete();
  }

  // Stage 4: terminal isolation
  {
    const s=makeStageCard(body,'Step 5 — Isolate terminals in long rules','In rules with 2+ symbols, replace each terminal t with a new variable Tt where Tt → t');
    s.setActive();s.setBadge('running');await tick();
    const termMap={};let anyIsolated=false;
    const termRules=deepCopy(rules);const termOrder=[...order];
    for(const lhs of order){
      termRules[lhs]=[];
      for(const prod of rules[lhs]){
        if(prod.length>=2){
          const newNTs=[];
          const np=prod.map(sym=>{
            if(nts.has(sym)||sym==='ε')return sym;
            if(!termMap[sym]){
              const tn=freshNT('T');
              termMap[sym]=tn;termRules[tn]=[[sym]];termOrder.push(tn);nts.add(tn);
              newNTs.push({tn,sym});anyIsolated=true;
            }
            return termMap[sym];
          });
          for(const{tn,sym}of newNTs)
            await addLogLine(s.changesId,`<span style="color:var(--green)">ADD</span> &nbsp; ${tn} → ${sym} &nbsp; (terminal wrapper for '${sym}')`, 'added');
          termRules[lhs].push(np);
          if(prod.some(x=>!nts.has(x)&&x!=='ε'))
            await addLogLine(s.changesId,`<span style="color:var(--amber)">MODIFY</span> &nbsp; ${lhs} → ${np.join(' ')} &nbsp; (terminals replaced)`,'changed');
        }else termRules[lhs].push(prod);
      }
    }
    if(!anyIsolated)await addLogLine(s.changesId,'No terminals in long rules — nothing to do','info');
    Object.assign(rules,termRules);order=[...termOrder];
    await tick();s.setBadge('done');s.setComplete();
  }

  // Stage 5: binarize
  {
    const s=makeStageCard(body,'Step 6 — Binarize long rules','Break A → B₁B₂...Bₙ (n>2) into binary rules using new helper variables');
    s.setActive();s.setBadge('running');await tick();
    const binRules={};const binOrder=[];
    for(const lhs of order){binRules[lhs]=[];binOrder.push(lhs);}
    let binCtr=1;let anyBin=false;
    for(const lhs of order){
      for(const prod of rules[lhs]){
        if(prod.length<=2){binRules[lhs].push(prod);continue;}
        anyBin=true;
        let curLhs=lhs;
        let rem=[...prod];
        while(rem.length>2){
          const xn=freshNT('X');
          binRules[xn]=[];binOrder.push(xn);nts.add(xn);
          const rhs=[rem[0],xn];
          binRules[curLhs].push(rhs);
          await addLogLine(
            s.changesId,
            `<span style="color:${curLhs===lhs?'var(--amber)':'var(--green)'}">${curLhs===lhs?'MODIFY':'ADD'}</span> &nbsp; ${curLhs} → ${rhs.join(' ')}`,
            curLhs===lhs?'changed':'added'
          );
          curLhs=xn;
          rem=rem.slice(1);
          await tick();
        }
        binRules[curLhs].push(rem);
        await addLogLine(s.changesId,`<span style="color:var(--green)">ADD</span> &nbsp; ${curLhs} → ${rem.join(' ')}`,'added');
      }
    }
    if(!anyBin)await addLogLine(s.changesId,'All rules already binary — nothing to do','info');
    await tick();s.setBadge('done');s.setComplete();

    // Show final CNF
    const finalDiv=document.createElement('div');
    finalDiv.style.cssText='margin-top:14px;background:var(--green-bg);border:1.5px solid var(--green-border);border-radius:10px;padding:14px 16px';
    finalDiv.innerHTML=`<div style="font-family:var(--font);font-size:11px;font-weight:700;color:var(--green);letter-spacing:.08em;text-transform:uppercase;margin-bottom:10px">✓ CNF Conversion Complete</div>`+
      binOrder.filter(k=>binRules[k]).map(lhs=>
        `<div style="font-size:12px;font-family:var(--mono);padding:2px 0;display:flex;gap:4px;flex-wrap:wrap;align-items:baseline">
          <span style="color:var(--accent);font-weight:600">${lhs}</span><span style="color:var(--text3);margin:0 3px">→</span>
          <span>${binRules[lhs].map(p=>p.map(s=>[...nts].includes(s)?`<span style="color:#7c3aed">${s}</span>`:s==='ε'?`<span style="color:var(--red)">${s}</span>`:`<span style="color:var(--green)">${s}</span>`).join(' ')).join('<span style="color:var(--text3);margin:0 4px">|</span>')}</span>
        </div>`
      ).join('');
    document.getElementById(body).appendChild(finalDiv);
    await tick();

    return{rules:binRules,order:binOrder,start:startSym,nts:[...nts],terms:g.terms};
  }
}

// ═══════════════════════════════════════════════
// ANIMATE CYK
// ═══════════════════════════════════════════════
async function animateCYK(cnf,str){
  const body='cyk-body';
  const res=runCYK(cnf,str);

  if(res.n===0){
    const d=document.createElement('div');
    d.className=`verdict ${res.accepts?'acc':'rej'}`;
    d.innerHTML=`<div class="v-icon">${res.accepts?'✅':'❌'}</div><div><div class="v-title">${res.accepts?'Accepted':'Rejected'}</div><div class="v-sub">Empty string ${res.accepts?'∈':'∉'} L(G)</div></div>`;
    document.getElementById(body).appendChild(d);
    return res;
  }

  // String display
  const strRow=document.createElement('div');
  strRow.style.cssText='display:flex;align-items:center;gap:6px;margin-bottom:14px;flex-wrap:wrap';
  strRow.innerHTML=`<span style="font-size:11px;color:var(--text3);font-family:var(--mono)">Input: </span>`+
    res.str.map((c,i)=>`<div id="sc-${i}" style="width:34px;height:34px;display:flex;align-items:center;justify-content:center;border-radius:7px;background:var(--bg3);border:1.5px solid var(--border);font-size:14px;font-weight:500;font-family:var(--mono);transition:all .3s">${c}</div>`).join('')+
    `<span style="font-size:11px;color:var(--text3);margin-left:6px;font-family:var(--mono)">|w| = ${res.n}</span>`;
  document.getElementById(body).appendChild(strRow);

  // Build table HTML (empty)
  const wrap=document.createElement('div');wrap.className='cyk-wrap';
  let html=`<table class="cyk"><thead><tr><th>i \\ j</th>`;
  for(let j=0;j<res.n;j++) html+=`<th>${j} &nbsp; <span style="color:var(--green);font-weight:600">'${res.str[j]}'</span></th>`;
  html+='</tr></thead><tbody>';
  for(let i=0;i<res.n;i++){
    html+=`<tr><th>${i}</th>`;
    for(let j=0;j<res.n;j++){
      if(j<i) html+=`<td style="background:var(--bg);border-color:var(--bg3)"></td>`;
      else html+=`<td id="cell-${i}-${j}" class="empty">—</td>`;
    }
    html+='</tr>';
  }
  html+='</tbody></table>';
  wrap.innerHTML=html;
  document.getElementById(body).appendChild(wrap);

  // CYK computation log
  const cykLogWrap=document.createElement('div');
  cykLogWrap.innerHTML=`<div style="font-family:var(--font);font-size:10px;font-weight:700;color:var(--text3);letter-spacing:.1em;text-transform:uppercase;margin:12px 0 6px">Live Computation Log</div>`;
  const cykLog=document.createElement('div');cykLog.className='cyk-log';cykLog.id='cyk-log-inner';
  cykLogWrap.appendChild(cykLog);
  document.getElementById(body).appendChild(cykLogWrap);

  // Step through cells with Next button
  const cellFilled={};
  for(const step of res.steps){
    if(abortFlag) throw new Error('__ABORTED__');
    const{i,j,added,type,k,B,C}=step;
    const cell=document.getElementById(`cell-${i}-${j}`);
    if(!cell) continue;

    // Highlight input chars for this substring
    for(let c=i;c<=j;c++){const ch=document.getElementById(`sc-${c}`);if(ch){ch.style.borderColor='var(--accent)';ch.style.background='var(--blue-bg)';}}

    // Mark cell as computing
    cell.classList.remove('empty');
    cell.classList.add('computing-cell');

    // Add log line
    const logLine=document.createElement('div');
    logLine.className='cyk-log-line show';
    if(type==='base')
      logLine.innerHTML=`<span class="checking">Diagonal [${i}][${j}]:</span> char <strong>'${res.str[i]}'</strong> matches rule <span class="found">${added} → ${res.str[i]}</span>`;
    else
      logLine.innerHTML=`<span class="checking">Cell [${i}][${j}], split at k=${k}:</span> table[${i}][${k}] has <span class="found">${B}</span> AND table[${k+1}][${j}] has <span class="found">${C}</span> → rule <span class="result-log">${added}→${B}${C}</span> fires → <span class="result-log">add ${added}</span>`;
    cykLog.appendChild(logLine);
    cykLog.scrollTop=cykLog.scrollHeight;

    // Wait for Next click
    const substr=res.str.slice(i,j+1).join('');
    const nextLabel=type==='base'
      ? `Filling diagonal cell [${i}][${i}] — single char '${res.str[i]}' → ${added}`
      : `Filling cell [${i}][${j}] — substring "${substr}" — ${added}→${B}${C} via split k=${k}`;
    await waitForNext(body, nextLabel);
    if(abortFlag) throw new Error('__ABORTED__');

    // Fill the cell
    cell.classList.remove('computing-cell');
    if(!cellFilled[`${i},${j}`]){
      cell.classList.add('just-filled');cellFilled[`${i},${j}`]=true;
      setTimeout(()=>cell.classList.remove('just-filled'),500);
    }
    const isAcc=i===0&&j===res.n-1&&res.accepts;
    cell.className=isAcc?'acc':'filled';
    cell.innerHTML=(cell.innerHTML&&cell.innerHTML!=='—'?cell.innerHTML+' ':'')+`<span class="cyk-tag ${added===cnfG.start?'s-tag':''}">${added}</span>`;
    if(isAcc) cell.style.fontWeight='600';

    // Unhighlight chars
    for(let c=i;c<=j;c++){const ch=document.getElementById(`sc-${c}`);if(ch){ch.style.borderColor='';ch.style.background='';}}
  }

  await tick();

  // Verdict
  const verdict=document.createElement('div');
  verdict.className=`verdict ${res.accepts?'acc':'rej'}`;
  verdict.style.marginTop='14px';
  verdict.innerHTML=`<div class="v-icon">${res.accepts?'✅':'❌'}</div>
    <div><div class="v-title">${res.accepts?`"${str}" is Accepted — it belongs to L(G)`:`"${str}" is Rejected — not in L(G)`}</div>
    <div class="v-sub">${res.accepts?`Start symbol ${cnfG.start} found in table[0][${res.n-1}]`:`Start symbol ${cnfG.start} not found in table[0][${res.n-1}]`}</div></div>`;
  document.getElementById(body).appendChild(verdict);
  await tick();

  return res;
}

// ═══════════════════════════════════════════════
// ANIMATE PARSE TREE
// ═══════════════════════════════════════════════
async function animateParseTree(res,str){
  const body='tree-body';
  if(!res.accepts){
    document.getElementById(body).innerHTML=`<div class="verdict rej"><div class="v-icon">❌</div><div><div class="v-title">No parse tree</div><div class="v-sub">String not accepted — no derivation exists</div></div></div>`;return;
  }
  const sa=str.split('');
  const tree=buildTree(cnfG,res.table,sa,cnfG.start,0,sa.length-1,{});
  if(!tree){document.getElementById(body).innerHTML=`<div style="color:var(--text3);font-size:12px;padding:12px">Could not reconstruct parse tree</div>`;return;}

  makeComputing(body,'Reconstructing parse tree from CYK table');
  await tick();removeComputing(body);

  const treeData=makeSVGTree(tree,cnfG);
  const wrap=document.createElement('div');wrap.className='tree-svg-wrap';
  document.getElementById(body).appendChild(wrap);
  renderSVGTree(treeData,wrap,'');

  // Reveal the tree automatically so the full structure is visible immediately.
  await animateTree(treeData.list, null);
  await tick();

  // Derivation steps — each appears on Next click
  const deriv=getDerivation(tree);
  if(deriv.length>1){
    const dd=document.createElement('div');
    dd.innerHTML=`<div style="font-family:var(--font);font-size:11px;font-weight:700;color:var(--text3);letter-spacing:.1em;text-transform:uppercase;margin:14px 0 8px">Leftmost Derivation — step by step</div>`;
    const stepsDiv=document.createElement('div');stepsDiv.className='deriv-steps';
    dd.appendChild(stepsDiv);
    document.getElementById(body).appendChild(dd);
    for(let i=0;i<deriv.length;i++){
      if(abortFlag) throw new Error('__ABORTED__');
      const row=document.createElement('div');row.className='deriv-row';
      row.innerHTML=`<span class="deriv-arrow">${i===0?'start:':'=>'}</span><span class="deriv-str">${deriv[i]}</span>`;
      stepsDiv.appendChild(row);
      row.classList.add('show');
      if(i<deriv.length-1)
        await waitForNext(body, `Derivation step ${i+1} of ${deriv.length-1} — apply next production rule`);
    }
  }
}

// ═══════════════════════════════════════════════
// ANIMATE AMBIGUITY
// ═══════════════════════════════════════════════
async function animateAmbiguity(res,str){
  const body='amb-body';
  if(!res.accepts){
    document.getElementById(body).innerHTML=`<div style="font-size:12px;color:var(--text3);font-family:var(--mono);padding:8px 0">Ambiguity check requires an accepted string</div>`;return;
  }
  makeComputing(body,'Searching for a second distinct parse tree');
  await tick();
  const sa=str.split('');
  const trees=buildTreeVariants(cnfG,res.table,sa,cnfG.start,0,sa.length-1,2);
  const t1=trees[0]||null;
  const t2=trees[1]||null;
  const isAmb=!!(t1&&t2);
  removeComputing(body);

  const logId=makeLogContainer(body);
  await addLogLine(logId,'Parse tree 1 reconstructed from CYK table','info');await tick();
  await addLogLine(logId,'Searching for alternative derivation with different split points...','info');await tick();
  if(isAmb) await addLogLine(logId,'<span style="color:var(--amber);font-weight:600">Second parse tree found — grammar is AMBIGUOUS</span>','highlight');
  else await addLogLine(logId,'No second parse tree found for this string','info');
  await tick();

  const verdict=document.createElement('div');
  verdict.className=`amb-result ${isAmb?'ambig':'unamb'}`;
  verdict.style.cssText='display:flex;align-items:center;gap:12px;padding:14px 18px;border-radius:10px;margin:10px 0';
  verdict.innerHTML=`<div style="font-size:22px">${isAmb?'⚠️':'✅'}</div>
    <div><div class="amb-label">${isAmb?'Grammar is AMBIGUOUS':'Grammar appears UNAMBIGUOUS for this string'}</div>
    <div style="font-size:11px;color:var(--text3);margin-top:2px;font-family:var(--mono)">${isAmb?`Two distinct parse trees exist for "${str}"`:`Only one parse tree found for "${str}"`}</div></div>`;
  document.getElementById(body).appendChild(verdict);
  await tick();

  if(isAmb){
    const note=document.createElement('div');
    note.style.cssText='font-size:11px;color:var(--text2);line-height:1.7;background:var(--amber-bg);border:1.5px solid var(--amber-border);border-radius:8px;padding:10px 13px;margin-bottom:12px;font-family:var(--mono)';
    note.innerHTML=`A grammar G is <strong>ambiguous</strong> if ∃w ∈ L(G) with two or more distinct leftmost derivations. Each derivation produces a different parse tree. Below are the two trees found for <strong>"${str}"</strong>:`;
    document.getElementById(body).appendChild(note);
    const grid=document.createElement('div');grid.className='amb-grid';
    const c1=document.createElement('div');c1.className='amb-tree-card';
    const c2=document.createElement('div');c2.className='amb-tree-card';
    const td1=makeSVGTree(t1,cnfG);const td2=makeSVGTree(t2,cnfG);
    renderSVGTree(td1,c1,'Parse Tree 1');
    renderSVGTree(td2,c2,'Parse Tree 2');
    grid.appendChild(c1);grid.appendChild(c2);
    document.getElementById(body).appendChild(grid);
    await animateTree(td1.list, null);await animateTree(td2.list, null);
  }
}

// ═══════════════════════════════════════════════
// ANIMATE FIRST & FOLLOW
// ═══════════════════════════════════════════════
async function animateFF(g){
  const body='ff-body';
  makeComputing(body,'Computing FIRST sets');
  await tick();
  const first=computeFirst(g);
  const logId=makeLogContainer(body);
  for(const nt of g.nts){
    await addLogLine(logId,`FIRST(${nt}) = { ${[...first[nt]].join(', ')||'∅'} }`,'info');
    await fastTick();
  }
  removeComputing(body);
  makeComputing(body,'Computing FOLLOW sets');
  await tick();
  const follow=computeFollow(g,first);
  for(const nt of g.nts){
    await addLogLine(logId,`FOLLOW(${nt}) = { ${[...follow[nt]].join(', ')||'∅'} }`,'result');
    await fastTick();
  }
  removeComputing(body);
  await tick();

  function renderSet(s){
    if(!s.size)return`<span style="color:var(--text3)">∅</span>`;
    return[...s].map(t=>`<span class="ff-tok ${t==='ε'?'ft-e':t==='$'?'ft-d':'ft-t'}">${t}</span>`).join('');
  }
  const tableDiv=document.createElement('div');
  tableDiv.innerHTML=`<table class="ff"><thead><tr><th>Variable</th><th>FIRST set</th><th>FOLLOW set</th></tr></thead><tbody>${
    g.nts.filter(nt=>g.rules[nt]).map(nt=>`<tr><td class="var-name">${nt}</td><td><div class="ff-set">${renderSet(first[nt])}</div></td><td><div class="ff-set">${renderSet(follow[nt])}</div></td></tr>`).join('')
  }</tbody></table>`;
  document.getElementById(body).appendChild(tableDiv);
  await tick();
  const legend=document.createElement('div');
  legend.style.cssText='display:flex;gap:10px;flex-wrap:wrap;font-size:11px;color:var(--text3);margin-top:10px;font-family:var(--mono)';
  legend.innerHTML=`Legend: <span class="ff-tok ft-t">a</span> terminal &nbsp; <span class="ff-tok ft-e">ε</span> empty string &nbsp; <span class="ff-tok ft-d">$</span> end of input`;
  document.getElementById(body).appendChild(legend);
}

// ═══════════════════════════════════════════════
// UTILITIES
// ═══════════════════════════════════════════════
function loadPreset(i){
  document.getElementById('grammar-input').value=PRESETS[i];
  document.getElementById('string-input').value=PSTRS[i]||'aabb';
}
function clearAll(){
  running=false;
  abortFlag=true;
  if(nextResolve){nextResolve();nextResolve=null;}
  setTimeout(()=>abortFlag=false,100);
  document.getElementById('run-btn').disabled=false;
  G=null;cnfG=null;cykRes=null;
  clearError();setStatus('Ready');
  ['grammar','cnf','cyk','tree','amb','ff'].forEach(id=>{
    document.getElementById('sec-'+id).classList.remove('visible');
    setNum(id,'pending');
    document.getElementById(id==='grammar'?'grammar-body':id+'-body').innerHTML='';
  });
}

// Load default
loadPreset(0);

