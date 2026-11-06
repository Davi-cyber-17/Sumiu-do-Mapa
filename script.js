'use strict';
const T=32,W=30,H=20,CW=W*T,CH=H*T,COUNT=10,HUNT=60,PAUSE=5;
const COLORS=['#ff6b6b','#4dabf7','#ffd43b','#69db7c','#da77f2','#ffa94d','#38d9a9','#f783ac','#a9e34b','#74c0fc'];
const PEER_OPTS={config:{iceServers:[{urls:'stun:stun.l.google.com:19302'},{urls:'stun:stun1.l.google.com:19302'},{urls:'stun:global.stun.twilio.com:3478'},{urls:['turn:openrelay.metered.ca:80','turn:openrelay.metered.ca:443','turn:openrelay.metered.ca:443?transport=tcp'],username:'openrelayproject',credential:'openrelayproject'}]}};
const $=s=>document.querySelector(s);
const clamp=(v,a,b)=>Math.max(a,Math.min(b,v));
const dist=(a,b)=>Math.hypot(a.x-b.x,a.y-b.y);
const cv=$('#cv'),ctx=cv.getContext('2d');

let mode=null,isHost=false,myId=null,humans=1,G=null,MAP=null,R=[],B=[],cur='menu';
let peer=null,conns={},hostConn=null,inGame=false,lastSig='',lastScore=0,rankShown=false;
const RP={},keys={};let joy={x:0,y:0};

/* ---------- telas ---------- */
function show(id){cur=id;document.querySelectorAll('.screen,#gameScr').forEach(s=>s.classList.toggle('hidden',s.id!==id))}
const setMsg=t=>$('#onMsg').textContent=t;
const nm=()=>($('#name').value.trim()||'Jogador').slice(0,12);
for(let i=2;i<=10;i++)$('#maxP').add(new Option(i+' jogadores',i,false,i===6));
$('#bOnline').onclick=()=>show('onlineScr');
$('#bLocal').onclick=()=>show('localScr');
document.querySelectorAll('.back').forEach(b=>b.onclick=()=>{setMsg('');show('menu')});
$('#bCreate').onclick=createRoom;
$('#bJoin').onclick=joinRoom;
$('#bStartLocal').onclick=startLocal;
$('#bLeave').onclick=()=>leave();
$('#bQuit').onclick=()=>{if(confirm('Sair da partida?'))leave()};
$('#bExit').onclick=()=>leave();
$('#roomCode').onclick=()=>{try{navigator.clipboard.writeText(G.code)}catch(e){}};
$('#bStart').onclick=()=>{
  if(G.players.length<2){$('#lobbyMsg').textContent='São necessários pelo menos 2 jogadores.';return}
  startGame();enterGame()};
$('#bAgain').onclick=()=>{
  if(mode==='local'){startLocal();return}
  G.phase='lobby';G.players.forEach(p=>p.role='hider');showLobby()};

function leave(msg){
  inGame=false;try{peer&&peer.destroy()}catch(e){}
  peer=null;conns={};hostConn=null;G=null;mode=null;isHost=false;show('menu');
  if(msg)setTimeout(()=>alert(msg),50)}

/* ---------- mapa ---------- */
function rng(a){return()=>{a|=0;a=a+0x6D2B79F5|0;let t=Math.imul(a^a>>>15,1|a);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296}}
function buildMap(seed){
  const r=rng(seed);MAP=[];
  for(let y=0;y<H;y++){MAP.push([]);for(let x=0;x<W;x++)MAP[y].push(x==0||y==0||x==W-1||y==H-1?1:0)}
  for(let i=0;i<22;i++){const w=1+(r()*3|0),h=1+(r()*3|0),x=2+(r()*(W-6)|0),y=2+(r()*(H-6)|0);
    for(let a=0;a<h;a++)for(let b=0;b<w;b++)MAP[y+a][x+b]=1}
  for(let i=0;i<14;i++){const cx=2+(r()*(W-4)|0),cy=2+(r()*(H-4)|0);
    for(let a=-1;a<=1;a++)for(let b=-1;b<=1;b++)if(r()<.7&&MAP[cy+a][cx+b]===0)MAP[cy+a][cx+b]=2}
  for(let y=H/2-2;y<H/2+2;y++)for(let x=W/2-2;x<W/2+2;x++)MAP[y][x]=0;
  R=[];B=[];const sx=W/2|0,sy=H/2|0,seen=new Set([sy*W+sx]),q=[[sx,sy]];
  while(q.length){const [x,y]=q.pop(),c=[x*T+T/2,y*T+T/2];R.push(c);if(MAP[y][x]===2)B.push(c);
    for(const [a,b] of [[1,0],[-1,0],[0,1],[0,-1]]){const nx=x+a,ny=y+b,k=ny*W+nx;
      if(nx>=0&&ny>=0&&nx<W&&ny<H&&MAP[ny][nx]!==1&&!seen.has(k)){seen.add(k);q.push([nx,ny])}}}
}
const solid=(x,y)=>{const tx=x/T|0,ty=y/T|0;return tx<0||ty<0||tx>=W||ty>=H||MAP[ty][tx]===1};
const hit=(x,y)=>{const r=10;return solid(x-r,y-r)||solid(x+r,y-r)||solid(x-r,y+r)||solid(x+r,y+r)};
const inBush=q=>MAP[q.y/T|0][q.x/T|0]===2;

/* ---------- motor (anfitrião / local) ---------- */
const newG=()=>({q:0,phase:'lobby',t:0,round:0,rounds:0,seed:0,seekerId:null,msg:'',players:[],code:'',max:10});
const freeColor=()=>{const u=G.players.map(p=>p.color);return COLORS.find(c=>!u.includes(c))||COLORS[0]};
const mk=(id,name,bot)=>({id,name,color:freeColor(),x:0,y:0,role:'hider',score:0,bot:!!bot,dx:0,dy:0});
const seeker=()=>G.players.find(p=>p.id===G.seekerId);

function startGame(){G.rounds=G.players.length;G.round=0;G.players.forEach(p=>p.score=0);nextRound()}
function nextRound(){
  if(++G.round>G.rounds){G.phase='over';G.msg='';return}
  G.seed=Math.random()*1e9|0;buildMap(G.seed);
  const sk=G.players[(G.round-1)%G.players.length];G.seekerId=sk.id;
  const far=R.filter(c=>Math.hypot(c[0]-CW/2,c[1]-CH/2)>220),pool=far.length>10?far:R;
  for(const p of G.players){
    p.role=p===sk?'seeker':'hider';p.dx=p.dy=0;p.tx=null;p.stuck=0;
    if(p===sk){p.x=CW/2;p.y=CH/2}else{const c=pool[Math.random()*pool.length|0];p.x=c[0];p.y=c[1]}}
  G.phase='count';G.t=COUNT;G.msg=''}
function endRound(seekerWon){
  const sk=seeker();G.phase='end';G.t=PAUSE;
  if(!sk){G.msg='O pegador saiu. Escondidos vencem!';G.players.forEach(p=>{if(p.role==='hider')p.score+=15});return}
  if(seekerWon){sk.score+=20;G.msg=sk.name+' achou todo mundo!'}
  else{G.players.forEach(p=>{if(p.role==='hider')p.score+=15});G.msg='O tempo acabou: escondidos vencem!'}}

function update(dt){
  if(G.phase==='lobby'||G.phase==='over')return;
  const sk=seeker();
  if(!sk&&(G.phase==='count'||G.phase==='hunt')){endRound(false);return}
  for(const p of G.players){
    if(p.bot&&(G.phase==='count'||G.phase==='hunt'))ai(p);
    let dx=p.dx||0,dy=p.dy||0;const l=Math.hypot(dx,dy);if(l>1){dx/=l;dy/=l}
    const frozen=p.role==='caught'||G.phase==='end'||(p.role==='seeker'&&G.phase==='count');
    if(frozen){p.stuck=0;continue}
    const sp=p.role==='seeker'?150:140,ox=p.x,oy=p.y;
    let nx=p.x+dx*sp*dt;if(!hit(nx,p.y))p.x=nx;
    let ny=p.y+dy*sp*dt;if(!hit(p.x,ny))p.y=ny;
    p.stuck=(dx||dy)&&Math.hypot(p.x-ox,p.y-oy)<sp*dt*.3?(p.stuck||0)+dt:0}
  G.t-=dt;
  if(G.phase==='count'){if(G.t<=0){G.phase='hunt';G.t=HUNT}}
  else if(G.phase==='hunt'){
    for(const q of G.players)if(q.role==='hider'&&dist(sk,q)<24){q.role='caught';sk.score+=10}
    if(!G.players.some(p=>p.role==='hider'))endRound(true);else if(G.t<=0)endRound(false)}
  else if(G.phase==='end'&&G.t<=0)nextRound()}

/* ---------- bots ---------- */
const spot=pb=>{const a=B.length&&Math.random()<pb?B:R,c=a[Math.random()*a.length|0];return[c[0],c[1]]};
function ai(p){
  const sk=seeker();let tx=p.tx,ty=p.ty;
  if(p.stuck>.4){tx=null;p.stuck=0}
  if(p.role==='seeker'){
    let b=null,bd=1e9;
    for(const q of G.players)if(q.role==='hider'){const d=dist(p,q);if(d<(inBush(q)?48:210)&&d<bd){bd=d;b=q}}
    if(b){tx=b.x;ty=b.y}
    else if(tx==null||dist(p,{x:tx,y:ty})<14){const s=spot(.3);tx=s[0];ty=s[1]}
  }else if(p.role==='hider'&&sk){
    if(G.phase==='hunt'&&dist(p,sk)<130){
      tx=clamp(p.x+(p.x-sk.x)*3+(Math.random()-.5)*60,40,CW-40);
      ty=clamp(p.y+(p.y-sk.y)*3+(Math.random()-.5)*60,40,CH-40);p.fl=1}
    else if(tx==null||p.fl){const s=spot(.85);tx=s[0];ty=s[1];p.fl=0}}
  p.tx=tx;p.ty=ty;
  const d=tx==null?0:dist(p,{x:tx,y:ty});
  p.dx=d>6?(tx-p.x)/d:0;p.dy=d>6?(ty-p.y)/d:0}

/* ---------- entrada ---------- */
addEventListener('keydown',e=>{const k=e.key.length===1?e.key.toLowerCase():e.key;keys[k]=true;
  if(inGame&&k.startsWith('Arrow'))e.preventDefault()});
addEventListener('keyup',e=>{keys[e.key.length===1?e.key.toLowerCase():e.key]=false});
addEventListener('blur',()=>{for(const k in keys)keys[k]=false});
const kin=a=>a==='w'?[(keys.d?1:0)-(keys.a?1:0),(keys.s?1:0)-(keys.w?1:0)]
  :[(keys.ArrowRight?1:0)-(keys.ArrowLeft?1:0),(keys.ArrowDown?1:0)-(keys.ArrowUp?1:0)];
function myInput(){
  let [x,y]=kin('w');
  if(!(mode==='local'&&humans>1)){const [a,b]=kin('a');x+=a;y+=b}
  return[clamp(x+joy.x,-1,1),clamp(y+joy.y,-1,1)]}
const joyEl=$('#joy'),stick=$('#stick');let jc=null,jid=null;
function jmove(e){
  let x=(e.clientX-jc.x)/60,y=(e.clientY-jc.y)/60;const l=Math.hypot(x,y);if(l>1){x/=l;y/=l}
  joy.x=Math.abs(x)>.18?x:0;joy.y=Math.abs(y)>.18?y:0;
  stick.style.transform=`translate(${x*40}px,${y*40}px)`}
function jend(e){if(e&&e.pointerId!==jid)return;jid=null;joy={x:0,y:0};stick.style.transform='';joyEl.classList.remove('on')}
// joystick flutuante: toque e arraste em qualquer lugar da tela (celular/tablet)
cv.addEventListener('pointerdown',e=>{
  if(e.pointerType==='mouse'||jid!==null)return;
  jid=e.pointerId;jc={x:e.clientX,y:e.clientY};cv.setPointerCapture(e.pointerId);
  joyEl.style.left=e.clientX+'px';joyEl.style.top=e.clientY+'px';joyEl.classList.add('on');jmove(e)});
cv.addEventListener('pointermove',e=>{if(e.pointerId===jid)jmove(e)});
cv.addEventListener('pointerup',jend);cv.addEventListener('pointercancel',jend);
cv.addEventListener('contextmenu',e=>e.preventDefault());

/* ---------- modo local ---------- */
function startLocal(){
  mode='local';isHost=false;humans=+$('#humans').value;
  const nb=clamp(+$('#bots').value||0,0,8);
  G=newG();myId='p1';
  G.players.push(mk('p1','Jogador 1'));
  if(humans>1)G.players.push(mk('p2','Jogador 2'));
  for(let i=1;i<=nb;i++)G.players.push(mk('b'+i,'Bot '+i,true));
  if(G.players.length<2){alert('Adicione pelo menos 1 bot ou o Jogador 2.');return}
  startGame();enterGame()}

/* ---------- modo online (salas via PeerJS) ---------- */
const genCode=()=>Array.from({length:5},()=>'ABCDEFGHJKLMNPQRSTUVWXYZ23456789'[Math.random()*32|0]).join('');
function needPeer(){if(typeof Peer==='undefined'){setMsg('Não foi possível carregar a biblioteca online. Verifique sua internet.');return false}return true}

function createRoom(){
  if(!needPeer())return;
  const code=genCode(),max=+$('#maxP').value;setMsg('Criando sala…');
  try{peer&&peer.destroy()}catch(e){}
  peer=new Peer('esconde-'+code,PEER_OPTS);
  peer.on('open',()=>{
    mode='online';isHost=true;myId='host';conns={};
    G=newG();G.code=code;G.max=max;G.players.push(mk('host',nm()));showLobby()});
  peer.on('error',e=>{if(e.type==='unavailable-id')createRoom();else setMsg('Erro de conexão: '+e.type)});
  peer.on('disconnected',()=>{try{peer.reconnect()}catch(e){}});
  peer.on('connection',c=>{c.on('data',d=>hostData(c,d));c.on('close',()=>dropPlayer(c.peer))})}

function hostData(c,d){
  if(!d||typeof d!=='object')return;
  if(d.t==='join'){
    if(!G||G.phase!=='lobby'||G.players.length>=G.max){
      c.send({t:'err',m:G&&G.phase!=='lobby'?'A partida já começou.':'A sala está cheia.'});
      setTimeout(()=>c.close(),400);return}
    conns[c.peer]=c;G.players.push(mk(c.peer,String(d.n||'Jogador').slice(0,12)));
    c.send({t:'welcome',id:c.peer});broadcast()}
  else if(d.t==='in'){const p=G&&G.players.find(p=>p.id===c.peer);if(p){p.dx=clamp(+d.x||0,-1,1);p.dy=clamp(+d.y||0,-1,1)}}}

function dropPlayer(id){
  delete conns[id];if(!G)return;
  const i=G.players.findIndex(p=>p.id===id);if(i<0)return;
  G.players.splice(i,1);
  if(G.phase!=='lobby'&&G.players.length<2){G.phase='lobby';G.players.forEach(p=>p.role='hider')}}

function broadcast(){
  const s={t:'s',q:++G.q,ph:G.phase,tm:G.t,r:G.round,rs:G.rounds,sd:G.seed,sk:G.seekerId,m:G.msg,c:G.code,mx:G.max,
    p:G.players.map(p=>[p.id,p.name,p.color,p.x|0,p.y|0,p.role,p.score])};
  for(const id in conns){const c=conns[id];
    if(c.open&&!(c.dataChannel&&c.dataChannel.bufferedAmount>32768))c.send(s)}} // não acumula fila em conexão lenta

function joinRoom(){
  const code=$('#code').value.trim().toUpperCase();
  if(code.length<5){setMsg('Digite o código de 5 letras.');return}
  if(!needPeer())return;
  setMsg('Conectando…');try{peer&&peer.destroy()}catch(e){}
  peer=new Peer(undefined,PEER_OPTS);
  peer.on('open',()=>{
    mode='online';isHost=false;
    hostConn=peer.connect('esconde-'+code,{reliable:false});
    hostConn.on('open',()=>hostConn.send({t:'join',n:nm()}));
    hostConn.on('data',clientData);
    hostConn.on('close',()=>{if(G||cur!=='menu')leave('A sala foi encerrada.')})});
  peer.on('error',e=>setMsg(e.type==='peer-unavailable'?'Sala não encontrada. Confira o código.':'Erro de conexão: '+e.type))}

function clientData(d){
  if(!d)return;
  if(d.t==='err'){setMsg(d.m);leave(d.m);return}
  if(d.t==='welcome'){myId=d.id;G=newG();lastQ=0;PRED.on=false;return}
  if(d.t!=='s'||!G)return;
  if(d.q&&d.q<=lastQ)return;lastQ=d.q||lastQ; // ignora pacotes velhos fora de ordem
  if(d.r!==G.round||(d.ph==='count'&&G.phase!=='count'))PRED.on=false;
  G.phase=d.ph;G.t=d.tm;G.round=d.r;G.rounds=d.rs;G.seekerId=d.sk;G.msg=d.m;G.code=d.c;G.max=d.mx;
  if(d.sd&&G.seed!==d.sd){G.seed=d.sd;buildMap(d.sd)}
  G.players=d.p.map(a=>({id:a[0],name:a[1],color:a[2],x:a[3],y:a[4],role:a[5],score:a[6]}));
  if(G.phase==='lobby'){if(cur!=='lobbyScr')showLobby()}else if(!inGame)enterGame()}

/* ---------- lobby ---------- */
function showLobby(){
  inGame=false;lastSig='';show('lobbyScr');
  $('#roomCode').textContent=G.code;
  $('#bStart').classList.toggle('hidden',!isHost);
  $('#lobbyMsg').classList.toggle('hidden',isHost);
  $('#lobbyMsg').textContent='Aguardando o anfitrião iniciar…'}
function lobbyUI(){
  const sig=G.players.map(p=>p.id+p.name+p.color).join('|');if(sig===lastSig)return;lastSig=sig;
  const ul=$('#plist');ul.textContent='';
  for(const p of G.players){
    const li=document.createElement('li'),d=document.createElement('span'),n=document.createElement('span');
    d.className='dot';d.style.background=p.color;
    n.textContent=p.name+(p.id===myId?' (você)':'')+(p.id==='host'?' ★':'');
    li.append(d,n);ul.append(li)}
  $('#count').textContent=G.players.length+'/'+G.max}

function enterGame(){inGame=true;rankShown=false;$('#endBox').classList.add('hidden');show('gameScr');resize();
  try{navigator.wakeLock&&navigator.wakeLock.request('screen').catch(()=>{})}catch(e){}}

/* ---------- desenho ---------- */
let VW=innerWidth,VH=innerHeight,DPR=1,SC=1,LAYER=null,LSEED=-1,LS=1,lastQ=0;
const PRED={x:0,y:0,on:false};
function resize(){
  const d=Math.min(devicePixelRatio||1,1.5),w=innerWidth,h=innerHeight;
  DPR=d;VW=w;VH=h;SC=clamp(Math.sqrt(w*h/360000),.6,3); // mesma área visível em qualquer tela
  const cw=Math.round(w*d),ch=Math.round(h*d);
  if(cv.width!==cw||cv.height!==ch){cv.width=cw;cv.height=ch}}
addEventListener('resize',resize);addEventListener('orientationchange',()=>setTimeout(resize,250));resize();

// mapa pré-renderizado: o brilho e as listras são desenhados UMA vez por rodada, não a cada quadro
function buildLayers(){
  LS=clamp(Math.round(DPR*SC),1,2);LSEED=G.seed;
  const mkc=()=>{const k=document.createElement('canvas');k.width=CW*LS;k.height=CH*LS;const g=k.getContext('2d');g.scale(LS,LS);return[k,g]};
  const [a,c]=mkc(),[b,d]=mkc();
  for(let y=0;y<H;y++)for(let x=0;x<W;x++){
    c.fillStyle=MAP[y][x]===1?'#0f2a40':((x+y)&1?'#081521':'#0a1826');c.fillRect(x*T,y*T,T,T)}
  c.strokeStyle='rgba(18,230,255,.07)';c.lineWidth=1;c.beginPath();
  for(let x=0;x<=W;x++){c.moveTo(x*T,0);c.lineTo(x*T,CH)}
  for(let y=0;y<=H;y++){c.moveTo(0,y*T);c.lineTo(CW,y*T)}
  c.stroke();
  c.strokeStyle='#12e6ff';c.lineWidth=2;c.shadowColor='#12e6ff';c.shadowBlur=10;c.beginPath();
  for(let y=0;y<H;y++)for(let x=0;x<W;x++)if(MAP[y][x]===1){
    const X=x*T,Y=y*T,o=(i,j)=>MAP[y+j]&&MAP[y+j][x+i]!==1;
    if(o(0,-1)){c.moveTo(X,Y);c.lineTo(X+T,Y)}if(o(0,1)){c.moveTo(X,Y+T);c.lineTo(X+T,Y+T)}
    if(o(-1,0)){c.moveTo(X,Y);c.lineTo(X,Y+T)}if(o(1,0)){c.moveTo(X+T,Y);c.lineTo(X+T,Y+T)}}
  c.stroke();
  const hat=document.createElement('canvas');hat.width=hat.height=8;const h=hat.getContext('2d');
  h.strokeStyle='rgba(182,255,59,.6)';h.lineWidth=1.4;h.beginPath();
  h.moveTo(0,8);h.lineTo(8,0);h.moveTo(-2,2);h.lineTo(2,-2);h.moveTo(6,10);h.lineTo(10,6);h.stroke();
  const pat=d.createPattern(hat,'repeat');
  for(let y=0;y<H;y++)for(let x=0;x<W;x++)if(MAP[y][x]===2){
    d.fillStyle='rgba(6,52,36,.8)';d.fillRect(x*T,y*T,T,T);d.fillStyle=pat;d.fillRect(x*T,y*T,T,T)}
  LAYER=[a,b]}
function blit(k,cx,cy,hw,hh){
  const sx=Math.max(0,cx-hw),sy=Math.max(0,cy-hh),ex=Math.min(CW,cx+hw),ey=Math.min(CH,cy+hh);
  if(ex>sx&&ey>sy)ctx.drawImage(k,sx*LS,sy*LS,(ex-sx)*LS,(ey-sy)*LS,sx,sy,ex-sx,ey-sy)}

// suaviza as posições (por tempo, não por quadro) e usa a posição prevista para o próprio jogador no online
function updateRP(dt){
  const k=1-Math.exp(-dt*18);
  for(const p of G.players){
    const r=RP[p.id]||(RP[p.id]={x:p.x,y:p.y});
    if(p.id===myId&&PRED.on&&mode==='online'&&!isHost){r.x=PRED.x;r.y=PRED.y;continue}
    if(Math.hypot(p.x-r.x,p.y-r.y)>120){r.x=p.x;r.y=p.y}else{r.x+=(p.x-r.x)*k;r.y+=(p.y-r.y)*k}}}

// previsão local: o jogador online se move na hora, sem esperar a resposta do anfitrião
function predict(me,dt){
  const frozen=me.role==='caught'||G.phase==='end'||G.phase==='lobby'||G.phase==='over'||(me.role==='seeker'&&G.phase==='count');
  const d=Math.hypot(me.x-PRED.x,me.y-PRED.y);
  if(!PRED.on||frozen||d>150){PRED.x=me.x;PRED.y=me.y;PRED.on=true}
  else if(d>60){PRED.x+=(me.x-PRED.x)*.15;PRED.y+=(me.y-PRED.y)*.15}
  if(frozen||!MAP)return;
  let [dx,dy]=myInput();const l=Math.hypot(dx,dy);if(l>1){dx/=l;dy/=l}
  const sp=me.role==='seeker'?150:140;let rem=dt;
  while(rem>0){const s=Math.min(rem,1/30);rem-=s;
    const nx=PRED.x+dx*sp*s;if(!hit(nx,PRED.y))PRED.x=nx;
    const ny=PRED.y+dy*sp*s;if(!hit(PRED.x,ny))PRED.y=ny}}

function drawP(q,self,t){
  const r=RP[q.id],c=ctx,col=q.role==='seeker'?'#ff2e9f':q.color,a=q.role==='caught'?.4:1;
  c.globalAlpha=.22*a;c.fillStyle=col;c.beginPath();c.arc(r.x,r.y,19,0,7);c.fill();
  c.globalAlpha=a;c.fillStyle=col;c.beginPath();c.arc(r.x,r.y,11,0,7);c.fill();
  c.fillStyle='#04101a';c.beginPath();c.arc(r.x,r.y,7,0,7);c.fill();
  c.fillStyle=col;c.beginPath();c.arc(r.x,r.y,3.5,0,7);c.fill();
  if(self){c.strokeStyle='#fff';c.lineWidth=2;c.beginPath();c.arc(r.x,r.y,15,0,7);c.stroke()}
  if(q.role==='seeker'){const k=(Math.sin(t/180)+1)/2;
    c.strokeStyle='rgba(255,46,159,'+(.9-k*.5)+')';c.lineWidth=2;c.beginPath();c.arc(r.x,r.y,18+k*7,0,7);c.stroke()}
  c.font='bold 12px Rajdhani,sans-serif';c.textAlign='center';c.lineWidth=3;c.strokeStyle='#02060cdd';c.fillStyle='#dff7ff';
  c.strokeText(q.name,r.x,r.y-22);c.fillText(q.name,r.x,r.y-22);c.globalAlpha=1}

function draw(){
  const me=G.players.find(p=>p.id===myId)||G.players[0];if(!me||!MAP||!RP[me.id])return;
  const want=clamp(Math.round(DPR*SC),1,2);if(!LAYER||LSEED!==G.seed||want!==LS)buildLayers();
  const c=ctx,t=performance.now(),fog=me.role==='seeker'&&G.phase!=='end'&&!(mode==='local'&&humans>1);
  const mr=RP[me.id],hw=VW/SC/2,hh=VH/SC/2;
  const cx=CW<=hw*2?CW/2:clamp(mr.x,hw,CW-hw),cy=CH<=hh*2?CH/2:clamp(mr.y,hh,CH-hh);
  c.setTransform(1,0,0,1,0,0);c.fillStyle='#02060c';c.fillRect(0,0,cv.width,cv.height);
  c.setTransform(DPR*SC,0,0,DPR*SC,DPR*(VW/2-cx*SC),DPR*(VH/2-cy*SC));
  blit(LAYER[0],cx,cy,hw,hh);
  for(const q of G.players){
    if(q===me||(q.role==='caught'&&me.role!=='caught'))continue;
    const r=RP[q.id];
    if(Math.abs(r.x-cx)>hw+30||Math.abs(r.y-cy)>hh+30)continue;
    if(fog){const d=Math.hypot(r.x-mr.x,r.y-mr.y);if(d>175||(inBush(q)&&d>48))continue}
    drawP(q,false,t)}
  blit(LAYER[1],cx,cy,hw,hh);
  drawP(me,true,t);
  c.setTransform(1,0,0,1,0,0);
  if(fog){
    if(G.phase==='count'){c.fillStyle='#02040a';c.fillRect(0,0,cv.width,cv.height)}
    else{const sx=(VW/2+(mr.x-cx)*SC)*DPR,sy=(VH/2+(mr.y-cy)*SC)*DPR,R1=185*SC*DPR;
      const g=c.createRadialGradient(sx,sy,R1*.5,sx,sy,R1);
      g.addColorStop(0,'rgba(2,6,12,0)');g.addColorStop(1,'rgba(2,6,12,.97)');
      c.fillStyle=g;c.fillRect(0,0,cv.width,cv.height);
      c.strokeStyle='rgba(18,230,255,.25)';c.lineWidth=1.5*DPR;c.beginPath();c.arc(sx,sy,175*SC*DPR,0,7);c.stroke()}}}

let hB='',hI='',hS='';
function hud(){
  const me=G.players.find(p=>p.id===myId)||G.players[0];if(!me)return;
  const t=Math.ceil(Math.max(0,G.t));let s='';
  if(G.phase==='count')s=me.role==='seeker'?`Conte até ${t}! Sem espiar`:`Esconda-se! Ele abre os olhos em ${t}s`;
  else if(G.phase==='hunt')s=me.role==='seeker'?`Ache todos! ${t}s`:me.role==='caught'?`Você foi pego. Assista! ${t}s`:`Não se deixe pegar! ${t}s`;
  else if(G.phase==='end')s=G.msg;
  if(s!==hB){hB=s;$('#banner').textContent=s}
  const inf=`Rodada ${Math.min(G.round,G.rounds)}/${G.rounds}`;
  if(inf!==hI){hI=inf;$('#info').textContent=inf}
  const now=performance.now();if(now-lastScore<250)return;lastScore=now;
  const list=[...G.players].sort((a,b)=>b.score-a.score),sig=list.map(p=>p.name+p.score+p.role).join('|');
  if(sig===hS)return;hS=sig;
  const box=$('#score');box.textContent='';
  for(const p of list){
    const d=document.createElement('div');
    d.textContent=(p.role==='seeker'?'🔍 ':p.role==='caught'?'✖ ':'')+p.name+': '+p.score;
    d.style.color=p.color;box.append(d)}}

function rankUI(){
  if(G.phase!=='over'){$('#endBox').classList.add('hidden');rankShown=false;return}
  if(rankShown)return;rankShown=true;
  const ol=$('#rank');ol.textContent='';
  for(const p of [...G.players].sort((a,b)=>b.score-a.score)){
    const li=document.createElement('li');li.textContent=p.name+': '+p.score+' pontos';ol.append(li)}
  $('#bAgain').classList.toggle('hidden',mode==='online'&&!isHost);
  $('#endBox').classList.remove('hidden')}

/* ---------- laço principal ---------- */
let last=performance.now(),netAcc=0,inAcc=0,lastIn='';
function sendInput(dt){
  const [x,y]=myInput(),k=x.toFixed(2)+','+y.toFixed(2);inAcc+=dt;
  if((k!==lastIn&&inAcc>=.033)||inAcc>=.25){lastIn=k;inAcc=0;hostConn.send({t:'in',x:+x.toFixed(2),y:+y.toFixed(2)})}}
function loop(ts){
  const dt=Math.min(.25,(ts-last)/1000);last=ts;
  if(G){
    if(mode==='local'||isHost){
      const me=G.players.find(p=>p.id==='p1'||p.id==='host');
      if(me&&G.phase!=='lobby'){const [x,y]=myInput();me.dx=x;me.dy=y}
      if(mode==='local'&&humans>1){const p2=G.players.find(p=>p.id==='p2'),[x,y]=kin('a');if(p2){p2.dx=x;p2.dy=y}}
      let rem=dt;while(rem>0){const s=Math.min(rem,1/30);rem-=s;update(s)} // passos fixos: não perde tempo em tela lenta
      if(isHost){netAcc+=dt;if(netAcc>=1/30){netAcc=0;broadcast()}}
    }else if(hostConn&&hostConn.open&&inGame){
      const me=G.players.find(p=>p.id===myId);if(me&&MAP)predict(me,dt);
      sendInput(dt)}
    if(cur==='lobbyScr')lobbyUI();
    if(inGame&&MAP){updateRP(dt);draw();hud();rankUI()}}
  requestAnimationFrame(loop)}
requestAnimationFrame(loop);
