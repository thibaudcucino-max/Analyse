/* =========================================================
   DVF Analyse — SAS De Mère en Fils MDB
   Fichier autonome. Charte : blanc/crème + olive MDB.
   ========================================================= */
const INK=[26,25,23], GOLD=[74,82,64], GOLD_DK=[58,65,50];
const nf=new Intl.NumberFormat('fr-FR');
const f0=n=>isFinite(n)?nf.format(Math.round(n)):'—';
const eur=n=>isFinite(n)?f0(n)+' €':'—';
const ppmF=n=>isFinite(n)?f0(n)+' €/m²':'—';
const km=m=> m<1000 ? Math.round(m)+' m' : (m/1000).toLocaleString('fr-FR',{minimumFractionDigits:2,maximumFractionDigits:2})+' km';

let DPE_COEF={A:0.10,B:0.07,C:0.03,D:0.00,E:-0.04,F:-0.09,G:-0.13};
const DPE_ORDER=['A','B','C','D','E','F','G'];

const state={
  addresses:[],       // {label,lat,lon,insee}
  raw:[],             // lignes DVF normalisées
  rows:[],            // lignes exploitables (dans secteur)
  filtered:[],        // après filtres
  view:'carte', macro:'secteur', csvLoaded:false, rawSource:'',
  sort:{key:'date',dir:-1},
  targetDPE:'D', anomaliesRemoved:0,
  qual:{rows:[],target:null,targetMatch:null,targetPublic:null,targetAudit:null,running:false,worksRunning:false,enrichedCount:0,enrichedAll:false,dpeErrors:0,publicEnrichedCount:0,publicEnrichedAll:false,publicErrors:0,auditEnrichedCount:0,auditEnrichedAll:false,auditErrors:0,selectionInitialized:false,filters:{dpe:'all',surface:'all',pieces:'all',period:'all',distance:'all',recency:'all',mutation:'all',floor:'all',copro:'all',interior:'all',works:'all'},sort:{key:'score',dir:-1}}
};
const dpeQueryCache=new Map();
const banIdCache=new Map(),bdnbCache=new Map(),rnicCache=new Map();
const auditQueryCache=new Map();
let dpeMetaPromise=null,rnicResourcePromise=null,rnicProfilePromise=null,auditMetaPromise=null;


/* ---------------- Stabilisation des enrichissements ----------------
   Une fois un rapprochement obtenu, il est figé localement pendant 7 jours.
   Ainsi : même vente + mêmes paramètres = mêmes DPE / BDNB / RNIC / OSM / AUDIT.
   Le bouton « Actualiser depuis les sources » efface volontairement ce snapshot.
   ------------------------------------------------------------------ */
const STABLE_CACHE_PREFIX='dvf-analyse-stable-v6:';
const STABLE_CACHE_LEGACY_PREFIX='dvf-analyse-stable-v5:';
const STABLE_CACHE_TTL=7*24*60*60*1000;
const STABLE_NAN='__DVF_NAN__';
function stableJsonStringify(v){return JSON.stringify(v,(k,x)=>(typeof x==='number'&&!Number.isFinite(x))?STABLE_NAN:x);}
function stableJsonParse(v){return JSON.parse(v,(k,x)=>x===STABLE_NAN?NaN:x);}
function stableRowId(r){return [r.id||'',r.date||'',normTxt(r.voie||''),normTxt(r.commune||''),r.type||'',isFinite(r.surface)?r.surface:'',isFinite(r.val)?r.val:''].join('|');}
function stableStorageKey(r,prefix=STABLE_CACHE_PREFIX){return prefix+encodeURIComponent(stableRowId(r));}
function slimBdnb(b){if(!b)return null;return{id:b.id||'',rnb:b.rnb||'',address:b.address||'',coproId:b.coproId||'',year:b.year,nbLog:b.nbLog,levels:b.levels,height:b.height,dpe:b.dpe||'',ambiguous:!!b.ambiguous,alternatives:b.alternatives||0,confidence:b.confidence||''};}
function slimRnic(r){if(!r)return null;return{fields:Array.isArray(r.fields)?r.fields.slice(0,18):[],lots:r.lots,procedureFields:r.procedureFields||0,procedureAlert:!!r.procedureAlert};}
function slimOsm(o){if(!o)return null;return{found:!!o.found,elevator:!!o.elevator,parking:!!o.parking,garage:!!o.garage,balcony:!!o.balcony,terrace:!!o.terrace,garden:!!o.garden,parkingDetail:o.parkingDetail||'',buildingFootprint:o.buildingFootprint,buildingConfidence:o.buildingConfidence||'none',signals:Array.isArray(o.signals)?o.signals.slice(0,12):[]};}
function slimPublic(p){if(!p)return null;return{sig:p.sig||'',done:!!p.done,osmChecked:!!p.osmChecked,banId:p.banId||'',bdnb:slimBdnb(p.bdnb),bdnbChecked:!!p.bdnbChecked,rnic:slimRnic(p.rnic),immat:p.immat||'',immatSource:p.immatSource||'',coproDecision:p.coproDecision?{value:p.coproDecision.value===true?true:p.coproDecision.value===false?false:null,confidence:p.coproDecision.confidence||'none',source:p.coproDecision.source||'',immat:p.coproDecision.immat||'',key:p.coproDecision.key||'',checkedAt:p.coproDecision.checkedAt||0}:null,osm:slimOsm(p.osm),errors:Array.isArray(p.errors)?p.errors.slice(0,8):[]};}
function slimAudit(a){if(!a)return null;return{numero:a.numero||'',date:a.date||'',address:a.address||'',surface:a.surface,confidence:a.confidence||'',matchScore:a.matchScore,costMin:a.costMin,costMax:a.costMax,costMid:a.costMid,works:Array.isArray(a.works)?a.works.slice(0,8):[]};}
function saveStableRow(r){try{const payload={ts:Date.now(),dpeChecked:!!r.dpeChecked,dpeInfo:r.dpeInfo??null,publicInfo:slimPublic(r.publicInfo),auditChecked:!!r.auditChecked,auditInfo:slimAudit(r.auditInfo)};localStorage.setItem(stableStorageKey(r),stableJsonStringify(payload));r.stableSnapshotTs=payload.ts;}catch(e){console.warn('snapshot local',e);}}
function loadStableRow(r){try{let raw=localStorage.getItem(stableStorageKey(r)),legacy=false;if(!raw){raw=localStorage.getItem(stableStorageKey(r,STABLE_CACHE_LEGACY_PREFIX));legacy=!!raw;}if(!raw)return false;const p=stableJsonParse(raw);if(!p?.ts||Date.now()-p.ts>STABLE_CACHE_TTL){if(!legacy)localStorage.removeItem(stableStorageKey(r));return false;}if(legacy){const oldPositive=!!(p.publicInfo?.immat||p.publicInfo?.coproDecision?.value===true);if(!oldPositive)return false;}if(p.dpeChecked){r.dpeChecked=true;r.dpeInfo=p.dpeInfo||null;}if(p.publicInfo){r.publicInfo=p.publicInfo;}if(p.auditChecked){r.auditChecked=true;r.auditInfo=p.auditInfo||null;}r.stableSnapshotTs=p.ts;if(legacy)saveStableRow(r);return true;}catch(e){return false;}}
function clearStableRow(r){try{localStorage.removeItem(stableStorageKey(r));}catch(e){}delete r.stableSnapshotTs;}
function clearRuntimeEnrichmentCaches(){dpeQueryCache.clear();auditQueryCache.clear();banIdCache.clear();bdnbCache.clear();rnicCache.clear();osmCache.clear();dpeMetaPromise=null;rnicResourcePromise=null;rnicProfilePromise=null;auditMetaPromise=null;}

/* ---------------- Carte ---------------- */
const map=L.map('map',{zoomControl:true}).setView([48.817,2.516],13);
const bases={
  clair:L.tileLayer('https://{s}.basemaps.cartocdn.com/light_all/{z}/{x}/{y}{r}.png',{maxZoom:20,attribution:'© OpenStreetMap © CARTO'}),
  osm:L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png',{maxZoom:19,attribution:'© OpenStreetMap'}),
  ign:L.tileLayer('https://data.geopf.fr/wmts?SERVICE=WMTS&REQUEST=GetTile&VERSION=1.0.0&LAYER=GEOGRAPHICALGRIDSYSTEMS.PLANIGNV2&STYLE=normal&TILEMATRIXSET=PM&FORMAT=image/png&TILEMATRIX={z}&TILEROW={y}&TILECOL={x}',{maxZoom:19,attribution:'© IGN'}),
  ortho:L.tileLayer('https://data.geopf.fr/wmts?SERVICE=WMTS&REQUEST=GetTile&VERSION=1.0.0&LAYER=ORTHOIMAGERY.ORTHOPHOTOS&STYLE=normal&TILEMATRIXSET=PM&FORMAT=image/jpeg&TILEMATRIX={z}&TILEROW={y}&TILECOL={x}',{maxZoom:20,attribution:'© IGN'})
};
let curBase=bases.clair; curBase.addTo(map);
let addrMarkers=L.layerGroup().addTo(map), mutMarkers=L.layerGroup().addTo(map), radiusRings=L.layerGroup().addTo(map);
function switchBase(k){ map.removeLayer(curBase); curBase=bases[k]; curBase.addTo(map); }
map.zoomControl.setPosition('topright');
const TYPE_COLOR={Appartement:'#3A4150',Maison:'#4A5240',Local:'#8A6D3B','Dépendance':'#6B7078',Autre:'#9AA1AD'};
const TYPE_LABEL={Appartement:'Appartement',Maison:'Maison',Local:'Local industriel, commercial ou assimilé','Dépendance':'Dépendance',Autre:'Autre'};
let legendDiv=null;
const legend=L.control({position:'topleft'});
legend.onAdd=()=>{legendDiv=L.DomUtil.create('div','legend maplegend');
  legendDiv.innerHTML='<b>Type de bien</b><br><span class="lg-muted">Applique les filtres</span>';return legendDiv;};
legend.addTo(map);
function updateLegend(present){
  if(!legendDiv)return;
  const order=['Appartement','Maison','Local','Dépendance','Autre'].filter(t=>present.has(t));
  legendDiv.innerHTML='<b>Type de bien</b><br>'+
    (order.length?order.map(t=>`<span class="dot" style="background:${TYPE_COLOR[t]}"></span>${TYPE_LABEL[t]}`).join('<br>'):'<span class="lg-muted">Aucun bien</span>');
}
// Déplacement du point : glisser le marqueur, ou double-clic sur la carte pour repositionner le plus proche.
map.doubleClickZoom.disable();
map.on('dblclick', e=>{
  if(!state.addresses.length) return;
  let best=0, bd=Infinity;
  state.addresses.forEach((a,i)=>{const d=haversine(a.lat,a.lon,e.latlng.lat,e.latlng.lng); if(d<bd){bd=d;best=i;}});
  markAddressMoved(state.addresses[best],e.latlng.lat,e.latlng.lng);
  drawAddrMarkers(); drawRings();
  setStatus('Point déplacé — clique « Lancer l’analyse » pour recharger le secteur.','info');
});

/* ---------------- Vues ---------------- */
function setView(v){
  state.view=v;
  document.getElementById('viewSel').value=v;
  document.getElementById('mapView').classList.toggle('active', v==='carte');
  document.getElementById('view-vendus').classList.toggle('active', v==='vendus');
  document.getElementById('view-qualifies').classList.toggle('active', v==='qualifies');
  if(v==='carte') setTimeout(()=>{map.invalidateSize();fitMap();},60);
  if(v==='qualifies' && !state.qual.running){
    if(state.qual.rows.length) renderQualifiedResults();
    else renderQualifiedBase();
  }
}
function toggleAcc(id){ document.getElementById(id).classList.toggle('closed'); }
function updateRadius(){
  const m=+document.getElementById('radius').value;
  document.getElementById('radiusVal').textContent=km(m);
  drawRings();
}

/* ---------------- Adresses ---------------- */
function renderChips(){
  document.getElementById('chips').innerHTML=state.addresses.map((a,i)=>
    `<span class="chip"><b>${a.label.length>26?a.label.slice(0,24)+'…':a.label}</b><span class="x" onclick="removeAddress(${i})">×</span></span>`).join('');
}
function addAddress(label,lat,lon,insee,banId=''){
  const duplicate=state.addresses.some(a=>(banId&&a.banId===banId)||(!banId&&Math.abs(a.lat-lat)<1e-6&&Math.abs(a.lon-lon)<1e-6));
  if(duplicate){setStatus('Cette adresse est déjà dans la recherche.','info');return;}
  state.addresses.push({label,lat,lon,insee,banId});
  invalidateQualifiedForSourceChange();
  renderChips(); drawAddrMarkers(); drawRings();
  map.setView([lat,lon],Math.max(map.getZoom(),15));
  // Lance immédiatement le préchargement DVF de la commune sélectionnée.
  // Ainsi, le téléchargement a déjà commencé avant le clic sur « Lancer l’analyse ».
  if(insee) prefetchCommune(insee);
}
function removeAddress(i){ state.addresses.splice(i,1); invalidateQualifiedForSourceChange(); renderChips(); drawAddrMarkers(); drawRings(); }
function invalidateQualifiedForSourceChange(){
  state.qual.rows=[];state.qual.targetMatch=null;state.qual.targetPublic=null;state.qual.targetAudit=null;
  state.qual.enrichedCount=0;state.qual.enrichedAll=false;state.qual.publicEnrichedCount=0;state.qual.publicEnrichedAll=false;
  state.qual.auditEnrichedCount=0;state.qual.auditEnrichedAll=false;state.qual.selectionInitialized=false;
}
async function markAddressMoved(a,lat,lon){
  a.lat=lat;a.lon=lon;a.banId='';a.insee='';invalidateQualifiedForSourceChange();
  try{
    const r=await fetchTO(`https://api-adresse.data.gouv.fr/reverse/?lon=${encodeURIComponent(lon)}&lat=${encodeURIComponent(lat)}&limit=1`,5000);
    if(!r.ok)throw new Error('HTTP '+r.status);
    const j=await r.json(),f=j.features&&j.features[0];
    if(f){a.label=f.properties?.label||a.label;a.insee=f.properties?.citycode||'';a.banId=f.properties?.id||'';renderChips();if(a.insee)prefetchCommune(a.insee);}
  }catch(e){console.warn('Reverse BAN après déplacement',e);}
}
function drawAddrMarkers(){
  addrMarkers.clearLayers();
  state.addresses.forEach((a,i)=>{
    const m=L.marker([a.lat,a.lon],{draggable:true,
      icon:L.divIcon({className:'',iconSize:[18,18],iconAnchor:[9,9],html:'<div class="addr-dot"></div>'})});
    m.bindTooltip(a.label+' — glisse pour déplacer');
    m.on('dragend',()=>{const ll=m.getLatLng();markAddressMoved(a,ll.lat,ll.lng);drawRings();
      setStatus('Point déplacé — clique « Lancer l’analyse » pour recharger le secteur.','info');});
    m.addTo(addrMarkers);
  });
}
function drawRings(){
  radiusRings.clearLayers();
  const r=+document.getElementById('radius').value;
  state.addresses.forEach(a=>L.circle([a.lat,a.lon],{radius:r,color:'#4A5240',weight:1.5,fillColor:'#4A5240',fillOpacity:.05,dashArray:'5,5'}).addTo(radiusRings));
}

/* Autocomplete BAN */
let acTimer,acItems=[],acHl=-1;
const qEl=document.getElementById('q'),acEl=document.getElementById('ac');
qEl.addEventListener('input',()=>{clearTimeout(acTimer);const v=qEl.value.trim();if(v.length<3){acEl.classList.remove('open');return;}acTimer=setTimeout(()=>banSearch(v),250);});
qEl.addEventListener('keydown',e=>{
  if(!acEl.classList.contains('open'))return;
  if(e.key==='ArrowDown'){acHl=Math.min(acHl+1,acItems.length-1);renderAc();e.preventDefault();}
  else if(e.key==='ArrowUp'){acHl=Math.max(acHl-1,0);renderAc();e.preventDefault();}
  else if(e.key==='Enter'){if(acHl>=0){pickAc(acHl);e.preventDefault();}}
  else if(e.key==='Escape')acEl.classList.remove('open');
});
document.addEventListener('click',e=>{if(!acEl.contains(e.target)&&e.target!==qEl)acEl.classList.remove('open');});
async function banSearch(v){
  try{const r=await fetch('https://api-adresse.data.gouv.fr/search/?limit=6&q='+encodeURIComponent(v));
    const j=await r.json();acItems=j.features||[];acHl=-1;renderAc();acEl.classList.add('open');}
  catch(e){acEl.classList.remove('open');}
}
function renderAc(){acEl.innerHTML=acItems.map((f,i)=>{const p=f.properties;
  return `<div class="ac-item ${i===acHl?'hl':''}" onclick="pickAc(${i})">${p.label}<div class="ctx">${p.context||''} · ${p.type||''}</div></div>`;}).join('');}
function pickAc(i){const f=acItems[i];if(!f)return;const[lon,lat]=f.geometry.coordinates;const p=f.properties;
  qEl.value='';acEl.classList.remove('open');addAddress(p.label,lat,lon,p.citycode,p.id||'');}

/* ---------------- Réglages ---------------- */
function openSettings(){document.getElementById('settingsModal').classList.add('open');}
function closeSettings(){document.getElementById('settingsModal').classList.remove('open');}
function openExport(){if(!state.filtered.length){setStatus('Lancez d\'abord une analyse.','err');return;}document.getElementById('exportModal').classList.add('open');}
function closeExport(){document.getElementById('exportModal').classList.remove('open');}
function relayBuilders(){
  const custom=document.getElementById('proxyUrl').value.trim();
  if(custom) return [u=>custom+encodeURIComponent(u)];
  // 1er choix : proxy Vercel intégré (/api/relay) s'il est déployé avec l'outil
  const builders=[ u=>'/api/relay?url='+encodeURIComponent(u), u=>u ];
  const useRelay=document.getElementById('useRelay')&&document.getElementById('useRelay').checked;
  if(useRelay) builders.push(
    u=>'https://api.allorigins.win/raw?url='+encodeURIComponent(u),
    u=>'https://corsproxy.io/?url='+encodeURIComponent(u)
  );
  return builders;
}
function fetchTO(url,ms=9000){
  const ctl=new AbortController(); const id=setTimeout(()=>ctl.abort(),ms);
  return fetch(url,{signal:ctl.signal}).finally(()=>clearTimeout(id));
}
async function robustFetch(url,label){
  const builders=relayBuilders(); let lastErr;
  const info=document.getElementById('srcInfo');
  for(let i=0;i<builders.length;i++){
    try{
      if(info&&label) info.textContent=label+' — essai '+(i+1)+'/'+builders.length+'…';
      const built=builders[i](url),r=await fetchTO(built);
      if(r.ok) return r;
      // Un 404/410 est définitif uniquement si l'on sait qu'il vient de la source distante.
      // Avec un ancien /api/relay non déployé, un 404 Vercel ne doit pas bloquer les autres chemins.
      const relayConfirmed=r.headers.get('x-mdb-relay')==='1';
      const direct=built===url;
      if((r.status===404 || r.status===410) && (direct||relayConfirmed)){
        const e=new Error('HTTP '+r.status); e.definitive=true; throw e;
      }
      lastErr=new Error('HTTP '+r.status);
    }catch(e){
      if(e&&e.definitive) throw e;
      lastErr=e;
    }
  }
  throw lastErr||new Error('réseau indisponible');
}

/* ---------------- Normalisation DVF ---------------- */
const toNum=v=>{if(v==null||v==='')return NaN;return parseFloat(String(v).replace(',','.').replace(/\s/g,''));};
function normType(t){t=(t||'').toLowerCase();
  if(t.includes('maison'))return'Maison';if(t.includes('appartement'))return'Appartement';
  if(t.includes('local'))return'Local';if(t.includes('dépendance')||t.includes('dependance'))return'Dépendance';return'Autre';}
function normRow(o){
  const surf=toNum(o.surface_reelle_bati??o.surface_relle_bati??o.surface_bati);
  const val=toNum(o.valeur_fonciere);
  const date=o.date_mutation||o.date||'';
  return{
    id:o.id_mutation||o.id||'', date, year:date?+date.slice(0,4):NaN,
    nature:o.nature_mutation||o.nature||'', typeRaw:o.type_local||'',
    type:normType(o.type_local), val, surface:surf,
    ppm:(val>0&&surf>0)?val/surf:NaN,
    pieces:toNum(o.nombre_pieces_principales), terrain:toNum(o.surface_terrain),
    lat:toNum(o.latitude??o.lat), lon:toNum(o.longitude??o.lon),
    parcelle:o.id_parcelle||'',
    localId:o.id_local||o.identifiant_local||o.id_local_mutation||'',
    lot:[o.lot1_numero,o.lot2_numero,o.lot3_numero,o.lot4_numero,o.lot5_numero].filter(Boolean).join(','),
    voie:[o.adresse_numero,o.adresse_suffixe,o.adresse_nom_voie].filter(Boolean).join(' ').trim()||o.adresse||'',
    commune:o.nom_commune||'', selected:true
  };
}
function haversine(la1,lo1,la2,lo2){const R=6371000,d=Math.PI/180;
  const dLa=(la2-la1)*d,dLo=(lo2-lo1)*d;
  const a=Math.sin(dLa/2)**2+Math.cos(la1*d)*Math.cos(la2*d)*Math.sin(dLo/2)**2;return 2*R*Math.asin(Math.sqrt(a));}
function minDistToAddr(row){let m=Infinity;for(const a of state.addresses){if(isFinite(row.lat)&&isFinite(row.lon))m=Math.min(m,haversine(a.lat,a.lon,row.lat,row.lon));}return m;}

// Supprime les doublons DVF correspondant au même bien / à la même mutation.
// La parcelle n'entre volontairement pas dans la clé : une même vente peut être
// répétée sur plusieurs parcelles alors qu'elle correspond au même comparable.
function dedupeRows(rows){
  const seen=new Set();
  return rows.filter(r=>{
    const identity=r.localId||r.lot||'';
    const geo=!r.id&&isFinite(r.lat)&&isFinite(r.lon)?`${r.lat.toFixed(5)},${r.lon.toFixed(5)}`:'';
    const key=[
      r.id||'', identity, r.date||'', r.type||'',
      isFinite(r.val)?Math.round(r.val*100)/100:'',
      isFinite(r.surface)?Math.round(r.surface*100)/100:'',
      isFinite(r.pieces)?r.pieces:'',
      (r.voie||'').trim().toLowerCase(),
      (r.commune||'').trim().toLowerCase(),geo
    ].join('|');
    if(seen.has(key)) return false;
    seen.add(key);return true;
  });
}

/* ---------------- Chargement (automatique) ---------------- */
async function loadData(){
  const info=document.getElementById('srcInfo');
  if(state.csvLoaded){ state.rawSource='csv'; info.textContent=state.raw.length+' lignes (CSV).'; return; }
  state.raw=[];
  // 1) Geo-DVF reste la source de référence. Une panne temporaire ne provoque
  // plus un basculement silencieux vers une autre base pouvant donner un jeu différent.
  let geoErr=null;
  try{ info.textContent='Chargement DVF…'; await loadGeodvf(); }catch(e){ geoErr=e;console.warn('geodvf',e); }
  if(!state.raw.length&&geoErr) throw new Error('Geo-DVF est momentanément indisponible. Réessaie dans quelques instants : aucune autre source n’est substituée afin de garder des résultats stables.');
  // Repli Cquest seulement si Geo-DVF a répondu mais ne possède réellement aucune donnée.
  if(!state.raw.length){ try{ info.textContent='Chargement DVF (repli)…'; await loadCquest(); }catch(e){ console.warn('cquest',e); } }
  if(!state.raw.length) throw new Error('DVF injoignable (réseau/relais). Charge un CSV geo-dvf dans ⚙, ou renseigne ton proxy.');
  info.textContent=state.raw.length+' lignes DVF.';
}
async function loadCquest(){
  const dist=+document.getElementById('radius').value;
  const all=[];
  for(const a of state.addresses){
    const url=`https://api.cquest.org/dvf?lat=${a.lat}&lon=${a.lon}&dist=${dist}`;
    const r=await robustFetch(url,'DVF repli');
    let j; try{ j=await r.json(); }catch(e){ const t=await r.text(); j=JSON.parse(t); }
    const arr=j.resultats||j.features?.map(f=>Object.assign({},f.properties,{lat:f.geometry?.coordinates?.[1],lon:f.geometry?.coordinates?.[0]}))||[];
    arr.forEach(o=>all.push(normRow(o)));
  }
  if(all.length){ state.raw=all.sort((a,b)=>stableRowId(a).localeCompare(stableRowId(b),'fr')); state.rawSource='cquest'; }
}
const communeCache=new Map();    // "insee:année" -> lignes normalisées
const communeInflight=new Map(); // "insee:année" -> Promise (téléchargement en cours, évite les doublons)
function fetchCommune(insee,dep,y,silent=false){
  const key=insee+':'+y;
  if(communeCache.has(key)) return Promise.resolve(communeCache.get(key));
  if(communeInflight.has(key)) return communeInflight.get(key);
  const p=robustFetch(`https://files.data.gouv.fr/geo-dvf/latest/csv/${y}/communes/${dep}/${insee}.csv`,silent?null:'geo-dvf '+y)
    .then(r=>r.text())
    .then(txt=>{const rows=Papa.parse(txt,{header:true,skipEmptyLines:true}).data.map(normRow);communeCache.set(key,rows);return rows;})
    .catch(e=>{if(e?.definitive){communeCache.set(key,[]);return [];}throw e;})
    .finally(()=>communeInflight.delete(key));
  communeInflight.set(key,p); return p;
}
async function loadGeodvf(){
  const yFrom=+document.getElementById('yFrom').value, yTo=+document.getElementById('yTo').value;
  const inseeArr=[...new Set(state.addresses.map(a=>a.insee).filter(Boolean))];
  if(!inseeArr.length)return;
  const tasks=[];
  for(const insee of inseeArr){
    const dep=insee.startsWith('97')||insee.startsWith('98')?insee.slice(0,3):insee.slice(0,2);
    for(let y=yTo;y>=yFrom;y--) tasks.push(fetchCommune(insee,dep,y));
  }
  const results=await Promise.all(tasks); // parallèle
  const all=[]; results.forEach(rows=>{for(const r of rows) all.push(r);});
  if(all.length){ state.raw=all.sort((a,b)=>stableRowId(a).localeCompare(stableRowId(b),'fr')); state.rawSource='geodvf'; }
}
// Préchargement ciblé : uniquement les communes réellement sélectionnées.
function prefetchCommune(insee){
  if(!insee) return;
  const dep=insee.startsWith('97')||insee.startsWith('98')?insee.slice(0,3):insee.slice(0,2);
  const yFrom=+document.getElementById('yFrom').value, yTo=+document.getElementById('yTo').value;
  for(let y=yTo;y>=yFrom;y--) fetchCommune(insee,dep,y,true);
}
function prefetchSelectedCommunes(){
  [...new Set(state.addresses.map(a=>a.insee).filter(Boolean))].forEach(prefetchCommune);
}
function loadCsv(ev){const f=ev.target.files[0];if(!f)return;
  Papa.parse(f,{header:true,skipEmptyLines:true,complete:res=>{
    state.raw=res.data.map(normRow); state.csvLoaded=true; state.rawSource='csv'; lastLoadSig='CSV';
    document.getElementById('srcInfo').textContent=state.raw.length+' lignes ('+f.name+').';
    const cs=document.getElementById('csvState'); if(cs)cs.textContent='✓ '+f.name+' ('+state.raw.length+' lignes).';
    setStatus('CSV chargé et prioritaire. Ajoute une adresse puis lance l’analyse.','ok');
  }});}

/* ---------------- Analyse ---------------- */
let lastLoadSig='';
function loadSig(){
  const insee=[...new Set(state.addresses.map(a=>a.insee).filter(Boolean))].sort().join(',');
  const base=insee+'|'+document.getElementById('yFrom').value+'|'+document.getElementById('yTo').value;
  // geo-dvf charge toute la commune : rayon/coordonnées ne nécessitent pas de nouveau téléchargement.
  // Le repli cquest, lui, dépend directement du point et du rayon.
  if(state.rawSource==='cquest'){
    const pts=state.addresses.map(a=>`${(+a.lat).toFixed(5)},${(+a.lon).toFixed(5)}`).sort().join(';');
    return base+'|r='+document.getElementById('radius').value+'|'+pts;
  }
  return base;
}
async function apply(){
  const b=document.getElementById('btnApply');
  if(!state.addresses.length){setStatus('Ajoutez au moins une adresse.','err');return;}
  const yf=+document.getElementById('yFrom').value,yt=+document.getElementById('yTo').value;
  if(!isFinite(yf)||!isFinite(yt)||yf>yt){setStatus('Période invalide : l’année de début doit être antérieure ou égale à l’année de fin.','err');return;}
  b.disabled=true;b.innerHTML='<span class="spinner"></span>Traitement…';
  try{
    const sig=loadSig();
    if(sig!==lastLoadSig || !state.raw.length){ await loadData(); lastLoadSig=sig; }
    const minEur=+document.getElementById('minEur').value||0, maxEur=+document.getElementById('maxEur').value||1e9;
    const dist=+document.getElementById('radius').value;
    const sectorRows=state.raw
      .filter(r=>r.val>0)
      .filter(r=>{r.dist=minDistToAddr(r);return r.dist<=dist;})
      .filter(r=>!isFinite(r.ppm)||(r.ppm>=minEur&&r.ppm<=maxEur));
    state.rows=dedupeRows(sectorRows);
    if(!state.rows.length){setStatus(`0 bien dans le secteur — ${state.raw.length} lignes chargées. Élargis le rayon, ou vérifie l'adresse.`,'err');return;}
    applyFilters();
    const drawn=mutMarkers.getLayers().length;
    if(state.filtered.length && !drawn){
      setStatus(`${state.filtered.length} biens filtrés mais 0 coordonnée exploitable (source sans lat/lon).`,'err');
    }else{
      const anom=state.anomaliesRemoved?` · ${state.anomaliesRemoved} anomalie${state.anomaliesRemoved>1?'s':''} retirée${state.anomaliesRemoved>1?'s':''}`:'';
      setStatus(`${state.raw.length} brut · ${state.rows.length} secteur · ${state.filtered.length} filtrés${anom} · ${drawn} points`,'ok');
    }
    if(state.view==='carte') fitMap();
  }catch(e){setStatus('Erreur : '+e.message,'err');}
  finally{b.disabled=false;b.textContent='Lancer l’analyse';}
}

function selectedTypes(){
  const opts=[...document.getElementById('fType').selectedOptions].map(o=>o.value);
  return opts.includes('Tous')||!opts.length?null:opts;
}

// Écarte automatiquement les prix au m² manifestement aberrants.
// Le calcul est fait séparément par type de bien afin de ne pas comparer
// une maison avec un appartement ou un local. Avec moins de 5 références
// d'un même type, aucun bien n'est supprimé automatiquement.
// Méthode : médiane + MAD (écart absolu médian), avec une tolérance minimale
// de ±50 % autour de la médiane pour rester volontairement conservateur.
function removePpmOutliers(rows){
  const groups=new Map();
  rows.forEach(r=>{
    if(!isFinite(r.ppm)||r.ppm<=0) return;
    const k=r.type||'Autre';
    if(!groups.has(k)) groups.set(k,[]);
    groups.get(k).push(r.ppm);
  });

  const bounds=new Map();
  groups.forEach((values,type)=>{
    if(values.length<5) return;
    const med=median(values);
    if(!isFinite(med)||med<=0) return;
    const deviations=values.map(v=>Math.abs(v-med));
    const mad=median(deviations);
    const robustSigma=isFinite(mad)?mad*1.4826:0;
    // Seuil statistique robuste, mais jamais plus serré que ±50 % de la médiane.
    const tolerance=Math.max(3.5*robustSigma, med*0.50);
    bounds.set(type,{low:Math.max(0,med-tolerance),high:med+tolerance,med});
  });

  let removed=0;
  const kept=rows.filter(r=>{
    if(!isFinite(r.ppm)||r.ppm<=0) return true;
    const b=bounds.get(r.type||'Autre');
    if(!b) return true;
    const ok=r.ppm>=b.low&&r.ppm<=b.high;
    if(!ok) removed++;
    return ok;
  });
  return {rows:kept,removed};
}

function applyFilters(){
  if(!state.rows.length){setStatus('Lancez d\'abord l\'analyse.','err');return;}
  const types=selectedTypes();
  const pMin=+document.getElementById('pMin').value||null,pMax=+document.getElementById('pMax').value||null;
  const sMin=+document.getElementById('sMin').value||null,sMax=+document.getElementById('sMax').value||null;
  const vMin=+document.getElementById('vMin').value||null,vMax=+document.getElementById('vMax').value||null;
  const ppmMin=+document.getElementById('ppmMin').value||null,ppmMax=+document.getElementById('ppmMax').value||null;
  const terrain=document.querySelector('input[name=terrain]:checked').value;
  const yFrom=+document.getElementById('yFrom').value,yTo=+document.getElementById('yTo').value;

  const filteredBeforeOutliers=state.rows.filter(r=>{
    if(types&&!types.includes(r.type))return false;
    if(isFinite(r.year)&&(r.year<yFrom||r.year>yTo))return false;
    if(pMin&&!(r.pieces>=pMin))return false; if(pMax&&!(r.pieces<=pMax))return false;
    if(sMin&&!(r.surface>=sMin))return false; if(sMax&&!(r.surface<=sMax))return false;
    if(vMin&&!(r.val>=vMin))return false; if(vMax&&!(r.val<=vMax))return false;
    if(ppmMin&&!(r.ppm>=ppmMin))return false; if(ppmMax&&!(r.ppm<=ppmMax))return false;
    if(terrain==='oui'&&!(r.terrain>0))return false; if(terrain==='non'&&r.terrain>0)return false;
    return true;
  });
  const cleaned=removePpmOutliers(filteredBeforeOutliers);
  state.filtered=cleaned.rows;
  state.anomaliesRemoved=cleaned.removed;
  state.filtered.forEach(r=>{if(typeof r.selected!=='boolean')r.selected=true;});
  drawMutations();
  try{ renderVendus(); }catch(err){ console.error('renderVendus:',err); }
  // Une nouvelle analyse invalide l'ancien enrichissement ET remet à zéro les filtres
  // de « Détermination du prix ». On évite ainsi qu'un filtre d'une recherche précédente
  // (ex. « Copro maison = Oui ») masque toutes les ventes de la nouvelle recherche.
  state.qual.rows=[]; state.qual.targetMatch=null; state.qual.targetPublic=null; state.qual.targetAudit=null; state.qual.enrichedCount=0; state.qual.enrichedAll=false; state.qual.dpeErrors=0; state.qual.publicEnrichedCount=0; state.qual.publicEnrichedAll=false; state.qual.publicErrors=0; state.qual.auditEnrichedCount=0; state.qual.auditEnrichedAll=false; state.qual.auditErrors=0; state.qual.selectionInitialized=false; state.qual.simpleStarted=false;
  state.qual.filters={type:'all',dpe:'all',surface:'all',pieces:'all',period:'all',floor:'all',copro:'all',terrain:'all',equipment:'all',works:'all',distance:'all',recency:'all',mutation:'all',ppmMin:'',ppmMax:''};
  state.qual.sort={key:'date',dir:-1};
  try{ renderQualifiedBase(); }catch(err){ console.error('renderQualifiedBase:',err); }
}

/* ---------------- Stats ---------------- */
function median(a){if(!a.length)return NaN;const s=[...a].sort((x,y)=>x-y);const m=s.length>>1;return s.length%2?s[m]:(s[m-1]+s[m])/2;}
function arrMin(a){let m=Infinity;for(const x of a)if(x<m)m=x;return isFinite(m)?m:NaN;}
function arrMax(a){let m=-Infinity;for(const x of a)if(x>m)m=x;return isFinite(m)?m:NaN;}
function mean(a){return a.length?a.reduce((x,y)=>x+y,0)/a.length:NaN;}
function quant(a,q){if(!a.length)return NaN;const s=[...a].sort((x,y)=>x-y);const p=(s.length-1)*q,b=Math.floor(p);return s[b+1]!==undefined?s[b]+(p-b)*(s[b+1]-s[b]):s[b];}
function sel(){return state.filtered.filter(r=>r.selected);}

/* ---------------- Rendu VENDUS ---------------- */
function renderVendus(){
  document.getElementById('emptyVendus').style.display='none';
  document.getElementById('vendusBody').style.display='block';
  const S=sel();
  const vals=S.map(r=>r.val).filter(isFinite);
  const ppms=S.map(r=>r.ppm).filter(isFinite);
  const surfs=S.map(r=>r.surface).filter(v=>v>0);

  const body=document.getElementById('vendusBody');
  body.innerHTML=`
  <div class="block">
    <div class="vendus-title-row">
      <h2 class="sec-title">Statistiques clés</h2>
      <button class="vendus-pdf-btn" onclick="exportComparablesVendusPdf()" title="Exporter uniquement les comparables cochés en PDF">⬇ Exporter les comparables en PDF</button>
    </div>
    <div class="stat-cards" id="statCards">${statCardsHtml(S,vals,ppms,surfs)}</div>
  </div>

  <div class="block">
    <div class="goldbar" onclick="toggleCollapse('detailStats',this)"><span class="caret">▼</span> Voir les statistiques détaillées</div>
    <div class="collapse" id="detailStats">
      <div class="detail-grid" id="detailGrid">${detailGridHtml(vals,ppms)}</div>
    </div>
  </div>

  <div class="block">
    <div class="darkbar" onclick="toggleCollapse('mutList',this)"><span class="caret">▼</span> <span id="mutLabel">Liste des mutations (${S.length} sélectionnées / ${state.filtered.length} total)</span></div>
    <div class="collapse" id="mutList">
      <div class="tbl-head" style="margin-top:12px">
        <button class="mini-btn" id="selBtn" onclick="toggleAll()">${S.length===state.filtered.length?'Tout désélectionner':'Tout sélectionner'} (${S.length} / ${state.filtered.length})</button>
      </div>
      <div class="tbl-scroll"><table id="mutTable">${mutTableHtml()}</table></div>
    </div>
  </div>

  <div class="block">
    <h2 class="sec-title">Évolution annuelle</h2>
    <div class="year-grid" id="yearGrid">${yearCardsHtml(S)}</div>
  </div>`;
}
function statCardsHtml(S,vals,ppms,surfs){
  return `
    <div class="scard"><div class="v">${f0(S.length)}</div><div class="l">Mutations sélectionnées</div></div>
    <div class="scard"><div class="v">${eur(mean(vals))}</div><div class="l">Prix moyen</div></div>
    <div class="scard"><div class="v">${f0(mean(ppms))}<span style="font-size:16px"> €/m²</span></div><div class="l">Prix m² moyen</div></div>
    <div class="scard"><div class="v">${f0(mean(surfs))}<span style="font-size:16px"> m²</span></div><div class="l">Surface moyenne</div></div>`;
}
function detailGridHtml(vals,ppms){
  return `${detailCol('Valeurs minimales',arrMin(vals),arrMin(ppms))}${detailCol('Valeurs maximales',arrMax(vals),arrMax(ppms))}${detailCol('Valeurs médianes',median(vals),median(ppms))}`;
}
// Met à jour les chiffres sans reconstruire le tableau (préserve l'ouverture de la liste)
function updateAggregates(){
  const S=sel();
  const vals=S.map(r=>r.val).filter(isFinite),ppms=S.map(r=>r.ppm).filter(isFinite),surfs=S.map(r=>r.surface).filter(v=>v>0);
  const sc=document.getElementById('statCards'); if(sc) sc.innerHTML=statCardsHtml(S,vals,ppms,surfs);
  const dg=document.getElementById('detailGrid'); if(dg) dg.innerHTML=detailGridHtml(vals,ppms);
  const yg=document.getElementById('yearGrid'); if(yg) yg.innerHTML=yearCardsHtml(S);
  const ml=document.getElementById('mutLabel'); if(ml) ml.textContent=`Liste des mutations (${S.length} sélectionnées / ${state.filtered.length} total)`;
  const sb=document.getElementById('selBtn'); if(sb) sb.textContent=`${S.length===state.filtered.length?'Tout désélectionner':'Tout sélectionner'} (${S.length} / ${state.filtered.length})`;
  drawMutations();
}
function detailCol(title,vf,pm){
  return `<div class="detail-col"><h4>${title}</h4>
    <div class="detail-row"><span class="k">Valeur foncière</span><span class="val">${eur(vf)}</span></div>
    <div class="detail-row"><span class="k">Prix/m²</span><span class="val">${ppmF(pm)}</span></div></div>`;
}
function toggleCollapse(id,el){document.getElementById(id).classList.toggle('closed');el.classList.toggle('closed');}

/* Table */
function mutTableHtml(){
  const hdr=[['','',''],['date','Date',''],['type','Type',''],['pieces','Pièces','num'],['surface','Surface','num'],['val','Valeur','num'],['ppm','Prix m²','num'],['voie','Adresse','']];
  let h='<thead><tr>';
  h+='<th style="width:30px"></th>';
  hdr.slice(1).forEach(([k,lab,cls])=>h+=`<th class="${cls}" onclick="sortBy('${k}')">${lab} ↕</th>`);
  h+='</tr></thead><tbody>';
  const arr=[...state.filtered].sort(sorter());
  arr.forEach(r=>{
    const idx=state.filtered.indexOf(r);
    h+=`<tr>
      <td><input class="ck" type="checkbox" ${r.selected?'checked':''} onchange="toggleRow(${idx},this.checked)"></td>
      <td>${r.date||'—'}</td>
      <td><span class="tag ${tagCls(r.type)}">${r.type}</span></td>
      <td class="num">${isFinite(r.pieces)?r.pieces+' p.':'—'}</td>
      <td class="num">${r.surface>0?f0(r.surface)+' m²':'—'}</td>
      <td class="num"><b>${eur(r.val)}</b></td>
      <td class="num">${ppmF(r.ppm)}</td>
      <td>${addrLink(r)}</td>
    </tr>`;
  });
  return h+'</tbody>';
}
function mapsUrl(r){
  const q = r.voie ? `${r.voie}, ${r.commune||''}` : (isFinite(r.lat)&&isFinite(r.lon)?`${r.lat},${r.lon}`:(r.commune||''));
  return 'https://www.google.com/maps/search/?api=1&query='+encodeURIComponent(q.trim());
}
function addrLink(r){
  const txt=r.voie||r.commune||'—';
  if(txt==='—') return '—';
  return `<a class="addr-link" href="${mapsUrl(r)}" target="_blank" rel="noopener" title="Ouvrir dans Google Maps">${txt} ↗</a>`;
}
function tagCls(t){return t==='Appartement'?'appart':t==='Maison'?'maison':t==='Local'?'local':'dep';}
function sorter(){const{key,dir}=state.sort;return(a,b)=>{let x=a[key],y=b[key];if(typeof x==='string'){x=x||'';y=y||'';return dir*x.localeCompare(y);}x=isFinite(x)?x:-Infinity;y=isFinite(y)?y:-Infinity;return dir*(x-y);};}
function sortBy(k){state.sort.key===k?state.sort.dir*=-1:(state.sort={key:k,dir:1});document.getElementById('mutTable').innerHTML=mutTableHtml();}
function syncQualifiedAfterVendusSelection(){
  if(!state.qual.target||!state.qual.rows.length)return;
  recalcQualifiedScores();
  if(state.view==='qualifies')renderQualifiedResults();
}
function toggleRow(i,v){state.filtered[i].selected=v;syncQualifiedAfterVendusSelection();refreshAgg();}
function toggleAll(){
  const all=state.filtered.every(r=>r.selected);
  state.filtered.forEach(r=>r.selected=!all);
  document.querySelectorAll('#mutTable .ck').forEach(cb=>cb.checked=!all);
  syncQualifiedAfterVendusSelection();
  updateAggregates();
}
let statTimer;
function refreshAgg(){clearTimeout(statTimer);statTimer=setTimeout(updateAggregates,120);}

/* Année */
function yearCardsHtml(S){
  const by={};S.forEach(r=>{if(!isFinite(r.year))return;(by[r.year]=by[r.year]||[]).push(r);});
  const years=Object.keys(by).map(Number).sort();
  let prevPpm=null,prevVf=null,out='';
  years.forEach(y=>{
    const g=by[y];const vf=mean(g.map(r=>r.val).filter(isFinite));const pm=mean(g.map(r=>r.ppm).filter(isFinite));
    const cVf=prevVf!=null?(vf/prevVf-1)*100:null, cPm=prevPpm!=null?(pm/prevPpm-1)*100:null;
    out+=`<div class="year-card"><div class="yh">Année <div class="yr">${y}</div></div>
      <div class="yb">
        <div><div class="kk">VF moyenne</div><div class="vv">${eur(vf)}</div>${chg(cVf)}</div>
        <div><div class="kk">Prix/m² moyen</div><div class="vv">${f0(pm)} €/m²</div>${chg(cPm)}</div>
      </div></div>`;
    prevVf=vf;prevPpm=pm;
  });
  return out||'<div class="placeholder">Pas de données annuelles.</div>';
}
function chg(c){if(c==null)return'<div class="chg zero">—</div>';const cls=c>0.05?'pos':c<-0.05?'neg':'zero';const s=c>0?'+':'';return`<div class="chg ${cls}">${s}${c.toFixed(1)}%</div>`;}




/* =========================================================
   DÉTERMINATION DU PRIX — ÉTAPE 1 TER · TRAVAUX · DVF + DPE/AUDIT ADEME + BDNB + RNIC + OSM
   ========================================================= */
const DPE_API='https://data.ademe.fr/data-fair/api/v1/datasets/dpe03existant/lines';
const DPE_META='https://data.ademe.fr/data-fair/api/v1/datasets/dpe03existant';
const DPE_BASE_FIELDS=['numero_dpe','etiquette_dpe','etiquette_ges','date_etablissement_dpe','date_fin_validite_dpe','surface_habitable_logement','annee_construction','periode_construction','type_batiment','adresse_brut','adresse_ban','code_postal_ban','nom_commune_ban','numero_voie_ban','nom_rue_ban'];
const DPE_OPTIONAL_FIELDS=['numero_immatriculation_copropriete','identifiant_ban','id_rnb','compl_etage_appartement','num_etage_appartement','numero_etage_appartement','nombre_niveau_immeuble','nombre_niveau_logement','logement_traversant','position_logement_dans_immeuble','orientation_logement'];
const DPE_DYNAMIC_FIELD_RE=/(orientation|baie|vitr|fenetre|exposition)/i;
const OVERPASS_API='https://overpass-api.de/api/interpreter';
const BDNB_ADDRESS_API='https://api.bdnb.io/v1/bdnb/donnees/batiment_groupe_complet/adresse';
const RNIC_DATASET_API='https://www.data.gouv.fr/api/1/datasets/registre-national-dimmatriculation-des-coproprietes/';
const RNIC_TABULAR_BASE='https://tabular-api.data.gouv.fr/api/resources';
const BDNB_PARCEL_API='https://api.bdnb.io/v1/bdnb/donnees/batiment_groupe_complet/parcelle';
const COPRO_LOCK_PREFIX='dvf-copro-positive-v4:';
const COPRO_LEGACY_PREFIXES=['dvf-copro-positive-v3:','dvf-copro-lock-v2:'];
const coproDecisionCache=new Map();
const AUDIT_API='https://data.ademe.fr/data-fair/api/v1/datasets/audit-opendata/lines';
const AUDIT_META='https://data.ademe.fr/data-fair/api/v1/datasets/audit-opendata';
const INTERIOR_STATES=[
  ['UNKNOWN','Inconnu'],['RENOVATED','Neuf / entièrement rénové'],['VERY_GOOD','Très bon état'],['GOOD','Bon état'],['REFRESH','À rafraîchir'],['RENOVATE','À rénover']
];
const INTERIOR_RANK={RENOVATED:0,VERY_GOOD:1,GOOD:2,REFRESH:3,RENOVATE:4};
// Coefficients indicatifs et modifiables : référence = Bon état (0%).
// Ils servent à homogénéiser l'état du comparable avec celui du bien cible.
const INTERIOR_COEF_DEFAULT={UNKNOWN:0,RENOVATED:12,VERY_GOOD:7,GOOD:0,REFRESH:-5,RENOVATE:-12};

const PERIODS=[
  ['pre1948','Avant 1948'],['1948_1974','1948–1974'],['1975_1988','1975–1988'],['1989_2000','1989–2000'],
  ['2001_2012','2001–2012'],['2013_2020','2013–2020'],['post2020','Après 2020']
];
const periodIndex=Object.fromEntries(PERIODS.map((p,i)=>[p[0],i]));
const ORIENTATIONS=['N','NE','E','SE','S','SO','O','NO'];
const sleep=ms=>new Promise(r=>setTimeout(r,ms));
function esc(v){return String(v??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));}
function normTxt(v){return String(v||'').normalize('NFD').replace(/[\u0300-\u036f]/g,'').toLowerCase().replace(/[^a-z0-9 ]/g,' ').replace(/\b(rue|avenue|av|boulevard|bd|route|chemin|allee|impasse|place|quai|cours|de|du|des|la|le|les|d|l)\b/g,' ').replace(/\s+/g,' ').trim();}
function normKey(v){return String(v||'').normalize('NFD').replace(/[\u0300-\u036f]/g,'').toLowerCase().replace(/[^a-z0-9]+/g,' ').trim();}
function houseNum(v){const m=String(v||'').trim().match(/^(\d+[a-zA-Z]?)/);return m?m[1].toLowerCase():'';}
function rowKey(r){return [r.id,r.date,r.voie,r.commune,r.surface,r.val].join('|');}
function pctGap(a,b){return isFinite(a)&&isFinite(b)&&b>0?Math.abs(a-b)/b:NaN;}
function monthsBetween(a,b){if(!a||!b)return NaN;const da=new Date(a),db=new Date(b);if(isNaN(da)||isNaN(db))return NaN;return Math.abs((da-db)/(1000*60*60*24*30.4375));}
function signedMonthsBetween(a,b){if(!a||!b)return NaN;const da=new Date(a),db=new Date(b);if(isNaN(da)||isNaN(db))return NaN;return (da-db)/(1000*60*60*24*30.4375);}
function monthsAgo(date){if(!date)return NaN;const d=new Date(date);if(isNaN(d))return NaN;return Math.max(0,(Date.now()-d)/(1000*60*60*24*30.4375));}
function periodFromYear(y){y=+y;if(!isFinite(y)||y<=0)return null;if(y<1948)return'pre1948';if(y<=1974)return'1948_1974';if(y<=1988)return'1975_1988';if(y<=2000)return'1989_2000';if(y<=2012)return'2001_2012';if(y<=2020)return'2013_2020';return'post2020';}
function periodFromDpe(d){if(!d)return null;const y=+d.annee_construction;if(isFinite(y)&&y>0)return periodFromYear(y);const p=String(d.periode_construction||'');const nums=p.match(/\d{4}/g);if(nums&&nums.length){const ys=nums.map(Number);return periodFromYear(Math.round(ys.reduce((a,b)=>a+b,0)/ys.length));}if(/avant|<|inf/i.test(p)&&/1948/.test(p))return'pre1948';return null;}
function periodLabel(k){return PERIODS.find(p=>p[0]===k)?.[1]||'—';}
function dpeBadge(letter){const l=DPE_ORDER.includes(letter)?letter:null;return `<span class="dpebadge ${l||'none'}">${l||'—'}</span>`;}
function confidenceLabel(c){return c==='high'?'✓ certain':c==='medium'?'~ probable':c==='low'?'? incertain':'non trouvé';}
function qualityInfo(score){if(score>=90)return['Excellent comparable','quality-excellent'];if(score>=75)return['Très bon','quality-verygood'];if(score>=60)return['Bon','quality-good'];return['À examiner','quality-review'];}
function qualifiedSourceRows(){return sel();}
function defaultTargetType(){const t=selectedTypes(),src=qualifiedSourceRows();return t&&t.length===1?t[0]:(src.find(r=>r.type==='Appartement')?'Appartement':(src[0]?.type||'Appartement'));}
function parseBoolish(v){if(v===true||v===1||v==='1')return true;if(v===false||v===0||v==='0')return false;const n=normTxt(v);if(['oui','yes','vrai','true'].includes(n))return true;if(['non','no','faux','false'].includes(n))return false;return null;}
function boolLabel(v){return v===true?'Oui':v===false?'Non':'—';}
function parseFloor(v){if(v==null||v==='')return NaN;const n=normTxt(v);if(/rdc|rez de chaussee|rez chaussee/.test(n))return 0;const m=String(v).match(/-?\d+/);return m?+m[0]:NaN;}
function floorLabel(v){if(!isFinite(v))return'—';return +v===0?'RDC':(+v===1?'1er':f0(v)+'e');}
function normalizeOrientation(v){if(v==null||v==='')return null;let n=normTxt(v).toUpperCase();n=n.replace(/NORD/g,'N').replace(/SUD/g,'S').replace(/EST/g,'E').replace(/OUEST/g,'O').replace(/[^NSEO]/g,'');const map={'N':'N','NE':'NE','E':'E','SE':'SE','S':'S','SO':'SO','O':'O','NO':'NO'};return map[n]||null;}
function firstDefined(o,keys){for(const k of keys){if(o&&o[k]!=null&&o[k]!=='')return o[k];}return null;}
function findField(o,patterns,reject=[]){if(!o)return null;for(const [k,v] of Object.entries(o)){if(v==null||v==='')continue;const nk=normKey(k);if(patterns.every(p=>nk.includes(p))&&!reject.some(p=>nk.includes(p)))return {key:k,value:v};}return null;}
function meaningful(v){return !(v==null||v===''||String(v).trim()===''||String(v).toLowerCase()==='nan');}
function interiorLabel(v){return INTERIOR_STATES.find(x=>x[0]===v)?.[1]||'Inconnu';}
function interiorClass(v){return v==='RENOVATED'||v==='VERY_GOOD'?'low':v==='GOOD'?'mid':v==='REFRESH'||v==='RENOVATE'?'high':'unknown';}
function defaultInteriorCoef(v){return Number(INTERIOR_COEF_DEFAULT[v]??0);}
function pct1(v){if(!isFinite(v))return'—';return`${v>0?'+':''}${(+v).toLocaleString('fr-FR',{minimumFractionDigits:1,maximumFractionDigits:1})} %`;}
function targetInteriorCoef(){const t=state.qual.target||{};return isFinite(+t.interiorCoef)?+t.interiorCoef:defaultInteriorCoef(t.interior||'UNKNOWN');}
function comparableInteriorCoef(r){const m=r?.workManual||{};if(isFinite(+m.interiorCoef))return +m.interiorCoef;return defaultInteriorCoef(m.interior||'UNKNOWN');}
function stateCorrectionFactor(r){const tc=targetInteriorCoef(),cc=comparableInteriorCoef(r),den=1+cc/100;if(den<=0)return 1;return (1+tc/100)/den;}
function stateCorrectionPct(r){return (stateCorrectionFactor(r)-1)*100;}
function correctionMode(){return state.qual.target?.correctionMode||'STATE';}
function useStateCorrection(){return correctionMode()==='STATE'||correctionMode()==='BOTH';}
function useBudgetCorrection(){return correctionMode()==='BUDGET'||correctionMode()==='BOTH';}
function moneyNum(v){if(v==null||v==='')return NaN;const n=Number(String(v).replace(/[^0-9,.-]/g,'').replace(',','.'));return isFinite(n)?n:NaN;}


// --- Schéma DPE dynamique : on ne demande que les champs réellement publiés par l'ADEME ---
async function getDpeSelect(){
  if(!dpeMetaPromise)dpeMetaPromise=(async()=>{
    const r=await robustFetch(DPE_META,null),j=await r.json(),schema=j.schema||[],keys=new Set(schema.map(x=>x.key).filter(Boolean));
    if(!keys.size)return DPE_BASE_FIELDS.join(',');
    const base=DPE_BASE_FIELDS.filter(k=>keys.has(k));
    const optional=DPE_OPTIONAL_FIELDS.filter(k=>keys.has(k));
    const dynamic=schema.map(x=>x.key).filter(k=>k&&DPE_DYNAMIC_FIELD_RE.test(k)).slice(0,28);
    return [...new Set([...base,...optional,...dynamic])].join(',');
  })();
  try{return await dpeMetaPromise;}catch(e){dpeMetaPromise=null;console.warn('Métadonnées ADEME',e);return DPE_BASE_FIELDS.join(',');}
}


// --- Étape 1 bis : orientation DPE, annexes DVF, OSM et extérieur potentiel ---
const osmCache=new Map();
function directionFromAny(v){
  if(v==null||v==='')return null;
  const direct=normalizeOrientation(v);if(direct)return direct;
  const n=normTxt(v);
  if(/sud.*ouest|sud ouest/.test(n))return'SO';if(/sud.*est|sud est/.test(n))return'SE';if(/nord.*ouest|nord ouest/.test(n))return'NO';if(/nord.*est|nord est/.test(n))return'NE';
  if(/\bsud\b/.test(n))return'S';if(/\bnord\b/.test(n))return'N';if(/\best\b/.test(n))return'E';if(/\bouest\b/.test(n))return'O';return null;
}
function deriveDpeOrientation(c){
  const explicit=directionFromAny(firstDefined(c,['orientation_logement','exposition_logement','orientation_principale']));
  if(explicit)return{value:explicit,method:'explicite',confidence:'medium'};
  const scores={N:0,NE:0,E:0,SE:0,S:0,SO:0,O:0,NO:0};
  for(const [k,v] of Object.entries(c||{})){
    const nk=normKey(k);if(!/(orientation|exposition|baie|vitr|fenetre)/.test(nk))continue;
    let d=directionFromAny(v);
    if(!d){for(const x of ORIENTATIONS){const long={N:'nord',NE:'nord est',E:'est',SE:'sud est',S:'sud',SO:'sud ouest',O:'ouest',NO:'nord ouest'}[x];if(nk.includes(long)||nk.split(' ').includes(long)){d=x;break;}}}
    if(!d)continue;
    let w=1;const nv=toNum(v);if(isFinite(nv)&&nv>0&&/(surface|m2|aire)/.test(nk))w=Math.min(30,nv);
    scores[d]+=w;
  }
  const vals=Object.entries(scores).filter(([,v])=>v>0).sort((a,b)=>b[1]-a[1]);
  if(!vals.length)return{value:null,method:'',confidence:'none'};
  if(vals.length>1&&vals[1][1]>=vals[0][1]*.72)return{value:vals[0][0]+'/'+vals[1][0],method:'baies / orientations DPE',confidence:'low'};
  return{value:vals[0][0],method:'baies / orientations DPE',confidence:'low'};
}
function mainOrientationForScore(di){const v=di?.orientation;if(!v)return null;return String(v).split('/')[0]||null;}
function annexeInfoForRow(r){const p=r?.qMutationProfile;if(!p)return null;return{dependences:p.dependences||0,primary:p.primaryAssets?.size||0,parcels:p.parcels?.size||0};}
function osmFeatureCenter(e){if(isFinite(+e.lat)&&isFinite(+e.lon))return{lat:+e.lat,lon:+e.lon};if(e.center&&isFinite(+e.center.lat)&&isFinite(+e.center.lon))return{lat:+e.center.lat,lon:+e.center.lon};if(Array.isArray(e.geometry)&&e.geometry.length){let a=0,b=0,n=0;for(const g of e.geometry){if(isFinite(+g.lat)&&isFinite(+g.lon)){a+=+g.lat;b+=+g.lon;n++;}}if(n)return{lat:a/n,lon:b/n};}return null;}
function polygonAreaMeters(geom){if(!Array.isArray(geom)||geom.length<3)return NaN;const lat0=geom.reduce((a,p)=>a+(+p.lat||0),0)/geom.length*Math.PI/180;const R=6371000,pts=geom.map(p=>({x:R*(+p.lon)*Math.PI/180*Math.cos(lat0),y:R*(+p.lat)*Math.PI/180}));let area=0;for(let i=0,j=pts.length-1;i<pts.length;j=i++)area+=(pts[j].x*pts[i].y-pts[i].x*pts[j].y);return Math.abs(area/2);}
function pointInPolygon(lat,lon,geom){if(!Array.isArray(geom)||geom.length<3)return false;let inside=false;for(let i=0,j=geom.length-1;i<geom.length;j=i++){const xi=+geom[i].lon,yi=+geom[i].lat,xj=+geom[j].lon,yj=+geom[j].lat;const inter=((yi>lat)!==(yj>lat))&&(lon<(xj-xi)*(lat-yi)/(yj-yi||1e-12)+xi);if(inter)inside=!inside;}return inside;}
function normalizeOsm(elements,lat,lon){
  const info={found:false,elevator:false,parking:false,garage:false,balcony:false,terrace:false,garden:false,parkingDetail:'',nearestBuilding:null,buildingFootprint:NaN,buildingConfidence:'none',signals:[]};
  let best=null,bestD=Infinity;
  for(const e of elements||[]){const t=e.tags||{},c=osmFeatureCenter(e),d=c?haversine(lat,lon,c.lat,c.lon):Infinity;const building=String(t.building||'');
    if(t.highway==='elevator'||t.elevator==='yes'){if(d<=35){info.elevator=true;info.signals.push('ascenseur');}}
    if(t.amenity==='parking'||t.amenity==='parking_space'||t.amenity==='parking_entrance'){if(d<=35){info.parking=true;info.parkingDetail=t.parking||t.access||'';info.signals.push('parking');}}
    if(['garage','garages','carport','parking'].includes(building)||t.parking==='garage_boxes'){if(d<=35){info.garage=true;info.signals.push('garage');}}
    if(t['building:part']==='balcony'||t.balcony==='yes'){if(d<=30){info.balcony=true;info.signals.push('balcon');}}
    if(t['building:part']==='terrace'||t.terrace==='yes'){if(d<=30){info.terrace=true;info.signals.push('terrasse');}}
    if(t.leisure==='garden'||t['garden:type']||t.garden==='yes'){if(d<=35){info.garden=true;info.signals.push('jardin');}}
    if(building&&!['garage','garages','carport','parking','shed'].includes(building)){
      const contained=pointInPolygon(lat,lon,e.geometry);const rank=contained?-1:d;
      if(rank<bestD&&d<=45){bestD=rank;best={e,d,contained,area:polygonAreaMeters(e.geometry)};}
    }
  }
  if(best){info.nearestBuilding=best.e;info.buildingFootprint=best.area;info.buildingConfidence=best.contained?'medium':'low';}
  info.signals=[...new Set(info.signals)];info.found=info.signals.length>0||!!best;return info;
}
async function queryOsmAround(lat,lon){
  if(!isFinite(lat)||!isFinite(lon))return null;const key=(+lat).toFixed(5)+'|'+(+lon).toFixed(5);if(osmCache.has(key))return osmCache.get(key);
  const p=(async()=>{const q=`[out:json][timeout:7];(nwr(around:38,${lat},${lon})["highway"="elevator"];nwr(around:38,${lat},${lon})["elevator"="yes"];nwr(around:38,${lat},${lon})["amenity"~"^(parking|parking_space|parking_entrance)$"];nwr(around:38,${lat},${lon})["building"~"^(garage|garages|carport|parking)$"];nwr(around:32,${lat},${lon})["building:part"="balcony"];nwr(around:32,${lat},${lon})["building:part"="terrace"];nwr(around:38,${lat},${lon})["leisure"="garden"];nwr(around:38,${lat},${lon})["garden:type"];nwr(around:45,${lat},${lon})["building"];);out tags center geom;`;
    const r=await robustFetch(OVERPASS_API+'?data='+encodeURIComponent(q),null),j=await r.json();return normalizeOsm(j.elements||[],+lat,+lon);})();
  osmCache.set(key,p);try{return await p;}catch(e){osmCache.delete(key);console.warn('OSM Overpass',e);throw e;}
}
function exteriorPotential(row){const o=row?.publicInfo?.osm,terrain=+row?.terrain;if(!(terrain>0)||!o||o.buildingConfidence!=='medium'||!(o.buildingFootprint>0))return NaN;return Math.max(0,terrain-o.buildingFootprint);}
function freeFeaturesHtml(r){const chips=[],a=annexeInfoForRow(r),o=r.publicInfo?.osm;if(a?.dependences)chips.push(`<span class="feature-chip gold" title="Dépendance enregistrée dans la même mutation DVF">DVF · ${a.dependences} dépend.</span>`);if(o?.elevator)chips.push('<span class="feature-chip green">OSM · ascenseur</span>');if(o?.garage)chips.push('<span class="feature-chip green">OSM · garage</span>');if(o?.parking)chips.push('<span class="feature-chip blue">OSM · parking</span>');if(o?.balcony)chips.push('<span class="feature-chip blue">OSM · balcon</span>');if(o?.terrace)chips.push('<span class="feature-chip blue">OSM · terrasse</span>');if(o?.garden)chips.push('<span class="feature-chip green">OSM · jardin</span>');const ext=exteriorPotential(r);if(isFinite(ext))chips.push(`<span class="feature-chip gold">Extérieur ≈ ${f0(ext)} m²</span>`);if(!chips.length)return'<span class="conf">aucun signal gratuit fiable</span>';return`<div class="feature-stack">${chips.join('')}</div><span class="feature-note">OSM = indice cartographique, pas preuve d\'appartenance au lot.</span>`;}

// --- Qualité de mutation / micro-localisation / médiane secteur ---
function buildMutationProfiles(){
  const map=new Map(),source=(state.raw&&state.raw.length)?state.raw:state.rows;
  for(const r of source){if(!r.id)continue;let p=map.get(r.id);if(!p){p={parcels:new Set(),assets:new Set(),primaryAssets:new Set(),dependences:0,natures:new Set()};map.set(r.id,p);}if(r.parcelle)p.parcels.add(String(r.parcelle));const asset=r.localId?('local:'+r.localId):(r.lot?('lot:'+r.lot):[normTxt(r.voie),r.type,isFinite(r.surface)?r.surface:'',isFinite(r.pieces)?r.pieces:''].join('|'));p.assets.add(asset);if(r.type==='Dépendance')p.dependences++;else p.primaryAssets.add(asset);if(r.nature)p.natures.add(normTxt(r.nature));}
  return map;
}
function classifyMutation(r,profiles){const nature=String(r.nature||'').trim(),nn=normTxt(nature),p=r.id?profiles.get(r.id):null,reasons=[];if(!r.id)reasons.push('identifiant mutation absent');if(nn!=='vente')reasons.push(nature||'nature inconnue');if(p&&p.parcels.size>1)reasons.push(p.parcels.size+' parcelles');if(p&&p.primaryAssets.size>1)reasons.push(p.primaryAssets.size+' biens principaux');const unknown=!r.id||!nature;const simple=!unknown&&nn==='vente'&&(!p||p.parcels.size<=1)&&(!p||p.primaryAssets.size<=1);if(p?.dependences)reasons.push(p.dependences+' dépendance'+(p.dependences>1?'s':'')+' associée'+(p.dependences>1?'s':''));return {simple,status:simple?'simple':(unknown?'unknown':'complex'),reason:simple?(p?.dependences?('Vente simple · '+p.dependences+' dépendance'+(p.dependences>1?'s':'')):'Vente simple'):(reasons.join(' · ')||'À vérifier'),nature:nature||'—',profile:p};}
function targetStreetSimilarity(r){const target=normTxt(state.addresses[0]?.label||''),rt=normTxt(r.voie||'');if(!target||!rt)return 0;const toks=rt.split(' ').filter(x=>x.length>2&&!/^\d+$/.test(x));if(!toks.length)return 0;return toks.filter(x=>target.includes(x)).length/toks.length;}
function microLocationInfo(r){const sameStreet=targetStreetSimilarity(r)>=.8;let bonus=0,label='';if(sameStreet)bonus+=3;if(isFinite(r.dist)){if(r.dist<=100)bonus+=2;else if(r.dist<=200)bonus+=1;}bonus=Math.min(5,bonus);if(sameStreet&&isFinite(r.dist)&&r.dist<=100)label='Même rue · très proche';else if(sameStreet)label='Même rue';else if(isFinite(r.dist)&&r.dist<=100)label='Très proche';else if(isFinite(r.dist)&&r.dist<=200)label='Proximité forte';return{sameStreet,bonus,label};}
function qualifiedSectorMedian(){const t=state.qual.target||{},src=qualifiedSourceRows();let pool=src.filter(r=>isFinite(r.ppm)&&(!t.type||r.type===t.type));if(pool.length<3)pool=src.filter(r=>isFinite(r.ppm));return median(pool.map(r=>r.ppm));}
function medianGapPct(r){const m=qualifiedSectorMedian();return isFinite(m)&&m>0&&isFinite(r.ppm)?(r.ppm/m-1)*100:NaN;}
function medianGapHtml(r){const p=medianGapPct(r);if(!isFinite(p))return'—';const a=Math.abs(p),cls=a<=10?'gap-good':a<=20?'gap-mid':'gap-bad';return`<span class="${cls}">${p>=0?'+':''}${p.toFixed(1)}%</span>`;}
function mutationBadgeHtml(r){const m=r.qMutation||{status:'unknown',reason:'Non analysée',nature:r.nature||'—'};const cls=m.simple?'simple':(m.status==='unknown'?'unknown':'warn');return`<span class="mutationpill ${cls}" title="${esc(m.reason)}">${m.simple?'✓ Vente simple':'⚠ À vérifier'}</span><span class="conf">${esc(m.reason)}</span>`;}
function microLocationHtml(r){const m=r.qMicro||microLocationInfo(r);return m.label?`<span class="microtag">${esc(m.label)}</span>`:'';}

// --- DPE ADEME ---
function makePseudoTargetRow(t){const a=state.addresses[0]||{};return{voie:a.label||'',commune:'',surface:t.surface,date:'',type:t.type,terrain:t.terrain,lat:a.lat,lon:a.lon};}
async function queryDpeAddress(query){
  const key=normTxt(query);if(!key)return[];if(dpeQueryCache.has(key))return dpeQueryCache.get(key);
  const p=(async()=>{const select=await getDpeSelect();const params=new URLSearchParams({size:'40',q:query,q_fields:'adresse_ban,adresse_brut',select,sort:'-_score,-date_etablissement_dpe'});const r=await robustFetch(DPE_API+'?'+params.toString(),null);const j=await r.json();return Array.isArray(j.results)?j.results:[];})();
  dpeQueryCache.set(key,p);try{return await p;}catch(e){dpeQueryCache.delete(key);console.warn('DPE ADEME',query,e);throw e;}
}
function streetSimilarity(row,c){const rt=normTxt(row.voie),ct=normTxt(c.adresse_ban||c.adresse_brut);if(!rt||!ct)return 0;const toks=rt.split(' ').filter(x=>x.length>2&&!/^\d+$/.test(x));if(!toks.length)return 0;const hits=toks.filter(x=>ct.includes(x)).length;return hits/toks.length;}
function dpePropertyType(c){const n=normTxt(c?.type_batiment||c?.type_logement||'');if(/maison|individuel/.test(n))return'Maison';if(/appartement|collectif/.test(n))return'Appartement';return'';}
function chooseDpeCandidate(row,cands){
  if(!cands.length)return null;const rn=houseNum(row.voie);let best=null,bestScore=-1;
  for(const c of cands){
    const addr=c.adresse_ban||c.adresse_brut||'',cn=houseNum(addr),sim=streetSimilarity(row,c),surf=+c.surface_habitable_logement,sg=pctGap(surf,row.surface),ct=dpePropertyType(c);
    if(['Maison','Appartement'].includes(row.type)&&ct&&ct!==row.type)continue;
    const rel=signedMonthsBetween(c.date_etablissement_dpe,row.date),md=isFinite(rel)?Math.abs(rel):NaN;let sc=0;
    if(ct&&ct===row.type)sc+=10;if(rn&&cn&&rn===cn)sc+=40;else if(rn&&cn)sc-=25;sc+=Math.round(sim*25);if(row.commune&&normTxt(addr).includes(normTxt(row.commune)))sc+=8;
    if(isFinite(sg)){if(sg<=.03)sc+=25;else if(sg<=.08)sc+=22;else if(sg<=.15)sc+=16;else if(sg<=.25)sc+=8;else if(sg<=.40)sc+=2;}
    if(isFinite(rel)){
      if(rel<=0){if(md<=6)sc+=12;else if(md<=18)sc+=9;else if(md<=36)sc+=4;else if(md>60)sc-=8;}
      else if(rel<=3)sc+=4;else if(rel<=12)sc-=4;else sc-=12;
    }
    if(c.etiquette_dpe)sc+=3;const tie=String(c.numero_dpe||'');
    if(sc>bestScore||(sc===bestScore&&tie<String(best?.c?.numero_dpe||'~'))){bestScore=sc;best={c,sg,md,rel,exactNum:rn&&cn&&rn===cn,streetSim:sim,score:sc};}
  }
  if(!best||best.score<30)return null;let confidence='low';
  const temporalOk=!row.date||!isFinite(best.rel)||(best.rel<=3&&best.rel>=-30);
  if(best.exactNum&&isFinite(best.sg)&&best.sg<=.10&&temporalOk)confidence='high';
  else if(((best.exactNum&&(!isFinite(best.sg)||best.sg<=.25))||(best.streetSim>=.8&&isFinite(best.sg)&&best.sg<=.12))&&(!isFinite(best.rel)||best.rel<=6))confidence='medium';
  if(confidence==='low')return null;
  return normalizeDpeInfo(best.c,confidence,best.score);
}
function orientationFromDpe(c){return deriveDpeOrientation(c).value;}
function normalizeDpeInfo(c,confidence,matchScore){const floorRaw=firstDefined(c,['compl_etage_appartement','num_etage_appartement','numero_etage_appartement']);return{
  dpe:DPE_ORDER.includes(c.etiquette_dpe)?c.etiquette_dpe:null,ges:DPE_ORDER.includes(c.etiquette_ges)?c.etiquette_ges:null,numero:c.numero_dpe||'',date:c.date_etablissement_dpe||'',surface:+c.surface_habitable_logement||NaN,
  year:+c.annee_construction||NaN,period:periodFromDpe(c),periodRaw:c.periode_construction||'',type:c.type_batiment||'',address:c.adresse_ban||c.adresse_brut||'',confidence,matchScore,
  floor:parseFloor(floorRaw),buildingLevels:+firstDefined(c,['nombre_niveau_immeuble'])||NaN,homeLevels:+firstDefined(c,['nombre_niveau_logement'])||NaN,traversant:parseBoolish(firstDefined(c,['logement_traversant'])),position:firstDefined(c,['position_logement_dans_immeuble'])||'',orientation:orientationFromDpe(c),orientationInfo:deriveDpeOrientation(c),
  coproId:firstDefined(c,['numero_immatriculation_copropriete'])||'',banId:firstDefined(c,['identifiant_ban'])||'',rnbId:firstDefined(c,['id_rnb'])||''
};}
async function lookupTargetDpe(t){const a=state.addresses[0];if(!a)return null;const pseudo=makePseudoTargetRow(t);pseudo.voie=a.label;const cands=await queryDpeAddress(a.label);return chooseDpeCandidate(pseudo,cands);}
async function enrichRowsDpe(rows,progress){const groups=new Map();rows.forEach(r=>{if(r.dpeChecked===undefined&&r.dpeInfo!==undefined)r.dpeChecked=true;const k=normTxt([r.voie,r.commune].filter(Boolean).join(' '));if(k&&!r.dpeChecked){if(!groups.has(k))groups.set(k,[]);groups.get(k).push(r);}});const entries=[...groups.values()];let done=0,errors=0,cursor=0;async function worker(){while(cursor<entries.length){const group=entries[cursor++],sample=group[0];try{const cands=await queryDpeAddress([sample.voie,sample.commune].filter(Boolean).join(' '));group.forEach(r=>{r.dpeInfo=chooseDpeCandidate(r,cands);r.dpeChecked=true;saveStableRow(r);});}catch(e){errors++;group.forEach(r=>{r.dpeChecked=false;delete r.dpeInfo;});}done++;progress(done,entries.length,errors);await sleep(120);}}await Promise.all(Array.from({length:Math.min(5,entries.length)},worker));return{groups:entries.length,errors};}

// --- Étape 1 ter : AUDIT ADEME / travaux ---
async function getAuditMeta(){
  if(!auditMetaPromise)auditMetaPromise=(async()=>{
    const r=await robustFetch(AUDIT_META,null),j=await r.json(),schema=j.schema||[],keys=schema.map(x=>x.key).filter(Boolean);
    const pick=re=>keys.filter(k=>re.test(normKey(k)));
    const address=pick(/adresse|libelle.*adr|nom.*rue/).slice(0,8),surface=pick(/surface.*(habitable|logement|reference)|shab/).slice(0,6),date=pick(/date.*(audit|etablissement|realisation|visite)/).slice(0,6),id=pick(/numero.*audit|identifiant.*audit|num.*audit/).slice(0,4),cost=pick(/(cout|montant).*(trav|renov|scenario|etape|bouquet)|(trav|renov|scenario|etape|bouquet).*(cout|montant)/).slice(0,38),works=pick(/travaux|scenario|etape|bouquet|poste.*renov/).filter(k=>!cost.includes(k)).slice(0,20),energy=pick(/etiquette.*(dpe|energie)|classe.*(dpe|energie)|conso.*apres|gain.*energie/).slice(0,8);
    const select=[...new Set([...id,...address,...surface,...date,...cost,...works,...energy])].slice(0,72);return{keys,address,surface,date,id,cost,works,energy,select};
  })();
  try{return await auditMetaPromise;}catch(e){auditMetaPromise=null;console.warn('Métadonnées AUDIT ADEME',e);throw e;}
}
async function queryAuditAddress(query){
  const key=normTxt(query);if(!key)return[];if(auditQueryCache.has(key))return auditQueryCache.get(key);
  const p=(async()=>{const meta=await getAuditMeta();const params=new URLSearchParams({size:'30',q:query});if(meta.address.length)params.set('q_fields',meta.address.slice(0,4).join(','));if(meta.select.length)params.set('select',meta.select.join(','));const r=await robustFetch(AUDIT_API+'?'+params.toString(),null),j=await r.json();return Array.isArray(j.results)?j.results:[];})();
  auditQueryCache.set(key,p);try{return await p;}catch(e){auditQueryCache.delete(key);console.warn('AUDIT ADEME',query,e);throw e;}
}
function valueByMeta(c,fields){for(const k of fields||[]){if(meaningful(c?.[k]))return c[k];}return null;}
function numericByMeta(c,fields){for(const k of fields||[]){const n=moneyNum(c?.[k]);if(isFinite(n))return n;}return NaN;}
function auditCostInfo(c,meta){
  const vals=[];
  for(const k of meta.cost||[]){const n=moneyNum(c?.[k]);if(!isFinite(n)||n<=0||n>5000000)continue;const nk=normKey(k);vals.push({k,n,min:/min|minimum/.test(nk),max:/max|maximum/.test(nk),total:/total|global|ensemble|scenario|etape/.test(nk)});}
  if(!vals.length)return{min:NaN,max:NaN,mid:NaN,fields:[]};
  const mins=vals.filter(x=>x.min).map(x=>x.n),maxs=vals.filter(x=>x.max).map(x=>x.n),totals=vals.filter(x=>x.total&&!x.min&&!x.max).map(x=>x.n);
  let min=mins.length?Math.min(...mins):NaN,max=maxs.length?Math.max(...maxs):NaN,mid=NaN;
  if(isFinite(min)&&isFinite(max)&&max>=min)mid=(min+max)/2;
  else if(totals.length){mid=Math.max(...totals);min=mid;max=mid;}
  else {const ns=vals.map(x=>x.n).sort((a,b)=>a-b);mid=ns[Math.floor(ns.length/2)];min=ns[0];max=ns[ns.length-1];}
  return{min,max,mid,fields:vals.slice(0,12)};
}
function auditWorkLabels(c,meta){const out=[];for(const k of meta.works||[]){const v=c?.[k];if(!meaningful(v))continue;const txt=String(v).trim();if(txt.length<2||txt.length>180||/^\d+(\.\d+)?$/.test(txt)||/^[0-9a-f]{8}-[0-9a-f-]{27,}$/i.test(txt))continue;if(!out.includes(txt))out.push(txt);if(out.length>=5)break;}return out;}
function chooseAuditCandidate(row,cands,meta){
  if(!cands.length)return null;const rn=houseNum(row.voie),rowAddr=normTxt(row.voie+' '+(row.commune||''));let best=null,bestScore=-1;
  for(const c of cands){
    const addr=String(valueByMeta(c,meta.address)||''),cn=houseNum(addr),sim=textTokenSimilarity(rowAddr,addr),surf=numericByMeta(c,meta.surface),sg=pctGap(surf,row.surface),date=String(valueByMeta(c,meta.date)||''),rel=signedMonthsBetween(date,row.date);let sc=0;
    if(rn&&cn&&rn===cn)sc+=42;else if(rn&&cn)sc-=28;sc+=Math.round(sim*35);
    if(isFinite(sg)){if(sg<=.05)sc+=23;else if(sg<=.12)sc+=17;else if(sg<=.25)sc+=8;else if(sg>.45)sc-=10;}
    if(isFinite(rel)){const md=Math.abs(rel);if(rel<=0){if(md<=12)sc+=10;else if(md<=30)sc+=4;else if(md>60)sc-=6;}else if(rel<=3)sc+=2;else if(rel<=12)sc-=6;else sc-=12;}
    const tie=String(valueByMeta(c,meta.id)||'');if(sc>bestScore||(sc===bestScore&&tie<String(best?.c?valueByMeta(best.c,meta.id):'~'))){bestScore=sc;best={c,addr,surf,sg,sim,rel,score:sc};}
  }
  if(!best||best.score<34)return null;const costs=auditCostInfo(best.c,meta),date=String(valueByMeta(best.c,meta.date)||''),id=String(valueByMeta(best.c,meta.id)||'');let confidence='low';const temporalOk=!row.date||!isFinite(best.rel)||(best.rel<=3&&best.rel>=-36);
  if(rn&&houseNum(best.addr)===rn&&isFinite(best.sg)&&best.sg<=.12&&temporalOk)confidence='high';
  else if(best.sim>=.75&&(!isFinite(best.sg)||best.sg<=.25)&&(!isFinite(best.rel)||best.rel<=6))confidence='medium';
  if(confidence==='low')return null;
  return{numero:id,date,address:best.addr,surface:best.surf,confidence,matchScore:best.score,costMin:costs.min,costMax:costs.max,costMid:costs.mid,costFields:costs.fields,works:auditWorkLabels(best.c,meta),raw:best.c};
}
async function lookupAuditForRow(row){const meta=await getAuditMeta(),cands=await queryAuditAddress([row.voie,row.commune].filter(Boolean).join(' '));return chooseAuditCandidate(row,cands,meta);}
async function enrichRowsAudit(rows,progress){const todo=rows.filter(r=>r.selected&&!r.auditChecked);let done=0,errors=0,cursor=0;async function worker(){while(cursor<todo.length){const r=todo[cursor++];try{r.auditInfo=await lookupAuditForRow(r);r.auditChecked=true;}catch(e){errors++;r.auditInfo=null;r.auditChecked=false;}done++;progress(done,todo.length,errors);await sleep(180);}}await Promise.all(Array.from({length:Math.min(3,todo.length)},worker));return{count:todo.length,errors};}
function energyWorksInfo(r){const a=r?.auditInfo;if(a){const per=(isFinite(a.costMid)&&r.surface>0)?a.costMid/r.surface:NaN;const cls=isFinite(per)?(per>=700?'high':per>=300?'mid':'low'):'mid';return{label:'Audit ADEME disponible',cls,source:'audit',detail:isFinite(a.costMid)?('≈ '+eur(a.costMid)):''};}const d=r?.dpeInfo?.dpe;if(!d)return{label:'Énergie inconnue',cls:'unknown',source:'none',detail:''};if(['A','B'].includes(d))return{label:'Indice énergie faible',cls:'low',source:'dpe',detail:'DPE '+d};if(['C','D'].includes(d))return{label:'Indice énergie modéré',cls:'mid',source:'dpe',detail:'DPE '+d};return{label:'Indice énergie élevé',cls:'high',source:'dpe',detail:'DPE '+d};}
function manualWorkBudget(r){const n=+r?.workManual?.budget;return isFinite(n)&&n>=0?n:NaN;}
function targetWorkBudget(){const t=state.qual.target||{};const manual=+t.workBudget;if(isFinite(manual)&&manual>=0)return manual;if(t.useAudit==='YES'&&isFinite(state.qual.targetAudit?.costMid))return state.qual.targetAudit.costMid;return 0;}
function comparableWorkBudget(r){const m=manualWorkBudget(r);if(isFinite(m))return{value:m,source:'manual'};if((state.qual.target||{}).useAudit==='YES'&&isFinite(r.auditInfo?.costMid))return{value:r.auditInfo.costMid,source:'audit'};return{value:0,source:'none'};}
function workCorrectionPerM2(r){const t=state.qual.target||{};if(!(r.surface>0)||!(t.surface>0))return NaN;const cb=comparableWorkBudget(r).value,tb=targetWorkBudget();return cb/r.surface-tb/t.surface;}
function correctedPpm(r){if(!isFinite(r.ppm))return NaN;let v=r.ppm;if(useStateCorrection())v*=stateCorrectionFactor(r);if(useBudgetCorrection()){const c=workCorrectionPerM2(r);if(isFinite(c))v+=c;}return Math.max(0,v);}
function totalCorrectionPerM2(r){const cp=correctedPpm(r);return isFinite(cp)&&isFinite(r.ppm)?cp-r.ppm:NaN;}
function correctionBreakdownHtml(r){const sp=stateCorrectionPct(r),bc=workCorrectionPerM2(r),tc=totalCorrectionPerM2(r),parts=[];if(useStateCorrection())parts.push(`<span class="cb">État : <b>${pct1(sp)}</b></span>`);if(useBudgetCorrection())parts.push(`<span class="cb">Budget : <b>${isFinite(bc)?((bc>=0?'+':'')+f0(bc)+' €/m²'):'—'}</b></span>`);parts.push(`<span class="total">Total : ${isFinite(tc)?((tc>=0?'+':'')+f0(tc)+' €/m²'):'—'}</span>`);return`<div class="correction-breakdown">${parts.join('')}</div>`;}
function worksSourceType(r){if(isFinite(manualWorkBudget(r)))return'manual';if(r.auditInfo)return'audit';return r.dpeInfo?.dpe?'dpe':'none';}
function worksCellHtml(r){const e=energyWorksInfo(r),m=r.workManual||{},b=comparableWorkBudget(r),corr=totalCorrectionPerM2(r);const interior=m.interior&&m.interior!=='UNKNOWN'?interiorLabel(m.interior):'État intérieur inconnu';const chips=[`<span class="work-pill ${e.cls}">${esc(e.label)}</span>`];if(m.interior&&m.interior!=='UNKNOWN')chips.push(`<span class="work-pill manual">${esc(interior)} · ${pct1(comparableInteriorCoef(r))}</span>`);if(isFinite(b.value)&&b.value>0)chips.push(`<span class="work-pill ${b.source==='audit'?'audit':'manual'}">${b.source==='audit'?'AUDIT':'Manuel'} · ${eur(b.value)}</span>`);const c=isFinite(corr)?`${corr>=0?'+':''}${f0(corr)} €/m²`:'—';return`<div class="work-stack"><div class="work-line">${chips.join('')}</div><span class="work-sub">Correction totale actuelle : <b>${c}</b>${e.detail?' · '+esc(e.detail):''}</span><button class="work-edit" onclick="openWorkModal('${encodeURIComponent(rowKey(r))}')">✎ État / travaux</button></div>`;}
function targetWorksSummaryHtml(){const t=state.qual.target||{},a=state.qual.targetAudit,b=targetWorkBudget(),coef=targetInteriorCoef(),mode=correctionMode(),src=(isFinite(+t.workBudget)&&+t.workBudget>=0)?'budget saisi':(t.useAudit==='YES'&&a?'audit ADEME':'aucun budget');const per=t.surface>0?b/t.surface:NaN;const modeLab=mode==='STATE'?'État (%)':mode==='BUDGET'?'Budget travaux':'État (%) + budget';return`<div class="works-summary"><div class="ws"><div class="wk">État intérieur cible</div><div class="wv">${esc(interiorLabel(t.interior||'UNKNOWN'))}</div></div><div class="ws"><div class="wk">Coefficient état</div><div class="wv">${pct1(coef)}</div></div><div class="ws"><div class="wk">Méthode retenue</div><div class="wv" style="font-size:14px">${esc(modeLab)}</div></div><div class="ws"><div class="wk">Budget travaux cible</div><div class="wv">${eur(b)}</div></div><div class="ws"><div class="wk">Travaux cible / m²</div><div class="wv">${isFinite(per)?ppmF(per):'—'}</div></div><div class="ws"><div class="wk">Source budget</div><div class="wv" style="font-size:14px">${esc(src)}</div></div></div>${a?`<div class="audit-note"><span class="audit-found">Audit ADEME rapproché ${confidenceLabel(a.confidence)}</span>${isFinite(a.costMid)?` · budget énergétique repéré ≈ <b>${eur(a.costMid)}</b>`:''}. L’audit décrit la rénovation énergétique, pas l’état décoratif intérieur.</div>`:'<div class="audit-note">Le coefficient d’état est indicatif et modifiable. Le budget manuel reste indépendant ; utilise le mode combiné seulement si tu veux volontairement cumuler les deux corrections.</div>'}`;}
async function enrichQualifiedWorks(all=false){if(state.qual.worksRunning||!state.qual.rows.length)return;state.qual.worksRunning=true;try{const t=state.qual.target||{};if(!state.qual.targetAudit&&state.addresses[0]){const pseudo=makePseudoTargetRow(t);pseudo.voie=state.addresses[0].label;try{state.qual.targetAudit=await lookupAuditForRow(pseudo);}catch(e){state.qual.targetAudit=null;}}const rows=all?state.qual.rows:state.qual.rows.slice(0,10),todo=rows.filter(r=>!r.auditChecked);if(todo.length)setStatus(`Recherche des AUDITS ADEME travaux (${todo.length} bien${todo.length>1?'s':''})…`,'info');const ae=await enrichRowsAudit(rows,(d,n)=>{const info=document.getElementById('srcInfo');if(info)info.textContent=`AUDIT ADEME travaux ${d}/${n}…`;});state.qual.auditErrors+=ae.errors;const src=qualifiedSourceRows();state.qual.auditEnrichedCount=src.filter(r=>r.auditChecked).length;state.qual.auditEnrichedAll=src.length>0&&state.qual.auditEnrichedCount>=src.length;recalcQualifiedScores();renderQualifiedResults();setStatus(`${state.qual.auditEnrichedCount} comparable${state.qual.auditEnrichedCount>1?'s':''} vérifié${state.qual.auditEnrichedCount>1?'s':''} dans la base AUDIT ADEME.`,'ok');}catch(e){console.error(e);setStatus('AUDIT travaux : '+e.message,'err');}finally{state.qual.worksRunning=false;}}


// --- BAN -> BDNB Open -> RNIC ---
function textTokenSimilarity(a,b){const A=new Set(normTxt(a).split(' ').filter(x=>x.length>2&&!/^\d+$/.test(x))),B=new Set(normTxt(b).split(' ').filter(x=>x.length>2&&!/^\d+$/.test(x)));if(!A.size||!B.size)return 0;let hit=0;A.forEach(x=>{if(B.has(x))hit++;});return hit/Math.max(A.size,B.size);}
async function lookupBanId(query){const key=normTxt(query);if(!key)return'';if(banIdCache.has(key))return banIdCache.get(key);const p=(async()=>{const r=await robustFetch('https://api-adresse.data.gouv.fr/search/?limit=6&q='+encodeURIComponent(query),null);const j=await r.json(),features=j.features||[],qn=houseNum(query);let best=null,bestScore=-1;for(const f of features){const lab=f?.properties?.label||'',cn=houseNum(lab);if(qn&&cn&&qn!==cn)continue;let sc=textTokenSimilarity(query,lab)*60;if(qn&&cn&&qn===cn)sc+=40;sc+=Math.min(10,(+f?.properties?.score||0)*10);if(sc>bestScore){bestScore=sc;best=f;}}if(!best||bestScore<45)return'';return best.properties?.id||'';})();banIdCache.set(key,p);try{return await p;}catch(e){banIdCache.delete(key);console.warn('BAN id',e);throw e;}}
function extractRows(j){if(Array.isArray(j))return j;if(Array.isArray(j?.data))return j.data;if(Array.isArray(j?.results))return j.results;if(Array.isArray(j?.items))return j.items;return[];}
function sameOrNaN(values){const a=values.filter(v=>v!=null&&v!==''&&(!(typeof v==='number')||isFinite(v)));if(!a.length)return NaN;const first=a[0];return a.every(v=>String(v)===String(first))?first:NaN;}
function mergeBdnbCandidates(rows,preferredRnb=''){const norms=rows.map(normalizeBdnbInfo).filter(Boolean);if(!norms.length)return null;if(preferredRnb){const exact=norms.find(x=>x.rnb&&String(x.rnb)===String(preferredRnb));if(exact)return{...exact,ambiguous:false,alternatives:norms.length,confidence:'high'};}if(norms.length===1)return{...norms[0],ambiguous:false,alternatives:1,confidence:'high'};const coproVals=[...new Set(norms.map(x=>String(x.coproId||'')).filter(Boolean))];const allHaveSameCopro=coproVals.length===1&&norms.every(x=>String(x.coproId||'')===coproVals[0]);const addrVals=[...new Set(norms.map(x=>x.address).filter(Boolean))];return{raw:null,id:'',rnb:'',address:addrVals.length===1?addrVals[0]:'',coproId:allHaveSameCopro?coproVals[0]:'',year:sameOrNaN(norms.map(x=>x.year)),nbLog:sameOrNaN(norms.map(x=>x.nbLog)),levels:sameOrNaN(norms.map(x=>x.levels)),height:sameOrNaN(norms.map(x=>x.height)),dpe:'',ambiguous:true,alternatives:norms.length,confidence:'low'};}
async function queryBdnbByBanId(banId,preferredRnb=''){if(!banId)return null;const ck='ban|'+banId+'|'+String(preferredRnb||'');if(bdnbCache.has(ck))return bdnbCache.get(ck);const p=(async()=>{const urls=[BDNB_ADDRESS_API+'?cle_interop_adr='+encodeURIComponent('eq.'+banId)+'&limit=20','https://api.bdnb.io/v1/bdnb/donnees/batiment_groupe_complet?cle_interop_adr_principale_ban='+encodeURIComponent('eq.'+banId)+'&limit=20'];let lastErr=null;for(const url of urls){try{const r=await robustFetch(url,null),rows=extractRows(await r.json());if(rows.length)return mergeBdnbCandidates(rows,preferredRnb);}catch(e){lastErr=e;}}if(lastErr)throw lastErr;return null;})();bdnbCache.set(ck,p);try{return await p;}catch(e){bdnbCache.delete(ck);console.warn('BDNB BAN',banId,e);throw e;}}
async function queryBdnbByParcel(parcelId,preferredRnb=''){const pid=String(parcelId||'').replace(/\s/g,'').toUpperCase();if(!pid)return null;const ck='parcel|'+pid+'|'+String(preferredRnb||'');if(bdnbCache.has(ck))return bdnbCache.get(ck);const p=(async()=>{const urls=[BDNB_PARCEL_API+'?parcelle_id='+encodeURIComponent('eq.'+pid)+'&limit=20','https://api.bdnb.io/v1/bdnb/donnees/batiment_groupe_complet?parcelle_id='+encodeURIComponent('eq.'+pid)+'&limit=20'];let lastErr=null;for(const url of urls){try{const r=await robustFetch(url,null),rows=extractRows(await r.json());if(rows.length)return mergeBdnbCandidates(rows,preferredRnb);}catch(e){lastErr=e;}}if(lastErr)throw lastErr;return null;})();bdnbCache.set(ck,p);try{return await p;}catch(e){bdnbCache.delete(ck);console.warn('BDNB parcelle',pid,e);throw e;}}
function numberFromFields(o,candidates,patterns=[]){const v=firstDefined(o,candidates);if(v!=null&&isFinite(+v))return +v;for(const pats of patterns){const f=findField(o,pats);if(f&&isFinite(+f.value))return +f.value;}return NaN;}
function normalizeBdnbInfo(o){if(!o)return null;const copro=firstDefined(o,['numero_immat_principal','numero_immatriculation_copropriete','numero_immat_copropriete'])||findField(o,['immat'])?.value||'';const year=numberFromFields(o,['annee_construction','annee_construction_dpe'],[['annee','construction']]);const nbLog=numberFromFields(o,['nb_log','nb_logement','nombre_logement','nombre_logements'],[['nb','log'],['nombre','logement']]);const levels=numberFromFields(o,['nombre_niveau_immeuble','nb_niveau','nombre_niveaux'],[['nombre','niveau'],['nb','niveau']]);const h=numberFromFields(o,['hauteur_mean','hauteur_moyenne','hauteur_max'],[['hauteur','mean'],['hauteur','moy']]);const dpe=firstDefined(o,['classe_dpe','etiquette_dpe','classe_bilan_dpe'])||findField(o,['dpe'],['identifiant','numero'])?.value||'';return{raw:o,id:firstDefined(o,['batiment_groupe_id'])||'',rnb:firstDefined(o,['id_rnb','rnb_id'])||findField(o,['rnb'])?.value||'',address:firstDefined(o,['libelle_adr_principale_ban','adresse'])||'',coproId:String(copro||''),year,nbLog,levels,height:h,dpe:String(dpe||'')};}
async function getRnicResourceId(){if(!rnicResourcePromise)rnicResourcePromise=(async()=>{const r=await robustFetch(RNIC_DATASET_API,null);const j=await r.json();const rs=(j.resources||[]).filter(x=>String(x.format||'').toLowerCase()==='csv');const main=rs.find(x=>x.type==='main')||rs.sort((a,b)=>new Date(b.last_modified||b.published||0)-new Date(a.last_modified||a.published||0))[0];return main?.id||'';})();try{return await rnicResourcePromise;}catch(e){rnicResourcePromise=null;console.warn('RNIC resource',e);throw e;}}
async function getRnicProfile(){if(!rnicProfilePromise)rnicProfilePromise=(async()=>{const rid=await getRnicResourceId();if(!rid)return null;const r=await robustFetch(`${RNIC_TABULAR_BASE}/${rid}/profile/`,null);const j=await r.json();const headers=j?.profile?.header||[];return{rid,headers};})();try{return await rnicProfilePromise;}catch(e){rnicProfilePromise=null;console.warn('RNIC profile',e);throw e;}}
function findHeader(headers,groups){for(const h of headers||[]){const n=normKey(h);if(groups.some(g=>g.every(x=>n.includes(x))))return h;}return'';}
function isAlertValue(v){if(v===true||v===1)return true;const n=normTxt(v);if(!n||['non','0','false','aucune','neant','sans objet'].includes(n))return false;if(['oui','1','true'].includes(n))return true;return false;}
function normalizeRnicInfo(o){if(!o)return null;const rel=[];for(const [k,v] of Object.entries(o)){if(k==='__id'||!meaningful(v))continue;const n=normKey(k);if(/immat|syndic|lot|procedure|arrete|administrateur|carence|nom.*copro|nom.*syndicat|date.*creation/.test(n))rel.push([k,v]);}const lotCandidates=rel.filter(([k,v])=>normKey(k).includes('lot')&&isFinite(+v));const total=lotCandidates.find(([k])=>/total|nombre.*lot|nb.*lot/.test(normKey(k)))||lotCandidates[0];const proc=rel.filter(([k])=>/procedure|arrete|administrateur|carence/.test(normKey(k)));const alert=proc.some(([,v])=>isAlertValue(v));return{raw:o,fields:rel.slice(0,18),lots:total?+total[1]:NaN,procedureFields:proc.length,procedureAlert:alert};}
async function queryRnicByImmat(immat){immat=String(immat||'').trim();if(!immat)return null;if(rnicCache.has(immat))return rnicCache.get(immat);const p=(async()=>{const prof=await getRnicProfile();if(!prof)return null;const h=findHeader(prof.headers,[["numero","immat"],["immatriculation"],["num","immat"]]);if(!h)return null;const base=`${RNIC_TABULAR_BASE}/${prof.rid}/data/`;let lastErr=null;for(const op of ['__exact','__contains']){try{const params=new URLSearchParams({page_size:'5'});params.set(h+op,immat);const r=await robustFetch(base+'?'+params.toString(),null);const rows=extractRows(await r.json());if(rows.length)return normalizeRnicInfo(rows[0]);}catch(e){lastErr=e;console.warn('RNIC',immat,op,e);}}if(lastErr)throw lastErr;return null;})();rnicCache.set(immat,p);try{return await p;}catch(e){rnicCache.delete(immat);throw e;}}
function coproCoreKey(row){
  const addr=normTxt([row?.voie,row?.commune].filter(Boolean).join(' '));
  const mut=String(row?.id||'').trim();
  const local=String(row?.localId||'').trim();
  const typ=String(row?.type||'');
  const surf=isFinite(+row?.surface)?Math.round(+row.surface*10)/10:'';
  const val=isFinite(+row?.val)?Math.round(+row.val):'';
  const date=String(row?.date||'');
  // L'identité principale ne dépend JAMAIS de la parcelle représentative gardée après dédoublonnage.
  if(mut)return `MUT:${mut}|ADR:${addr}|TYPE:${typ}|SURF:${surf}`;
  if(local)return `LOCAL:${local}|ADR:${addr}|TYPE:${typ}|SURF:${surf}`;
  return `ADR:${addr}|DATE:${date}|TYPE:${typ}|SURF:${surf}|VAL:${val}`;
}
function coproParcelIds(row){
  const ids=[];
  const add=v=>{v=String(v||'').replace(/\s/g,'').toUpperCase();if(v&&!ids.includes(v))ids.push(v);};
  add(row?.parcelle);
  const ps=row?.qMutationProfile?.parcels;
  if(ps&&typeof ps.forEach==='function')ps.forEach(add);
  return ids;
}
function coproAliasKeys(row,banId=''){
  const out=[];const add=k=>{if(k&&!out.includes(k))out.push(k);};
  add('CORE:'+coproCoreKey(row));
  const addr=normTxt([row?.voie,row?.commune].filter(Boolean).join(' '));
  if(row?.id)add('MUTADR:'+String(row.id)+'|'+addr);
  if(row?.localId)add('LOCAL:'+String(row.localId));
  const rnb=String(row?.dpeInfo?.rnbId||row?.publicInfo?.bdnb?.rnb||'').trim();if(rnb)add('RNB:'+rnb);
  // Les parcelles servent d'alias et de migration, jamais d'identité principale.
  coproParcelIds(row).forEach(pid=>add('PARCEL:'+pid));
  return out;
}
function coproStorageKey(key,prefix=COPRO_LOCK_PREFIX){return prefix+encodeURIComponent(key);}
function readPositiveCoproKey(key,prefix){
  try{const raw=localStorage.getItem(coproStorageKey(key,prefix));if(!raw)return null;const d=JSON.parse(raw);if(d?.state!=='yes')return null;return{value:true,confidence:d.confidence||'high',source:d.source||'cache copro confirmée',immat:d.immat||'',checkedAt:d.checkedAt||0,locked:true};}catch(e){return null;}
}
function loadCoproDecision(row,banId=''){
  const core='CORE:'+coproCoreKey(row);
  if(coproDecisionCache.has(core))return coproDecisionCache.get(core);
  // Une preuve positive déjà présente sur la ligne est prioritaire.
  const existing=row?.publicInfo?.coproDecision,existingSource=String(existing?.source||row?.publicInfo?.immatSource||'');
  const existingTrusted=(existing?.value===true||row?.publicInfo?.immat)&&(
    existing?.confidence==='high'||/RNIC|BDNB|DPE certain/i.test(existingSource)
  );
  if(existingTrusted){
    const out={value:true,confidence:existing?.confidence||'high',source:existingSource||'source publique déjà confirmée',immat:existing?.immat||row?.publicInfo?.immat||'',key:core,checkedAt:existing?.checkedAt||Date.now(),locked:true};
    return saveCoproDecision(row,banId,out);
  }
  // Un DPE suffisamment rapproché portant une immatriculation reste une preuve positive.
  const dpeId=String(row?.dpeInfo?.coproId||'').trim();
  if(dpeId&&row?.dpeInfo?.confidence==='high'){
    const out={value:true,confidence:'high',source:'DPE certain',immat:dpeId,key:core,checkedAt:Date.now(),locked:true};
    return saveCoproDecision(row,banId,out);
  }
  const aliases=coproAliasKeys(row,banId);
  // Nouvelle clé d'abord.
  for(const key of aliases){const d=readPositiveCoproKey(key,COPRO_LOCK_PREFIX);if(d){const out={...d,key:core};return saveCoproDecision(row,banId,out);}}
  // Migration des anciens verrous positifs, notamment ceux enregistrés sur une parcelle aléatoire.
  for(const prefix of COPRO_LEGACY_PREFIXES){for(const key of aliases){const d=readPositiveCoproKey(key,prefix);if(d){
    const trusted=d.confidence==='high'||/RNIC|BDNB|DPE certain/i.test(String(d.source||''));
    if(!trusted)continue; // on ne migre pas les anciens « DPE probable » non vérifiés
    const out={...d,key:core,source:d.source||'ancienne copro confirmée migrée'};return saveCoproDecision(row,banId,out);
  }}}
  return null;
}
function saveCoproDecision(row,banId,decision){
  if(!decision||decision.value!==true)return decision?{...decision,key:'CORE:'+coproCoreKey(row),locked:false}:null;
  const core='CORE:'+coproCoreKey(row),d={...decision,value:true,key:core,checkedAt:decision.checkedAt||Date.now(),locked:true};
  coproDecisionCache.set(core,d);
  // On écrit la même preuve sous plusieurs alias afin qu'un changement de parcelle représentative ne puisse plus la faire disparaître.
  for(const key of coproAliasKeys(row,banId)){
    try{localStorage.setItem(coproStorageKey(key),JSON.stringify({state:'yes',confidence:d.confidence||'high',source:d.source||'',immat:d.immat||'',checkedAt:d.checkedAt}));}catch(e){}
  }
  return d;
}
function clearCoproDecision(row,banId=''){/* une copropriété confirmée n'est jamais effacée par une actualisation */}
function bdnbPositive(b){return !!(b&&b.coproId);}
function bdnbDefiniteNo(b){return !!(b&&!b.ambiguous&&!b.coproId);}
async function determineCoproDecision(row,banId,bdnbAddress,addressChecked){
  const cached=loadCoproDecision(row,banId);if(cached)return cached;

  // On vérifie TOUTES les parcelles connues de la mutation, et non la parcelle arbitraire de la ligne dédoublonnée.
  const parcelIds=coproParcelIds(row),parcelResults=[];let parcelErrors=0;
  for(const pid of parcelIds.slice(0,12)){
    try{parcelResults.push({pid,bdnb:await queryBdnbByParcel(pid,row.dpeInfo?.rnbId||''),checked:true});}
    catch(e){parcelErrors++;parcelResults.push({pid,bdnb:null,checked:false});}
  }

  const ids=new Map();
  const addId=(id,src)=>{id=String(id||'').trim();if(!id)return;ids.set(id,ids.has(id)?ids.get(id)+' + '+src:src);};
  if(bdnbPositive(bdnbAddress))addId(bdnbAddress.coproId,bdnbAddress.ambiguous?'BDNB adresse · copro commune aux bâtiments':'BDNB adresse');
  for(const pr of parcelResults)if(bdnbPositive(pr.bdnb))addId(pr.bdnb.coproId,`BDNB parcelle ${pr.pid}`);
  if(row.dpeInfo?.confidence==='high')addId(row.dpeInfo?.coproId,'DPE certain');
  // Un DPE seulement probable ne verrouille jamais une copropriété tout seul : son immatriculation doit exister dans le RNIC.
  if(row.dpeInfo?.confidence==='medium'&&row.dpeInfo?.coproId){
    try{const rn=await queryRnicByImmat(row.dpeInfo.coproId);if(rn){const decision=saveCoproDecision(row,banId,{value:true,confidence:'high',source:'RNIC + DPE probable',immat:row.dpeInfo.coproId});return{...decision,rnic:rn};}}catch(e){}
  }

  if(ids.size){
    const verified=[];
    for(const [immat,src] of ids){try{const rn=await queryRnicByImmat(immat);if(rn)verified.push({immat,src,rn});}catch(e){}}
    const chosen=verified[0]||null,first=[...ids.entries()][0];
    const immat=chosen?.immat||first?.[0]||'',src=chosen?('RNIC + '+chosen.src):(ids.size>1?'Plusieurs sources positives BDNB/DPE':first?.[1]||'source positive');
    const decision=saveCoproDecision(row,banId,{value:true,confidence:chosen?'high':(String(src).includes('BDNB')?'high':'medium'),source:src,immat});
    return{...decision,rnic:chosen?.rn||null};
  }

  // Un NON n'est jamais verrouillé. On ne l'affiche que si l'adresse ET toutes les parcelles connues ont répondu sans immatriculation.
  const parcelsFullyChecked=parcelIds.length>0&&parcelErrors===0&&parcelResults.length===parcelIds.length;
  const parcelsAllNo=parcelsFullyChecked&&parcelResults.every(x=>bdnbDefiniteNo(x.bdnb));
  if(addressChecked&&bdnbDefiniteNo(bdnbAddress)&&parcelsAllNo)return{value:false,confidence:'high',source:'BDNB adresse + toutes parcelles',immat:'',key:'CORE:'+coproCoreKey(row),locked:false};
  return{value:null,confidence:'low',source:'Données insuffisantes',immat:'',key:'CORE:'+coproCoreKey(row),locked:false};
}
function publicEnrichmentSig(row,banId=''){
  const parcels=coproParcelIds(row).slice().sort().join(',');
  const rnb=String(row?.dpeInfo?.rnbId||'');
  const lat=isFinite(+row?.lat)?(+row.lat).toFixed(5):'',lon=isFinite(+row?.lon)?(+row.lon).toFixed(5):'';
  return [coproCoreKey(row),String(banId||''),parcels,rnb,lat,lon].join('|');
}
async function enrichPublicForRow(row){
  let banId=row.dpeInfo?.banId||row.publicInfo?.banId||'';
  const cachedDecision=loadCoproDecision(row,banId);
  const sig=publicEnrichmentSig(row,banId);
  if(row.publicInfo?.done&&row.publicInfo?.osmChecked&&row.publicInfo?.sig===sig&&row.publicInfo?.coproDecision)return row.publicInfo;
  const errors=[];
  if(!banId){try{banId=await lookupBanId([row.voie,row.commune].filter(Boolean).join(' '));}catch(e){errors.push('BAN');}}
  let bdnb=null,bdnbChecked=false;if(banId){try{bdnb=await queryBdnbByBanId(banId,row.dpeInfo?.rnbId||'');bdnbChecked=true;}catch(e){errors.push('BDNB');}}
  let coproDecision=cachedDecision||loadCoproDecision(row,banId)||null;if(!coproDecision){try{coproDecision=await determineCoproDecision(row,banId,bdnb,bdnbChecked);}catch(e){errors.push('COPRO');coproDecision=loadCoproDecision(row,banId)||{value:null,confidence:'low',source:'Erreur de vérification',immat:'',key:'CORE:'+coproCoreKey(row),locked:false};}}
  const immat=coproDecision?.value===true?(coproDecision.immat||''):'';const immatSource=coproDecision?.source||'';
  let rnic=null;if(immat){try{rnic=await queryRnicByImmat(immat);}catch(e){errors.push('RNIC');}}
  let osm=row.publicInfo?.osm||null,osmChecked=!!row.publicInfo?.osmChecked;if(!osmChecked){try{osm=await queryOsmAround(row.lat,row.lon);osmChecked=true;}catch(e){errors.push('OSM');}}
  // La copropriété est sauvegardée indépendamment d'OSM. Une panne OSM ne peut donc plus faire varier le statut copro.
  const criticalError=errors.includes('BAN')||errors.includes('BDNB');row.publicInfo={sig:publicEnrichmentSig(row,banId),done:!criticalError,osmChecked,banId,bdnb,bdnbChecked,rnic,immat,immatSource,coproDecision,osm,errors};
  if(coproDecision?.value!==null)saveCoproDecision(row,banId,coproDecision);
  if(row.publicInfo.done)saveStableRow(row);return row.publicInfo;
}
async function enrichTargetPublic(t){const a=state.addresses[0]||{},pseudo=makePseudoTargetRow(t);pseudo.voie=a.label;pseudo.commune='';pseudo.dpeInfo=state.qual.targetMatch;if(a.banId&&!pseudo.dpeInfo?.banId){pseudo.dpeInfo={...(pseudo.dpeInfo||{}),banId:a.banId};}return enrichPublicForRow(pseudo);}
async function enrichRowsPublic(rows,progress){const todo=rows.filter(r=>!r.publicInfo?.done||!r.publicInfo?.coproDecision);let done=0,errors=0,cursor=0;async function worker(){while(cursor<todo.length){const r=todo[cursor++];try{await enrichPublicForRow(r);if(r.publicInfo?.errors?.length)errors++;}catch(e){errors++;const locked=loadCoproDecision(r,r.publicInfo?.banId||r.dpeInfo?.banId||'');r.publicInfo={...(r.publicInfo||{}),done:false,osmChecked:false,coproDecision:locked||r.publicInfo?.coproDecision||null,errors:['public']};}done++;progress(done,todo.length,errors);await sleep(350);}}await Promise.all(Array.from({length:Math.min(3,todo.length)},worker));return{count:todo.length,errors};}

// --- Fiche cible / score ---
function renderQualifiedBase(){
  const body=document.getElementById('qualBody');if(!body)return;const source=qualifiedSourceRows();if(!source.length){body.innerHTML='<div class="qual-empty">Aucun comparable n’est actuellement sélectionné dans « Comparables Vendus ». Coche au moins une vente avant de déterminer le prix.</div>';return;}const prev=state.qual.target||{},typ=prev.type||defaultTargetType();
  const tr=prev.traversant||'AUTO',ori=prev.orientation||'AUTO',cop=prev.copro||'AUTO',interior=prev.interior||'UNKNOWN',useAudit=prev.useAudit||'NO',corrMode=prev.correctionMode||'STATE',interiorCoef=isFinite(+prev.interiorCoef)?+prev.interiorCoef:defaultInteriorCoef(interior);
  body.innerHTML=`<div class="qual-hero"><div><h2>Détermination du prix</h2><p>Étape 1 ter : le classement croise DVF, DPE/AUDIT ADEME, BDNB, RNIC et OSM, puis permet de corriger les comparables selon les travaux du bien cible.</p></div><div class="qual-source">ÉTAPE 1 TER · TRAVAUX</div></div>
  <div class="qual-panel"><h3>Bien à estimer</h3><div class="subtxt">Les données publiques enrichissent le bien ; l’état intérieur et le budget travaux peuvent être saisis manuellement. Un budget manuel est toujours prioritaire.</div>
  <div class="qual-form-grid">
    <div class="qual-field"><label>Type de bien</label><select id="qtType" onchange="updateCoproTargetVisibility()"><option ${typ==='Appartement'?'selected':''}>Appartement</option><option ${typ==='Maison'?'selected':''}>Maison</option><option ${typ==='Local'?'selected':''}>Local</option></select></div>
    <div class="qual-field"><label>Surface cible (m²) *</label><input id="qtSurface" type="number" min="1" step="0.1" value="${prev.surface||''}" placeholder="Ex : 70"></div>
    <div class="qual-field"><label>Nombre de pièces</label><input id="qtPieces" type="number" min="1" step="1" value="${prev.pieces||''}" placeholder="Ex : 3"></div>
    <div class="qual-field"><label>DPE cible</label><select id="qtDpe"><option value="AUTO" ${!prev.dpe||prev.dpe==='AUTO'?'selected':''}>Auto via ADEME</option>${DPE_ORDER.map(x=>`<option value="${x}" ${prev.dpe===x?'selected':''}>${x}</option>`).join('')}<option value="NONE" ${prev.dpe==='NONE'?'selected':''}>Inconnu</option></select></div>
    <div class="qual-field"><label>Période construction</label><select id="qtPeriod"><option value="AUTO" ${!prev.period||prev.period==='AUTO'?'selected':''}>Auto via DPE</option>${PERIODS.map(([v,l])=>`<option value="${v}" ${prev.period===v?'selected':''}>${l}</option>`).join('')}<option value="NONE" ${prev.period==='NONE'?'selected':''}>Inconnue</option></select></div>
    <div class="qual-field"><label>Terrain cible (m², maison)</label><input id="qtTerrain" type="number" min="0" step="1" value="${prev.terrain||''}" placeholder="Ex : 250"></div>
    <div class="qual-field" id="qtCoproWrap"><label>Maison en copropriété</label><select id="qtCopro"><option value="AUTO" ${cop==='AUTO'?'selected':''}>Auto via BDNB / RNIC</option><option value="YES" ${cop==='YES'?'selected':''}>Oui</option><option value="NO" ${cop==='NO'?'selected':''}>Non</option><option value="NONE" ${cop==='NONE'?'selected':''}>Inconnu</option></select></div>
    <div class="qual-field"><label>Étage cible (appartement)</label><input id="qtFloor" type="number" min="0" step="1" value="${isFinite(prev.floor)?prev.floor:''}" placeholder="Auto via DPE"></div>
    <div class="qual-field"><label>Traversant</label><select id="qtTraversant"><option value="AUTO" ${tr==='AUTO'?'selected':''}>Auto via DPE</option><option value="YES" ${tr==='YES'?'selected':''}>Oui</option><option value="NO" ${tr==='NO'?'selected':''}>Non</option><option value="NONE" ${tr==='NONE'?'selected':''}>Inconnu</option></select></div>
    <div class="qual-field"><label>Orientation</label><select id="qtOrientation"><option value="AUTO" ${ori==='AUTO'?'selected':''}>Auto si disponible</option>${ORIENTATIONS.map(x=>`<option value="${x}" ${ori===x?'selected':''}>${x}</option>`).join('')}<option value="NONE" ${ori==='NONE'?'selected':''}>Inconnue</option></select></div>
  </div>
  <div class="works-target-grid"><div class="works-title"><h4>État & travaux</h4><span class="works-help">La correction prix ne modifie jamais la valeur DVF d’origine.</span></div>
    <div class="qual-field"><label>État intérieur cible</label><select id="qtInterior" onchange="syncTargetInteriorCoef()">${INTERIOR_STATES.map(([v,l])=>`<option value="${v}" ${interior===v?'selected':''}>${l}</option>`).join('')}</select></div>
    <div class="qual-field state-coef-wrap"><label>Coefficient état (%)</label><input class="state-coef-input" id="qtInteriorCoef" type="number" min="-40" max="40" step="0.5" value="${interiorCoef}"></div>
    <div class="qual-field"><label>Méthode de correction prix</label><select id="qtCorrectionMode"><option value="STATE" ${corrMode==='STATE'?'selected':''}>État (%) uniquement</option><option value="BUDGET" ${corrMode==='BUDGET'?'selected':''}>Budget travaux uniquement</option><option value="BOTH" ${corrMode==='BOTH'?'selected':''}>État (%) + budget — expert</option></select></div>
    <div class="qual-field"><label>Budget travaux cible (€)</label><input id="qtWorkBudget" type="number" min="0" step="1000" value="${isFinite(+prev.workBudget)?+prev.workBudget:''}" placeholder="Ex : 80000"></div>
    <div class="qual-field"><label>Budget AUDIT ADEME dans correction</label><select id="qtUseAudit"><option value="NO" ${useAudit!=='YES'?'selected':''}>Non — prudent</option><option value="YES" ${useAudit==='YES'?'selected':''}>Oui — si audit fiable</option></select></div>
    <div class="qual-field"><label>Principe</label><input value="Prix comparable → état cible → budget selon méthode" disabled></div>
    <div class="state-scale"><span class="ss pos">Neuf +12 %</span><span class="ss pos">Très bon +7 %</span><span class="ss zero">Bon 0 %</span><span class="ss neg">À rafraîchir −5 %</span><span class="ss neg">À rénover −12 %</span><span class="ss zero">Coefficients modifiables</span></div>
  </div>
  <div class="qual-actions"><button class="qual-primary" id="qualRunBtn" onclick="runQualifiedRanking(false)">Classer les comparables</button><span class="qual-progress" id="qualProgress">${source.length} ventes sélectionnées dans « Comparables Vendus ».</span></div>
  <div class="target-dpe-note">Travaux : le DPE donne seulement un indice énergétique ; l’AUDIT ADEME, lorsqu’il existe, peut apporter un budget/scénario énergétique. L’état intérieur reste manuel tant qu’aucune annonce historique fiable n’est disponible.<br><b>Copropriété maison :</b> un « Oui » n’est affiché qu’avec une immatriculation fiable (DPE certain, BDNB ou RNIC) ; un « Non détectée » uniquement après réponse BDNB non ambiguë. En cas d’échec réseau ou de plusieurs bâtiments possibles, le statut reste « Inconnu ».</div></div>`;
  updateCoproTargetVisibility();
}
function updateCoproTargetVisibility(){const wrap=document.getElementById('qtCoproWrap'),typ=document.getElementById('qtType')?.value;if(wrap)wrap.style.display=typ==='Maison'?'':'none';}
function syncTargetInteriorCoef(){const st=document.getElementById('qtInterior')?.value||'UNKNOWN',el=document.getElementById('qtInteriorCoef');if(el)el.value=defaultInteriorCoef(st);}
function readQualifiedTarget(){const wb=document.getElementById('qtWorkBudget')?.value,ic=document.getElementById('qtInteriorCoef')?.value;const t={type:document.getElementById('qtType').value,surface:+document.getElementById('qtSurface').value||NaN,pieces:+document.getElementById('qtPieces').value||NaN,dpe:document.getElementById('qtDpe').value,period:document.getElementById('qtPeriod').value,terrain:+document.getElementById('qtTerrain').value||NaN,floor:document.getElementById('qtFloor').value===''?NaN:+document.getElementById('qtFloor').value,traversant:document.getElementById('qtTraversant').value,orientation:document.getElementById('qtOrientation').value,copro:document.getElementById('qtCopro')?.value||'AUTO',interior:document.getElementById('qtInterior')?.value||'UNKNOWN',interiorCoef:ic===''?defaultInteriorCoef(document.getElementById('qtInterior')?.value||'UNKNOWN'):+ic,correctionMode:document.getElementById('qtCorrectionMode')?.value||'STATE',workBudget:wb===''?NaN:+wb,useAudit:document.getElementById('qtUseAudit')?.value||'NO'};state.qual.target=t;return t;}
function criterionCurve(gap,steps){for(const [limit,ratio] of steps)if(gap<=limit)return ratio;return 0;}
function publicCoproStatus(row){const p=row?.publicInfo,d=p?.coproDecision||loadCoproDecision(row,p?.banId||row?.dpeInfo?.banId||'');if(d){if(d.value===true)return{value:true,confidence:d.confidence||'high',label:'Oui · '+(d.source||'source publique'),immat:d.immat||''};if(d.value===false)return{value:false,confidence:d.confidence||'high',label:'Non détectée · '+(d.source||'vérification croisée'),immat:''};}if(!p)return{value:null,confidence:'none',label:'à vérifier'};if(p.errors?.includes('BAN')||p.errors?.includes('BDNB')||p.errors?.includes('COPRO'))return{value:null,confidence:'low',label:'Source indisponible · à revalider'};return{value:null,confidence:'low',label:'Inconnu · données insuffisantes'};}
function resolveTarget(t){const m=state.qual.targetMatch,autoCopro=publicCoproStatus({publicInfo:state.qual.targetPublic});return{dpe:t.dpe==='AUTO'?(m?.dpe||null):(DPE_ORDER.includes(t.dpe)?t.dpe:null),period:t.period==='AUTO'?(m?.period||null):(periodIndex[t.period]!=null?t.period:null),floor:isFinite(t.floor)?t.floor:(isFinite(m?.floor)?m.floor:NaN),traversant:t.traversant==='AUTO'?(m?.traversant??null):(t.traversant==='YES'?true:t.traversant==='NO'?false:null),orientation:t.orientation==='AUTO'?(m?.orientation||null):(ORIENTATIONS.includes(t.orientation)?t.orientation:null),copro:t.copro==='AUTO'?autoCopro.value:(t.copro==='YES'?true:t.copro==='NO'?false:null),interior:t.interior&&t.interior!=='UNKNOWN'?t.interior:null};}
function orientationGap(a,b){if(!a||!b)return NaN;a=String(a).split('/')[0];b=String(b).split('/')[0];const ia=ORIENTATIONS.indexOf(a),ib=ORIENTATIONS.indexOf(b);if(ia<0||ib<0)return NaN;const d=Math.abs(ia-ib);return Math.min(d,8-d);}
function computeQualifiedScore(r,t,targetResolved){
  const house=t.type==='Maison';const weights=house?{type:15,surface:19,pieces:9,dpe:13,period:9,distance:14,recency:9,terrain:5,copro:5,orientation:2,interior:10}:{type:17,surface:19,pieces:9,dpe:12,period:8,distance:13,recency:8,floor:5,traversant:3,orientation:2,interior:10};let earned=0,available=0;const detail={};const add=(k,ratio,known=true)=>{if(!known)return;const w=weights[k]||0;available+=w;earned+=w*Math.max(0,Math.min(1,ratio));detail[k]=Math.round(100*ratio);};
  add('type',r.type===t.type?1:0,!!t.type&&!!r.type);const sg=pctGap(r.surface,t.surface);add('surface',criterionCurve(sg,[[.05,1],[.10,.90],[.15,.75],[.20,.55],[.30,.30],[.45,.10]]),isFinite(sg));const pd=isFinite(r.pieces)&&isFinite(t.pieces)?Math.abs(r.pieces-t.pieces):NaN;add('pieces',pd===0?1:pd===1?.7:pd===2?.3:0,isFinite(pd));
  const td=targetResolved.dpe,rd=r.dpeInfo?.dpe;const di=td&&rd?Math.abs(DPE_ORDER.indexOf(td)-DPE_ORDER.indexOf(rd)):NaN;add('dpe',di===0?1:di===1?.8:di===2?.45:di===3?.2:0,isFinite(di));const tp=targetResolved.period,rp=r.dpeInfo?.period;const pi=tp&&rp?Math.abs(periodIndex[tp]-periodIndex[rp]):NaN;add('period',pi===0?1:pi===1?.7:pi===2?.3:0,isFinite(pi));const d=r.dist;add('distance',d<=100?1:d<=250?.9:d<=500?.72:d<=1000?.48:d<=2000?.24:0,isFinite(d));const ma=monthsAgo(r.date);add('recency',ma<=12?1:ma<=24?.8:ma<=36?.6:ma<=60?.3:0,isFinite(ma));
  if(house){const tg=pctGap(r.terrain,t.terrain);add('terrain',criterionCurve(tg,[[.10,1],[.20,.75],[.35,.45],[.60,.15]]),isFinite(tg));const rc=publicCoproStatus(r);add('copro',rc.value===targetResolved.copro?1:0,targetResolved.copro!==null&&rc.value!==null);}else{const fd=isFinite(targetResolved.floor)&&isFinite(r.dpeInfo?.floor)?Math.abs(targetResolved.floor-r.dpeInfo.floor):NaN;add('floor',fd===0?1:fd===1?.75:fd===2?.4:0,isFinite(fd));const tr=targetResolved.traversant,rr=r.dpeInfo?.traversant;add('traversant',tr===rr?1:0,tr!==null&&rr!==null);}
  const og=orientationGap(targetResolved.orientation,mainOrientationForScore(r.dpeInfo));add('orientation',og===0?1:og===1?.75:og===2?.4:0,isFinite(og));const ti=targetResolved.interior,ri=r.workManual?.interior&&r.workManual.interior!=='UNKNOWN'?r.workManual.interior:null;const ig=ti&&ri?Math.abs(INTERIOR_RANK[ti]-INTERIOR_RANK[ri]):NaN;add('interior',ig===0?1:ig===1?.75:ig===2?.4:0,isFinite(ig));const micro=r.qMicro||microLocationInfo(r),mutation=r.qMutation||{status:'unknown',simple:false};let score=available?earned/available*100:0;score+=micro.bonus;const penalty=mutation.simple?0:(mutation.status==='unknown'?4:8);score-=penalty;detail.microBonus=micro.bonus;detail.mutationPenalty=penalty;score=Math.max(0,Math.min(100,Math.round(score)));return{score,coverage:Math.round(available/Object.values(weights).reduce((a,b)=>a+b,0)*100),detail};
}
function preliminarySort(rows,t){const tr={dpe:null,period:null,floor:NaN,traversant:null,orientation:null,copro:null,interior:null};return rows.map(r=>({r,s:computeQualifiedScore(r,t,tr).score})).sort((a,b)=>b.s-a.s||(a.r.dist-b.r.dist)).map(x=>x.r);}
function recalcQualifiedScores(){const t=state.qual.target||{},resolved=resolveTarget(t);state.qual.rows=qualifiedSourceRows().map(r=>{const sc=computeQualifiedScore(r,t,resolved);r.qScore=sc.score;r.qCoverage=sc.coverage;r.qDetail=sc.detail;return r;}).sort((a,b)=>b.qScore-a.qScore||(a.dist-b.dist));}
async function runQualifiedRanking(allDpe=false){
  if(state.qual.running)return;
  const editing=!!document.getElementById('qtType');
  const t=(allDpe&&!editing&&state.qual.target)?state.qual.target:readQualifiedTarget();
  if(editing){state.qual.targetAudit=null;}
  if(!isFinite(t.surface)||t.surface<=0){setStatus('Renseigne la surface du bien à estimer.','err');return;}
  state.qual.running=true;
  const btn=document.getElementById('qualRunBtn');if(btn)btn.disabled=true;
  const prog=document.getElementById('qualProgress');
  try{
    if(prog)prog.textContent='Préparation du classement…';
    const source=qualifiedSourceRows();
    if(!source.length){setStatus('Aucun comparable sélectionné dans « Comparables Vendus ».','err');return;}
    const mutationProfiles=buildMutationProfiles();
    source.forEach(r=>{r.qMutationProfile=r.id?mutationProfiles.get(r.id):null;r.qMutation=classifyMutation(r,mutationProfiles);r.qMicro=microLocationInfo(r);});
    if(!allDpe)state.qual.sort={key:'score',dir:-1};

    // Premier passage volontairement limité : le tableau arrive plus vite.
    // Le bouton « Enrichir tous les DPE » reste disponible pour le passage complet.
    const ordered=preliminarySort([...source],t);
    const batch=allDpe?ordered:ordered.slice(0,Math.min(24,ordered.length));
    const needsTarget=t.dpe==='AUTO'||t.period==='AUTO'||!isFinite(t.floor)||t.traversant==='AUTO'||t.orientation==='AUTO';
    if(needsTarget)state.qual.targetMatch=null;
    else state.qual.targetMatch=null;

    if(prog)prog.textContent=`Classement rapide · enrichissement de ${new Set(batch.map(r=>normTxt(r.voie+' '+r.commune))).size} adresse(s)…`;
    // La cible et les comparables ADEME sont maintenant recherchés en parallèle.
    const targetPromise=needsTarget?lookupTargetDpe(t):Promise.resolve(null);
    const rowsPromise=enrichRowsDpe(batch,(d,n,e)=>{if(prog)prog.textContent=`Classement rapide ADEME : ${d}/${n}${e?' · '+e+' erreur(s)':''}…`;});
    const [targetMatch,er]=await Promise.all([targetPromise,rowsPromise]);
    state.qual.targetMatch=targetMatch;
    state.qual.dpeErrors=er.errors;
    state.qual.enrichedCount=batch.length;
    state.qual.enrichedAll=allDpe||batch.length===ordered.length;
    recalcQualifiedScores();
    if(!state.qual.selectionInitialized){
      state.qual.rows.forEach(r=>r.qSelected=false);
      state.qual.rows.filter(r=>r.qScore>=60).slice(0,5).forEach(r=>r.qSelected=true);
      state.qual.selectionInitialized=true;
    }
    if(prog)prog.textContent='Classement prêt · données bâtiment/copropriété et audits continuent en arrière-plan…';
    renderQualifiedResults();
    if(!allDpe)setTimeout(()=>enrichQualifiedPublic(false),40);
  }catch(e){console.error(e);setStatus('Détermination du prix : '+e.message,'err');}
  finally{state.qual.running=false;if(btn)btn.disabled=false;}
}

async function enrichQualifiedPublic(all=false){
  if(state.qual.running||!state.qual.rows.length)return;
  state.qual.running=true;
  try{
    if(!state.qual.targetPublic&&state.qual.target){
      setStatus('Enrichissement BDNB / RNIC / OSM du bien cible…','info');
      state.qual.targetPublic=await enrichTargetPublic(state.qual.target);
    }
    // La copropriété est un critère important : on enrichit toutes les ventes sélectionnées,
    // pas uniquement le Top 10. Cela rend le résultat stable d'une exécution à l'autre.
    const rows=state.qual.rows;
    const todo=rows.filter(r=>!r.publicInfo?.done);
    if(todo.length){
      setStatus(`Classement prêt · enrichissement BDNB / RNIC / OSM en arrière-plan (${todo.length} bien${todo.length>1?'s':''})…`,'info');
      const pe=await enrichRowsPublic(rows,(d,n)=>{const info=document.getElementById('srcInfo');if(info)info.textContent=`BDNB / RNIC / OSM ${d}/${n}…`;});
      state.qual.publicErrors+=pe.errors;
    }
    const selectedSource=qualifiedSourceRows();
    state.qual.publicEnrichedCount=selectedSource.filter(r=>r.publicInfo?.done).length;
    state.qual.publicEnrichedAll=selectedSource.length>0&&state.qual.publicEnrichedCount>=selectedSource.length;
    recalcQualifiedScores();renderQualifiedResults();
    setStatus(`${state.qual.publicEnrichedCount}/${selectedSource.length} bien${selectedSource.length>1?'s':''} vérifié${selectedSource.length>1?'s':''} pour les données publiques${state.qual.publicEnrichedCount<selectedSource.length?' · certaines sources seront retentées':''} · les statuts incertains restent « Inconnu ».`,state.qual.publicEnrichedCount<selectedSource.length?'info':'ok');if(!all)setTimeout(()=>enrichQualifiedWorks(false),120);
  }catch(e){setStatus('Enrichissement public : '+e.message,'err');}
  finally{state.qual.running=false;}
}

// --- Tri / filtres ---
function qualifiedSortValue(r,key){const t=state.qual.target||{};if(key==='score'||key==='quality')return r.qScore;if(key==='date')return r.date?Date.parse(r.date):NaN;if(key==='distance')return r.dist;if(key==='type')return r.type||'';if(key==='surface')return r.surface;if(key==='surfaceGap')return isFinite(r.surface)&&isFinite(t.surface)&&t.surface>0?Math.abs(r.surface/t.surface-1)*100:NaN;if(key==='pieces')return r.pieces;if(key==='dpe')return r.dpeInfo?.dpe?DPE_ORDER.indexOf(r.dpeInfo.dpe):NaN;if(key==='construction')return r.dpeInfo?.period?periodIndex[r.dpeInfo.period]:NaN;if(key==='floor')return r.dpeInfo?.floor;if(key==='traversant')return r.dpeInfo?.traversant===true?1:r.dpeInfo?.traversant===false?0:NaN;if(key==='orientation'){const o=mainOrientationForScore(r.dpeInfo);return o?ORIENTATIONS.indexOf(o):NaN;}if(key==='building')return r.publicInfo?.bdnb?.nbLog;if(key==='copro'){const c=publicCoproStatus(r);return c.value===true?0:c.value===false?1:2;}if(key==='terrain')return r.terrain;if(key==='interior')return r.workManual?.interior&&r.workManual.interior!=='UNKNOWN'?INTERIOR_RANK[r.workManual.interior]:NaN;if(key==='stateCoef')return (r.workManual?.interior&&r.workManual.interior!=='UNKNOWN')||isFinite(+r.workManual?.interiorCoef)?comparableInteriorCoef(r):NaN;if(key==='works')return worksSourceType(r);if(key==='workBudget')return comparableWorkBudget(r).value;if(key==='correctedPpm')return correctedPpm(r);if(key==='val')return r.val;if(key==='ppm')return r.ppm;if(key==='medianGap'){const g=medianGapPct(r);return isFinite(g)?Math.abs(g):NaN;}if(key==='mutation')return r.qMutation?.simple?0:(r.qMutation?.status==='unknown'?1:2);if(key==='voie')return r.voie||'';return 0;}
function qualifiedSortRows(rows){const srt=state.qual.sort||{key:'score',dir:-1};return[...rows].sort((a,b)=>{const va=qualifiedSortValue(a,srt.key),vb=qualifiedSortValue(b,srt.key),ma=va==null||(typeof va==='number'&&!isFinite(va))||va==='',mb=vb==null||(typeof vb==='number'&&!isFinite(vb))||vb==='';if(ma!==mb)return ma?1:-1;if(ma&&mb)return(b.qScore||0)-(a.qScore||0);const cmp=(typeof va==='string'||typeof vb==='string')?String(va).localeCompare(String(vb),'fr',{numeric:true,sensitivity:'base'}):va-vb;return cmp*srt.dir||((b.qScore||0)-(a.qScore||0));});}
function sortQualifiedBy(key){const srt=state.qual.sort||{key:'score',dir:-1};if(srt.key===key)srt.dir*=-1;else{srt.key=key;srt.dir=['score','quality','date','val','ppm','workBudget','stateCoef','correctedPpm'].includes(key)?-1:1;}state.qual.sort=srt;refreshQualifiedView();}
function qualHeader(key,label,cls=''){const srt=state.qual.sort||{},active=srt.key===key,mark=active?(srt.dir===1?'▲':'▼'):'↕';return`<th class="sortable ${cls}" onclick="sortQualifiedBy('${key}')">${label} <span class="sortmark ${active?'':'off'}">${mark}</span></th>`;}
function qualifiedFilteredRows(applySort=true){const rows=(state.qual.rows||[]).filter(r=>r.selected),t=state.qual.target||{},resolved=resolveTarget(t),f=state.qual.filters||{};const fd=document.getElementById('qfDpe')?.value||f.dpe||'all',fs=document.getElementById('qfSurface')?.value||f.surface||'all',fp=document.getElementById('qfPieces')?.value||f.pieces||'all',fy=document.getElementById('qfPeriod')?.value||f.period||'all',fdist=document.getElementById('qfDistance')?.value||f.distance||'all',fr=document.getElementById('qfRecency')?.value||f.recency||'all',fm=document.getElementById('qfMutation')?.value||f.mutation||'all',ff=document.getElementById('qfFloor')?.value||f.floor||'all',ft=document.getElementById('qfTraversant')?.value||f.traversant||'all',fc=document.getElementById('qfCopro')?.value||f.copro||'all',fi=document.getElementById('qfInterior')?.value||f.interior||'all',fw=document.getElementById('qfWorks')?.value||f.works||'all';const filtered=rows.filter(r=>{if(fd!=='all'){if(!resolved.dpe||!r.dpeInfo?.dpe)return false;const d=Math.abs(DPE_ORDER.indexOf(resolved.dpe)-DPE_ORDER.indexOf(r.dpeInfo.dpe));if(fd==='same'&&d!==0)return false;if(fd==='one'&&d>1)return false;}if(fs!=='all'){const g=pctGap(r.surface,t.surface);if(!isFinite(g)||g>+fs/100)return false;}if(fp!=='all'){if(!isFinite(t.pieces)||!isFinite(r.pieces))return false;const d=Math.abs(r.pieces-t.pieces);if(fp==='same'&&d!==0)return false;if(fp==='one'&&d>1)return false;}if(fy==='same'){if(!resolved.period||r.dpeInfo?.period!==resolved.period)return false;}if(fdist!=='all'&&(!isFinite(r.dist)||r.dist>+fdist))return false;if(fr!=='all'){const m=monthsAgo(r.date);if(!isFinite(m)||m>+fr)return false;}if(fm==='simple'&&!r.qMutation?.simple)return false;if(ff!=='all'){if(!isFinite(resolved.floor)||!isFinite(r.dpeInfo?.floor))return false;const d=Math.abs(resolved.floor-r.dpeInfo.floor);if(ff==='same'&&d!==0)return false;if(ff==='one'&&d>1)return false;}if(ft==='same'){if(resolved.traversant===null||r.dpeInfo?.traversant===null||r.dpeInfo?.traversant!==resolved.traversant)return false;}if(fc!=='all'){const c=publicCoproStatus(r);if(fc==='yes'&&c.value!==true)return false;if(fc==='no'&&c.value!==false)return false;}if(fi!=='all'&&(r.workManual?.interior||'UNKNOWN')!==fi)return false;if(fw!=='all'){const src=worksSourceType(r);if(fw==='audit'&&src!=='audit')return false;if(fw==='manual'&&src!=='manual')return false;if(fw==='known'&&src==='none')return false;}return true;});return applySort?qualifiedSortRows(filtered):filtered;}
function gapHtml(r,t){const g=pctGap(r.surface,t.surface);if(!isFinite(g))return'—';const p=(r.surface/t.surface-1)*100,cls=Math.abs(p)<=10?'gap-good':Math.abs(p)<=20?'gap-mid':'gap-bad';return`<span class="${cls}">${p>=0?'+':''}${p.toFixed(1)}%</span>`;}

// --- Affichage données publiques ---
function bdnbMini(b){if(!b)return'<span class="pubchip">BDNB —</span>';const bits=[];if(isFinite(b.levels))bits.push(f0(b.levels)+' niv.');if(isFinite(b.nbLog))bits.push(f0(b.nbLog)+' log.');if(isFinite(b.year))bits.push('≈ '+f0(b.year));return`<span class="pubchip ok">BDNB ${bits.length?'· '+bits.join(' · '):'trouvé'}</span>`;}
function rnicMini(p){if(!p?.immat)return'<span class="pubchip">RNIC —</span>';if(p.rnic?.procedureFields&&p.rnic.procedureAlert)return'<span class="pubchip warn">RNIC · ⚠ signal procédure</span>';if(p.rnic)return`<span class="pubchip ok">RNIC${isFinite(p.rnic.lots)?' · '+f0(p.rnic.lots)+' lots':''}</span>`;return'<span class="pubchip gold">RNIC · immatriculation trouvée</span>';}
function dpePublicMini(di){const bits=[];if(isFinite(di?.floor))bits.push(floorLabel(di.floor));if(di?.traversant!==null&&di?.traversant!==undefined)bits.push('Traversant '+boolLabel(di.traversant));if(di?.orientation)bits.push(di.orientation);return bits.length?bits.map(x=>`<span class="pubchip gold">${esc(x)}</span>`).join(''):'';}
function publicDetailsButton(r){return r.dpeInfo||r.publicInfo?.done||r.auditInfo?`<button class="pubbtn" onclick="openPublicModal('${encodeURIComponent(rowKey(r))}')">Détails</button>`:'—';}
function publicFieldRows(entries){return entries.filter(([,v])=>meaningful(v)).map(([k,v])=>`<div class="public-row"><span class="pk">${esc(k)}</span><span class="pv">${esc(v)}</span></div>`).join('')||'<div class="public-mini">Aucune donnée disponible.</div>';}
function targetPublicSummaryHtml(){const di=state.qual.targetMatch,p=state.qual.targetPublic,o=p?.osm,a=state.qual.targetAudit;const chips=[dpePublicMini(di),bdnbMini(p?.bdnb),rnicMini(p),o?.found?'<span class="pubchip ok">OSM · indices trouvés</span>':'',a?`<span class="pubchip gold">AUDIT · ${isFinite(a.costMid)?eur(a.costMid):'trouvé'}</span>`:''].filter(Boolean).join('');return`<div class="public-summary">${chips}</div>`;}
function openPublicModal(encoded){const k=decodeURIComponent(encoded),r=state.qual.rows.find(x=>rowKey(x)===k);if(!r)return;renderPublicModal(r,r.voie||'Comparable');}
function renderPublicModal(r,title){const di=r.dpeInfo||{},p=r.publicInfo||{},b=p.bdnb||{},rn=p.rnic,o=p.osm||{},an=annexeInfoForRow(r),ext=exteriorPotential(r),au=r.auditInfo;document.getElementById('publicModalTitle').textContent=title;const oi=di.orientationInfo||{};const dpeRows=[['DPE',di.dpe||'—'],['Fiabilité du rapprochement',confidenceLabel(di.confidence)],['N° DPE',di.numero],['Étage',floorLabel(di.floor)],['Niveaux immeuble',isFinite(di.buildingLevels)?f0(di.buildingLevels):''],['Niveaux logement',isFinite(di.homeLevels)?f0(di.homeLevels):''],['Traversant',di.traversant===null?'':boolLabel(di.traversant)],['Position logement',di.position],['Orientation / exposition',di.orientation],['Méthode orientation',oi.method||''],['Identifiant BAN',di.banId],['Identifiant RNB',di.rnbId],['Immatriculation copro',di.coproId]];const bdnbRows=[['Fiabilité bâtiment',b.ambiguous?('Ambigu · '+b.alternatives+' bâtiments possibles'):(b?'Rapprochement unique':'' )],['ID bâtiment BDNB',b.id],['ID RNB',b.rnb],['Adresse BDNB',b.address],['Année construction',isFinite(b.year)?f0(b.year):''],['Nombre de logements',isFinite(b.nbLog)?f0(b.nbLog):''],['Nombre de niveaux',isFinite(b.levels)?f0(b.levels):''],['Hauteur',isFinite(b.height)?b.height.toLocaleString('fr-FR',{maximumFractionDigits:1})+' m':''],['DPE bâtiment',b.dpe],['Immatriculation copro',b.coproId]];const rnicRows=rn?.fields||[];const osmRows=[['Ascenseur cartographié',o.elevator?'Oui':''],['Garage / carport cartographié',o.garage?'Oui':''],['Parking cartographié à proximité',o.parking?'Oui':''],['Balcon cartographié',o.balcony?'Oui':''],['Terrasse cartographiée',o.terrace?'Oui':''],['Jardin cartographié',o.garden?'Oui':''],['Emprise bâtiment OSM',isFinite(o.buildingFootprint)?'≈ '+f0(o.buildingFootprint)+' m²':''],['Extérieur potentiel',isFinite(ext)?'≈ '+f0(ext)+' m²':''],['Dépendances même mutation DVF',an?.dependences?String(an.dependences):'']];const auditRows=au?[['N° audit',au.numero],['Date audit',au.date],['Fiabilité rapprochement',confidenceLabel(au.confidence)],['Adresse audit',au.address],['Surface audit',isFinite(au.surface)?f0(au.surface)+' m²':''],['Coût min repéré dans l’audit',isFinite(au.costMin)?eur(au.costMin):''],['Coût max repéré dans l’audit',isFinite(au.costMax)?eur(au.costMax):''],['Budget travaux préconisés',au.confidence==='high'&&isFinite(au.costMid)?eur(au.costMid):(isFinite(au.costMid)?'Montant brut repéré · rapprochement à confirmer':'')],['Scénarios / travaux',(au.works||[]).join(' · ')]]:[];document.getElementById('publicModalBody').innerHTML=`<div class="public-grid"><div class="public-box"><h4>ADEME — DPE</h4>${publicFieldRows(dpeRows)}</div><div class="public-box"><h4>ADEME — AUDIT travaux</h4>${au?publicFieldRows(auditRows):'<div class="public-mini">Aucun audit énergétique suffisamment fiable rapproché.</div>'}</div><div class="public-box"><h4>BDNB Open — CSTB</h4>${publicFieldRows(bdnbRows)}</div><div class="public-box"><h4>RNIC — ANAH</h4>${rn?publicFieldRows(rnicRows):'<div class="public-mini">'+(p.immat?'Immatriculation trouvée mais détail RNIC indisponible via API tabulaire.':'Aucune immatriculation de copropriété rapprochée.')+'</div>'}</div><div class="public-box"><h4>OpenStreetMap + DVF — indices gratuits</h4>${publicFieldRows(osmRows)}<div class="public-mini">Une présence OSM est un indice cartographique. Son absence ne signifie jamais « non ». Parking/garage/jardin/balcon/terrasse ne sont pas automatiquement attribués juridiquement au lot.</div></div></div><div class="public-source-note">Étape 1 bis : l’application croise plusieurs sources gratuites. Une donnée absente reste inconnue ; elle n’est ni déduite ni assimilée à « non ». L’extérieur potentiel est une estimation = terrain DVF − emprise OSM du bâtiment lorsque les deux valeurs sont disponibles.</div>`;document.getElementById('publicModal').classList.add('open');}
function closePublicModal(){document.getElementById('publicModal').classList.remove('open');}
function openTargetPublicModal(){const t=state.qual.target||{},pseudo=makePseudoTargetRow(t);pseudo.dpeInfo=state.qual.targetMatch;pseudo.publicInfo=state.qual.targetPublic;pseudo.auditInfo=state.qual.targetAudit;renderPublicModal(pseudo,state.addresses[0]?.label||'Bien cible');}


function ensureWorkModal(){if(document.getElementById('workModal'))return;const d=document.createElement('div');d.className='modal-bg';d.id='workModal';d.innerHTML=`<div class="modal" style="width:620px"><div class="modal-h"><h3 id="workModalTitle">État & travaux du comparable</h3><button class="x" onclick="closeWorkModal()">×</button></div><div class="modal-b"><div id="workModalAuto" class="work-modal-note"></div><div class="work-modal-grid"><div class="qual-field"><label>État intérieur</label><select id="workInterior" onchange="syncComparableInteriorCoef()">${INTERIOR_STATES.map(([v,l])=>`<option value="${v}">${l}</option>`).join('')}</select></div><div class="qual-field state-coef-wrap"><label>Coefficient état (%)</label><input class="state-coef-input" id="workInteriorCoef" type="number" min="-40" max="40" step="0.5"></div><div class="qual-field"><label>Budget travaux estimé (€)</label><input id="workBudget" type="number" min="0" step="1000" placeholder="Ex : 60000"></div><div class="qual-field full"><label>Note libre</label><input id="workNote" type="text" placeholder="Ex : cuisine/SDB à refaire, peinture, électricité…"></div></div><div class="qual-actions"><button class="qual-primary" onclick="saveWorkModal()">Enregistrer</button><button class="qual-secondary" onclick="clearWorkModal()">Effacer la saisie</button><button class="qual-secondary" onclick="closeWorkModal()">Annuler</button></div></div></div>`;document.body.appendChild(d);}
let currentWorkRowKey='';
function syncComparableInteriorCoef(){const st=document.getElementById('workInterior')?.value||'UNKNOWN',el=document.getElementById('workInteriorCoef');if(el)el.value=defaultInteriorCoef(st);}
function openWorkModal(encoded){ensureWorkModal();const k=decodeURIComponent(encoded),r=state.qual.rows.find(x=>rowKey(x)===k);if(!r)return;currentWorkRowKey=k;document.getElementById('workModalTitle').textContent='État & travaux — '+(r.voie||'Comparable');const m=r.workManual||{},a=r.auditInfo,e=energyWorksInfo(r);document.getElementById('workInterior').value=m.interior||'UNKNOWN';document.getElementById('workInteriorCoef').value=isFinite(+m.interiorCoef)?+m.interiorCoef:defaultInteriorCoef(m.interior||'UNKNOWN');document.getElementById('workBudget').value=isFinite(+m.budget)?+m.budget:'';document.getElementById('workNote').value=m.note||'';document.getElementById('workModalAuto').innerHTML=`<b>Données automatiques :</b> ${esc(e.label)}${r.dpeInfo?.dpe?' · DPE '+esc(r.dpeInfo.dpe):''}${a?` · AUDIT ${confidenceLabel(a.confidence)}${a.confidence==='high'&&isFinite(a.costMid)?' · travaux énergétiques préconisés ≈ <b>'+eur(a.costMid)+'</b>':(isFinite(a.costMid)?' · montant repéré mais non retenu car rapprochement insuffisant':'')}`:' · aucun audit rapproché'}.<br>La saisie manuelle ci-dessous est prioritaire. Le coefficient d’état se remplit automatiquement d’après l’état choisi mais reste modifiable.`;document.getElementById('workModal').classList.add('open');}
function closeWorkModal(){document.getElementById('workModal')?.classList.remove('open');currentWorkRowKey='';}
function saveWorkModal(){const r=state.qual.rows.find(x=>rowKey(x)===currentWorkRowKey);if(!r)return;const v=document.getElementById('workBudget').value;r.workManual={interior:document.getElementById('workInterior').value,interiorCoef:+document.getElementById('workInteriorCoef').value||0,budget:v===''?NaN:+v,note:document.getElementById('workNote').value.trim()};recalcQualifiedScores();closeWorkModal();renderQualifiedResults();}
function clearWorkModal(){const r=state.qual.rows.find(x=>rowKey(x)===currentWorkRowKey);if(!r)return;r.workManual=null;recalcQualifiedScores();closeWorkModal();renderQualifiedResults();}
function qualCardHtml(r,i){const q=qualityInfo(r.qScore),di=r.dpeInfo,p=r.publicInfo,a=annexeInfoForRow(r),o=p?.osm,w=energyWorksInfo(r),cp=correctedPpm(r);const sig=[];if(a?.dependences)sig.push('DVF + annexe');if(o?.garage)sig.push('garage');if(o?.parking)sig.push('parking');if(o?.elevator)sig.push('ascenseur');if(o?.garden)sig.push('jardin');if(o?.terrace)sig.push('terrasse');if(o?.balcony)sig.push('balcon');return`<div class="qual-card"><button class="keep ${r.qSelected?'on':''}" onclick="toggleQualified('${encodeURIComponent(rowKey(r))}')" title="Retenir comme comparable">★</button><div class="rank">#${i+1} · ${q[0]}</div><div class="score">${r.qScore}<span style="font-size:12px">/100</span></div><div class="quality">${esc(r.voie||r.commune||'Comparable')}</div><div class="meta"><b>${f0(r.surface)} m²</b> · ${isFinite(r.pieces)?r.pieces+' p.':'—'} · ${ppmF(r.ppm)}${isFinite(cp)&&Math.abs(cp-r.ppm)>=1?`<br><b style="color:#a9ddb9">Corrigé état/travaux : ${ppmF(cp)}</b>`:''}<br>${dpeBadge(di?.dpe)} <span class="conf ${di?.confidence||''}" style="display:inline">${confidenceLabel(di?.confidence)}</span><br><span style="color:#d9c57a">${esc(w.label)}</span>${r.workManual?.interior&&r.workManual.interior!=='UNKNOWN'?` · ${esc(interiorLabel(r.workManual.interior))}`:''}<br>${periodLabel(di?.period)} · ${isFinite(r.dist)?f0(r.dist)+' m':'—'}${sig.length?`<br><span style="color:#d9c57a">${esc(sig.slice(0,3).join(' · '))}</span>`:''}<br>${dpePublicMini(di)}${p?.done?bdnbMini(p.bdnb)+rnicMini(p):''}</div></div>`;}
function qualifiedSummaryHtml(){const S=state.qual.rows.filter(r=>r.selected&&r.qSelected),raw=S.map(r=>r.ppm).filter(isFinite),corr=S.map(correctedPpm).filter(isFinite),t=state.qual.target||{},rawMed=median(raw),low=quant(corr,.25),med=median(corr),high=quant(corr,.75),tb=targetWorkBudget(),coef=targetInteriorCoef(),mode=correctionMode(),modeLab=mode==='STATE'?'État %':mode==='BUDGET'?'Budget €':'État % + budget';return`<div class="qsummary"><div class="qsum"><div class="k">Comparables retenus</div><div class="v">${S.length}</div></div><div class="qsum"><div class="k">Médiane brute DVF</div><div class="v">${ppmF(rawMed)}</div></div><div class="qsum gold"><div class="k">Médiane corrigée</div><div class="v">${ppmF(med)}</div></div><div class="qsum"><div class="k">Fourchette corrigée</div><div class="v" style="font-size:16px">${ppmF(low)} – ${ppmF(high)}</div></div><div class="qsum"><div class="k">État cible</div><div class="v" style="font-size:15px">${pct1(coef)} · ${esc(modeLab)}</div></div><div class="qsum"><div class="k">Travaux cible</div><div class="v">${eur(tb)}</div></div><div class="qsum gold"><div class="k">Valeur cible corrigée</div><div class="v">${isFinite(med)&&isFinite(t.surface)?eur(med*t.surface):'—'}</div></div></div>`;}
function dpeMarketHtml(){const rows=state.qual.rows.filter(r=>r.selected&&r.dpeInfo?.dpe&&isFinite(r.ppm)),by={};rows.forEach(r=>(by[r.dpeInfo.dpe]=by[r.dpeInfo.dpe]||[]).push(r.ppm));const target=resolveTarget(state.qual.target||{}).dpe,base=target&&by[target]?.length>=2?median(by[target]):NaN;let any=false,h='';DPE_ORDER.forEach(d=>{const a=by[d]||[];if(a.length<2){h+=`<div class="dpe-market-card">${dpeBadge(d)}<div class="mppm">—</div><div class="mn">${a.length} réf.</div></div>`;return;}any=true;const m=median(a),delta=isFinite(base)?(m/base-1)*100:NaN;h+=`<div class="dpe-market-card">${dpeBadge(d)}<div class="mppm">${ppmF(m)}</div><div class="mn">${a.length} références</div><div class="mdelta">${isFinite(delta)?((delta>=0?'+':'')+delta.toFixed(1)+'% vs '+target):'médiane locale'}</div></div>`;});return`<div class="qual-panel"><h3>Effet DPE observé dans les références enrichies</h3><div class="subtxt">Médianes locales uniquement lorsque la classe contient au moins 2 références. À interpréter avec prudence : ce n’est pas un coefficient national.</div>${any?`<div class="dpe-market">${h}</div>`:'<div class="placeholder">Pas encore assez de DPE rapprochés pour comparer les classes.</div>'}</div>`;}
function buildingCell(r){const p=r.publicInfo,b=p?.bdnb;if(!p?.done)return'<span class="conf">non enrichi</span>';if(!b)return'<span class="conf">non trouvé</span>';const bits=[];if(isFinite(b.levels))bits.push(f0(b.levels)+' niv.');if(isFinite(b.nbLog))bits.push(f0(b.nbLog)+' log.');if(isFinite(b.year))bits.push('≈ '+f0(b.year));const warn=b.ambiguous?`<span class="conf low">⚠ ${b.alternatives} bâtiments possibles — seules les données communes sont affichées</span>`:'';return`${bits.join(' · ')||(b.ambiguous?'BDNB ambigu':'BDNB trouvé')}<span class="conf">${esc(b.id||'')}</span>${warn}`;}
function coproCell(r){const p=r.publicInfo,c=publicCoproStatus(r);if(c.value===true){const immat=c.immat||p?.immat||'';if(p?.rnic?.procedureFields&&p.rnic.procedureAlert)return`<span class="mutationpill warn">⚠ Copro · signal RNIC</span><span class="conf">${esc(immat)}</span>`;return`<span class="mutationpill simple">✓ Copropriété confirmée</span><span class="conf">${esc(c.label)}${immat?' · '+esc(immat):''}${isFinite(p?.rnic?.lots)?' · '+f0(p.rnic.lots)+' lots':''}</span>`;}if(c.value===false&&r.type==='Maison')return`<span class="mutationpill simple">○ Non détectée</span><span class="conf">${esc(c.label)} · résultat figé jusqu’à actualisation</span>`;if(!p?.done)return'<span class="conf">vérification en cours / source indisponible</span>';return`<span class="conf">${esc(c.label||'Inconnu')}</span>`;}
function qualifiedTableHtml(rows){const t=state.qual.target||{};let h=`<thead><tr><th>Retenir</th>${qualHeader('score','Score')}${qualHeader('quality','Qualité')}${qualHeader('date','Date')}${qualHeader('distance','Distance','num')}${qualHeader('type','Type')}${qualHeader('surface','Surface','num')}${qualHeader('surfaceGap','Écart surface','num')}${qualHeader('pieces','Pièces','num')}${qualHeader('dpe','DPE')}${qualHeader('construction','Construction')}${qualHeader('floor','Étage')}${qualHeader('copro','Copropriété')}${qualHeader('terrain','Terrain','num')}<th>Équipements / extérieurs</th>${qualHeader('works','Travaux / source')}${qualHeader('workBudget','Budget travaux préconisés (audit)','num')}${qualHeader('val','Prix vendu','num')}${qualHeader('ppm','€/m² brut','num')}<th>Correction travaux</th>${qualHeader('correctedPpm','€/m² corrigé','num')}${qualHeader('medianGap','Écart médiane','num')}${qualHeader('mutation','Mutation')}${qualHeader('voie','Adresse')}<th>Sources</th></tr></thead><tbody>`;rows.forEach(r=>{const q=qualityInfo(r.qScore),di=r.dpeInfo,wb=comparableWorkBudget(r),c=totalCorrectionPerM2(r),cp=correctedPpm(r);h+=`<tr class="${r.qSelected?'qkept':''}"><td><input class="starck" type="checkbox" ${r.qSelected?'checked':''} onchange="toggleQualified('${encodeURIComponent(rowKey(r))}')"></td><td><span class="scorepill">${r.qScore}</span><span class="conf">couverture ${r.qCoverage}%</span></td><td><span class="qualitypill ${q[1]}">${q[0]}</span></td><td>${r.date||'—'}</td><td class="num">${isFinite(r.dist)?f0(r.dist)+' m':'—'}${microLocationHtml(r)}</td><td>${esc(r.type)}</td><td class="num">${r.surface>0?f0(r.surface)+' m²':'—'}</td><td class="num">${gapHtml(r,t)}</td><td class="num">${isFinite(r.pieces)?r.pieces:'—'}</td><td>${dpeBadge(di?.dpe)}<span class="conf ${di?.confidence||''}">${confidenceLabel(di?.confidence)}</span></td><td>${periodLabel(di?.period)}${isFinite(di?.year)?`<span class="conf">${di.year}</span>`:''}</td><td>${floorLabel(di?.floor)}</td><td>${coproCell(r)}</td><td class="num">${r.terrain>0?f0(r.terrain)+' m²':'—'}</td><td>${freeFeaturesHtml(r)}</td><td>${worksCellHtml(r)}</td><td class="num">${wb.value>0?`<b>${eur(wb.value)}</b><span class="conf">${wb.source==='audit'?'AUDIT ADEME':'saisie manuelle'}</span>`:'—'}</td><td class="num"><b>${eur(r.val)}</b></td><td class="num">${ppmF(r.ppm)}</td><td>${correctionBreakdownHtml(r)}</td><td class="num">${isFinite(cp)?`<span class="corrected-price">${ppmF(cp)}</span>`:'—'}</td><td class="num">${medianGapHtml(r)}</td><td>${mutationBadgeHtml(r)}</td><td>${addrLink(r)}</td><td>${publicDetailsButton(r)}</td></tr>`;});return h+'</tbody>';}
function filterBarHtml(){const f=state.qual.filters||{},o=(v,k)=>String(f[k]||'all')===String(v)?' selected':'';return`<div class="qual-filterbar"><div class="qf"><label>DPE</label><select id="qfDpe" onchange="refreshQualifiedView()"><option value="all"${o('all','dpe')}>Tous</option><option value="same"${o('same','dpe')}>Identique</option><option value="one"${o('one','dpe')}>± 1 classe</option></select></div><div class="qf"><label>Surface</label><select id="qfSurface" onchange="refreshQualifiedView()"><option value="all"${o('all','surface')}>Toutes</option><option value="5"${o('5','surface')}>± 5 %</option><option value="10"${o('10','surface')}>± 10 %</option><option value="15"${o('15','surface')}>± 15 %</option><option value="20"${o('20','surface')}>± 20 %</option></select></div><div class="qf"><label>Pièces</label><select id="qfPieces" onchange="refreshQualifiedView()"><option value="all"${o('all','pieces')}>Toutes</option><option value="same"${o('same','pieces')}>Identique</option><option value="one"${o('one','pieces')}>± 1 pièce</option></select></div><div class="qf"><label>Construction</label><select id="qfPeriod" onchange="refreshQualifiedView()"><option value="all"${o('all','period')}>Toutes</option><option value="same"${o('same','period')}>Même période</option></select></div><div class="qf"><label>Étage</label><select id="qfFloor" onchange="refreshQualifiedView()"><option value="all"${o('all','floor')}>Tous</option><option value="same"${o('same','floor')}>Identique</option><option value="one"${o('one','floor')}>± 1 étage</option></select></div><div class="qf"><label>Traversant</label><select id="qfTraversant" onchange="refreshQualifiedView()"><option value="all"${o('all','traversant')}>Tous</option><option value="same"${o('same','traversant')}>Identique</option></select></div><div class="qf"><label>Distance</label><select id="qfDistance" onchange="refreshQualifiedView()"><option value="all"${o('all','distance')}>Toutes</option><option value="250"${o('250','distance')}>≤ 250 m</option><option value="500"${o('500','distance')}>≤ 500 m</option><option value="1000"${o('1000','distance')}>≤ 1 km</option></select></div><div class="qf"><label>Récence</label><select id="qfRecency" onchange="refreshQualifiedView()"><option value="all"${o('all','recency')}>Toutes</option><option value="12"${o('12','recency')}>≤ 12 mois</option><option value="24"${o('24','recency')}>≤ 24 mois</option><option value="36"${o('36','recency')}>≤ 36 mois</option></select></div><div class="qf"><label>Mutation</label><select id="qfMutation" onchange="refreshQualifiedView()"><option value="all"${o('all','mutation')}>Toutes</option><option value="simple"${o('simple','mutation')}>Ventes simples uniquement</option></select></div><div class="qf"><label>Copro maison</label><select id="qfCopro" onchange="refreshQualifiedView()"><option value="all"${o('all','copro')}>Toutes</option><option value="yes"${o('yes','copro')}>En copropriété</option><option value="no"${o('no','copro')}>Non détectée</option></select></div><div class="qf"><label>État intérieur</label><select id="qfInterior" onchange="refreshQualifiedView()"><option value="all"${o('all','interior')}>Tous</option>${INTERIOR_STATES.filter(x=>x[0]!=='UNKNOWN').map(([v,l])=>`<option value="${v}"${o(v,'interior')}>${l}</option>`).join('')}</select></div><div class="qf"><label>Travaux</label><select id="qfWorks" onchange="refreshQualifiedView()"><option value="all"${o('all','works')}>Tous</option><option value="known"${o('known','works')}>Info travaux connue</option><option value="audit"${o('audit','works')}>Audit ADEME</option><option value="manual"${o('manual','works')}>Saisie manuelle</option></select></div><button class="qual-secondary" onclick="resetQualifiedFilters()">Réinitialiser</button></div>`;}
function targetMatchNote(){const t=state.qual.target||{},m=state.qual.targetMatch,resolved=resolveTarget(t);if(!m&&t.dpe==='AUTO')return`Aucun DPE suffisamment fiable n’a été rapproché automatiquement du bien cible. Les critères publics inconnus ne pénalisent pas le score.`;let txt=`DPE : ${dpeBadge(resolved.dpe)} · Construction : <b>${periodLabel(resolved.period)}</b>`;if(isFinite(resolved.floor))txt+=` · Étage : <b>${floorLabel(resolved.floor)}</b>`;if(resolved.traversant!==null)txt+=` · Traversant : <b>${boolLabel(resolved.traversant)}</b>`;if(resolved.orientation)txt+=` · Orientation : <b>${resolved.orientation}</b>`;if(t.type==='Maison'&&resolved.copro!==null){const auto=t.copro==='AUTO',lab=resolved.copro?'Oui':'Non détectée';txt+=` · Copropriété : <b>${lab}${auto?' (auto)':''}</b>`;}if(m?.date)txt+=` · DPE du ${esc(m.date)}`;return txt+'.';}
function renderQualifiedResults(){const body=document.getElementById('qualBody');if(!body||!state.qual.rows.length){renderQualifiedBase();return;}const source=qualifiedSourceRows(),baseRows=qualifiedFilteredRows(false),rows=qualifiedSortRows(baseRows),top=[...baseRows].sort((a,b)=>b.qScore-a.qScore||(a.dist-b.dist)).slice(0,5);const remainingDpe=state.qual.enrichedAll?'':`<button class="qual-secondary" onclick="runQualifiedRanking(true)">Enrichir tous les DPE (${source.length})</button>`,remainingPublic=state.qual.publicEnrichedAll?'':`<button class="qual-secondary" onclick="enrichQualifiedPublic(true)">Enrichir toutes les données publiques (${source.length})</button>`,remainingAudit=state.qual.auditEnrichedAll?'':`<button class="qual-secondary" onclick="enrichQualifiedWorks(true)">Enrichir tous les AUDITS travaux (${source.length})</button>`;body.innerHTML=`<div class="qual-hero"><div><h2>Détermination du prix</h2><p>Étape 1 ter : le prix DVF reste intact, puis une seconde lecture calcule un €/m² corrigé selon l’état intérieur (%) et/ou le budget travaux.</p></div><div class="qual-source">${Math.min(state.qual.enrichedCount,source.length)}/${source.length} DPE · ${source.filter(r=>r.publicInfo?.done).length}/${source.length} public · ${source.filter(r=>r.auditChecked).length}/${source.length} audit</div></div>
  <div class="qual-panel"><h3>Bien à estimer</h3><div class="subtxt">${esc(state.addresses[0]?.label||'')}</div><div class="target-dpe-note">${targetMatchNote()}</div>${targetPublicSummaryHtml()}${targetWorksSummaryHtml()}<div class="qual-actions"><button class="qual-secondary" onclick="editQualifiedTarget()">Modifier les caractéristiques / travaux</button><button class="qual-secondary" onclick="openTargetPublicModal()">Voir les données publiques cible</button>${remainingDpe}${remainingPublic}${remainingAudit}</div></div>
  ${qualifiedSummaryHtml()}
  <div class="qual-panel"><h3>Top 5 des comparables</h3><div class="subtxt">L’état et son coefficient restent modifiables via « ✎ État / travaux », sans encombrer le tableau. La colonne Travaux conserve le budget éventuel et la correction appliquée.</div><div class="qual-top">${top.length?top.map(qualCardHtml).join(''):'<div class="placeholder">Aucun comparable avec les filtres actuels.</div>'}</div>${filterBarHtml()}<div class="qual-table-wrap"><table class="qual-table" id="qualTable">${qualifiedTableHtml(rows)}</table></div><div class="qual-warn">Correction prix : le coefficient d’état est calculé par différence entre l’état cible et l’état du comparable. Barème par défaut : neuf +12 %, très bon +7 %, bon 0 %, à rafraîchir −5 %, à rénover −12 %. Tous ces pourcentages sont modifiables. Le mode « État + budget » cumule volontairement les deux corrections : utilise-le seulement si tu veux éviter qu’elles décrivent deux fois les mêmes travaux. La valeur DVF d’origine reste toujours intacte.</div></div>${dpeMarketHtml()}`;}
function refreshQualifiedView(){state.qual.filters={dpe:document.getElementById('qfDpe')?.value||'all',surface:document.getElementById('qfSurface')?.value||'all',pieces:document.getElementById('qfPieces')?.value||'all',period:document.getElementById('qfPeriod')?.value||'all',distance:document.getElementById('qfDistance')?.value||'all',recency:document.getElementById('qfRecency')?.value||'all',mutation:document.getElementById('qfMutation')?.value||'all',floor:document.getElementById('qfFloor')?.value||'all',traversant:document.getElementById('qfTraversant')?.value||'all',copro:document.getElementById('qfCopro')?.value||'all',interior:document.getElementById('qfInterior')?.value||'all',works:document.getElementById('qfWorks')?.value||'all'};const baseRows=qualifiedFilteredRows(false),rows=qualifiedSortRows(baseRows),tbl=document.getElementById('qualTable');if(tbl)tbl.innerHTML=qualifiedTableHtml(rows);const top=document.querySelector('.qual-top');if(top){const topRows=[...baseRows].sort((a,b)=>b.qScore-a.qScore||(a.dist-b.dist)).slice(0,5);top.innerHTML=topRows.map(qualCardHtml).join('')||'<div class="placeholder">Aucun comparable avec les filtres actuels.</div>';}}
function resetQualifiedFilters(){state.qual.filters={dpe:'all',surface:'all',pieces:'all',period:'all',distance:'all',recency:'all',mutation:'all',floor:'all',traversant:'all',copro:'all',interior:'all',works:'all'};['qfDpe','qfSurface','qfPieces','qfPeriod','qfDistance','qfRecency','qfMutation','qfFloor','qfTraversant','qfCopro','qfInterior','qfWorks'].forEach(id=>{const e=document.getElementById(id);if(e)e.value='all';});refreshQualifiedView();}
function toggleQualified(encoded){const k=decodeURIComponent(encoded),r=state.qual.rows.find(x=>rowKey(x)===k);if(!r)return;r.qSelected=!r.qSelected;renderQualifiedResults();}
function editQualifiedTarget(){state.qual.rows=[];state.qual.targetPublic=null;state.qual.targetAudit=null;renderQualifiedBase();}




/* =========================================================
   DÉTERMINATION DU PRIX — MODE TABLEAU SIMPLE
   Toutes les ventes conservées dans l'analyse sont affichées. Aucun score,
   aucun Top 5 et aucun prix cible automatique : l'utilisateur
   arbitre directement avec les filtres et les tris.
   ========================================================= */
function qualifiedSourceRows(){return sel();}

function simpleEquipmentMatch(r,kind){
  const o=r?.publicInfo?.osm||{},a=annexeInfoForRow(r);
  if(kind==='any')return !!(o.elevator||o.parking||o.garage||o.balcony||o.terrace||o.garden||a?.dependences);
  if(kind==='dependence')return !!a?.dependences;
  return !!o?.[kind];
}
function simpleWorkBudget(r){
  const m=manualWorkBudget(r);if(isFinite(m))return{value:m,source:'manual',confirmed:true};
  const a=r?.auditInfo;
  // Un montant AUDIT n'est affiché comme exploitable que si le rapprochement
  // adresse + surface + temporalité est classé "high".
  if(a&&isFinite(a.costMid)&&a.costMid>0){
    if(a.confidence==='high')return{value:a.costMid,source:'audit',confirmed:true};
    return{value:NaN,source:'audit_unconfirmed',confirmed:false,rawValue:a.costMid};
  }
  return{value:NaN,source:a?'audit_no_cost':'none',confirmed:false};
}
function simpleWorksCellHtml(r){
  const a=r?.auditInfo,b=simpleWorkBudget(r),e=energyWorksInfo(r),chips=[];
  if(a){
    const certain=a.confidence==='high';
    chips.push(`<span class="work-pill ${certain?'audit':'unknown'}">${certain?'Audit ADEME rapproché':'Audit ADEME possible'}</span>`);
    if(a?.works?.length&&certain)chips.push(`<span class="work-pill audit">${esc(a.works[0])}</span>`);
    if(b.source==='audit'&&isFinite(b.value)&&b.value>0)chips.push(`<span class="work-pill audit">Travaux préconisés · ${eur(b.value)}</span>`);
    else if(b.source==='audit_unconfirmed')chips.push(`<span class="work-pill unknown">Budget à confirmer</span>`);
  }else{
    chips.push(`<span class="work-pill ${e.cls}">${esc(e.label)}</span>`);
  }
  return `<div class="work-stack"><div class="work-line">${chips.join('')}</div>${a?.date?`<span class="work-sub">Audit du ${esc(a.date)} · ${confidenceLabel(a.confidence)}${a.confidence!=='high'?' · montant non retenu':''}</span>`:''}<button class="work-edit" onclick="openWorkModal('${encodeURIComponent(rowKey(r))}')">✎ Détails travaux</button></div>`;
}

async function enrichAllAuditsSimple(rows,progress){
  const todo=rows.filter(r=>!r.auditChecked);let done=0,errors=0,cursor=0;
  async function worker(){while(cursor<todo.length){const r=todo[cursor++];try{r.auditInfo=await lookupAuditForRow(r);r.auditChecked=true;saveStableRow(r);}catch(e){errors++;r.auditInfo=null;r.auditChecked=false;}done++;progress?.(done,todo.length,errors);await sleep(150);}}
  await Promise.all(Array.from({length:Math.min(3,todo.length)},worker));return{count:todo.length,errors};
}

function simpleEnrichmentCounts(){
  const rows=state.qual.rows||[];return{
    total:rows.length,
    dpe:rows.filter(r=>r.dpeChecked).length,
    public:rows.filter(r=>r.publicInfo?.done).length,
    audit:rows.filter(r=>r.auditChecked).length
  };
}

async function enrichSimpleDetermination(force=false){
  if(state.qual.running||!state.qual.rows.length)return;
  state.qual.simpleStarted=true;state.qual.running=true;
  try{
    const rows=state.qual.rows;
    if(force){
      clearRuntimeEnrichmentCaches();
      rows.forEach(r=>{const locked=loadCoproDecision(r,r.publicInfo?.banId||r.dpeInfo?.banId||'');clearStableRow(r);r.dpeChecked=false;delete r.dpeInfo;r.publicInfo=locked?{done:false,osmChecked:false,coproDecision:locked,immat:locked.immat||'',immatSource:locked.source||'',errors:[]}:null;r.auditChecked=false;r.auditInfo=null;});
    }
    setStatus(`Tableau affiché · enrichissement DPE en arrière-plan (${rows.length} ventes)…`,'info');
    const er=await enrichRowsDpe(rows,(d,n,e)=>{const info=document.getElementById('srcInfo');if(info)info.textContent=`DPE ADEME ${d}/${n}${e?' · '+e+' erreur(s)':''}…`;});
    state.qual.dpeErrors=er.errors;state.qual.enrichedCount=rows.filter(r=>r.dpeInfo!=null).length;state.qual.enrichedAll=true;
    renderQualifiedResults();
    setStatus(`DPE chargé · enrichissement copropriété / équipements / travaux en parallèle…`,'info');
    const [pe,ae]=await Promise.all([
      enrichRowsPublic(rows,(d,n)=>{const info=document.getElementById('srcInfo');if(info)info.textContent=`BDNB / RNIC / OSM ${d}/${n}…`;}),
      enrichAllAuditsSimple(rows,(d,n)=>{const el=document.getElementById('simpleProgress');if(el)el.textContent=`AUDIT ADEME ${d}/${n}…`;})
    ]);
    state.qual.publicErrors+=pe.errors;state.qual.auditErrors+=ae.errors;
    state.qual.publicEnrichedCount=rows.filter(r=>r.publicInfo?.done).length;state.qual.publicEnrichedAll=state.qual.publicEnrichedCount>=rows.length;
    state.qual.auditEnrichedCount=rows.filter(r=>r.auditChecked).length;state.qual.auditEnrichedAll=state.qual.auditEnrichedCount>=rows.length;
    renderQualifiedResults();
    const c=simpleEnrichmentCounts();
    setStatus(`Tableau enrichi : ${c.total} ventes · ${c.dpe} DPE · ${c.public} données bâtiment/copro/OSM · ${c.audit} audits vérifiés.`,'ok');
  }catch(e){console.error(e);setStatus('Enrichissement du tableau : '+e.message,'err');}
  finally{state.qual.running=false;}
}

function renderQualifiedBase(){
  const body=document.getElementById('qualBody');if(!body)return;
  const source=qualifiedSourceRows();
  if(!source.length){body.innerHTML='<div class="qual-empty">Lance d’abord une analyse DVF. Toutes les ventes issues de cette analyse apparaîtront ensuite ici.</div>';return;}
  state.qual.rows=[...source];
  const profiles=buildMutationProfiles();let restored=0;
  state.qual.rows.forEach(r=>{if(loadStableRow(r))restored++;r.qMutationProfile=r.id?profiles.get(r.id):null;r.qMutation=classifyMutation(r,profiles);r.qMicro=microLocationInfo(r);});
  state.qual.snapshotRestored=restored;
  if(!state.qual.sort||['score','quality','surfaceGap','correctedPpm','stateCoef','medianGap'].includes(state.qual.sort.key))state.qual.sort={key:'date',dir:-1};
  renderQualifiedResults();
}

function qualifiedSortValue(r,key){
  if(key==='date')return r.date?Date.parse(r.date):NaN;if(key==='distance')return r.dist;if(key==='type')return r.type||'';if(key==='surface')return r.surface;if(key==='pieces')return r.pieces;
  if(key==='dpe')return r.dpeInfo?.dpe?DPE_ORDER.indexOf(r.dpeInfo.dpe):NaN;if(key==='construction')return r.dpeInfo?.period?periodIndex[r.dpeInfo.period]:NaN;if(key==='floor')return r.dpeInfo?.floor;
  if(key==='traversant')return r.dpeInfo?.traversant===true?1:r.dpeInfo?.traversant===false?0:NaN;if(key==='orientation'){const o=mainOrientationForScore(r.dpeInfo);return o?ORIENTATIONS.indexOf(o):NaN;}
  if(key==='copro'){const c=publicCoproStatus(r);return c.value===true?0:c.value===false?1:2;}if(key==='terrain')return r.terrain;if(key==='works')return worksSourceType(r);if(key==='workBudget')return simpleWorkBudget(r).value;
  if(key==='val')return r.val;if(key==='ppm')return r.ppm;if(key==='mutation')return r.qMutation?.simple?0:(r.qMutation?.status==='unknown'?1:2);if(key==='voie')return r.voie||'';return NaN;
}
function qualifiedSortRows(rows){const srt=state.qual.sort||{key:'date',dir:-1};return[...rows].sort((a,b)=>{const va=qualifiedSortValue(a,srt.key),vb=qualifiedSortValue(b,srt.key),ma=va==null||(typeof va==='number'&&!isFinite(va))||va==='',mb=vb==null||(typeof vb==='number'&&!isFinite(vb))||vb==='';if(ma!==mb)return ma?1:-1;let cmp=0;if(!(ma&&mb))cmp=(typeof va==='string'||typeof vb==='string')?String(va).localeCompare(String(vb),'fr',{numeric:true,sensitivity:'base'}):va-vb;if(cmp)return cmp*srt.dir;const dc=(Date.parse(b.date||0)||0)-(Date.parse(a.date||0)||0);if(dc)return dc;return stableRowId(a).localeCompare(stableRowId(b),'fr',{numeric:true,sensitivity:'base'});});}
function sortQualifiedBy(key){const srt=state.qual.sort||{key:'date',dir:-1};if(srt.key===key)srt.dir*=-1;else{srt.key=key;srt.dir=['date','val','ppm','workBudget'].includes(key)?-1:1;}state.qual.sort=srt;refreshQualifiedView();}

function simpleSurfaceOk(v,f){if(f==='all')return true;if(!isFinite(v))return false;if(f==='lt50')return v<50;if(f==='50_75')return v>=50&&v<75;if(f==='75_100')return v>=75&&v<100;if(f==='100_125')return v>=100&&v<125;if(f==='125_150')return v>=125&&v<150;if(f==='gte150')return v>=150;return true;}
function simplePiecesOk(v,f){if(f==='all')return true;if(!isFinite(v))return false;if(f==='6plus')return v>=6;return v===+f;}
function simpleFloorOk(v,f){if(f==='all')return true;if(f==='unknown')return !isFinite(v);if(!isFinite(v))return false;if(f==='rdc')return +v===0;if(f==='1')return +v===1;if(f==='2plus')return +v>=2;return true;}
function qualifiedFilteredRows(applySort=true){
  const rows=state.qual.rows||[],f=state.qual.filters||{};
  const g=(id,k)=>document.getElementById(id)?.value||f[k]||'all';
  const ft=g('qfType','type'),fd=g('qfDpe','dpe'),fs=g('qfSurface','surface'),fp=g('qfPieces','pieces'),fy=g('qfPeriod','period'),ff=g('qfFloor','floor'),fc=g('qfCopro','copro'),fter=g('qfTerrain','terrain'),fe=g('qfEquipment','equipment'),fw=g('qfWorks','works'),fdist=g('qfDistance','distance'),fr=g('qfRecency','recency'),fm=g('qfMutation','mutation');
  const ppmMin=+(document.getElementById('qfPpmMin')?.value||f.ppmMin||0),ppmMax=+(document.getElementById('qfPpmMax')?.value||f.ppmMax||0);
  const filtered=rows.filter(r=>{
    if(ft!=='all'&&r.type!==ft)return false;
    if(fd!=='all'){if(fd==='none'){if(r.dpeInfo?.dpe)return false;}else if(r.dpeInfo?.dpe!==fd)return false;}
    if(!simpleSurfaceOk(r.surface,fs)||!simplePiecesOk(r.pieces,fp))return false;
    if(fy!=='all'&&r.dpeInfo?.period!==fy)return false;
    if(!simpleFloorOk(r.dpeInfo?.floor,ff))return false;
    if(fc!=='all'){const c=publicCoproStatus(r);if(fc==='yes'&&c.value!==true)return false;if(fc==='no'&&c.value!==false)return false;if(fc==='unknown'&&c.value!==null)return false;}
    if(fter==='yes'&&!(r.terrain>0))return false;if(fter==='no'&&r.terrain>0)return false;
    if(fe!=='all'&&!simpleEquipmentMatch(r,fe))return false;
    if(fw!=='all'){const src=worksSourceType(r);if(fw==='audit'&&src!=='audit')return false;if(fw==='manual'&&src!=='manual')return false;if(fw==='known'&&src==='none')return false;if(fw==='none'&&src!=='none')return false;}
    if(fdist!=='all'&&(!isFinite(r.dist)||r.dist>+fdist))return false;
    if(fr!=='all'){const m=monthsAgo(r.date);if(!isFinite(m)||m>+fr)return false;}
    if(fm==='simple'&&!r.qMutation?.simple)return false;
    if(ppmMin&&(!isFinite(r.ppm)||r.ppm<ppmMin))return false;if(ppmMax&&(!isFinite(r.ppm)||r.ppm>ppmMax))return false;
    return true;
  });return applySort?qualifiedSortRows(filtered):filtered;
}

function qualifiedTableHtml(rows){
  let h=`<thead><tr>${qualHeader('date','Date')}${qualHeader('distance','Distance','num')}${qualHeader('type','Type')}${qualHeader('surface','Surface','num')}${qualHeader('pieces','Pièces','num')}${qualHeader('dpe','DPE')}${qualHeader('construction','Construction')}${qualHeader('floor','Étage')}${qualHeader('copro','Copropriété')}${qualHeader('terrain','Terrain','num')}<th>Équipements / extérieurs</th>${qualHeader('works','Travaux / source')}${qualHeader('workBudget','Budget travaux préconisés (audit)','num')}${qualHeader('val','Prix vendu','num')}${qualHeader('ppm','€/m²','num')}${qualHeader('mutation','Mutation')}${qualHeader('voie','Adresse')}<th>Sources</th></tr></thead><tbody>`;
  rows.forEach(r=>{const di=r.dpeInfo,b=simpleWorkBudget(r);h+=`<tr><td>${r.date||'—'}</td><td class="num">${isFinite(r.dist)?f0(r.dist)+' m':'—'}${microLocationHtml(r)}</td><td>${esc(r.type)}</td><td class="num">${r.surface>0?f0(r.surface)+' m²':'—'}</td><td class="num">${isFinite(r.pieces)?r.pieces:'—'}</td><td>${dpeBadge(di?.dpe)}<span class="conf ${di?.confidence||''}">${confidenceLabel(di?.confidence)}</span></td><td>${periodLabel(di?.period)}${isFinite(di?.year)?`<span class="conf">${di.year}</span>`:''}</td><td>${floorLabel(di?.floor)}</td><td>${coproCell(r)}</td><td class="num">${r.terrain>0?f0(r.terrain)+' m²':'—'}</td><td>${freeFeaturesHtml(r)}</td><td>${simpleWorksCellHtml(r)}</td><td class="num">${isFinite(b.value)&&b.value>0?`<b>${eur(b.value)}</b><span class="conf">${b.source==='audit'?'travaux énergétiques préconisés · audit certain':'saisie manuelle'}</span>`:(b.source==='audit_unconfirmed'?`<span class="conf low"><b>À confirmer</b><br>audit non suffisamment rapproché</span>`:'—')}</td><td class="num"><b>${eur(r.val)}</b></td><td class="num"><b>${ppmF(r.ppm)}</b></td><td>${mutationBadgeHtml(r)}</td><td>${addrLink(r)}</td><td>${publicDetailsButton(r)}</td></tr>`;});
  if(!rows.length)h+=`<tr><td colspan="18" style="padding:28px;text-align:center"><b>Aucune vente ne correspond aux filtres actuels.</b><br><span class="conf" style="display:block;margin-top:6px">Clique « Réinitialiser » pour afficher toutes les ventes de l’analyse.</span></td></tr>`;
  return h+'</tbody>';
}

function filterBarHtml(){
  const f=state.qual.filters||{},o=(v,k)=>String(f[k]||'all')===String(v)?' selected':'';
  return `<div class="qual-filterbar simple-filters">
    <div class="qf"><label>Type</label><select id="qfType" onchange="refreshQualifiedView()"><option value="all"${o('all','type')}>Tous</option><option value="Maison"${o('Maison','type')}>Maison</option><option value="Appartement"${o('Appartement','type')}>Appartement</option><option value="Local"${o('Local','type')}>Local</option><option value="Dépendance"${o('Dépendance','type')}>Dépendance</option></select></div>
    <div class="qf"><label>DPE</label><select id="qfDpe" onchange="refreshQualifiedView()"><option value="all"${o('all','dpe')}>Tous</option>${DPE_ORDER.map(x=>`<option value="${x}"${o(x,'dpe')}>${x}</option>`).join('')}<option value="none"${o('none','dpe')}>Non trouvé</option></select></div>
    <div class="qf"><label>Surface</label><select id="qfSurface" onchange="refreshQualifiedView()"><option value="all"${o('all','surface')}>Toutes</option><option value="lt50"${o('lt50','surface')}>&lt; 50 m²</option><option value="50_75"${o('50_75','surface')}>50–74 m²</option><option value="75_100"${o('75_100','surface')}>75–99 m²</option><option value="100_125"${o('100_125','surface')}>100–124 m²</option><option value="125_150"${o('125_150','surface')}>125–149 m²</option><option value="gte150"${o('gte150','surface')}>≥ 150 m²</option></select></div>
    <div class="qf"><label>Pièces</label><select id="qfPieces" onchange="refreshQualifiedView()"><option value="all"${o('all','pieces')}>Toutes</option>${[1,2,3,4,5].map(x=>`<option value="${x}"${o(String(x),'pieces')}>${x}</option>`).join('')}<option value="6plus"${o('6plus','pieces')}>6 et +</option></select></div>
    <div class="qf"><label>Construction</label><select id="qfPeriod" onchange="refreshQualifiedView()"><option value="all"${o('all','period')}>Toutes</option>${PERIODS.map(([v,l])=>`<option value="${v}"${o(v,'period')}>${l}</option>`).join('')}</select></div>
    <div class="qf"><label>Étage</label><select id="qfFloor" onchange="refreshQualifiedView()"><option value="all"${o('all','floor')}>Tous</option><option value="rdc"${o('rdc','floor')}>RDC</option><option value="1"${o('1','floor')}>1er</option><option value="2plus"${o('2plus','floor')}>2e et +</option><option value="unknown"${o('unknown','floor')}>Inconnu</option></select></div>
    <div class="qf"><label>Copro maison</label><select id="qfCopro" onchange="refreshQualifiedView()"><option value="all"${o('all','copro')}>Toutes</option><option value="yes"${o('yes','copro')}>Oui</option><option value="no"${o('no','copro')}>Non détectée</option><option value="unknown"${o('unknown','copro')}>Inconnu</option></select></div>
    <div class="qf"><label>Terrain</label><select id="qfTerrain" onchange="refreshQualifiedView()"><option value="all"${o('all','terrain')}>Tous</option><option value="yes"${o('yes','terrain')}>Avec terrain</option><option value="no"${o('no','terrain')}>Sans terrain</option></select></div>
    <div class="qf"><label>Équipement</label><select id="qfEquipment" onchange="refreshQualifiedView()"><option value="all"${o('all','equipment')}>Tous</option><option value="any"${o('any','equipment')}>Au moins un signal</option><option value="garage"${o('garage','equipment')}>Garage</option><option value="parking"${o('parking','equipment')}>Parking</option><option value="garden"${o('garden','equipment')}>Jardin</option><option value="terrace"${o('terrace','equipment')}>Terrasse</option><option value="balcony"${o('balcony','equipment')}>Balcon</option><option value="elevator"${o('elevator','equipment')}>Ascenseur</option><option value="dependence"${o('dependence','equipment')}>Dépendance DVF</option></select></div>
    <div class="qf"><label>Travaux</label><select id="qfWorks" onchange="refreshQualifiedView()"><option value="all"${o('all','works')}>Tous</option><option value="known"${o('known','works')}>Info connue</option><option value="audit"${o('audit','works')}>Audit ADEME</option><option value="manual"${o('manual','works')}>Saisie manuelle</option><option value="none"${o('none','works')}>Aucune info</option></select></div>
    <div class="qf"><label>Distance</label><select id="qfDistance" onchange="refreshQualifiedView()"><option value="all"${o('all','distance')}>Toutes</option><option value="250"${o('250','distance')}>≤ 250 m</option><option value="500"${o('500','distance')}>≤ 500 m</option><option value="1000"${o('1000','distance')}>≤ 1 km</option><option value="2000"${o('2000','distance')}>≤ 2 km</option></select></div>
    <div class="qf"><label>Récence</label><select id="qfRecency" onchange="refreshQualifiedView()"><option value="all"${o('all','recency')}>Toutes</option><option value="12"${o('12','recency')}>≤ 12 mois</option><option value="24"${o('24','recency')}>≤ 24 mois</option><option value="36"${o('36','recency')}>≤ 36 mois</option></select></div>
    <div class="qf"><label>Mutation</label><select id="qfMutation" onchange="refreshQualifiedView()"><option value="all"${o('all','mutation')}>Toutes</option><option value="simple"${o('simple','mutation')}>Ventes simples</option></select></div>
    <div class="qf qf-price"><label>€/m² min</label><input id="qfPpmMin" type="number" step="100" value="${esc(f.ppmMin||'')}" placeholder="Min" onchange="refreshQualifiedView()"></div>
    <div class="qf qf-price"><label>€/m² max</label><input id="qfPpmMax" type="number" step="100" value="${esc(f.ppmMax||'')}" placeholder="Max" onchange="refreshQualifiedView()"></div>
    <button class="qual-secondary" onclick="resetQualifiedFilters()">Réinitialiser</button>
  </div>`;
}

function refreshQualifiedView(){
  const get=id=>document.getElementById(id)?.value||'all';
  state.qual.filters={type:get('qfType'),dpe:get('qfDpe'),surface:get('qfSurface'),pieces:get('qfPieces'),period:get('qfPeriod'),floor:get('qfFloor'),copro:get('qfCopro'),terrain:get('qfTerrain'),equipment:get('qfEquipment'),works:get('qfWorks'),distance:get('qfDistance'),recency:get('qfRecency'),mutation:get('qfMutation'),ppmMin:document.getElementById('qfPpmMin')?.value||'',ppmMax:document.getElementById('qfPpmMax')?.value||''};
  const rows=qualifiedFilteredRows(true),tbl=document.getElementById('qualTable');if(tbl)tbl.innerHTML=qualifiedTableHtml(rows);const c=document.getElementById('qualVisibleCount');if(c)c.textContent=`${rows.length} / ${state.qual.rows.length} ventes affichées`;const gp=document.getElementById('simpleGlobalPrice');if(gp)gp.innerHTML=simpleGlobalPriceHtml(rows);
}
function resetQualifiedFilters(){state.qual.filters={type:'all',dpe:'all',surface:'all',pieces:'all',period:'all',floor:'all',copro:'all',terrain:'all',equipment:'all',works:'all',distance:'all',recency:'all',mutation:'all',ppmMin:'',ppmMax:''};renderQualifiedResults();}

function simpleGlobalPriceStats(rows){
  const vals=rows.map(r=>r.val).filter(v=>isFinite(v)&&v>0),ppms=rows.map(r=>r.ppm).filter(v=>isFinite(v)&&v>0);
  return{count:rows.length,price:median(vals),ppm:median(ppms)};
}
function simpleGlobalPriceHtml(rows){
  const st=simpleGlobalPriceStats(rows);
  return `<div class="simple-global-price-card"><div><div class="sgp-label">Prix global médian</div><div class="sgp-value">${isFinite(st.price)?eur(st.price):'—'}</div></div><div class="sgp-meta"><b>${st.count}</b> vente${st.count>1?'s':''} affichée${st.count>1?'s':''}<br>€/m² médian : <b>${isFinite(st.ppm)?ppmF(st.ppm):'—'}</b><br><span>Recalculé automatiquement selon les filtres.</span></div></div>`;
}

function renderQualifiedResults(){
  const body=document.getElementById('qualBody');if(!body)return;if(!state.qual.rows.length){renderQualifiedBase();return;}
  const source=qualifiedSourceRows();if(source.length!==state.qual.rows.length||source.some((r,i)=>rowKey(r)!==rowKey(state.qual.rows[i]))){state.qual.simpleStarted=false;renderQualifiedBase();return;}
  const rows=qualifiedFilteredRows(true),c=simpleEnrichmentCounts();
  body.innerHTML=`<div class="qual-hero simple-qual-hero"><div><h2>Détermination du prix</h2><p>Toutes les ventes issues de l’analyse sont regroupées ici. Trie et filtre les caractéristiques pour retenir mentalement les références les plus pertinentes.</p></div><div class="qual-source">${c.total} VENTES · ${c.dpe} DPE · ${c.public} PUBLIC</div></div>
  <div class="qual-panel simple-table-panel"><div class="simple-table-head"><div><h3>Tableau des ventes analysées</h3><div class="subtxt">Aucun score ni prix cible automatique : les données DVF restent brutes et les caractéristiques publiques servent uniquement à ton appréciation.</div></div><div class="simple-head-actions"><span id="qualVisibleCount" class="visible-count">${rows.length} / ${state.qual.rows.length} ventes affichées</span><span id="simpleProgress" class="qual-progress"></span><button class="qual-secondary" onclick="enrichSimpleDetermination(true)">Actualiser depuis les sources</button></div></div><div id="simpleGlobalPrice">${simpleGlobalPriceHtml(rows)}</div>${filterBarHtml()}<div class="qual-table-wrap simple-table-wrap"><table class="qual-table simple-qual-table" id="qualTable">${qualifiedTableHtml(rows)}</table></div><div class="qual-warn"><b>Données stabilisées :</b> la copropriété est vérifiée séparément et verrouillée dès qu’une immatriculation fiable est confirmée. L’identité du bien est basée sur la mutation DVF + l’adresse, et toutes les parcelles de la mutation sont contrôlées : un changement de parcelle représentative après dédoublonnage ne peut plus déplacer le statut copropriété. Un « Non détectée » n’est retenu qu’après contrôle BDNB concordant par adresse et toutes les parcelles connues. Une copropriété confirmée est mémorisée durablement par mutation/adresse et un simple rafraîchissement ne peut plus la faire disparaître. Un DPE seulement probable ne suffit plus : il doit être confirmé par le RNIC. Les statuts « Non détectée » ne sont jamais verrouillés : en cas de doute ils repassent à « Inconnu ». Les autres enrichissements sont conservés localement pendant 7 jours. « Actualiser depuis les sources » recontrôle les données sans effacer les copropriétés déjà confirmées.</div></div>`;
  if(state.view==='qualifies'&&!state.qual.simpleStarted&&!state.qual.running){state.qual.simpleStarted=true;setTimeout(()=>enrichSimpleDetermination(false),40);}
}


/* =========================================================
   MDB — Filtrage manuel + prix médian sélectionné + annulation
   ========================================================= */
let enrichmentEpoch=0;

function normalizeManualFilterState(f={}){
  return {
    dpe:Array.isArray(f.dpe)?f.dpe:[],
    pieces:Array.isArray(f.pieces)?f.pieces:[],
    constructionMin:f.constructionMin||'',
    constructionMax:f.constructionMax||'',
    floor:f.floor||'all',
    copro:f.copro||'all',
    terrain:f.terrain||'all'
  };
}
function getCheckedValues(name,fallback=[]){
  const els=[...document.querySelectorAll(`input[name="${name}"]`)];
  return els.length?els.filter(x=>x.checked).map(x=>x.value):fallback;
}
function shouldShowFloor(){
  return (state.qual.rows||[]).some(r=>r.type==='Appartement');
}
function constructionRangeForRow(r){
  const y=+r?.dpeInfo?.year;
  if(isFinite(y)&&y>0)return[y,y];
  const p=r?.dpeInfo?.period;
  const map={
    pre1948:[1800,1947],1948_1974:[1948,1974],1975_1988:[1975,1988],
    1989_2000:[1989,2000],2001_2012:[2001,2012],2013_2020:[2013,2020],post2020:[2021,2200]
  };
  return map[p]||[NaN,NaN];
}
function constructionInRange(r,min,max){
  if(!min&&!max)return true;
  const [lo,hi]=constructionRangeForRow(r);
  if(!isFinite(lo)||!isFinite(hi))return false;
  if(min&&hi<min)return false;
  if(max&&lo>max)return false;
  return true;
}
const PRICE_CONDITIONS=[
  ['TURNKEY','Clé en main',12],
  ['VERY_GOOD','Très bon état',7],
  ['GOOD','Bon état',0],
  ['REFRESH','À rafraîchir',-5],
  ['RENOVATE','À rénover',-12],
  ['HEAVY','Rénovation lourde',-20]
];
const PRICE_CONDITION_DEFAULTS=Object.fromEntries(PRICE_CONDITIONS.map(([k,,v])=>[k,v]));
function ensurePriceConditionState(){
  if(!state.qual.priceCondition||!Object.prototype.hasOwnProperty.call(PRICE_CONDITION_DEFAULTS,state.qual.priceCondition))state.qual.priceCondition='GOOD';
  if(!state.qual.conditionAdjustments)state.qual.conditionAdjustments={...PRICE_CONDITION_DEFAULTS};
  for(const [k,,v] of PRICE_CONDITIONS)if(!isFinite(+state.qual.conditionAdjustments[k]))state.qual.conditionAdjustments[k]=v;
}
function priceConditionLabel(k){return PRICE_CONDITIONS.find(x=>x[0]===k)?.[1]||'Bon état';}
function priceConditionCoef(){ensurePriceConditionState();return Number(state.qual.conditionAdjustments[state.qual.priceCondition]??0);}
function priceConditionPct(v){v=Number(v)||0;return `${v>0?'+':''}${v.toLocaleString('fr-FR',{maximumFractionDigits:1})} %`;}
function priceRowIsKept(r){return r.priceSelected!==false;}
function togglePriceKeep(encoded){
  const k=decodeURIComponent(encoded),r=(state.qual.rows||[]).find(x=>rowKey(x)===k);
  if(!r)return;
  r.priceSelected=!priceRowIsKept(r);
  refreshQualifiedView();
}
function setDisplayedPriceSelection(on){
  qualifiedFilteredRows(false).forEach(r=>r.priceSelected=!!on);
  refreshQualifiedView();
}
function updateGlobalPriceOutputs(){
  const st=simpleGlobalPriceStats(qualifiedFilteredRows(true));
  const main=document.getElementById('sgpMainValue'),base=document.getElementById('sgpBaseValue'),cnt=document.getElementById('sgpSelectedCount'),rppm=document.getElementById('sgpRawPpm'),appm=document.getElementById('sgpAdjustedPpm'),formula=document.getElementById('sgpFormula');
  if(main)main.textContent=isFinite(st.price)?eur(st.price):'—';
  if(base)base.textContent=isFinite(st.basePrice)?eur(st.basePrice):'—';
  if(cnt)cnt.textContent=`${st.kept} bien${st.kept>1?'s':''} gardé${st.kept>1?'s':''}`;
  if(rppm)rppm.textContent=isFinite(st.rawPpm)?ppmF(st.rawPpm):'—';
  if(appm)appm.textContent=isFinite(st.adjustedPpm)?ppmF(st.adjustedPpm):'—';
  if(formula)formula.textContent=isFinite(st.rawPpm)&&isFinite(st.surface)?`${f0(st.surface)} m² × ${ppmF(st.rawPpm)} · ${priceConditionLabel(state.qual.priceCondition)} ${priceConditionPct(st.adj)}`:'Renseigne une surface cible pour calculer le prix global.';
}
function setValuationSurface(v){
  const n=Number(v);state.qual.valuationSurface=isFinite(n)&&n>0?n:NaN;updateGlobalPriceOutputs();
}
function setPriceCondition(k){
  ensurePriceConditionState();if(Object.prototype.hasOwnProperty.call(PRICE_CONDITION_DEFAULTS,k))state.qual.priceCondition=k;
  const coef=document.getElementById('sgpConditionCoef');if(coef)coef.value=priceConditionCoef();
  document.querySelectorAll('.sgp-state-chip').forEach(el=>el.classList.toggle('active',el.dataset.condition===state.qual.priceCondition));
  updateGlobalPriceOutputs();
}
function setPriceConditionCoef(v){
  ensurePriceConditionState();let n=Number(v);if(!isFinite(n))n=0;n=Math.max(-50,Math.min(50,n));
  state.qual.conditionAdjustments[state.qual.priceCondition]=n;
  const sel=document.getElementById('sgpCondition');if(sel){const op=sel.querySelector(`option[value="${state.qual.priceCondition}"]`);if(op)op.textContent=`${priceConditionLabel(state.qual.priceCondition)} (${priceConditionPct(n)})`;}
  updateGlobalPriceOutputs();
}

function qualifiedFilteredRows(applySort=true){
  const rows=state.qual.rows||[],f=normalizeManualFilterState(state.qual.filters||{});
  const dpes=getCheckedValues('qfDpe',f.dpe);
  const pieces=getCheckedValues('qfPieces',f.pieces);
  const cMin=+(document.getElementById('qfConstructionMin')?.value||f.constructionMin||0);
  const cMax=+(document.getElementById('qfConstructionMax')?.value||f.constructionMax||0);
  const floor=document.getElementById('qfFloor')?.value||f.floor||'all';
  const copro=document.getElementById('qfCopro')?.value||f.copro||'all';
  const terrain=document.getElementById('qfTerrain')?.value||f.terrain||'all';
  const filtered=rows.filter(r=>{
    if(dpes.length){
      const d=r.dpeInfo?.dpe||'UNKNOWN';
      if(!dpes.includes(d))return false;
    }
    if(pieces.length){
      const p=isFinite(r.pieces)?(+r.pieces>=6?'6plus':String(+r.pieces)):'UNKNOWN';
      if(!pieces.includes(p))return false;
    }
    if(!constructionInRange(r,cMin,cMax))return false;
    if(shouldShowFloor()&&floor!=='all'){
      const v=r.dpeInfo?.floor;
      if(floor==='unknown'&&isFinite(v))return false;
      if(floor!=='unknown'){
        if(!isFinite(v))return false;
        if(floor==='rdc'&&+v!==0)return false;
        if(floor==='1'&&+v!==1)return false;
        if(floor==='2plus'&&+v<2)return false;
      }
    }
    if(copro!=='all'){
      const c=publicCoproStatus(r);
      if(copro==='yes'&&c.value!==true)return false;
      if(copro==='no'&&c.value!==false)return false;
      if(copro==='unknown'&&c.value!==null)return false;
    }
    if(terrain==='yes'&&!(r.terrain>0))return false;
    if(terrain==='no'&&r.terrain>0)return false;
    return true;
  });
  return applySort?qualifiedSortRows(filtered):filtered;
}

function qualifiedTableHtml(rows){
  const showFloor=shouldShowFloor(),cols=showFloor?19:18;
  let h=`<thead><tr><th class="keep-head">Garder</th>${qualHeader('date','Date')}${qualHeader('distance','Distance','num')}${qualHeader('type','Type')}${qualHeader('surface','Surface','num')}${qualHeader('pieces','Pièces','num')}${qualHeader('dpe','DPE')}${qualHeader('construction','Construction')}${showFloor?qualHeader('floor','Étage'):''}${qualHeader('copro','Copro')}${qualHeader('terrain','Terrain','num')}<th>Équipements / extérieurs</th>${qualHeader('works','Travaux / source')}${qualHeader('workBudget','Budget travaux préconisés (audit)','num')}${qualHeader('val','Prix vendu','num')}${qualHeader('ppm','€/m²','num')}${qualHeader('mutation','Mutation')}${qualHeader('voie','Adresse')}<th>Sources</th></tr></thead><tbody>`;
  rows.forEach(r=>{
    const di=r.dpeInfo,b=simpleWorkBudget(r),keep=priceRowIsKept(r);
    h+=`<tr class="${keep?'price-kept':'price-excluded'}"><td class="keep-head"><input class="price-keep" type="checkbox" ${keep?'checked':''} onchange="togglePriceKeep('${encodeURIComponent(rowKey(r))}')" title="Inclure ce bien dans le Prix global médian"></td><td>${r.date||'—'}</td><td class="num">${isFinite(r.dist)?f0(r.dist)+' m':'—'}${microLocationHtml(r)}</td><td>${esc(r.type)}</td><td class="num">${r.surface>0?f0(r.surface)+' m²':'—'}</td><td class="num">${isFinite(r.pieces)?r.pieces:'—'}</td><td>${dpeBadge(di?.dpe)}<span class="conf ${di?.confidence||''}">${confidenceLabel(di?.confidence)}</span></td><td>${periodLabel(di?.period)}${isFinite(di?.year)?`<span class="conf">${di.year}</span>`:''}</td>${showFloor?`<td>${floorLabel(di?.floor)}</td>`:''}<td>${coproCell(r)}</td><td class="num">${r.terrain>0?f0(r.terrain)+' m²':'—'}</td><td>${freeFeaturesHtml(r)}</td><td>${simpleWorksCellHtml(r)}</td><td class="num">${isFinite(b.value)&&b.value>0?`<b>${eur(b.value)}</b><span class="conf">${b.source==='audit'?'travaux énergétiques préconisés · audit certain':'saisie manuelle'}</span>`:(b.source==='audit_unconfirmed'?`<span class="conf low"><b>À confirmer</b><br>audit non suffisamment rapproché</span>`:'—')}</td><td class="num"><b>${eur(r.val)}</b></td><td class="num"><b>${ppmF(r.ppm)}</b></td><td>${mutationBadgeHtml(r)}</td><td>${addrLink(r)}</td><td>${publicDetailsButton(r)}</td></tr>`;
  });
  if(!rows.length)h+=`<tr><td colspan="${cols}" style="padding:28px;text-align:center"><b>Aucune vente ne correspond aux filtres actuels.</b><br><span class="conf" style="display:block;margin-top:6px">Clique « Réinitialiser » pour afficher toutes les ventes de l’analyse.</span></td></tr>`;
  return h+'</tbody>';
}

function multiChoiceHtml(name,values,current){
  const cur=Array.isArray(current)?current:[];
  return `<div class="multi-choice">${values.map(([v,l])=>`<label><input type="checkbox" name="${name}" value="${v}" ${cur.includes(v)?'checked':''} onchange="refreshQualifiedView()"><span>${l}</span></label>`).join('')}</div>`;
}
function filterBarHtml(){
  const f=normalizeManualFilterState(state.qual.filters||{}),showFloor=shouldShowFloor();
  const pill=(name,v,l,active)=>`<label style="display:inline-flex;align-items:center;gap:3px;padding:3px 8px;border-radius:5px;border:1.5px solid ${active?'#7D721A':'#E5E4DF'};background:${active?'#F7F4E6':'#fff'};color:${active?'#7D721A':'#3A3A36'};font-size:11px;font-weight:700;cursor:pointer;transition:all .12s"><input type="checkbox" name="${name}" value="${v}" ${active?'checked':''} onchange="refreshQualifiedView()" style="display:none">${l}</label>`;
  const dpeVals=[...DPE_ORDER.map(x=>[x,x]),['UNKNOWN','?']];
  const pieceVals=[['1','1p'],['2','2p'],['3','3p'],['4','4p'],['5','5p'],['6plus','6p+'],['UNKNOWN','?']];
  const dpe=f.dpe||[];const pieces=f.pieces||[];
  return `<div style="display:flex;flex-wrap:wrap;gap:6px;align-items:center;padding:8px 12px;background:#F7F4E6;border:1px solid #E3DCBE;border-radius:8px;margin:8px 0">
    <span style="font-size:9px;font-weight:800;color:#6B6A65;text-transform:uppercase;letter-spacing:.6px;margin-right:2px">DPE</span>
    ${dpeVals.map(([v,l])=>pill('qfDpe',v,l,dpe.includes(v))).join('')}
    <span style="color:#E5E4DF;margin:0 4px">|</span>
    <span style="font-size:9px;font-weight:800;color:#6B6A65;text-transform:uppercase;letter-spacing:.6px;margin-right:2px">Pièces</span>
    ${pieceVals.map(([v,l])=>pill('qfPieces',v,l,pieces.includes(v))).join('')}
    ${showFloor?`<span style="color:#E5E4DF;margin:0 4px">|</span><span style="font-size:9px;font-weight:800;color:#6B6A65;text-transform:uppercase;letter-spacing:.6px;margin-right:2px">Étage</span><select id="qfFloor" onchange="refreshQualifiedView()" style="padding:3px 6px;border:1.5px solid #E5E4DF;border-radius:5px;font-size:11px;font-weight:700;background:#fff;color:#191917"><option value="all" ${f.floor==='all'?'selected':''}>Tous</option><option value="rdc" ${f.floor==='rdc'?'selected':''}>RDC</option><option value="1" ${f.floor==='1'?'selected':''}>1er</option><option value="2plus" ${f.floor==='2plus'?'selected':''}>2e+</option><option value="unknown" ${f.floor==='unknown'?'selected':''}>?</option></select>`:''}
    <span style="color:#E5E4DF;margin:0 4px">|</span>
    <span style="font-size:9px;font-weight:800;color:#6B6A65;text-transform:uppercase;letter-spacing:.6px;margin-right:2px">Copro</span>
    <select id="qfCopro" onchange="refreshQualifiedView()" style="padding:3px 6px;border:1.5px solid #E5E4DF;border-radius:5px;font-size:11px;font-weight:700;background:#fff;color:#191917"><option value="all" ${f.copro==='all'?'selected':''}>Tous</option><option value="yes" ${f.copro==='yes'?'selected':''}>Oui</option><option value="no" ${f.copro==='no'?'selected':''}>Non</option><option value="unknown" ${f.copro==='unknown'?'selected':''}>?</option></select>
    <span style="color:#E5E4DF;margin:0 4px">|</span>
    <span style="font-size:9px;font-weight:800;color:#6B6A65;text-transform:uppercase;letter-spacing:.6px;margin-right:2px">Terrain</span>
    <select id="qfTerrain" onchange="refreshQualifiedView()" style="padding:3px 6px;border:1.5px solid #E5E4DF;border-radius:5px;font-size:11px;font-weight:700;background:#fff;color:#191917"><option value="all" ${f.terrain==='all'?'selected':''}>Tous</option><option value="yes" ${f.terrain==='yes'?'selected':''}>Avec</option><option value="no" ${f.terrain==='no'?'selected':''}>Sans</option></select>
    <button onclick="resetQualifiedFilters()" style="margin-left:6px;padding:3px 10px;border:1.5px solid #E5E4DF;border-radius:5px;background:#fff;font-size:11px;font-weight:700;color:#6B6A65;cursor:pointer">↺</button>
  </div>`;
}
function refreshQualifiedView(){
  const current=normalizeManualFilterState(state.qual.filters||{});
  state.qual.filters={
    dpe:getCheckedValues('qfDpe',current.dpe),
    pieces:getCheckedValues('qfPieces',current.pieces),
    constructionMin:document.getElementById('qfConstructionMin')?.value??current.constructionMin,
    constructionMax:document.getElementById('qfConstructionMax')?.value??current.constructionMax,
    floor:document.getElementById('qfFloor')?.value||'all',
    copro:document.getElementById('qfCopro')?.value||'all',
    terrain:document.getElementById('qfTerrain')?.value||'all'
  };
  const rows=qualifiedFilteredRows(true),tbl=document.getElementById('qualTable');
  if(tbl)tbl.innerHTML=qualifiedTableHtml(rows);
  const c=document.getElementById('qualVisibleCount');if(c)c.textContent=`${rows.length} / ${state.qual.rows.length} ventes affichées`;
  const gp=document.getElementById('simpleGlobalPrice');if(gp)gp.innerHTML=simpleGlobalPriceHtml(rows);
}
function resetQualifiedFilters(){
  state.qual.filters={dpe:[],pieces:[],constructionMin:'',constructionMax:'',floor:'all',copro:'all',terrain:'all'};
  renderQualifiedResults();
}

function simpleGlobalPriceStats(rows){
  ensurePriceConditionState();
  const kept=rows.filter(priceRowIsKept);
  const ppms=kept.map(r=>r.ppm).filter(v=>isFinite(v)&&v>0);
  const rawPpm=median(ppms),surface=Number(state.qual.valuationSurface),adj=priceConditionCoef(),factor=1+adj/100;
  const validSurface=isFinite(surface)&&surface>0?surface:NaN;
  const basePrice=isFinite(rawPpm)&&isFinite(validSurface)?rawPpm*validSurface:NaN;
  return{displayed:rows.length,kept:kept.length,rawPpm,surface:validSurface,adj,basePrice,price:isFinite(basePrice)?basePrice*factor:NaN,adjustedPpm:isFinite(rawPpm)?rawPpm*factor:NaN};
}
function simpleGlobalPriceHtml(rows){
  ensurePriceConditionState();
  const st=simpleGlobalPriceStats(rows),cond=state.qual.priceCondition,coef=priceConditionCoef();
  const options=PRICE_CONDITIONS.map(([k,l])=>`<option value="${k}" ${k===cond?'selected':''}>${esc(l)} (${priceConditionPct(Number(state.qual.conditionAdjustments[k]))})</option>`).join('');
  const chips=PRICE_CONDITIONS.map(([k,l])=>`<span class="sgp-state-chip ${k===cond?'active':''}" data-condition="${k}">${esc(l)} ${priceConditionPct(Number(state.qual.conditionAdjustments[k]))}</span>`).join('');
  return `<div class="simple-global-price-card">
    <div>
      <div class="sgp-label">Prix global médian</div>
      <div class="sgp-value" id="sgpMainValue">${isFinite(st.price)?eur(st.price):'—'}</div>
      <div class="sgp-subvalue">Prix avant ajustement d’état : <b id="sgpBaseValue">${isFinite(st.basePrice)?eur(st.basePrice):'—'}</b></div>
      <div class="keep-actions"><button onclick="setDisplayedPriceSelection(true)">✓ Garder tous les biens affichés</button><button onclick="setDisplayedPriceSelection(false)">× Tout retirer</button></div>
    </div>
    <div>
      <div class="sgp-controls">
        <div class="sgp-control"><label>Surface cible (m²)</label><input id="sgpSurface" type="number" min="1" step="1" value="${isFinite(st.surface)?st.surface:''}" placeholder="Ex : 100" oninput="setValuationSurface(this.value)"></div>
        <div class="sgp-control"><label>État du bien</label><select id="sgpCondition" onchange="setPriceCondition(this.value)">${options}</select></div>
        <div class="sgp-control coef"><label>Ajustement (%)</label><div class="sgp-coef-row"><input id="sgpConditionCoef" type="number" min="-50" max="50" step="0.5" value="${coef}" oninput="setPriceConditionCoef(this.value)"><span class="pct">%</span></div></div>
      </div>
      <div class="sgp-formula" id="sgpFormula">${isFinite(st.rawPpm)&&isFinite(st.surface)?`${f0(st.surface)} m² × ${ppmF(st.rawPpm)} · ${priceConditionLabel(cond)} ${priceConditionPct(st.adj)}`:'Renseigne une surface cible pour calculer le prix global.'}</div>
      <div class="sgp-state-scale">${chips}</div>
    </div>
    <div class="sgp-meta"><span class="selected-count" id="sgpSelectedCount">${st.kept} bien${st.kept>1?'s':''} gardé${st.kept>1?'s':''}</span> sur ${st.displayed} affiché${st.displayed>1?'s':''}<br>€/m² médian retenu : <b id="sgpRawPpm">${isFinite(st.rawPpm)?ppmF(st.rawPpm):'—'}</b><br>€/m² après état : <b id="sgpAdjustedPpm">${isFinite(st.adjustedPpm)?ppmF(st.adjustedPpm):'—'}</b></div>
  </div>`;
}

function coproCell(r){
  const p=r.publicInfo,c=publicCoproStatus(r);
  if(c.value===true){
    const immat=c.immat||p?.immat||'';
    if(p?.rnic?.procedureFields&&p.rnic.procedureAlert)return`<span class="mutationpill warn">⚠ Copro · signal RNIC</span><span class="conf">${esc(immat)}</span>`;
    return`<span class="mutationpill simple">✓ Copro confirmée</span><span class="conf">${esc(c.label)}${immat?' · '+esc(immat):''}${isFinite(p?.rnic?.lots)?' · '+f0(p.rnic.lots)+' lots':''}</span>`;
  }
  if(c.value===false)return`<span class="mutationpill simple">○ Non détectée</span><span class="conf">${esc(c.label||'BDNB sans immatriculation rapprochée')} · à confirmer</span>`;
  if(!p?.done)return'<span class="conf">vérification en cours / source indisponible</span>';
  return`<span class="conf">${esc(c.label||'Inconnu')}</span>`;
}

function renderQualifiedBase(){
  const body=document.getElementById('qualBody');if(!body)return;
  const source=qualifiedSourceRows();
  if(!source.length){body.innerHTML='<div class="qual-empty">Lance d’abord une analyse DVF. Toutes les ventes issues de cette analyse apparaîtront ensuite ici.</div>';return;}
  state.qual.rows=[...source];
  const selectionKey=state.qual.rows.map(stableRowId).sort().join('||');
  const isNewSelection=state.qual.manualSelectionKey!==selectionKey;
  if(isNewSelection){
    state.qual.manualSelectionKey=selectionKey;
    state.qual.valuationSurface=NaN;
    state.qual.priceCondition='GOOD';
    state.qual.conditionAdjustments={...PRICE_CONDITION_DEFAULTS};
    state.qual.filters={dpe:[],pieces:[],constructionMin:'',constructionMax:'',floor:'all',copro:'all',terrain:'all'};
  }
  const profiles=buildMutationProfiles();let restored=0;
  state.qual.rows.forEach(r=>{
    if(loadStableRow(r))restored++;
    r.qMutationProfile=r.id?profiles.get(r.id):null;
    r.qMutation=classifyMutation(r,profiles);
    r.qMicro=microLocationInfo(r);
    if(isNewSelection||typeof r.priceSelected!=='boolean')r.priceSelected=true;
  });
  state.qual.snapshotRestored=restored;
  if(!state.qual.sort||['score','quality','surfaceGap','correctedPpm','stateCoef','medianGap'].includes(state.qual.sort.key))state.qual.sort={key:'date',dir:-1};
  renderQualifiedResults();
}

function renderQualifiedResults(){
  const body=document.getElementById('qualBody');if(!body)return;if(!state.qual.rows.length){renderQualifiedBase();return;}
  const source=qualifiedSourceRows();
  if(source.length!==state.qual.rows.length||source.some((r,i)=>rowKey(r)!==rowKey(state.qual.rows[i]))){
    state.qual.simpleStarted=false;renderQualifiedBase();return;
  }
  const rows=qualifiedFilteredRows(true),c=simpleEnrichmentCounts();
  body.innerHTML=`<div class="qual-hero simple-qual-hero"><div><h2>Détermination du prix</h2><p>Filtre les ventes, puis coche uniquement les biens que tu veux conserver dans le calcul du prix médian.</p></div><div class="qual-source">${c.total} VENTES · ${c.dpe} DPE · ${c.public} PUBLIC</div></div>
  <div class="qual-panel simple-table-panel"><div class="simple-table-head"><div><h3>Tableau des ventes analysées</h3><div class="subtxt">Le Prix global médian est calculé uniquement sur les ventes affichées que tu laisses cochées dans « Garder ».</div></div><div class="simple-head-actions"><span id="qualVisibleCount" class="visible-count">${rows.length} / ${state.qual.rows.length} ventes affichées</span><span id="simpleProgress" class="qual-progress"></span><button class="qual-secondary" onclick="enrichSimpleDetermination(true)">Actualiser depuis les sources</button></div></div><div id="simpleGlobalPrice">${simpleGlobalPriceHtml(rows)}</div>${filterBarHtml()}<div class="qual-table-wrap simple-table-wrap"><table class="qual-table simple-qual-table" id="qualTable">${qualifiedTableHtml(rows)}</table></div><div class="qual-warn"><b>Données stabilisées :</b> les enrichissements DPE / BDNB / RNIC / OSM / AUDIT sont réutilisés lorsqu’ils sont déjà fiabilisés. Si tu relances une nouvelle analyse, les recherches de l’analyse précédente sont immédiatement abandonnées et la priorité passe au nouveau jeu de ventes.</div></div>`;
  if(state.view==='qualifies'&&!state.qual.simpleStarted&&!state.qual.running){state.qual.simpleStarted=true;setTimeout(()=>enrichSimpleDetermination(false),40);}
}

/* Annulation des enrichissements obsolètes : une nouvelle analyse prend la priorité. */
async function enrichRowsDpe(rows,progress,guard=()=>true){
  const groups=new Map();
  rows.forEach(r=>{
    if(r.dpeChecked===undefined&&r.dpeInfo!==undefined)r.dpeChecked=true;
    const k=normTxt([r.voie,r.commune].filter(Boolean).join(' '));
    if(k&&!r.dpeChecked){if(!groups.has(k))groups.set(k,[]);groups.get(k).push(r);}
  });
  const entries=[...groups.values()];let done=0,errors=0,cursor=0;
  async function worker(){
    while(cursor<entries.length&&guard()){
      const group=entries[cursor++],sample=group[0];
      try{
        const cands=await queryDpeAddress([sample.voie,sample.commune].filter(Boolean).join(' '));
        if(!guard())return;
        group.forEach(r=>{r.dpeInfo=chooseDpeCandidate(r,cands);r.dpeChecked=true;saveStableRow(r);});
      }catch(e){
        if(!guard())return;
        errors++;group.forEach(r=>{r.dpeChecked=false;delete r.dpeInfo;});
      }
      done++;progress?.(done,entries.length,errors);
      await sleep(90);
    }
  }
  await Promise.all(Array.from({length:Math.min(5,entries.length)},worker));
  return{groups:entries.length,errors,cancelled:!guard()};
}
async function enrichRowsPublic(rows,progress,guard=()=>true){
  const todo=rows.filter(r=>!r.publicInfo?.done||!r.publicInfo?.coproDecision);let done=0,errors=0,cursor=0;
  async function worker(){
    while(cursor<todo.length&&guard()){
      const r=todo[cursor++];
      try{
        await enrichPublicForRow(r);
        if(!guard())return;
        if(r.publicInfo?.errors?.length)errors++;
      }catch(e){
        if(!guard())return;
        errors++;
        const locked=loadCoproDecision(r,r.publicInfo?.banId||r.dpeInfo?.banId||'');
        r.publicInfo={...(r.publicInfo||{}),done:false,osmChecked:false,coproDecision:locked||r.publicInfo?.coproDecision||null,errors:['public']};
      }
      done++;progress?.(done,todo.length,errors);
      await sleep(230);
    }
  }
  await Promise.all(Array.from({length:Math.min(3,todo.length)},worker));
  return{count:todo.length,errors,cancelled:!guard()};
}
async function enrichAllAuditsSimple(rows,progress,guard=()=>true){
  const todo=rows.filter(r=>!r.auditChecked);let done=0,errors=0,cursor=0;
  async function worker(){
    while(cursor<todo.length&&guard()){
      const r=todo[cursor++];
      try{
        const found=await lookupAuditForRow(r);
        if(!guard())return;
        r.auditInfo=found;r.auditChecked=true;saveStableRow(r);
      }catch(e){
        if(!guard())return;
        errors++;r.auditInfo=null;r.auditChecked=false;
      }
      done++;progress?.(done,todo.length,errors);
      await sleep(100);
    }
  }
  await Promise.all(Array.from({length:Math.min(3,todo.length)},worker));
  return{count:todo.length,errors,cancelled:!guard()};
}

async function enrichSimpleDetermination(force=false){
  if(state.qual.running||!state.qual.rows.length)return;
  const myEpoch=++enrichmentEpoch,alive=()=>myEpoch===enrichmentEpoch;
  state.qual.simpleStarted=true;state.qual.running=true;
  try{
    const rows=[...state.qual.rows];
    if(force){
      clearRuntimeEnrichmentCaches();
      rows.forEach(r=>{
        const locked=loadCoproDecision(r,r.publicInfo?.banId||r.dpeInfo?.banId||'');
        clearStableRow(r);r.dpeChecked=false;delete r.dpeInfo;
        r.publicInfo=locked?{done:false,osmChecked:false,coproDecision:locked,immat:locked.immat||'',immatSource:locked.source||'',errors:[]}:null;
        r.auditChecked=false;r.auditInfo=null;
      });
    }
    if(!alive())return;
    setStatus(`Tableau affiché · enrichissement DPE en arrière-plan (${rows.length} ventes)…`,'info');
    const er=await enrichRowsDpe(rows,(d,n,e)=>{if(!alive())return;const info=document.getElementById('srcInfo');if(info)info.textContent=`DPE ADEME ${d}/${n}${e?' · '+e+' erreur(s)':''}…`;},alive);
    if(!alive())return;
    state.qual.dpeErrors=er.errors;state.qual.enrichedCount=rows.filter(r=>r.dpeInfo!=null).length;state.qual.enrichedAll=true;
    renderQualifiedResults();
    setStatus(`DPE chargé · enrichissement copropriété / équipements / travaux en parallèle…`,'info');
    const [pe,ae]=await Promise.all([
      enrichRowsPublic(rows,(d,n)=>{if(!alive())return;const info=document.getElementById('srcInfo');if(info)info.textContent=`BDNB / RNIC / OSM ${d}/${n}…`;},alive),
      enrichAllAuditsSimple(rows,(d,n)=>{if(!alive())return;const el=document.getElementById('simpleProgress');if(el)el.textContent=`AUDIT ADEME ${d}/${n}…`;},alive)
    ]);
    if(!alive())return;
    state.qual.publicErrors+=pe.errors;state.qual.auditErrors+=ae.errors;
    state.qual.publicEnrichedCount=rows.filter(r=>r.publicInfo?.done).length;state.qual.publicEnrichedAll=state.qual.publicEnrichedCount>=rows.length;
    state.qual.auditEnrichedCount=rows.filter(r=>r.auditChecked).length;state.qual.auditEnrichedAll=state.qual.auditEnrichedCount>=rows.length;
    renderQualifiedResults();
    const c=simpleEnrichmentCounts();
    setStatus(`Tableau enrichi : ${c.total} ventes · ${c.dpe} DPE · ${c.public} données bâtiment/copro/OSM · ${c.audit} audits vérifiés.`,'ok');
  }catch(e){
    if(alive()){console.error(e);setStatus('Enrichissement du tableau : '+e.message,'err');}
  }finally{
    if(alive())state.qual.running=false;
  }
}

/* Chaque nouvelle analyse invalide immédiatement les enrichissements de la précédente. */
const __mdbApplyBase=apply;
apply=async function(){
  enrichmentEpoch++;
  state.qual.running=false;
  state.qual.simpleStarted=false;
  return __mdbApplyBase();
};


/* Mutations sur carte — couleur par type, taille fixe */
const DOT_RADIUS=5;
function drawMutations(){
  mutMarkers.clearLayers();
  const S=sel().filter(r=>isFinite(r.lat)&&isFinite(r.lon));
  const present=new Set();
  S.forEach(r=>{
    present.add(r.type);
    const color=TYPE_COLOR[r.type]||TYPE_COLOR.Autre;
    L.circleMarker([r.lat,r.lon],{radius:DOT_RADIUS,color:'#ffffff',weight:1,fillColor:color,fillOpacity:.85})
      .bindTooltip(
        `<div style="font-weight:800;margin-bottom:2px">${r.type}</div>${f0(r.surface)} m²<br>Prix : <b>${eur(r.val)}</b><br>Prix/m² : ${ppmF(r.ppm)}<br>Pièces : ${isFinite(r.pieces)?r.pieces:'—'}<br>${r.commune||''}`,
        {direction:'top',opacity:1,sticky:true,className:'mut-tip'})
      .addTo(mutMarkers);
  });
  updateLegend(present);
}
function fitMap(){
  try{
    const layers=mutMarkers.getLayers();
    if(layers.length){ map.fitBounds(L.featureGroup(layers).getBounds().pad(0.12)); }
    else if(state.addresses.length){ map.setView([state.addresses[0].lat,state.addresses[0].lon],14); }
  }catch(e){}
}

/* ---------------- Statut ---------------- */
let stTimer;
function setStatus(m,t){
  const s=document.getElementById('status');s.className='status show '+t;s.textContent=m;s.onclick=()=>s.classList.remove('show');
  const info=document.getElementById('srcInfo'); if(info) info.textContent=m;
  clearTimeout(stTimer); if(t==='ok') stTimer=setTimeout(()=>s.classList.remove('show'),8000);
}

/* ---------------- Export ---------------- */
function exportExcel(){
  const S=sel();if(!S.length)return;closeExport();
  const wb=XLSX.utils.book_new();
  const rows=S.map(r=>({Date:r.date,Type:r.type,'Pièces':isFinite(r.pieces)?r.pieces:'','Surface m²':r.surface||'','Valeur €':r.val,'€/m²':isFinite(r.ppm)?Math.round(r.ppm):'',Adresse:r.voie,Commune:r.commune,Parcelle:r.parcelle}));
  const ws=XLSX.utils.json_to_sheet(rows);ws['!cols']=[{wch:11},{wch:12},{wch:7},{wch:9},{wch:11},{wch:9},{wch:28},{wch:18},{wch:16}];
  XLSX.utils.book_append_sheet(wb,ws,'Mutations');
  const vals=S.map(r=>r.val).filter(isFinite),ppms=S.map(r=>r.ppm).filter(isFinite),surfs=S.map(r=>r.surface).filter(v=>v>0);
  const syn=[['SAS De Mère en Fils MDB — Synthèse DVF'],[],
    ['Secteur',state.addresses.map(a=>a.label).join(' ; ')],
    ['Rayon',km(+document.getElementById('radius').value)],
    ['Période',document.getElementById('yFrom').value+' – '+document.getElementById('yTo').value],
    ['Mutations',S.length],[],
    ['Indicateur','Valeur foncière','Prix/m²'],
    ['Moyenne',Math.round(mean(vals)),Math.round(mean(ppms))],
    ['Médiane',Math.round(median(vals)),Math.round(median(ppms))],
    ['Min',Math.round(arrMin(vals)),Math.round(arrMin(ppms))],
    ['Max',Math.round(arrMax(vals)),Math.round(arrMax(ppms))],
    ['Surface moyenne (m²)',Math.round(mean(surfs))]];
  const ws2=XLSX.utils.aoa_to_sheet(syn);ws2['!cols']=[{wch:24},{wch:16},{wch:14}];
  XLSX.utils.book_append_sheet(wb,ws2,'Synthèse');
  XLSX.writeFile(wb,'DVF_Secteur_MDB.xlsx');
}
function exportPdf(){
  const S=sel();if(!S.length)return;closeExport();
  // Formatage sûr pour jsPDF : séparateur = espace ASCII normal (pas d'espace insécable)
  const pfNum=n=>isFinite(n)?String(Math.round(n)).replace(/\B(?=(\d{3})+(?!\d))/g,' '):'-';
  const pEur=n=>isFinite(n)?pfNum(n)+' €':'-';
  const pPpm=n=>isFinite(n)?pfNum(n)+' €/m²':'-';
  const{jsPDF}=window.jspdf;const doc=new jsPDF('p','mm','a4');const W=doc.internal.pageSize.getWidth();
  doc.setFillColor(...INK);doc.rect(0,0,W,26,'F');doc.setFillColor(...GOLD);doc.rect(0,26,W,1.4,'F');
  doc.setTextColor(255,255,255);doc.setFont('helvetica','bold');doc.setFontSize(14);doc.text('SAS De Mère en Fils MDB',14,12);
  doc.setFont('helvetica','normal');doc.setFontSize(9);doc.setTextColor(200,200,200);doc.text('Analyse foncière · DVF · Étude de secteur',14,18);
  doc.setFontSize(8);doc.text('SIREN 990 726 432 · Saint-Maur-des-Fossés',W-14,12,{align:'right'});doc.text(new Date().toLocaleDateString('fr-FR'),W-14,18,{align:'right'});
  let y=36;doc.setTextColor(...INK);doc.setFont('helvetica','bold');doc.setFontSize(11);doc.text('Secteur',14,y);
  doc.setFont('helvetica','normal');doc.setFontSize(9);doc.setTextColor(60,60,60);
  y+=6;doc.text(state.addresses.map(a=>a.label).join(' ; ').slice(0,110),14,y);
  y+=5;doc.text(`Rayon ${km(+document.getElementById('radius').value)} · Période ${document.getElementById('yFrom').value}–${document.getElementById('yTo').value} · ${S.length} mutations`,14,y);
  const vals=S.map(r=>r.val).filter(isFinite),ppms=S.map(r=>r.ppm).filter(isFinite);
  y+=8;doc.autoTable({startY:y,head:[['Indicateur','Valeur foncière','Prix/m²']],
    body:[['Moyenne',pEur(mean(vals)),pPpm(mean(ppms))],['Médiane',pEur(median(vals)),pPpm(median(ppms))],
      ['Min',pEur(arrMin(vals)),pPpm(arrMin(ppms))],['Max',pEur(arrMax(vals)),pPpm(arrMax(ppms))]],
    theme:'grid',headStyles:{fillColor:INK,textColor:255,fontSize:8.5},bodyStyles:{fontSize:8.5},margin:{left:14,right:14},
    columnStyles:{1:{halign:'right'},2:{halign:'right'}}});
  y=doc.lastAutoTable.finalY+8;
  if(y>235){doc.addPage();y=20;}
  doc.setFont('helvetica','bold');doc.setFontSize(11);doc.setTextColor(...INK);doc.text('Mutations',14,y);
  doc.autoTable({startY:y+3,head:[['Date','Type','P.','Surf.','Valeur','€/m²','Adresse']],
    body:S.slice(0,60).map(r=>[r.date,r.type,isFinite(r.pieces)?r.pieces:'',r.surface||'',pEur(r.val),isFinite(r.ppm)?pfNum(r.ppm):'',(r.voie||'').slice(0,34)]),
    theme:'striped',headStyles:{fillColor:INK,textColor:255,fontSize:7.5},bodyStyles:{fontSize:7},margin:{left:14,right:14},
    columnStyles:{2:{halign:'right'},3:{halign:'right'},4:{halign:'right'},5:{halign:'right'}}});
  const pages=doc.internal.getNumberOfPages();
  for(let i=1;i<=pages;i++){doc.setPage(i);const H=doc.internal.pageSize.getHeight();doc.setFontSize(7);doc.setTextColor(140,140,140);
    doc.text('SAS De Mère en Fils MDB — Analyse indicative DVF (DGFiP). Document de travail, sans valeur d\'expertise.',14,H-8);
    doc.text(`${i}/${pages}`,W-14,H-8,{align:'right'});}
  doc.save('DVF_Secteur_MDB.pdf');
}

/* init */
updateRadius();
setView('carte');
setDefaultSector();
// Le préchargement est maintenant déclenché automatiquement par addAddress().
// Si la période change, on prépare immédiatement les nouvelles années en arrière-plan.
document.getElementById('yFrom').addEventListener('change',prefetchSelectedCommunes);
document.getElementById('yTo').addEventListener('change',prefetchSelectedCommunes);
// Point par défaut : siège SAS De Mère en Fils MDB (la géoloc PC est trop imprécise).
async function setDefaultSector(){
  const HOME={q:'81 Boulevard Rabelais 94100 Saint-Maur-des-Fossés', lat:48.79646, lon:2.48787, insee:'94068', label:'81 Boulevard Rabelais, 94100 Saint-Maur-des-Fossés'};
  try{
    const r=await fetch('https://api-adresse.data.gouv.fr/search/?limit=1&q='+encodeURIComponent(HOME.q));
    const j=await r.json(); const f=j.features&&j.features[0];
    if(f){ if(state.addresses.length)return; const [lon,lat]=f.geometry.coordinates;
      addAddress(f.properties.label,lat,lon,f.properties.citycode,f.properties.id||''); map.setView([lat,lon],16);
      setStatus('Secteur par défaut : '+f.properties.label,'ok'); return; }
    throw new Error('no result');
  }catch(e){
    if(state.addresses.length)return;
    addAddress(HOME.label, HOME.lat, HOME.lon, HOME.insee); map.setView([HOME.lat,HOME.lon],16);
    setStatus('Secteur par défaut : '+HOME.label,'ok');
  }
}


/* ============================================================
   OPTIMISATION PROGRESSION + ENRICHISSEMENT PUBLIC
   - affiche BDNB/RNIC/OSM et AUDIT simultanément
   - parallélise uniquement les appels indépendants
   - conserve exactement les mêmes règles de fiabilité copro
   ============================================================ */
function simpleProgressText(){
  const c=simpleEnrichmentCounts(),p=state.qual._dualProgress||{};
  const pubDone=Number.isFinite(p.pubDone)?p.pubDone:c.public, pubTotal=Number.isFinite(p.pubTotal)?p.pubTotal:c.total;
  const audDone=Number.isFinite(p.audDone)?p.audDone:c.audit, audTotal=Number.isFinite(p.audTotal)?p.audTotal:c.total;
  return `<span class="pubp">BDNB / RNIC / OSM ${pubDone}/${pubTotal}</span><span class="sep">·</span><span class="auditp">AUDIT ADEME ${audDone}/${audTotal}</span>`;
}
function updateSimpleDualProgress(pubDone,pubTotal,audDone,audTotal){
  const prev=state.qual._dualProgress||{};
  state.qual._dualProgress={
    pubDone:Number.isFinite(pubDone)?pubDone:prev.pubDone,
    pubTotal:Number.isFinite(pubTotal)?pubTotal:prev.pubTotal,
    audDone:Number.isFinite(audDone)?audDone:prev.audDone,
    audTotal:Number.isFinite(audTotal)?audTotal:prev.audTotal
  };
  const el=document.getElementById('simpleProgress');if(el)el.innerHTML=simpleProgressText();
}

async function publicMapLimitFast(items,limit,fn,guard=()=>true){
  const out=new Array(items.length);let cursor=0;
  async function worker(){while(cursor<items.length&&guard()){const i=cursor++;out[i]=await fn(items[i],i);}}
  await Promise.all(Array.from({length:Math.min(limit,items.length)},worker));
  return out;
}

/* Même règle de décision qu'avant, mais parcelles et vérifications RNIC sont parallélisées. */
determineCoproDecision=async function(row,banId,bdnbAddress,addressChecked){
  const cached=loadCoproDecision(row,banId);if(cached)return cached;
  const parcelIds=coproParcelIds(row).slice(0,12);let parcelErrors=0;
  const parcelResults=await publicMapLimitFast(parcelIds,3,async pid=>{
    try{return{pid,bdnb:await queryBdnbByParcel(pid,row.dpeInfo?.rnbId||''),checked:true};}
    catch(e){parcelErrors++;return{pid,bdnb:null,checked:false};}
  });
  const ids=new Map();
  const addId=(id,src)=>{id=String(id||'').trim();if(!id)return;ids.set(id,ids.has(id)?ids.get(id)+' + '+src:src);};
  if(bdnbPositive(bdnbAddress))addId(bdnbAddress.coproId,bdnbAddress.ambiguous?'BDNB adresse · copro commune aux bâtiments':'BDNB adresse');
  for(const pr of parcelResults)if(bdnbPositive(pr.bdnb))addId(pr.bdnb.coproId,`BDNB parcelle ${pr.pid}`);
  if(row.dpeInfo?.confidence==='high')addId(row.dpeInfo?.coproId,'DPE certain');

  if(row.dpeInfo?.confidence==='medium'&&row.dpeInfo?.coproId){
    try{const rn=await queryRnicByImmat(row.dpeInfo.coproId);if(rn){const decision=saveCoproDecision(row,banId,{value:true,confidence:'high',source:'RNIC + DPE probable',immat:row.dpeInfo.coproId});return{...decision,rnic:rn};}}catch(e){}
  }
  if(ids.size){
    const entries=[...ids.entries()];
    const checks=await publicMapLimitFast(entries,3,async ([immat,src])=>{try{const rn=await queryRnicByImmat(immat);return rn?{immat,src,rn}:null;}catch(e){return null;}});
    const verified=checks.filter(Boolean),chosen=verified[0]||null,first=entries[0];
    const immat=chosen?.immat||first?.[0]||'',src=chosen?('RNIC + '+chosen.src):(ids.size>1?'Plusieurs sources positives BDNB/DPE':first?.[1]||'source positive');
    const decision=saveCoproDecision(row,banId,{value:true,confidence:chosen?'high':(String(src).includes('BDNB')?'high':'medium'),source:src,immat});
    return{...decision,rnic:chosen?.rn||null};
  }
  const parcelsFullyChecked=parcelIds.length>0&&parcelErrors===0&&parcelResults.length===parcelIds.length;
  const parcelsAllNo=parcelsFullyChecked&&parcelResults.every(x=>bdnbDefiniteNo(x.bdnb));
  if(addressChecked&&bdnbDefiniteNo(bdnbAddress)&&parcelsAllNo)return{value:false,confidence:'high',source:'BDNB adresse + toutes parcelles',immat:'',key:'CORE:'+coproCoreKey(row),locked:false};
  return{value:null,confidence:'low',source:'Données insuffisantes',immat:'',key:'CORE:'+coproCoreKey(row),locked:false};
};

/* OSM démarre immédiatement pendant BAN/BDNB. Aucun seuil de fiabilité n'est modifié. */
enrichPublicForRow=async function(row){
  let banId=row.dpeInfo?.banId||row.publicInfo?.banId||'';
  const cachedDecision=loadCoproDecision(row,banId),sig=publicEnrichmentSig(row,banId);
  if(row.publicInfo?.done&&row.publicInfo?.osmChecked&&row.publicInfo?.sig===sig&&row.publicInfo?.coproDecision)return row.publicInfo;
  const errors=[];
  let osm=row.publicInfo?.osm||null,osmChecked=!!row.publicInfo?.osmChecked;
  const osmPromise=osmChecked?Promise.resolve({ok:true,value:osm}):queryOsmAround(row.lat,row.lon).then(v=>({ok:true,value:v})).catch(e=>({ok:false,error:e}));

  if(!banId){try{banId=await lookupBanId([row.voie,row.commune].filter(Boolean).join(' '));}catch(e){errors.push('BAN');}}
  let bdnb=null,bdnbChecked=false;
  if(banId){try{bdnb=await queryBdnbByBanId(banId,row.dpeInfo?.rnbId||'');bdnbChecked=true;}catch(e){errors.push('BDNB');}}

  let coproDecision=cachedDecision||loadCoproDecision(row,banId)||null;
  if(!coproDecision){try{coproDecision=await determineCoproDecision(row,banId,bdnb,bdnbChecked);}catch(e){errors.push('COPRO');coproDecision=loadCoproDecision(row,banId)||{value:null,confidence:'low',source:'Erreur de vérification',immat:'',key:'CORE:'+coproCoreKey(row),locked:false};}}
  const immat=coproDecision?.value===true?(coproDecision.immat||''):'',immatSource=coproDecision?.source||'';
  let rnic=coproDecision?.rnic||null;
  if(immat&&!rnic){try{rnic=await queryRnicByImmat(immat);}catch(e){errors.push('RNIC');}}

  if(!osmChecked){const or=await osmPromise;if(or.ok){osm=or.value;osmChecked=true;}else errors.push('OSM');}
  const criticalError=errors.includes('BAN')||errors.includes('BDNB');
  row.publicInfo={sig:publicEnrichmentSig(row,banId),done:!criticalError,osmChecked,banId,bdnb,bdnbChecked,rnic,immat,immatSource,coproDecision,osm,errors};
  if(coproDecision?.value!==null)saveCoproDecision(row,banId,coproDecision);
  if(row.publicInfo.done)saveStableRow(row);return row.publicInfo;
};

/* 4 lignes à la fois au lieu de 3, avec temporisation réduite mais conservatrice. */
enrichRowsPublic=async function(rows,progress,guard=()=>true){
  const todo=rows.filter(r=>!r.publicInfo?.done||!r.publicInfo?.coproDecision);let done=0,errors=0,cursor=0;
  async function worker(){
    while(cursor<todo.length&&guard()){
      const r=todo[cursor++];
      try{await enrichPublicForRow(r);if(!guard())return;if(r.publicInfo?.errors?.length)errors++;}
      catch(e){if(!guard())return;errors++;const locked=loadCoproDecision(r,r.publicInfo?.banId||r.dpeInfo?.banId||'');r.publicInfo={...(r.publicInfo||{}),done:false,osmChecked:false,coproDecision:locked||r.publicInfo?.coproDecision||null,errors:['public']};}
      done++;progress?.(done,todo.length,errors);await sleep(120);
    }
  }
  await Promise.all(Array.from({length:Math.min(4,todo.length)},worker));
  return{count:todo.length,errors,cancelled:!guard()};
};

/* Affichage principal : une case de progression combinée, toujours visible. */
renderQualifiedResults=function(){
  const body=document.getElementById('qualBody');if(!body)return;if(!state.qual.rows.length){renderQualifiedBase();return;}
  const source=qualifiedSourceRows();
  if(source.length!==state.qual.rows.length||source.some((r,i)=>rowKey(r)!==rowKey(state.qual.rows[i]))){state.qual.simpleStarted=false;renderQualifiedBase();return;}
  const rows=qualifiedFilteredRows(true),c=simpleEnrichmentCounts();
  body.innerHTML=`<div class="qual-hero simple-qual-hero"><div><h2>Détermination du prix</h2><p>Filtre les ventes, puis coche uniquement les biens que tu veux conserver dans le calcul du prix médian.</p></div><div class="qual-source">${c.total} VENTES · ${c.dpe} DPE · ${c.public} PUBLIC</div></div>
  <div class="qual-panel simple-table-panel"><div class="simple-table-head"><div><h3>Tableau des ventes analysées</h3><div class="subtxt">Le Prix global médian est calculé uniquement sur les ventes affichées que tu laisses cochées dans « Garder ».</div></div><div class="simple-head-actions"><span id="qualVisibleCount" class="visible-count">${rows.length} / ${state.qual.rows.length} ventes affichées</span><span id="simpleProgress" class="simple-progress-box">${simpleProgressText()}</span><button class="qual-secondary" onclick="enrichSimpleDetermination(true)">Actualiser depuis les sources</button></div></div><div id="simpleGlobalPrice">${simpleGlobalPriceHtml(rows)}</div>${filterBarHtml()}<div class="qual-table-wrap simple-table-wrap"><table class="qual-table simple-qual-table" id="qualTable">${qualifiedTableHtml(rows)}</table></div><div class="qual-warn"><b>Données stabilisées :</b> les enrichissements DPE / BDNB / RNIC / OSM / AUDIT sont réutilisés lorsqu’ils sont déjà fiabilisés. Si tu relances une nouvelle analyse, les recherches de l’analyse précédente sont immédiatement abandonnées et la priorité passe au nouveau jeu de ventes.</div></div>`;
  if(state.view==='qualifies'&&!state.qual.simpleStarted&&!state.qual.running){state.qual.simpleStarted=true;setTimeout(()=>enrichSimpleDetermination(false),40);}
};

/* Les deux compteurs progressent côte à côte pendant les chargements parallèles. */
enrichSimpleDetermination=async function(force=false){
  if(state.qual.running||!state.qual.rows.length)return;
  const myEpoch=++enrichmentEpoch,alive=()=>myEpoch===enrichmentEpoch;
  state.qual.simpleStarted=true;state.qual.running=true;
  try{
    const rows=[...state.qual.rows];
    if(force){
      clearRuntimeEnrichmentCaches();
      rows.forEach(r=>{const locked=loadCoproDecision(r,r.publicInfo?.banId||r.dpeInfo?.banId||'');clearStableRow(r);r.dpeChecked=false;delete r.dpeInfo;r.publicInfo=locked?{done:false,osmChecked:false,coproDecision:locked,immat:locked.immat||'',immatSource:locked.source||'',errors:[]}:null;r.auditChecked=false;r.auditInfo=null;});
    }
    state.qual._dualProgress={pubDone:rows.filter(r=>r.publicInfo?.done).length,pubTotal:rows.length,audDone:rows.filter(r=>r.auditChecked).length,audTotal:rows.length};
    updateSimpleDualProgress();
    if(!alive())return;
    setStatus(`Tableau affiché · enrichissement DPE en arrière-plan (${rows.length} ventes)…`,'info');
    const er=await enrichRowsDpe(rows,(d,n,e)=>{if(!alive())return;const info=document.getElementById('srcInfo');if(info)info.textContent=`DPE ADEME ${d}/${n}${e?' · '+e+' erreur(s)':''}…`;},alive);
    if(!alive())return;
    state.qual.dpeErrors=er.errors;state.qual.enrichedCount=rows.filter(r=>r.dpeInfo!=null).length;state.qual.enrichedAll=true;
    renderQualifiedResults();updateSimpleDualProgress();
    setStatus(`DPE chargé · enrichissement copropriété / équipements / travaux en parallèle…`,'info');
    let pd=rows.filter(r=>r.publicInfo?.done).length,ad=rows.filter(r=>r.auditChecked).length;
    updateSimpleDualProgress(pd,rows.length,ad,rows.length);
    const [pe,ae]=await Promise.all([
      enrichRowsPublic(rows,(d,n)=>{if(!alive())return;pd=d;updateSimpleDualProgress(pd,n,ad,rows.length);const info=document.getElementById('srcInfo');if(info)info.textContent=`BDNB / RNIC / OSM ${d}/${n}…`;},alive),
      enrichAllAuditsSimple(rows,(d,n)=>{if(!alive())return;ad=d;updateSimpleDualProgress(pd,rows.length,ad,n);},alive)
    ]);
    if(!alive())return;
    state.qual.publicErrors+=pe.errors;state.qual.auditErrors+=ae.errors;
    state.qual.publicEnrichedCount=rows.filter(r=>r.publicInfo?.done).length;state.qual.publicEnrichedAll=state.qual.publicEnrichedCount>=rows.length;
    state.qual.auditEnrichedCount=rows.filter(r=>r.auditChecked).length;state.qual.auditEnrichedAll=state.qual.auditEnrichedCount>=rows.length;
    state.qual._dualProgress={pubDone:state.qual.publicEnrichedCount,pubTotal:rows.length,audDone:state.qual.auditEnrichedCount,audTotal:rows.length};
    renderQualifiedResults();updateSimpleDualProgress();
    const c=simpleEnrichmentCounts();setStatus(`Tableau enrichi : ${c.total} ventes · ${c.dpe} DPE · ${c.public} données bâtiment/copro/OSM · ${c.audit} audits vérifiés.`,'ok');
  }catch(e){if(alive()){console.error(e);setStatus('Enrichissement du tableau : '+e.message,'err');}}
  finally{if(alive())state.qual.running=false;}
};
/* ============================================================
   AIDE À LA DÉCISION — FIABILITÉ / FOURCHETTE / DISPERSION / CARTE / COMPARATEUR / EXPORT
   ============================================================ */
function qtile(values,p){const a=(values||[]).filter(v=>isFinite(v)).sort((x,y)=>x-y);if(!a.length)return NaN;if(a.length===1)return a[0];const pos=(a.length-1)*p,lo=Math.floor(pos),hi=Math.ceil(pos);return lo===hi?a[lo]:a[lo]+(a[hi]-a[lo])*(pos-lo);}
function reliabilityInfo(r){
  const d=r?.dpeInfo,dc=d?.confidence||'none',c=publicCoproStatus(r),pc=c?.confidence||'none',pub=r?.publicInfo;
  const low=dc==='low'||pc==='low'||(pub?.errors?.length>0);
  let level='none',label='Partielle';
  if(low){level='low';label='À vérifier';}
  else if(dc==='high'&&c?.value!==null&&pc==='high'){level='high';label='Forte';}
  else if(['high','medium'].includes(dc)||['high','medium'].includes(pc)){level='medium';label='Bonne';}
  const detail=`DPE : ${confidenceLabel(dc)} · Copro : ${c?.value===true?'confirmée':c?.value===false?'non détectée':c?.label||'inconnue'}`;
  return{level,label,detail};
}
function reliabilityHtml(r){const x=reliabilityInfo(r);return`<span class="reliability-badge ${x.level}" title="${esc(x.detail)}">${x.level==='high'?'●':x.level==='medium'?'●':x.level==='low'?'▲':'○'} ${x.label}</span><span class="rel-detail">${esc(x.detail)}</span>`;}

simpleGlobalPriceStats=function(rows){
  ensurePriceConditionState();
  const kept=(rows||[]).filter(priceRowIsKept),ppms=kept.map(r=>r.ppm).filter(v=>isFinite(v)&&v>0);
  const q1=qtile(ppms,.25),rawPpm=qtile(ppms,.5),q3=qtile(ppms,.75),surface=Number(state.qual.valuationSurface),adj=priceConditionCoef(),factor=1+adj/100;
  const validSurface=isFinite(surface)&&surface>0?surface:NaN,basePrice=isFinite(rawPpm)&&isFinite(validSurface)?rawPpm*validSurface:NaN;
  const dispersion=isFinite(q1)&&isFinite(q3)&&isFinite(rawPpm)&&rawPpm>0?(q3-q1)/rawPpm*100:NaN;
  const dispersionLevel=!isFinite(dispersion)?'none':dispersion<=10?'low':dispersion<=20?'medium':'high';
  const dispersionLabel=dispersionLevel==='low'?'Faible':dispersionLevel==='medium'?'Modérée':dispersionLevel==='high'?'Élevée':'Non calculable';
  return{displayed:(rows||[]).length,kept:kept.length,rawPpm,q1,q3,surface:validSurface,adj,basePrice,price:isFinite(basePrice)?basePrice*factor:NaN,adjustedPpm:isFinite(rawPpm)?rawPpm*factor:NaN,lowPpm:isFinite(q1)?q1*factor:NaN,highPpm:isFinite(q3)?q3*factor:NaN,lowPrice:isFinite(q1)&&isFinite(validSurface)?q1*validSurface*factor:NaN,highPrice:isFinite(q3)&&isFinite(validSurface)?q3*validSurface*factor:NaN,dispersion,dispersionLevel,dispersionLabel};
};

simpleGlobalPriceHtml=function(rows){
  ensurePriceConditionState();const st=simpleGlobalPriceStats(rows),cond=state.qual.priceCondition,coef=priceConditionCoef();
  const options=PRICE_CONDITIONS.map(([k,l])=>`<option value="${k}" ${k===cond?'selected':''}>${esc(l)} (${priceConditionPct(Number(state.qual.conditionAdjustments[k]))})</option>`).join('');
  const chips=PRICE_CONDITIONS.map(([k,l])=>`<span class="sgp-state-chip ${k===cond?'active':''}" data-condition="${k}">${esc(l)} ${priceConditionPct(Number(state.qual.conditionAdjustments[k]))}</span>`).join('');
  return `<div class="simple-global-price-card">
    <div>
      <div class="sgp-label">Prix global médian</div><div class="sgp-value" id="sgpMainValue">${isFinite(st.price)?eur(st.price):'—'}</div>
      <div class="sgp-subvalue">Prix avant ajustement d’état : <b id="sgpBaseValue">${isFinite(st.basePrice)?eur(st.basePrice):'—'}</b></div>
      <div class="price-range-grid"><div class="price-range-box"><div class="k">Fourchette basse</div><div class="v" id="sgpLowPrice">${isFinite(st.lowPrice)?eur(st.lowPrice):'—'}</div></div><div class="price-range-box mid"><div class="k">Médiane</div><div class="v" id="sgpMedianPrice">${isFinite(st.price)?eur(st.price):'—'}</div></div><div class="price-range-box"><div class="k">Fourchette haute</div><div class="v" id="sgpHighPrice">${isFinite(st.highPrice)?eur(st.highPrice):'—'}</div></div></div>
      <div class="dispersion-pill ${st.dispersionLevel}" id="sgpDispersion">Dispersion ${st.dispersionLabel}${isFinite(st.dispersion)?' · '+st.dispersion.toFixed(1)+' %':''}</div>
      <div class="keep-actions"><button onclick="setDisplayedPriceSelection(true)">✓ Garder tous les biens affichés</button><button onclick="setDisplayedPriceSelection(false)">× Tout retirer</button></div>
    </div>
    <div><div class="sgp-controls"><div class="sgp-control"><label>Surface cible (m²)</label><input id="sgpSurface" type="number" min="1" step="1" value="${isFinite(st.surface)?st.surface:''}" placeholder="Ex : 100" oninput="setValuationSurface(this.value)"></div><div class="sgp-control"><label>État du bien</label><select id="sgpCondition" onchange="setPriceCondition(this.value)">${options}</select></div><div class="sgp-control coef"><label>Ajustement (%)</label><div class="sgp-coef-row"><input id="sgpConditionCoef" type="number" min="-50" max="50" step="0.5" value="${coef}" oninput="setPriceConditionCoef(this.value)"><span class="pct">%</span></div></div></div><div class="sgp-formula" id="sgpFormula">${isFinite(st.rawPpm)&&isFinite(st.surface)?`${f0(st.surface)} m² × ${ppmF(st.rawPpm)} · ${priceConditionLabel(cond)} ${priceConditionPct(st.adj)}`:'Renseigne une surface cible pour calculer le prix global.'}</div><div class="sgp-state-scale">${chips}</div></div>
    <div class="sgp-meta"><span class="selected-count" id="sgpSelectedCount">${st.kept} bien${st.kept>1?'s':''} gardé${st.kept>1?'s':''}</span> sur ${st.displayed} affiché${st.displayed>1?'s':''}<br>€/m² bas : <b id="sgpLowPpm">${isFinite(st.lowPpm)?ppmF(st.lowPpm):'—'}</b><br>€/m² médian : <b id="sgpAdjustedPpm">${isFinite(st.adjustedPpm)?ppmF(st.adjustedPpm):'—'}</b><br>€/m² haut : <b id="sgpHighPpm">${isFinite(st.highPpm)?ppmF(st.highPpm):'—'}</b></div>
  </div>`;
};

updateGlobalPriceOutputs=function(){
  const st=simpleGlobalPriceStats(qualifiedFilteredRows(true));
  const set=(id,text)=>{const e=document.getElementById(id);if(e)e.textContent=text;};
  set('sgpMainValue',isFinite(st.price)?eur(st.price):'—');set('sgpMedianPrice',isFinite(st.price)?eur(st.price):'—');set('sgpBaseValue',isFinite(st.basePrice)?eur(st.basePrice):'—');set('sgpLowPrice',isFinite(st.lowPrice)?eur(st.lowPrice):'—');set('sgpHighPrice',isFinite(st.highPrice)?eur(st.highPrice):'—');
  set('sgpSelectedCount',`${st.kept} bien${st.kept>1?'s':''} gardé${st.kept>1?'s':''}`);set('sgpAdjustedPpm',isFinite(st.adjustedPpm)?ppmF(st.adjustedPpm):'—');set('sgpLowPpm',isFinite(st.lowPpm)?ppmF(st.lowPpm):'—');set('sgpHighPpm',isFinite(st.highPpm)?ppmF(st.highPpm):'—');
  const f=document.getElementById('sgpFormula');if(f)f.textContent=isFinite(st.rawPpm)&&isFinite(st.surface)?`${f0(st.surface)} m² × ${ppmF(st.rawPpm)} · ${priceConditionLabel(state.qual.priceCondition)} ${priceConditionPct(st.adj)}`:'Renseigne une surface cible pour calculer le prix global.';
  const d=document.getElementById('sgpDispersion');if(d){d.className=`dispersion-pill ${st.dispersionLevel}`;d.textContent=`Dispersion ${st.dispersionLabel}${isFinite(st.dispersion)?' · '+st.dispersion.toFixed(1)+' %':''}`;}
};

function fullProgressState(){const rows=state.qual.rows||[],p=state.qual._fullProgress||{};return{dpeDone:Number.isFinite(p.dpeDone)?p.dpeDone:rows.filter(r=>r.dpeChecked).length,dpeTotal:Number.isFinite(p.dpeTotal)?p.dpeTotal:rows.length,pubDone:Number.isFinite(p.pubDone)?p.pubDone:rows.filter(r=>r.publicInfo?.done||r.publicInfo?.errors?.length).length,pubTotal:Number.isFinite(p.pubTotal)?p.pubTotal:rows.length,audDone:Number.isFinite(p.audDone)?p.audDone:rows.filter(r=>r.auditChecked).length,audTotal:Number.isFinite(p.audTotal)?p.audTotal:rows.length};}
function progressOne(label,done,total){const pct=total?Math.max(0,Math.min(100,done/total*100)):0,ok=total>0&&done>=total;return`<div class="ep-item ${ok?'done':''}"><div class="ep-head"><span>${label}</span><span>${done}/${total}${ok?' ✓':''}</span></div><div class="ep-track"><div class="ep-fill" style="width:${pct.toFixed(1)}%"></div></div></div>`;}
function fullProgressHtml(){const p=fullProgressState();return progressOne('DPE ADEME',p.dpeDone,p.dpeTotal)+progressOne('BDNB / RNIC / OSM',p.pubDone,p.pubTotal)+progressOne('AUDIT ADEME',p.audDone,p.audTotal);}
function updateFullProgress(dpeDone,dpeTotal,pubDone,pubTotal,audDone,audTotal){const old=state.qual._fullProgress||{};state.qual._fullProgress={dpeDone:Number.isFinite(dpeDone)?dpeDone:old.dpeDone,dpeTotal:Number.isFinite(dpeTotal)?dpeTotal:old.dpeTotal,pubDone:Number.isFinite(pubDone)?pubDone:old.pubDone,pubTotal:Number.isFinite(pubTotal)?pubTotal:old.pubTotal,audDone:Number.isFinite(audDone)?audDone:old.audDone,audTotal:Number.isFinite(audTotal)?audTotal:old.audTotal};const el=document.getElementById('simpleProgress');if(el)el.innerHTML=fullProgressHtml();}

qualifiedTableHtml=function(rows){
  const showFloor=shouldShowFloor(),cols=showFloor?20:19;let h=`<thead><tr><th class="keep-head">Garder</th>${qualHeader('date','Date')}${qualHeader('distance','Distance','num')}${qualHeader('type','Type')}${qualHeader('surface','Surface','num')}${qualHeader('pieces','Pièces','num')}${qualHeader('dpe','DPE')}${qualHeader('construction','Construction')}${showFloor?qualHeader('floor','Étage'):''}<th>Fiabilité</th>${qualHeader('copro','Copro')}${qualHeader('terrain','Terrain','num')}<th>Équipements / extérieurs</th>${qualHeader('works','Travaux / source')}${qualHeader('workBudget','Budget travaux préconisés (audit)','num')}${qualHeader('val','Prix vendu','num')}${qualHeader('ppm','€/m²','num')}${qualHeader('mutation','Mutation')}${qualHeader('voie','Adresse')}<th>Sources</th></tr></thead><tbody>`;
  rows.forEach(r=>{const di=r.dpeInfo,b=simpleWorkBudget(r),keep=priceRowIsKept(r),sk=encodeURIComponent(stableRowId(r));h+=`<tr data-sync-key="${sk}" class="${keep?'price-kept':'price-excluded'} ${state.qual.mapFocusKey===sk?'sync-focus':''}" onmouseenter="syncTableHover('${sk}',true)" onmouseleave="syncTableHover('${sk}',false)"><td class="keep-head"><input class="price-keep" type="checkbox" ${keep?'checked':''} onchange="togglePriceKeep('${encodeURIComponent(rowKey(r))}')" title="Inclure ce bien dans le Prix global médian"></td><td>${r.date||'—'}</td><td class="num">${isFinite(r.dist)?f0(r.dist)+' m':'—'}${microLocationHtml(r)}</td><td>${esc(r.type)}</td><td class="num">${r.surface>0?f0(r.surface)+' m²':'—'}</td><td class="num">${isFinite(r.pieces)?r.pieces:'—'}</td><td>${dpeBadge(di?.dpe)}<span class="conf ${di?.confidence||''}">${confidenceLabel(di?.confidence)}</span></td><td>${periodLabel(di?.period)}${isFinite(di?.year)?`<span class="conf">${di.year}</span>`:''}</td>${showFloor?`<td>${floorLabel(di?.floor)}</td>`:''}<td>${reliabilityHtml(r)}</td><td>${coproCell(r)}</td><td class="num">${r.terrain>0?f0(r.terrain)+' m²':'—'}</td><td>${freeFeaturesHtml(r)}</td><td>${simpleWorksCellHtml(r)}</td><td class="num">${isFinite(b.value)&&b.value>0?`<b>${eur(b.value)}</b><span class="conf">${b.source==='audit'?'travaux énergétiques préconisés · audit certain':'saisie manuelle'}</span>`:(b.source==='audit_unconfirmed'?`<span class="conf low"><b>À confirmer</b><br>audit non suffisamment rapproché</span>`:'—')}</td><td class="num"><b>${eur(r.val)}</b></td><td class="num"><b>${ppmF(r.ppm)}</b></td><td>${mutationBadgeHtml(r)}</td><td>${addrLink(r)}</td><td>${publicDetailsButton(r)}</td></tr>`;});
  if(!rows.length)h+=`<tr><td colspan="${cols}" style="padding:28px;text-align:center"><b>Aucune vente ne correspond aux filtres actuels.</b><br><span class="conf" style="display:block;margin-top:6px">Clique « Réinitialiser » pour afficher toutes les ventes de l’analyse.</span></td></tr>`;return h+'</tbody>';
};

function syncKeyForRow(r){return encodeURIComponent(stableRowId(r));}
function syncTableHover(key,on){const m=state._syncMarkers?.get(key);if(m){if(on)m.setStyle({radius:10,weight:3,color:'#fff',fillOpacity:1});else{const o=m._syncDefault||{};m.setStyle(o);}}const tr=document.querySelector(`[data-sync-key="${key}"]`);if(tr)tr.classList.toggle('sync-focus',!!on);}
function openRowFromMap(key){state.qual.mapFocusKey=key;setView('qualifies');setTimeout(()=>{const tr=document.querySelector(`[data-sync-key="${key}"]`);if(tr){tr.classList.add('sync-focus');tr.scrollIntoView({behavior:'smooth',block:'center'});}else setStatus('Ce bien est masqué par les filtres actuels de Détermination du prix.','info');},100);}

drawMutations=function(){
  mutMarkers.clearLayers();const S=sel().filter(r=>isFinite(r.lat)&&isFinite(r.lon)),present=new Set(),qmap=new Map((state.qual.rows||[]).map(r=>[stableRowId(r),r]));let visible=null;try{visible=new Set(qualifiedFilteredRows(false).map(stableRowId));}catch(e){visible=new Set();}state._syncMarkers=new Map();
  S.forEach(r=>{present.add(r.type);const q=qmap.get(stableRowId(r)),kept=q?priceRowIsKept(q):false,inFilters=q?visible.has(stableRowId(q)):false,color=kept&&inFilters?'#4A5240':(TYPE_COLOR[r.type]||TYPE_COLOR.Autre),opts={radius:kept&&inFilters?8:5,color:kept&&inFilters?'#fff':'#ffffff',weight:kept&&inFilters?2.5:1,fillColor:color,fillOpacity:kept&&inFilters?.98:.55};const m=L.circleMarker([r.lat,r.lon],opts).bindTooltip(`<div style="font-weight:800;margin-bottom:2px">${r.type}</div>${f0(r.surface)} m²<br>Prix : <b>${eur(r.val)}</b><br>Prix/m² : ${ppmF(r.ppm)}<br>${kept&&inFilters?'<b style="color:#a57f10">✓ Gardé pour le prix médian</b><br>':''}${r.commune||''}`,{direction:'top',opacity:1,sticky:true,className:'mut-tip'}).addTo(mutMarkers);m._syncDefault=opts;const key=syncKeyForRow(r);state._syncMarkers.set(key,m);m.on('mouseover',()=>syncTableHover(key,true));m.on('mouseout',()=>syncTableHover(key,false));m.on('click',()=>openRowFromMap(key));});updateLegend(present);
};

function renderComparator(){
  const body=document.getElementById('compareBody');if(!body)return;const visible=qualifiedFilteredRows(false),rows=visible.filter(priceRowIsKept),st=simpleGlobalPriceStats(visible);
  if(!rows.length){body.innerHTML='<div class="compare-hero"><h2>Comparateur</h2><p>Comparaison côte à côte des biens gardés.</p></div><div class="compare-panel"><div class="compare-empty">Aucun bien gardé avec les filtres actuels. Retourne dans « Détermination du prix » et coche les références à comparer.</div></div>';return;}
  const cell=(label,fn)=>`<tr><td>${label}</td>${rows.map(r=>`<td>${fn(r)}</td>`).join('')}</tr>`;
  let table=`<table class="compare-table"><thead><tr><th>Critère</th>${rows.map(r=>`<th><div class="compare-address">${esc(r.voie||r.commune||'Comparable')}</div><div class="compare-note">${r.date||'—'} · ${isFinite(r.dist)?f0(r.dist)+' m':'—'}</div></th>`).join('')}</tr></thead><tbody>`;
  table+=cell('Prix vendu',r=>`<div class="compare-price">${eur(r.val)}</div>`)+cell('€/m²',r=>`<b>${ppmF(r.ppm)}</b>`)+cell('Surface',r=>r.surface>0?f0(r.surface)+' m²':'—')+cell('Pièces',r=>isFinite(r.pieces)?r.pieces:'—')+cell('DPE',r=>`${dpeBadge(r.dpeInfo?.dpe)} <span class="conf">${confidenceLabel(r.dpeInfo?.confidence)}</span>`)+cell('Construction',r=>`${periodLabel(r.dpeInfo?.period)}${isFinite(r.dpeInfo?.year)?' · '+r.dpeInfo.year:''}`)+(shouldShowFloor()?cell('Étage',r=>floorLabel(r.dpeInfo?.floor)):'')+cell('Copropriété',r=>coproCell(r))+cell('Terrain',r=>r.terrain>0?f0(r.terrain)+' m²':'—')+cell('Fiabilité',r=>reliabilityHtml(r))+cell('Équipements / extérieurs',r=>freeFeaturesHtml(r))+cell('Travaux / audit',r=>simpleWorksCellHtml(r))+cell('Mutation',r=>mutationBadgeHtml(r));table+='</tbody></table>';
  body.innerHTML=`<div class="compare-hero"><h2>Comparateur</h2><p>${rows.length} bien${rows.length>1?'s':''} gardé${rows.length>1?'s':''} · comparaison des mêmes références utilisées pour le Prix global médian.</p></div><div class="compare-panel"><div style="display:flex;justify-content:space-between;gap:12px;align-items:center;margin-bottom:12px"><div><b>Fourchette actuelle :</b> ${isFinite(st.lowPrice)?eur(st.lowPrice):'—'} · <b>Médiane :</b> ${isFinite(st.price)?eur(st.price):'—'} · <b>Haute :</b> ${isFinite(st.highPrice)?eur(st.highPrice):'—'}</div><button class="decision-btn" onclick="setView('qualifies')">← Détermination du prix</button></div><div class="compare-scroll">${table}</div></div>`;
}

function exportFinalSelection(){
  const visible=qualifiedFilteredRows(false),rows=visible.filter(priceRowIsKept);if(!rows.length){setStatus('Aucun bien gardé à exporter.','err');return;}const st=simpleGlobalPriceStats(visible);
  const data=rows.map(r=>{const c=publicCoproStatus(r),rel=reliabilityInfo(r),b=simpleWorkBudget(r);return{'Date':r.date||'','Adresse':r.voie||'','Commune':r.commune||'','Distance (m)':isFinite(r.dist)?Math.round(r.dist):'','Type':r.type||'','Surface (m²)':r.surface||'','Pièces':isFinite(r.pieces)?r.pieces:'','DPE':r.dpeInfo?.dpe||'','Fiabilité DPE':confidenceLabel(r.dpeInfo?.confidence),'Construction':isFinite(r.dpeInfo?.year)?r.dpeInfo.year:periodLabel(r.dpeInfo?.period),'Copropriété':c.value===true?'Oui':c.value===false?'Non détectée':'Inconnue','Terrain (m²)':r.terrain||'','Fiabilité globale':rel.label,'Prix vendu (€)':r.val||'','Prix €/m²':r.ppm||'','Budget audit certain (€)':b.source==='audit'?b.value:'','Mutation':r.qMutation?.reason||''};});
  const wb=XLSX.utils.book_new(),ws=XLSX.utils.json_to_sheet(data);ws['!cols']=Object.keys(data[0]).map(k=>({wch:Math.min(34,Math.max(12,k.length+2))}));XLSX.utils.book_append_sheet(wb,ws,'Comparables gardés');
  const syn=[['SYNTHÈSE DE LA SÉLECTION FINALE',''],['Adresse recherchée',state.addresses.map(a=>a.label).join(' | ')],['Biens gardés',rows.length],['Surface cible (m²)',isFinite(st.surface)?st.surface:''],['État du bien',priceConditionLabel(state.qual.priceCondition)],['Ajustement (%)',st.adj],['€/m² bas',isFinite(st.lowPpm)?Math.round(st.lowPpm):''],['€/m² médian',isFinite(st.adjustedPpm)?Math.round(st.adjustedPpm):''],['€/m² haut',isFinite(st.highPpm)?Math.round(st.highPpm):''],['Prix bas (€)',isFinite(st.lowPrice)?Math.round(st.lowPrice):''],['Prix médian (€)',isFinite(st.price)?Math.round(st.price):''],['Prix haut (€)',isFinite(st.highPrice)?Math.round(st.highPrice):''],['Dispersion',st.dispersionLabel+(isFinite(st.dispersion)?' · '+st.dispersion.toFixed(1)+' %':'')]];const ws2=XLSX.utils.aoa_to_sheet(syn);ws2['!cols']=[{wch:28},{wch:45}];XLSX.utils.book_append_sheet(wb,ws2,'Synthèse');XLSX.writeFile(wb,'Selection_finale_DVF_MDB.xlsx');setStatus(`${rows.length} bien${rows.length>1?'s':''} gardé${rows.length>1?'s':''} exporté${rows.length>1?'s':''}.`,'ok');
}

refreshQualifiedView=function(){
  const current=normalizeManualFilterState(state.qual.filters||{});state.qual.filters={dpe:getCheckedValues('qfDpe',current.dpe),pieces:getCheckedValues('qfPieces',current.pieces),constructionMin:document.getElementById('qfConstructionMin')?.value??current.constructionMin,constructionMax:document.getElementById('qfConstructionMax')?.value??current.constructionMax,floor:document.getElementById('qfFloor')?.value||'all',copro:document.getElementById('qfCopro')?.value||'all',terrain:document.getElementById('qfTerrain')?.value||'all'};
  const rows=qualifiedFilteredRows(true),tbl=document.getElementById('qualTable');if(tbl)tbl.innerHTML=qualifiedTableHtml(rows);const c=document.getElementById('qualVisibleCount');if(c)c.textContent=`${rows.length} / ${state.qual.rows.length} ventes affichées`;const gp=document.getElementById('simpleGlobalPrice');if(gp)gp.innerHTML=simpleGlobalPriceHtml(rows);drawMutations();if(state.view==='comparateur')renderComparator();
};

togglePriceKeep=function(encoded){const k=decodeURIComponent(encoded),r=(state.qual.rows||[]).find(x=>rowKey(x)===k);if(!r)return;r.priceSelected=!priceRowIsKept(r);refreshQualifiedView();};
setDisplayedPriceSelection=function(on){qualifiedFilteredRows(false).forEach(r=>r.priceSelected=!!on);refreshQualifiedView();};

renderQualifiedResults=function(){
  const body=document.getElementById('qualBody');if(!body)return;if(!state.qual.rows.length){renderQualifiedBase();return;}const source=qualifiedSourceRows();if(source.length!==state.qual.rows.length||source.some((r,i)=>rowKey(r)!==rowKey(state.qual.rows[i]))){state.qual.simpleStarted=false;renderQualifiedBase();return;}const rows=qualifiedFilteredRows(true),c=simpleEnrichmentCounts();
  body.innerHTML=`<div class="qual-hero simple-qual-hero"><div><h2>Détermination du prix</h2><p>Filtre les ventes, puis coche uniquement les biens que tu veux conserver dans le calcul du prix médian.</p></div><div class="qual-source">${c.total} VENTES · ${c.dpe} DPE · ${c.public} PUBLIC</div></div><div class="qual-panel simple-table-panel"><div class="simple-table-head"><div><h3>Tableau des ventes analysées</h3><div class="subtxt">Le Prix global médian est calculé uniquement sur les ventes affichées que tu laisses cochées dans « Garder ».</div></div><div class="decision-actions"><span id="qualVisibleCount" class="visible-count">${rows.length} / ${state.qual.rows.length} ventes affichées</span><button class="decision-btn" onclick="setView('carte')">Voir sur la carte</button><button class="decision-btn" onclick="setView('comparateur')">Comparer</button><button class="decision-btn" onclick="exportFinalSelection()">Exporter la sélection</button><button class="qual-secondary" onclick="enrichSimpleDetermination(true)">Actualiser depuis les sources</button></div></div><div id="simpleProgress" class="enrichment-progress">${fullProgressHtml()}</div><div id="simpleGlobalPrice">${simpleGlobalPriceHtml(rows)}</div>${filterBarHtml()}<div class="qual-table-wrap simple-table-wrap"><table class="qual-table simple-qual-table" id="qualTable">${qualifiedTableHtml(rows)}</table></div><div class="qual-warn"><b>Données stabilisées :</b> les enrichissements DPE / BDNB / RNIC / OSM / AUDIT sont réutilisés lorsqu’ils sont déjà fiabilisés. Si tu relances une nouvelle analyse, les recherches de l’analyse précédente sont immédiatement abandonnées et la priorité passe au nouveau jeu de ventes.</div></div>`;
  if(state.view==='qualifies'&&!state.qual.simpleStarted&&!state.qual.running){state.qual.simpleStarted=true;setTimeout(()=>enrichSimpleDetermination(false),40);}drawMutations();
};

setView=function(v){state.view=v;document.getElementById('viewSel').value=v;document.getElementById('mapView').classList.toggle('active',v==='carte');document.getElementById('view-vendus').classList.toggle('active',v==='vendus');document.getElementById('view-qualifies').classList.toggle('active',v==='qualifies');document.getElementById('view-comparateur')?.classList.toggle('active',v==='comparateur');if(v==='carte')setTimeout(()=>{map.invalidateSize();drawMutations();fitMap();},60);if(v==='qualifies'&&!state.qual.running){if(state.qual.rows.length)renderQualifiedResults();else renderQualifiedBase();}if(v==='comparateur')renderComparator();};

/* Progression détaillée : chaque nouvelle analyse invalide l'ancienne grâce à enrichmentEpoch. */
enrichSimpleDetermination=async function(force=false){
  if(state.qual.running||!state.qual.rows.length)return;const myEpoch=++enrichmentEpoch,alive=()=>myEpoch===enrichmentEpoch;state.qual.simpleStarted=true;state.qual.running=true;
  try{const rows=[...state.qual.rows];if(force){clearRuntimeEnrichmentCaches();rows.forEach(r=>{const locked=loadCoproDecision(r,r.publicInfo?.banId||r.dpeInfo?.banId||'');clearStableRow(r);r.dpeChecked=false;delete r.dpeInfo;r.publicInfo=locked?{done:false,osmChecked:false,coproDecision:locked,immat:locked.immat||'',immatSource:locked.source||'',errors:[]}:null;r.auditChecked=false;r.auditInfo=null;});}
    state.qual._fullProgress={dpeDone:rows.filter(r=>r.dpeChecked).length,dpeTotal:rows.length,pubDone:rows.filter(r=>r.publicInfo?.done||r.publicInfo?.errors?.length).length,pubTotal:rows.length,audDone:rows.filter(r=>r.auditChecked).length,audTotal:rows.length};updateFullProgress();if(!alive())return;
    setStatus(`Tableau affiché · enrichissement DPE en arrière-plan (${rows.length} ventes)…`,'info');
    const er=await enrichRowsDpe(rows,()=>{if(!alive())return;updateFullProgress(rows.filter(r=>r.dpeChecked).length,rows.length,undefined,undefined,undefined,undefined);const info=document.getElementById('srcInfo');if(info)info.textContent=`DPE ADEME ${rows.filter(r=>r.dpeChecked).length}/${rows.length}…`;},alive);if(!alive())return;
    state.qual.dpeErrors=er.errors;state.qual.enrichedCount=rows.filter(r=>r.dpeInfo!=null).length;state.qual.enrichedAll=true;renderQualifiedResults();updateFullProgress(rows.filter(r=>r.dpeChecked).length,rows.length);setStatus('DPE chargé · enrichissement BDNB / RNIC / OSM et AUDIT en parallèle…','info');
    let pd=rows.filter(r=>r.publicInfo?.done||r.publicInfo?.errors?.length).length,ad=rows.filter(r=>r.auditChecked).length;updateFullProgress(undefined,undefined,pd,rows.length,ad,rows.length);
    const [pe,ae]=await Promise.all([enrichRowsPublic(rows,(d,n)=>{if(!alive())return;pd=d;updateFullProgress(undefined,undefined,pd,n,ad,rows.length);const info=document.getElementById('srcInfo');if(info)info.textContent=`BDNB / RNIC / OSM ${d}/${n}…`;},alive),enrichAllAuditsSimple(rows,(d,n)=>{if(!alive())return;ad=d;updateFullProgress(undefined,undefined,pd,rows.length,ad,n);},alive)]);if(!alive())return;
    state.qual.publicErrors+=pe.errors;state.qual.auditErrors+=ae.errors;state.qual.publicEnrichedCount=rows.filter(r=>r.publicInfo?.done).length;state.qual.publicEnrichedAll=true;state.qual.auditEnrichedCount=rows.filter(r=>r.auditChecked).length;state.qual.auditEnrichedAll=true;updateFullProgress(rows.length,rows.length,rows.length,rows.length,rows.length,rows.length);renderQualifiedResults();if(state.view==='comparateur')renderComparator();const c=simpleEnrichmentCounts();setStatus(`Analyse enrichie : ${c.total} ventes · ${c.dpe} DPE · ${c.public} données publiques · ${c.audit} audits vérifiés.`,'ok');
  }catch(e){if(alive()){console.error(e);setStatus('Enrichissement du tableau : '+e.message,'err');}}finally{if(alive())state.qual.running=false;}
};

</script>

<script id="selectionPdfPatch">
/* ============================================================
   PATCH - sélection finale + filtres allégés + export PDF
   ============================================================ */

/* Plus de filtre Année de construction. */
filterBarHtml=function(){
  const f=normalizeManualFilterState(state.qual.filters||{}),showFloor=shouldShowFloor();
  return `<div class="qual-filterbar simple-filters">
    <div class="qf qf-wide"><label>DPE</label>${multiChoiceHtml('qfDpe',[...DPE_ORDER.map(x=>[x,x]),['UNKNOWN','Inconnu']],f.dpe)}</div>
    <div class="qf qf-wide"><label>Pièces</label>${multiChoiceHtml('qfPieces',[['1','1'],['2','2'],['3','3'],['4','4'],['5','5'],['6plus','6+'],['UNKNOWN','Inconnu']],f.pieces)}</div>
    ${showFloor?`<div class="qf"><label>Étage</label><select id="qfFloor" onchange="refreshQualifiedView()"><option value="all" ${f.floor==='all'?'selected':''}>Tous</option><option value="rdc" ${f.floor==='rdc'?'selected':''}>RDC</option><option value="1" ${f.floor==='1'?'selected':''}>1er</option><option value="2plus" ${f.floor==='2plus'?'selected':''}>2e et +</option><option value="unknown" ${f.floor==='unknown'?'selected':''}>Inconnu</option></select></div>`:''}
    <div class="qf"><label>Copropriété</label><select id="qfCopro" onchange="refreshQualifiedView()"><option value="all" ${f.copro==='all'?'selected':''}>Tous</option><option value="yes" ${f.copro==='yes'?'selected':''}>Oui</option><option value="no" ${f.copro==='no'?'selected':''}>Non détectée</option><option value="unknown" ${f.copro==='unknown'?'selected':''}>Inconnu</option></select></div>
    <div class="qf"><label>Terrain</label><select id="qfTerrain" onchange="refreshQualifiedView()"><option value="all" ${f.terrain==='all'?'selected':''}>Tous</option><option value="yes" ${f.terrain==='yes'?'selected':''}>Avec terrain</option><option value="no" ${f.terrain==='no'?'selected':''}>Sans terrain</option></select></div>
    <button class="qual-secondary" onclick="resetQualifiedFilters()">Réinitialiser</button>
  </div>`;
};

qualifiedFilteredRows=function(applySort=true){
  const rows=state.qual.rows||[],f=normalizeManualFilterState(state.qual.filters||{});
  const dpes=getCheckedValues('qfDpe',f.dpe),pieces=getCheckedValues('qfPieces',f.pieces);
  const floor=document.getElementById('qfFloor')?.value||f.floor||'all',copro=document.getElementById('qfCopro')?.value||f.copro||'all',terrain=document.getElementById('qfTerrain')?.value||f.terrain||'all';
  const filtered=rows.filter(r=>{
    if(dpes.length){const d=r.dpeInfo?.dpe||'UNKNOWN';if(!dpes.includes(d))return false;}
    if(pieces.length){const p=isFinite(r.pieces)?(+r.pieces>=6?'6plus':String(+r.pieces)):'UNKNOWN';if(!pieces.includes(p))return false;}
    if(shouldShowFloor()&&floor!=='all'){
      const v=r.dpeInfo?.floor;
      if(floor==='unknown'&&isFinite(v))return false;
      if(floor!=='unknown'){
        if(!isFinite(v))return false;
        if(floor==='rdc'&&+v!==0)return false;
        if(floor==='1'&&+v!==1)return false;
        if(floor==='2plus'&&+v<2)return false;
      }
    }
    if(copro!=='all'){
      const c=publicCoproStatus(r);
      if(copro==='yes'&&c.value!==true)return false;
      if(copro==='no'&&c.value!==false)return false;
      if(copro==='unknown'&&c.value!==null)return false;
    }
    if(terrain==='yes'&&!(r.terrain>0))return false;
    if(terrain==='no'&&r.terrain>0)return false;
    return true;
  });
  return applySort?qualifiedSortRows(filtered):filtered;
};

function syncKeepAllCheckbox(){
  const cb=document.getElementById('keepAllDisplayed');if(!cb)return;
  const rows=qualifiedFilteredRows(false),kept=rows.filter(priceRowIsKept).length;
  cb.checked=rows.length>0&&kept===rows.length;
  cb.indeterminate=kept>0&&kept<rows.length;
}
function toggleAllDisplayedFromHeader(checked){setDisplayedPriceSelection(!!checked);}

/* Colonne Budget travaux préconisés supprimée. */
qualifiedTableHtml=function(rows){
  const showFloor=shouldShowFloor(),cols=showFloor?19:18;
  let h=`<thead><tr><th class="keep-head"><label class="keep-all-wrap" title="Tout sélectionner / désélectionner dans les ventes affichées"><input id="keepAllDisplayed" type="checkbox" onchange="toggleAllDisplayedFromHeader(this.checked)"><span>Garder</span></label></th>${qualHeader('date','Date')}${qualHeader('distance','Distance','num')}${qualHeader('type','Type')}${qualHeader('surface','Surface','num')}${qualHeader('pieces','Pièces','num')}${qualHeader('dpe','DPE')}${qualHeader('construction','Construction')}${showFloor?qualHeader('floor','Étage'):''}<th>Fiabilité</th>${qualHeader('copro','Copropriété')}${qualHeader('terrain','Terrain','num')}<th>Équipements / extérieurs</th>${qualHeader('works','Travaux / source')}${qualHeader('val','Prix vendu','num')}${qualHeader('ppm','€/m²','num')}${qualHeader('mutation','Mutation')}${qualHeader('voie','Adresse')}<th>Sources</th></tr></thead><tbody>`;
  rows.forEach(r=>{
    const di=r.dpeInfo,keep=priceRowIsKept(r),sk=encodeURIComponent(stableRowId(r));
    h+=`<tr data-sync-key="${sk}" class="${keep?'price-kept':'price-excluded'} ${state.qual.mapFocusKey===sk?'sync-focus':''}" onmouseenter="syncTableHover('${sk}',true)" onmouseleave="syncTableHover('${sk}',false)"><td class="keep-head"><input class="price-keep" type="checkbox" ${keep?'checked':''} onchange="togglePriceKeep('${encodeURIComponent(rowKey(r))}')" title="Inclure ce bien dans le Prix global médian"></td><td>${r.date||'—'}</td><td class="num">${isFinite(r.dist)?f0(r.dist)+' m':'—'}${microLocationHtml(r)}</td><td>${esc(r.type)}</td><td class="num">${r.surface>0?f0(r.surface)+' m²':'—'}</td><td class="num">${isFinite(r.pieces)?r.pieces:'—'}</td><td>${dpeBadge(di?.dpe)}<span class="conf ${di?.confidence||''}">${confidenceLabel(di?.confidence)}</span></td><td>${periodLabel(di?.period)}${isFinite(di?.year)?`<span class="conf">${di.year}</span>`:''}</td>${showFloor?`<td>${floorLabel(di?.floor)}</td>`:''}<td>${reliabilityHtml(r)}</td><td>${coproCell(r)}</td><td class="num">${r.terrain>0?f0(r.terrain)+' m²':'—'}</td><td>${freeFeaturesHtml(r)}</td><td>${simpleWorksCellHtml(r)}</td><td class="num"><b>${eur(r.val)}</b></td><td class="num"><b>${ppmF(r.ppm)}</b></td><td>${mutationBadgeHtml(r)}</td><td>${addrLink(r)}</td><td>${publicDetailsButton(r)}</td></tr>`;
  });
  if(!rows.length)h+=`<tr><td colspan="${cols}" style="padding:28px;text-align:center"><b>Aucune vente ne correspond aux filtres actuels.</b><br><span class="conf" style="display:block;margin-top:6px">Clique « Réinitialiser » pour afficher toutes les ventes de l’analyse.</span></td></tr>`;
  return h+'</tbody>';
};

/* Boutons de sélection explicites. */
const _simpleGlobalPriceHtmlSelectionPdf=simpleGlobalPriceHtml;
simpleGlobalPriceHtml=function(rows){
  return _simpleGlobalPriceHtmlSelectionPdf(rows)
    .replace('✓ Garder tous les biens affichés','✓ Tout sélectionner')
    .replace('× Tout retirer','× Tout désélectionner');
};

refreshQualifiedView=function(){
  const current=normalizeManualFilterState(state.qual.filters||{});
  state.qual.filters={
    dpe:getCheckedValues('qfDpe',current.dpe),
    pieces:getCheckedValues('qfPieces',current.pieces),
    floor:document.getElementById('qfFloor')?.value||'all',
    copro:document.getElementById('qfCopro')?.value||'all',
    terrain:document.getElementById('qfTerrain')?.value||'all'
  };
  const rows=qualifiedFilteredRows(true),tbl=document.getElementById('qualTable');if(tbl)tbl.innerHTML=qualifiedTableHtml(rows);
  const c=document.getElementById('qualVisibleCount');if(c)c.textContent=`${rows.length} / ${state.qual.rows.length} ventes affichées`;
  const gp=document.getElementById('simpleGlobalPrice');if(gp)gp.innerHTML=simpleGlobalPriceHtml(rows);
  syncKeepAllCheckbox();drawMutations();if(state.view==='comparateur')renderComparator();
};
resetQualifiedFilters=function(){state.qual.filters={dpe:[],pieces:[],floor:'all',copro:'all',terrain:'all'};renderQualifiedResults();};

togglePriceKeep=function(encoded){const k=decodeURIComponent(encoded),r=(state.qual.rows||[]).find(x=>rowKey(x)===k);if(!r)return;r.priceSelected=!priceRowIsKept(r);refreshQualifiedView();};
setDisplayedPriceSelection=function(on){qualifiedFilteredRows(false).forEach(r=>r.priceSelected=!!on);refreshQualifiedView();};

/* PDF moderne - uniquement la sélection finale actuellement visible et gardée. */
function pdfMoney(v){return isFinite(v)?Math.round(v).toLocaleString('fr-FR').replace(/\u202f/g,' ')+' EUR':'-';}
function pdfPpm(v){return isFinite(v)?Math.round(v).toLocaleString('fr-FR').replace(/\u202f/g,' ')+' EUR/m2':'-';}
function pdfClean(v){return String(v??'').replace(/[–—]/g,'-').replace(/\u202f/g,' ');}
function pdfCopro(r){const c=publicCoproStatus(r);return c.value===true?'Oui':c.value===false?'Non detectee':'Inconnue';}
function pdfWorks(r){const e=energyWorksInfo(r);return pdfClean(e?.label||'Inconnu');}
function safePdfFileName(){const a=state.addresses?.[0]?.label||'secteur';return ('Selection_DVF_'+a).normalize('NFD').replace(/[\u0300-\u036f]/g,'').replace(/[^a-zA-Z0-9]+/g,'_').replace(/^_+|_+$/g,'').slice(0,90)+'.pdf';}

exportFinalSelection=function(){
  const visible=qualifiedFilteredRows(false),rows=visible.filter(priceRowIsKept);
  if(!rows.length){setStatus('Aucun bien gardé à exporter.','err');return;}
  if(!window.jspdf?.jsPDF){setStatus('Le module PDF n’est pas disponible. Recharge la page puis réessaie.','err');return;}
  const st=simpleGlobalPriceStats(visible),{jsPDF}=window.jspdf;
  const doc=new jsPDF({orientation:'landscape',unit:'mm',format:'a4',compress:true});
  const W=doc.internal.pageSize.getWidth(),H=doc.internal.pageSize.getHeight(),gold=[202,167,56],ink=[27,32,42],muted=[112,122,136],paper=[247,248,250];
  const money=pdfMoney,ppm=pdfPpm;
  function roundRect(x,y,w,h,fill,stroke=null,r=3){if(fill){doc.setFillColor(...fill);doc.roundedRect(x,y,w,h,r,r,'F');}if(stroke){doc.setDrawColor(...stroke);doc.roundedRect(x,y,w,h,r,r,'S');}}
  function footer(){const pg=doc.internal.getCurrentPageInfo().pageNumber;doc.setDrawColor(224,227,232);doc.line(10,H-10,W-10,H-10);doc.setFont('helvetica','normal');doc.setFontSize(7);doc.setTextColor(...muted);doc.text('Analyse DVF - SAS De Mere en Fils MDB - Selection finale',10,H-5.5);doc.text('Page '+pg,W-10,H-5.5,{align:'right'});}
  function pageTop(){doc.setFillColor(...ink);doc.rect(0,0,W,14,'F');doc.setFont('helvetica','bold');doc.setFontSize(8.5);doc.setTextColor(255,255,255);doc.text('ETUDE DE SECTEUR DVF',10,9);doc.setTextColor(...gold);doc.text('MDB',W-10,9,{align:'right'});}
  pageTop();
  doc.setFont('helvetica','bold');doc.setFontSize(21);doc.setTextColor(...ink);doc.text('Selection finale des comparables',10,27);
  doc.setFont('helvetica','normal');doc.setFontSize(9);doc.setTextColor(...muted);const adr=pdfClean(state.addresses.map(a=>a.label).join(' | '));doc.text(adr||'Secteur analyse',10,33,{maxWidth:210});
  doc.setFontSize(7.5);doc.text('Export du '+new Date().toLocaleDateString('fr-FR')+' - '+rows.length+' bien'+(rows.length>1?'s':'')+' retenu'+(rows.length>1?'s':''),W-10,28,{align:'right'});

  const cardY=39,cardH=23,gap=4,cardW=(W-20-gap*2)/3;
  const cards=[['FOURCHETTE BASSE',st.lowPrice,st.lowPpm],['PRIX MEDIAN',st.price,st.adjustedPpm],['FOURCHETTE HAUTE',st.highPrice,st.highPpm]];
  cards.forEach((c,i)=>{const x=10+i*(cardW+gap);roundRect(x,cardY,cardW,cardH,i===1?ink:paper,i===1?null:[226,229,234],3.5);doc.setFont('helvetica','bold');doc.setFontSize(7.5);doc.setTextColor(...(i===1?gold:muted));doc.text(c[0],x+5,cardY+6);doc.setFontSize(15);doc.setTextColor(...(i===1?[255,255,255]:ink));doc.text(money(c[1]),x+5,cardY+14);doc.setFont('helvetica','normal');doc.setFontSize(7.5);doc.setTextColor(...(i===1?[202,208,218]:muted));doc.text(ppm(c[2]),x+5,cardY+19);});

  const metaY=67,metaH=16,metaGap=3,metaW=(W-20-metaGap*4)/5;
  const meta=[['Surface cible',isFinite(st.surface)?Math.round(st.surface)+' m2':'Non renseignee'],['Etat du bien',pdfClean(priceConditionLabel(state.qual.priceCondition))],['Ajustement',((st.adj||0)>0?'+':'')+(st.adj||0).toLocaleString('fr-FR')+' %'],['Biens retenus',String(rows.length)],['Dispersion',pdfClean(st.dispersionLabel+(isFinite(st.dispersion)?' - '+st.dispersion.toFixed(1)+' %':''))]];
  meta.forEach((m,i)=>{const x=10+i*(metaW+metaGap);roundRect(x,metaY,metaW,metaH,[251,251,252],[230,232,236],3);doc.setFont('helvetica','bold');doc.setFontSize(6.8);doc.setTextColor(...muted);doc.text(m[0].toUpperCase(),x+4,metaY+5);doc.setFontSize(9);doc.setTextColor(...ink);doc.text(m[1],x+4,metaY+11.5,{maxWidth:metaW-8});});

  const head=[['Date','Adresse','Dist.','Surf.','Pieces','DPE','Construction','Copro','Terrain','Fiabilite','Prix vendu','EUR/m2','Travaux']];
  const body=rows.map(r=>{const rel=reliabilityInfo(r);return[
    pdfClean(r.date||'-'),pdfClean(r.voie||r.commune||'-'),isFinite(r.dist)?Math.round(r.dist)+' m':'-',r.surface>0?Math.round(r.surface)+' m2':'-',isFinite(r.pieces)?String(r.pieces):'-',pdfClean(r.dpeInfo?.dpe||'-'),pdfClean(isFinite(r.dpeInfo?.year)?String(r.dpeInfo.year):periodLabel(r.dpeInfo?.period)),pdfCopro(r),r.terrain>0?Math.round(r.terrain)+' m2':'-',pdfClean(rel.label),money(r.val),ppm(r.ppm),pdfWorks(r)
  ];});
  doc.autoTable({
    head,body,startY:88,margin:{left:10,right:10,top:22,bottom:14},theme:'grid',
    styles:{font:'helvetica',fontSize:7.1,textColor:ink,cellPadding:2.2,lineColor:[229,232,236],lineWidth:.2,valign:'middle',overflow:'linebreak'},
    headStyles:{fillColor:ink,textColor:[255,255,255],fontStyle:'bold',fontSize:7.1,lineColor:ink},
    alternateRowStyles:{fillColor:[249,249,247]},
    columnStyles:{0:{cellWidth:17},1:{cellWidth:39},2:{cellWidth:13},3:{cellWidth:14},4:{cellWidth:11},5:{cellWidth:10},6:{cellWidth:22},7:{cellWidth:20},8:{cellWidth:16},9:{cellWidth:18},10:{cellWidth:22},11:{cellWidth:17},12:{cellWidth:25}},
    didDrawPage:()=>{pageTop();footer();}
  });
  const y=Math.min(H-22,(doc.lastAutoTable?.finalY||90)+7);
  if(y<H-20){doc.setFont('helvetica','normal');doc.setFontSize(6.8);doc.setTextColor(...muted);doc.text('Les enrichissements DPE / BDNB / RNIC / OSM sont des aides a la comparaison. Les donnees incertaines restent a verifier avant decision.',10,y,{maxWidth:W-20});}
  doc.save(safePdfFileName());setStatus(`${rows.length} bien${rows.length>1?'s':''} exporté${rows.length>1?'s':''} en PDF.`,'ok');
};

/* Après chaque rendu complet, met à jour la case Tout sélectionner. */
const _renderQualifiedResultsSelectionPdf=renderQualifiedResults;
renderQualifiedResults=function(){_renderQualifiedResultsSelectionPdf();setTimeout(syncKeepAllCheckbox,0);};

/* ============================================================
   EXPORT PDF MODERNE - COMPARABLES VENDUS
   Exporte uniquement les mutations cochees dans Comparables vendus.
   ============================================================ */
function safeComparablesPdfFileName(){
  const a=state.addresses?.[0]?.label||'secteur';
  return ('Comparables_vendus_DVF_'+a).normalize('NFD').replace(/[\u0300-\u036f]/g,'').replace(/[^a-zA-Z0-9]+/g,'_').replace(/^_+|_+$/g,'').slice(0,90)+'.pdf';
}
function exportComparablesVendusPdf(){
  const rows=sel();
  if(!rows.length){setStatus('Aucun comparable vendu selectionne a exporter.','err');return;}
  if(!window.jspdf?.jsPDF){setStatus('Le module PDF n est pas disponible. Recharge la page puis reessaie.','err');return;}
  const {jsPDF}=window.jspdf;
  const doc=new jsPDF({orientation:'landscape',unit:'mm',format:'a4',compress:true});
  const W=doc.internal.pageSize.getWidth(),H=doc.internal.pageSize.getHeight();
  const gold=[202,167,56],ink=[27,32,42],muted=[111,121,136],paper=[247,248,250],line=[226,229,234];
  const money=v=>isFinite(v)?Math.round(v).toLocaleString('fr-FR').replace(/\u202f/g,' ')+' EUR':'-';
  const ppm=v=>isFinite(v)?Math.round(v).toLocaleString('fr-FR').replace(/\u202f/g,' ')+' EUR/m2':'-';
  const clean=v=>String(v??'').replace(/[–—]/g,'-').replace(/\u202f/g,' ');
  const vals=rows.map(r=>r.val).filter(isFinite),ppms=rows.map(r=>r.ppm).filter(isFinite),surfs=rows.map(r=>r.surface).filter(v=>v>0);
  const radiusEl=document.getElementById('radius'),fromEl=document.getElementById('yFrom'),toEl=document.getElementById('yTo');
  const radius=radiusEl?km(+radiusEl.value):'-',period=(fromEl&&toEl)?fromEl.value+' - '+toEl.value:'-';
  const addresses=clean((state.addresses||[]).map(a=>a.label).join(' | '))||'Secteur analyse';
  function rr(x,y,w,h,fill,stroke=null,r=3){if(fill){doc.setFillColor(...fill);doc.roundedRect(x,y,w,h,r,r,'F');}if(stroke){doc.setDrawColor(...stroke);doc.roundedRect(x,y,w,h,r,r,'S');}}
  function pageTop(){doc.setFillColor(...ink);doc.rect(0,0,W,14,'F');doc.setFont('helvetica','bold');doc.setFontSize(8.5);doc.setTextColor(255,255,255);doc.text('ETUDE DE SECTEUR DVF',10,9);doc.setTextColor(...gold);doc.text('MDB',W-10,9,{align:'right'});}
  function footer(){const pg=doc.internal.getCurrentPageInfo().pageNumber;doc.setDrawColor(...line);doc.line(10,H-10,W-10,H-10);doc.setFont('helvetica','normal');doc.setFontSize(7);doc.setTextColor(...muted);doc.text('SAS De Mere en Fils MDB - Comparables vendus DVF - Document de travail',10,H-5.5);doc.text('Page '+pg,W-10,H-5.5,{align:'right'});}

  pageTop();
  doc.setFont('helvetica','bold');doc.setFontSize(21);doc.setTextColor(...ink);doc.text('Comparables vendus',10,27);
  doc.setFont('helvetica','normal');doc.setFontSize(9);doc.setTextColor(...muted);doc.text(addresses,10,33,{maxWidth:210});
  doc.setFontSize(7.5);doc.text('Export du '+new Date().toLocaleDateString('fr-FR')+' - '+rows.length+' mutation'+(rows.length>1?'s':'')+' selectionnee'+(rows.length>1?'s':''),W-10,27,{align:'right'});
  doc.text('Rayon '+radius+' - Periode '+period,W-10,33,{align:'right'});

  const cardY=40,cardH=23,gap=4,cardW=(W-20-gap*3)/4;
  const cards=[
    ['MUTATIONS RETENUES',String(rows.length),'sur '+state.filtered.length+' ventes filtrees'],
    ['PRIX MEDIAN',money(median(vals)),'moyenne '+money(mean(vals))],
    ['PRIX/M2 MEDIAN',ppm(median(ppms)),'moyenne '+ppm(mean(ppms))],
    ['SURFACE MOYENNE',isFinite(mean(surfs))?Math.round(mean(surfs))+' m2':'-','mediane '+(isFinite(median(surfs))?Math.round(median(surfs))+' m2':'-')]
  ];
  cards.forEach((c,i)=>{
    const x=10+i*(cardW+gap);
    rr(x,cardY,cardW,cardH,i===1?ink:paper,i===1?null:line,3.5);
    doc.setFont('helvetica','bold');doc.setFontSize(7.1);doc.setTextColor(...(i===1?gold:muted));doc.text(c[0],x+5,cardY+6);
    doc.setFontSize(i===0?16:13.5);doc.setTextColor(...(i===1?[255,255,255]:ink));doc.text(c[1],x+5,cardY+14,{maxWidth:cardW-10});
    doc.setFont('helvetica','normal');doc.setFontSize(6.8);doc.setTextColor(...(i===1?[205,211,220]:muted));doc.text(c[2],x+5,cardY+19,{maxWidth:cardW-10});
  });

  const statsBody=[
    ['Minimum',money(arrMin(vals)),ppm(arrMin(ppms))],
    ['Moyenne',money(mean(vals)),ppm(mean(ppms))],
    ['Mediane',money(median(vals)),ppm(median(ppms))],
    ['Maximum',money(arrMax(vals)),ppm(arrMax(ppms))]
  ];
  doc.autoTable({
    startY:69,head:[['STATISTIQUES','VALEUR FONCIERE','PRIX/M2']],body:statsBody,theme:'grid',margin:{left:10,right:10},
    styles:{font:'helvetica',fontSize:7.4,textColor:ink,cellPadding:2,lineColor:line,lineWidth:.2},
    headStyles:{fillColor:ink,textColor:[255,255,255],fontStyle:'bold'},
    alternateRowStyles:{fillColor:[249,249,247]},columnStyles:{1:{halign:'right'},2:{halign:'right'}}
  });

  const startY=(doc.lastAutoTable?.finalY||95)+7;
  const head=[['Date','Type','Pieces','Surface','Terrain','Valeur','EUR/m2','Adresse']];
  const body=rows.map(r=>[
    clean(r.date||'-'),clean(r.type||'-'),isFinite(r.pieces)?String(r.pieces):'-',r.surface>0?Math.round(r.surface)+' m2':'-',r.terrain>0?Math.round(r.terrain)+' m2':'-',money(r.val),ppm(r.ppm),clean(r.voie||r.commune||'-')
  ]);
  doc.autoTable({
    head,body,startY,margin:{left:10,right:10,top:22,bottom:14},theme:'grid',
    styles:{font:'helvetica',fontSize:7.3,textColor:ink,cellPadding:2.2,lineColor:line,lineWidth:.2,valign:'middle',overflow:'linebreak'},
    headStyles:{fillColor:ink,textColor:[255,255,255],fontStyle:'bold',fontSize:7.3,lineColor:ink},
    alternateRowStyles:{fillColor:[249,249,247]},
    columnStyles:{0:{cellWidth:21},1:{cellWidth:22},2:{cellWidth:14,halign:'right'},3:{cellWidth:18,halign:'right'},4:{cellWidth:18,halign:'right'},5:{cellWidth:28,halign:'right'},6:{cellWidth:24,halign:'right'},7:{cellWidth:118}},
    didDrawPage:()=>{pageTop();footer();}
  });
  const y=Math.min(H-22,(doc.lastAutoTable?.finalY||startY)+7);
  if(y<H-20){doc.setFont('helvetica','normal');doc.setFontSize(6.8);doc.setTextColor(...muted);doc.text('Source : DVF. Les mutations exportees correspondent uniquement aux lignes cochees dans Comparables vendus au moment de l export.',10,y,{maxWidth:W-20});}
  doc.save(safeComparablesPdfFileName());
  setStatus(`${rows.length} comparable${rows.length>1?'s':''} vendu${rows.length>1?'s':''} exporte${rows.length>1?'s':''} en PDF.`,'ok');
}

/* Le bouton PDF historique utilise maintenant le meme rapport moderne. */
exportPdf=function(){closeExport();exportComparablesVendusPdf();};
