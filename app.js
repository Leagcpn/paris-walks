// Paris Walks — vanilla JS GPS tracker + suivi des rues de Paris

// --- Constantes ---
const PARIS_CENTER = [48.8566, 2.3522];
const PARIS_BBOX = { south: 48.815, west: 2.224, north: 48.902, east: 2.470 };

const STORAGE_KEY = "paris-walks-history";
const STREETS_CACHE_KEY = "paris-walks-streets-v2";
const DONE_STREETS_KEY = "paris-walks-done-streets-v2";
const PARIS_BOUNDARY_KEY = "paris-boundary-v1";
const CURRENT_WALK_KEY = "paris-walks-current";

const TOTAL_PARIS_KM = 1800;
const AUTOSAVE_INTERVAL_MS = 30000;

// Poids par défaut pour l'estimation des calories (sans paramétrage utilisateur).
const DEFAULT_WEIGHT_KG = 70;

const COVERAGE_THRESHOLD = 0.6; // 60 % de la rue à parcourir
const SAMPLE_INTERVAL_M = 12;   // un échantillon tous les ~12 m
const HIT_RADIUS_M = 10;        // proximité GPS pour "couvrir" un échantillon
const EXIT_DISTANCE_M = 40;     // distance qui considère qu'on est sorti d'une rue

// Grille spatiale ~55 m de côté, calée sur la latitude de Paris
const GRID_LAT = 0.0005;
const GRID_LNG = 0.00074;

const motivations = [
  "Prêt·e pour une nouvelle balade ?",
  "Chaque pas compte. À vous de jouer !",
  "Paris vous attend. En route !",
  "Une rue à découvrir aujourd'hui ?",
  "Belle journée pour marcher ✨",
];

// --- DOM refs ---
const toggleBtn = document.getElementById("toggle-btn");
const btnLabel = toggleBtn.querySelector(".btn-label");
const statusEl = document.getElementById("status");
const distanceEl = document.getElementById("stat-distance");
const durationEl = document.getElementById("stat-duration");
const paceEl = document.getElementById("stat-pace");
const motivationEl = document.getElementById("motivation");
const historyList = document.getElementById("history-list");
const historyCount = document.getElementById("history-count");
const progressPctEl = document.getElementById("progress-pct");
const progressDetailEl = document.getElementById("progress-detail");
const progressFillEl = document.getElementById("progress-fill");
const backBtn = document.getElementById("back-btn");
const detailTitleEl = document.getElementById("detail-title");
const detailSubtitleEl = document.getElementById("detail-subtitle");
const detailDistanceEl = document.getElementById("detail-distance");
const detailDurationEl = document.getElementById("detail-duration");
const detailCaloriesEl = document.getElementById("detail-calories");
const mainOnlyEls = document.querySelectorAll(".main-only");
const detailOnlyEls = document.querySelectorAll(".detail-only");

motivationEl.textContent = motivations[Math.floor(Math.random() * motivations.length)];

// --- Map ---
// Bornes Paris larges (sécurité tant que la vraie frontière n'est pas chargée).
const PARIS_FALLBACK_BOUNDS = L.latLngBounds(
  [PARIS_BBOX.south, PARIS_BBOX.west],
  [PARIS_BBOX.north, PARIS_BBOX.east],
);

const map = L.map("map", {
  zoomControl: true,
  attributionControl: true,
  preferCanvas: true,
  minZoom: 12,
  maxZoom: 18,
  maxBounds: PARIS_FALLBACK_BOUNDS,
  maxBoundsViscosity: 1.0,
}).setView(PARIS_CENTER, 13);

// Pas de tuiles : fond noir + dessin pur des rues, plus épuré.
map.attributionControl.addAttribution("© OpenStreetMap contributors");

let parisMaskLayer = null;

// Renderer canvas dédié aux rues (perf : milliers de polylines)
const streetsRenderer = L.canvas({ padding: 0.5 });

const liveIcon = L.divIcon({
  className: "live-dot-wrapper",
  html: '<div class="live-dot"></div>',
  iconSize: [16, 16],
  iconAnchor: [8, 8],
});

let trackPolyline = null;
let liveMarker = null;
let pastLayers = [];
let detailTrack = null;       // tracé surligné dans la vue détail
let inDetailView = false;

// --- État du suivi GPS ---
let watchId = null;
let tracking = false;
let points = [];
let totalDistance = 0;
let startTime = null;
let durationTimer = null;

// --- État des rues de Paris ---
// Une "rue" = un nom OSM unique dans Paris, avec 1..N segments de géométrie.
let streets = []; // [{id, name, segments, samples, layer, covered: Set<int>}]
const streetGrid = new Map(); // "x,y" -> [streetIdx]
let doneStreetIds = new Set(loadDoneStreets());
const activeStreets = new Set(); // indices de rues "en cours d'exploration"

// --- Helpers géo ---
function haversine(a, b) {
  const R = 6371000;
  const toRad = (x) => (x * Math.PI) / 180;
  const dLat = toRad(b.lat - a.lat);
  const dLng = toRad(b.lng - a.lng);
  const lat1 = toRad(a.lat);
  const lat2 = toRad(b.lat);
  const h = Math.sin(dLat / 2) ** 2 + Math.cos(lat1) * Math.cos(lat2) * Math.sin(dLng / 2) ** 2;
  return 2 * R * Math.asin(Math.sqrt(h));
}

function cellKey(lat, lng) {
  return `${Math.floor(lat / GRID_LAT)},${Math.floor(lng / GRID_LNG)}`;
}

// --- Helpers format ---
function formatDistance(m) { return (m / 1000).toFixed(2).replace(".", ","); }

function formatDuration(ms) {
  const total = Math.floor(ms / 1000);
  const h = Math.floor(total / 3600);
  const m = Math.floor((total % 3600) / 60);
  const s = total % 60;
  const pad = (n) => String(n).padStart(2, "0");
  return h > 0 ? `${h}:${pad(m)}:${pad(s)}` : `${pad(m)}:${pad(s)}`;
}

function formatPace(distanceM, durationMs) {
  if (!distanceM || !durationMs) return "—";
  const kmh = distanceM / 1000 / (durationMs / 3600000);
  if (!isFinite(kmh) || kmh <= 0) return "—";
  return kmh.toFixed(1).replace(".", ",");
}

function formatDateLabel(ts) {
  const d = new Date(ts);
  return d.toLocaleDateString("fr-FR", {
    weekday: "long", day: "numeric", month: "long",
    hour: "2-digit", minute: "2-digit",
  });
}

// Date relative et lisible pour l'historique : "Aujourd'hui à 14h32",
// "Hier à 09h15", "Lundi à 18h00", ou "12 mars à 10h30" si plus ancien.
function formatRelativeDate(ts) {
  const d = new Date(ts);
  const now = new Date();
  const time = d.toLocaleTimeString("fr-FR", { hour: "2-digit", minute: "2-digit" }).replace(":", "h");

  const startOfDay = (x) => new Date(x.getFullYear(), x.getMonth(), x.getDate());
  const todayStart = startOfDay(now);
  const dStart = startOfDay(d);
  const dayDiff = Math.round((todayStart - dStart) / 86400000);

  if (dayDiff === 0)  return `Aujourd'hui à ${time}`;
  if (dayDiff === 1)  return `Hier à ${time}`;
  if (dayDiff < 7)    return `${d.toLocaleDateString("fr-FR", { weekday: "long" })} à ${time}`;
  return `${d.toLocaleDateString("fr-FR", { day: "numeric", month: "short" })} à ${time}`;
}

function setStatus(text, tone = "") {
  statusEl.textContent = text;
  if (tone) statusEl.dataset.tone = tone;
  else delete statusEl.dataset.tone;
}

function updateStats() {
  distanceEl.innerHTML = `${formatDistance(totalDistance)} <small>km</small>`;
  const dur = startTime ? Date.now() - startTime : 0;
  durationEl.textContent = formatDuration(dur);
  paceEl.innerHTML = `${formatPace(totalDistance, dur)} <small>km/h</small>`;
  // La progression intègre la balade en cours → mise à jour en direct.
  if (tracking) updateProgress();
}

function resetLiveStats() {
  totalDistance = 0;
  points = [];
  startTime = null;
  distanceEl.innerHTML = `0,00 <small>km</small>`;
  durationEl.textContent = "00:00";
  paceEl.innerHTML = `— <small>km/h</small>`;
}

// --- Historique des balades ---
function loadHistory() {
  try {
    const raw = localStorage.getItem(STORAGE_KEY);
    return raw ? JSON.parse(raw) : [];
  } catch { return []; }
}
function saveHistory(walks) {
  localStorage.setItem(STORAGE_KEY, JSON.stringify(walks));
}

function escapeHtml(s) {
  return String(s).replace(/[&<>"']/g, (c) =>
    ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c])
  );
}

function renderHistory() {
  const walks = loadHistory().sort((a, b) => b.startTime - a.startTime);
  pastLayers.forEach((l) => map.removeLayer(l));
  pastLayers = [];
  walks.forEach((w) => {
    if (w.points && w.points.length > 1) {
      const line = L.polyline(
        w.points.map((p) => [p.lat, p.lng]),
        { color: "#e85a4f", weight: 3, opacity: 0.9, lineCap: "round", lineJoin: "round" }
      ).addTo(map);
      pastLayers.push(line);
    }
  });
  historyCount.textContent = `${walks.length} balade${walks.length > 1 ? "s" : ""}`;
  if (walks.length === 0) {
    historyList.innerHTML = `<li class="history-empty">Aucune balade enregistrée pour l'instant.</li>`;
    return;
  }
  historyList.innerHTML = walks.slice(0, 10).map((w) => {
    const kcal = estimateCalories(w.distance, w.duration);
    const pace = formatPace(w.distance, w.duration);
    return `
    <li>
      <button type="button" class="history-item" data-id="${escapeHtml(w.id)}">
        <div class="history-item-top">
          <span class="history-item-date">${escapeHtml(formatRelativeDate(w.startTime))}</span>
          <span class="history-item-distance">${formatDistance(w.distance)}<small> km</small></span>
        </div>
        <div class="history-item-bottom">
          <span class="history-item-stat">
            <span class="history-stat-icon" aria-hidden="true">⏱</span>
            ${formatDuration(w.duration)}
          </span>
          <span class="history-item-stat">
            <span class="history-stat-icon" aria-hidden="true">⚡</span>
            ${pace}<small> km/h</small>
          </span>
          <span class="history-item-stat">
            <span class="history-stat-icon" aria-hidden="true">🔥</span>
            ${kcal}<small> kcal</small>
          </span>
          <span class="history-item-chevron" aria-hidden="true">›</span>
        </div>
      </button>
    </li>`;
  }).join("");

  historyList.querySelectorAll(".history-item").forEach((btn) => {
    btn.addEventListener("click", () => {
      const id = btn.dataset.id;
      const walk = loadHistory().find((w) => String(w.id) === id);
      if (walk) showWalkDetail(walk);
    });
  });
}

// --- Estimation des calories (formule MET × poids × heures) ---
function estimateCalories(distanceM, durationMs, weightKg = DEFAULT_WEIGHT_KG) {
  if (distanceM <= 0 || durationMs <= 0) return 0;
  const hours = durationMs / 3600000;
  const speedKmh = (distanceM / 1000) / hours;
  let met;
  if (speedKmh < 3.2)      met = 2.0;
  else if (speedKmh < 4.8) met = 3.0;
  else if (speedKmh < 6.4) met = 3.8;
  else if (speedKmh < 8)   met = 5.0;
  else                     met = 7.0;
  return Math.round(met * weightKg * hours);
}

// --- Rues "faites" : persistance ---
function loadDoneStreets() {
  try {
    const raw = localStorage.getItem(DONE_STREETS_KEY);
    return raw ? new Set(JSON.parse(raw)) : new Set();
  } catch { return new Set(); }
}
function saveDoneStreets() {
  try { localStorage.setItem(DONE_STREETS_KEY, JSON.stringify([...doneStreetIds])); }
  catch (e) { console.warn("Sauvegarde des rues faites impossible", e); }
}

// --- Mini cache IndexedDB (localStorage trop petit pour ~3 MB) ---
const IDB_NAME = "paris-walks-db";
const IDB_STORE = "cache";

function idbOpen() {
  return new Promise((resolve, reject) => {
    const req = indexedDB.open(IDB_NAME, 1);
    req.onupgradeneeded = () => req.result.createObjectStore(IDB_STORE);
    req.onsuccess = () => resolve(req.result);
    req.onerror = () => reject(req.error);
  });
}
function idbGet(key) {
  return idbOpen().then((db) => new Promise((resolve, reject) => {
    const tx = db.transaction(IDB_STORE, "readonly");
    const req = tx.objectStore(IDB_STORE).get(key);
    req.onsuccess = () => resolve(req.result);
    req.onerror = () => reject(req.error);
  })).catch(() => null);
}
function idbSet(key, value) {
  return idbOpen().then((db) => new Promise((resolve, reject) => {
    const tx = db.transaction(IDB_STORE, "readwrite");
    tx.objectStore(IDB_STORE).put(value, key);
    tx.oncomplete = () => resolve();
    tx.onerror = () => reject(tx.error);
  })).catch((e) => console.warn("Cache IndexedDB indisponible", e));
}

// --- Téléchargement des rues via Overpass (cache IndexedDB) ---
async function fetchStreetsData() {
  const cached = await idbGet(STREETS_CACHE_KEY);
  if (cached && Array.isArray(cached) && cached.length > 0) {
    console.log(`[streets] cache hit: ${cached.length} rues`);
    return cached;
  }

  console.log("[streets] téléchargement Overpass…");
  const t0 = performance.now();
  const { south, west, north, east } = PARIS_BBOX;
  const query = `[out:json][timeout:60];
    way["highway"~"^(primary|secondary|tertiary|residential|unclassified|living_street|pedestrian)$"]["name"](${south},${west},${north},${east});
    out geom;`;

  const resp = await fetch("https://overpass-api.de/api/interpreter", {
    method: "POST",
    body: "data=" + encodeURIComponent(query),
  });
  if (!resp.ok) throw new Error(`Overpass HTTP ${resp.status}`);
  const data = await resp.json();
  console.log(`[streets] Overpass ${(performance.now() - t0).toFixed(0)} ms, ${data.elements.length} ways`);

  // Regroupe par nom et compresse : { n: nom, s: [segment1, segment2, ...] }
  // Chaque segment est une liste de [lat, lng] arrondis à ~1 m.
  const byName = new Map();
  for (const e of data.elements) {
    if (e.type !== "way" || !e.geometry || e.geometry.length < 2) continue;
    const name = e.tags?.name;
    if (!name) continue;
    const seg = e.geometry.map((p) => [
      Math.round(p.lat * 1e5) / 1e5,
      Math.round(p.lon * 1e5) / 1e5,
    ]);
    let s = byName.get(name);
    if (!s) { s = { n: name, s: [] }; byName.set(name, s); }
    s.s.push(seg);
  }
  const slim = [...byName.values()];
  console.log(`[streets] ${slim.length} rues uniques après regroupement`);

  await idbSet(STREETS_CACHE_KEY, slim);
  return slim;
}

// --- Frontière de Paris (commune) via Overpass + cache IndexedDB ---
// Une relation OSM "outer" est constituée de plusieurs ways qu'il faut
// recoudre bout-à-bout pour former un anneau fermé.
function stitchRelationOuter(relation) {
  let ways = (relation.members || [])
    .filter((m) => m.type === "way" && m.role === "outer" && Array.isArray(m.geometry))
    .map((m) => m.geometry.map((p) => [p.lat, p.lon]));
  if (ways.length === 0) return null;

  const eq = (a, b) => Math.abs(a[0] - b[0]) < 1e-9 && Math.abs(a[1] - b[1]) < 1e-9;
  const ring = ways.shift().slice();

  while (ways.length > 0) {
    const last = ring[ring.length - 1];
    let foundIdx = -1;
    let reverse = false;
    for (let i = 0; i < ways.length; i++) {
      const w = ways[i];
      if (eq(w[0], last)) { foundIdx = i; break; }
      if (eq(w[w.length - 1], last)) { foundIdx = i; reverse = true; break; }
    }
    if (foundIdx === -1) break;
    let next = ways.splice(foundIdx, 1)[0];
    if (reverse) next = next.slice().reverse();
    for (let i = 1; i < next.length; i++) ring.push(next[i]);
  }
  return ring;
}

async function fetchParisBoundary() {
  const cached = await idbGet(PARIS_BOUNDARY_KEY);
  if (cached && Array.isArray(cached) && cached.length > 10) {
    console.log(`[boundary] cache hit: ${cached.length} points`);
    return cached;
  }
  console.log("[boundary] téléchargement Overpass…");
  // admin_level=8 = commune Paris (limites de la ville, ~ périphérique + bois)
  const query = `[out:json];relation["name"="Paris"]["boundary"="administrative"]["admin_level"="8"];out geom;`;
  const resp = await fetch("https://overpass-api.de/api/interpreter", {
    method: "POST",
    body: "data=" + encodeURIComponent(query),
  });
  if (!resp.ok) throw new Error(`Overpass HTTP ${resp.status}`);
  const data = await resp.json();
  const rel = data.elements.find((e) => e.type === "relation");
  if (!rel) throw new Error("Relation Paris introuvable");
  const ring = stitchRelationOuter(rel);
  if (!ring || ring.length < 10) throw new Error("Frontière Paris incomplète");
  console.log(`[boundary] ${ring.length} points après stitch`);
  await idbSet(PARIS_BOUNDARY_KEY, ring);
  return ring;
}

// Pose le masque sombre (donut : bbox monde – anneau Paris) et verrouille la
// navigation aux limites de Paris.
function applyParisBoundary(ring) {
  // Pane dédié au-dessus du pane "overlay" (rues), sous les marqueurs.
  if (!map.getPane("mask")) {
    map.createPane("mask");
    const p = map.getPane("mask");
    p.style.zIndex = 450;
    p.style.pointerEvents = "none";
  }
  // Bbox monde (en LatLng) — l'anneau Paris est un trou dans la polygone.
  const worldRing = [[-85, -180], [-85, 180], [85, 180], [85, -180]];
  parisMaskLayer = L.polygon([worldRing, ring], {
    stroke: false,
    fillColor: "#000000",
    fillOpacity: 1,
    interactive: false,
    pane: "mask",
    renderer: L.svg({ pane: "mask" }),
  }).addTo(map);

  const bounds = L.latLngBounds(ring);
  map.setMaxBounds(bounds);
  if (!inDetailView) map.fitBounds(bounds, { animate: false });
}

// --- Vue détail d'une balade ---
function showWalkDetail(walk) {
  if (tracking) {
    setStatus("Arrêtez la balade en cours pour consulter l'historique.", "error");
    return;
  }
  inDetailView = true;
  mainOnlyEls.forEach((el) => (el.hidden = true));
  detailOnlyEls.forEach((el) => (el.hidden = false));

  // Discrétise les autres tracés passés (les rend invisibles le temps du détail)
  pastLayers.forEach((l) => l.setStyle({ opacity: 0 }));

  // Tracé surligné de la balade sélectionnée
  const latlngs = (walk.points || []).map((p) => [p.lat, p.lng]);
  if (detailTrack) { map.removeLayer(detailTrack); detailTrack = null; }
  if (latlngs.length > 1) {
    detailTrack = L.polyline(latlngs, {
      color: "#e85a4f", weight: 5, opacity: 0.95,
      lineCap: "round", lineJoin: "round",
    }).addTo(map);
    map.fitBounds(detailTrack.getBounds(), { padding: [40, 40], maxZoom: 17 });
  }

  // Remplit les libellés
  detailTitleEl.textContent = `Balade du ${formatDateLabel(walk.startTime)}`;
  detailSubtitleEl.textContent = `${(walk.points || []).length} points GPS enregistrés`;
  detailDistanceEl.innerHTML = `${formatDistance(walk.distance)} <small>km</small>`;
  detailDurationEl.textContent = formatDuration(walk.duration);
  const kcal = estimateCalories(walk.distance, walk.duration);
  detailCaloriesEl.innerHTML = `${kcal} <small>kcal</small>`;

  // Recalcule le layout après changement d'affichage
  setTimeout(() => map.invalidateSize(), 50);
}

function showMainView() {
  inDetailView = false;
  detailOnlyEls.forEach((el) => (el.hidden = true));
  mainOnlyEls.forEach((el) => (el.hidden = false));
  if (detailTrack) { map.removeLayer(detailTrack); detailTrack = null; }
  pastLayers.forEach((l) => l.setStyle({ opacity: 0.9 }));
  // Recadre sur Paris
  if (parisMaskLayer) {
    map.fitBounds(map.options.maxBounds || PARIS_FALLBACK_BOUNDS, { animate: false });
  } else {
    map.setView(PARIS_CENTER, 13);
  }
  setTimeout(() => map.invalidateSize(), 50);
}

backBtn.addEventListener("click", showMainView);

// --- Construction des échantillons d'une rue (sur tous ses segments) ---
function makeSamplesForSegments(segments) {
  const samples = [];
  let total = 0;
  for (const seg of segments) {
    for (let i = 1; i < seg.length; i++) {
      const [aLat, aLng] = seg[i - 1];
      const [bLat, bLng] = seg[i];
      const segLen = haversine({ lat: aLat, lng: aLng }, { lat: bLat, lng: bLng });
      const steps = Math.max(1, Math.ceil(segLen / SAMPLE_INTERVAL_M));
      for (let s = 0; s < steps; s++) {
        const t = s / steps;
        samples.push([aLat + (bLat - aLat) * t, aLng + (bLng - aLng) * t]);
      }
      total += segLen;
    }
    samples.push(seg[seg.length - 1]);
  }
  return { samples, length: total };
}

// --- Index spatial : pour chaque cellule, la liste des rues présentes ---
function buildStreetIndex() {
  streetGrid.clear();
  streets.forEach((s, idx) => {
    const seen = new Set();
    for (const [lat, lng] of s.samples) {
      const k = cellKey(lat, lng);
      if (seen.has(k)) continue;
      seen.add(k);
      let arr = streetGrid.get(k);
      if (!arr) { arr = []; streetGrid.set(k, arr); }
      arr.push(idx);
    }
  });
}

// --- Dessin de toutes les rues sur la carte (1 layer multi-segments par rue) ---
// Style épuré : rues à faire en blanc fin et discret, rues parcourues en
// corail vif et plus épais — elles "s'illuminent" sur le fond noir.
const STREET_TODO = { color: "#ffffff", weight: 1, opacity: 0.35 };
const STREET_DONE = { color: "#e85a4f", weight: 2.5, opacity: 1 };

function drawAllStreets() {
  streets.forEach((s) => {
    const isDone = doneStreetIds.has(s.id);
    s.layer = L.polyline(s.segments, {
      renderer: streetsRenderer,
      ...(isDone ? STREET_DONE : STREET_TODO),
      lineCap: "round",
      lineJoin: "round",
    }).addTo(map);
  });
}

function paintStreetDone(idx) {
  const s = streets[idx];
  if (!s.layer) return;
  s.layer.setStyle(STREET_DONE);
  s.layer.bringToFront();
}

// --- Progression globale ---
// (km parcourus dans toute l'historique + balade en cours) / 1800 km × 100
function totalKmWalked() {
  const histM = loadHistory().reduce((sum, w) => sum + (w.distance || 0), 0);
  const liveM = tracking ? totalDistance : 0;
  return (histM + liveM) / 1000;
}

function updateProgress() {
  const km = totalKmWalked();
  const pct = (km / TOTAL_PARIS_KM) * 100;
  progressPctEl.textContent = `${pct.toFixed(3).replace(".", ",")} % de Paris parcouru`;
  progressDetailEl.textContent = `${km.toFixed(2).replace(".", ",")} / ${TOTAL_PARIS_KM} km`;
  progressFillEl.style.width = `${Math.min(100, pct)}%`;
}

// --- Calcul rapide : plus proche échantillon d'une rue ---
function nearestSampleDist(point, samples) {
  let best = Infinity;
  let bestIdx = -1;
  for (let i = 0; i < samples.length; i++) {
    const d = haversine(point, { lat: samples[i][0], lng: samples[i][1] });
    if (d < best) { best = d; bestIdx = i; }
  }
  return { dist: best, idx: bestIdx };
}

// --- Mise à jour de la couverture des rues à chaque tick GPS ---
function updateStreetCoverage(gpsPoint) {
  if (streets.length === 0) return;

  // 1) Trouver les rues candidates dans les cellules voisines
  const baseX = Math.floor(gpsPoint.lat / GRID_LAT);
  const baseY = Math.floor(gpsPoint.lng / GRID_LNG);
  const candidates = new Set();
  for (let dx = -1; dx <= 1; dx++) {
    for (let dy = -1; dy <= 1; dy++) {
      const list = streetGrid.get(`${baseX + dx},${baseY + dy}`);
      if (list) for (const i of list) candidates.add(i);
    }
  }

  // 2) Pour chaque candidate non-faite : marquer le sample couvert
  //    et activer la rue si on entre dedans
  for (const idx of candidates) {
    const s = streets[idx];
    if (doneStreetIds.has(s.id)) continue;
    const { dist, idx: sampleIdx } = nearestSampleDist(gpsPoint, s.samples);
    if (dist <= HIT_RADIUS_M) {
      s.covered.add(sampleIdx);
      activeStreets.add(idx);
    }
  }

  // 3) Pour chaque rue active : si on en est sorti, on évalue
  for (const idx of [...activeStreets]) {
    const s = streets[idx];
    if (doneStreetIds.has(s.id)) { activeStreets.delete(idx); continue; }
    const { dist } = nearestSampleDist(gpsPoint, s.samples);
    if (dist > EXIT_DISTANCE_M) {
      const ratio = s.covered.size / s.samples.length;
      if (ratio >= COVERAGE_THRESHOLD) {
        doneStreetIds.add(s.id);
        paintStreetDone(idx);
        saveDoneStreets();
        updateProgress();
      } else {
        // Sortie sans validation : on remet à zéro pour cette session
        s.covered.clear();
      }
      activeStreets.delete(idx);
    }
  }
}

// Évalue les rues encore actives quand on arrête la balade
function finalizeActiveStreets() {
  for (const idx of activeStreets) {
    const s = streets[idx];
    if (doneStreetIds.has(s.id)) continue;
    const ratio = s.covered.size / s.samples.length;
    if (ratio >= COVERAGE_THRESHOLD) {
      doneStreetIds.add(s.id);
      paintStreetDone(idx);
    }
    s.covered.clear();
  }
  activeStreets.clear();
  saveDoneStreets();
  updateProgress();
}

// --- Autosave de la balade en cours (anti-perte de données) ---
let autosaveTimer = null;

function snapshotCurrentWalk() {
  if (!startTime || points.length === 0) return null;
  return {
    id: String(startTime),
    startTime,
    duration: Date.now() - startTime,
    distance: totalDistance,
    points,
    autosavedAt: Date.now(),
  };
}

function autosaveCurrentWalk() {
  const snap = snapshotCurrentWalk();
  if (!snap) return;
  try {
    localStorage.setItem(CURRENT_WALK_KEY, JSON.stringify(snap));
    console.log(`[autosave] balade en cours sauvegardée (${snap.points.length} pts, ${(snap.distance / 1000).toFixed(2)} km)`);
  } catch (e) {
    console.warn("Autosave impossible", e);
  }
}

function clearCurrentWalk() {
  try { localStorage.removeItem(CURRENT_WALK_KEY); } catch {}
}

// Au démarrage : si une balade était en cours (crash, fermeture brutale),
// on la finalise dans l'historique pour ne rien perdre.
function recoverInterruptedWalk() {
  let raw;
  try { raw = localStorage.getItem(CURRENT_WALK_KEY); } catch { return; }
  if (!raw) return;
  let walk;
  try { walk = JSON.parse(raw); } catch { clearCurrentWalk(); return; }
  if (!walk || !walk.points || walk.points.length < 2 || (walk.distance || 0) <= 5) {
    clearCurrentWalk();
    return;
  }
  const walks = loadHistory();
  // Évite les doublons si la balade a déjà été sauvegardée proprement.
  if (!walks.some((w) => w.id === walk.id)) {
    walks.push({
      id: walk.id,
      startTime: walk.startTime,
      duration: walk.duration,
      distance: walk.distance,
      points: walk.points,
    });
    saveHistory(walks);
    console.log(`[recover] balade interrompue récupérée : ${(walk.distance / 1000).toFixed(2)} km`);
  }
  clearCurrentWalk();
}

// --- Snap-to-road via OSRM (router.project-osrm.org) ---
// On utilise DEUX endpoints OSRM :
//   1) /nearest/ : projette chaque point GPS sur la rue la plus proche.
//   2) /route/   : calcule l'itinéraire piéton entre deux points GPS consécutifs.
//      C'est cet endpoint qui fait que le tracé suit *réellement* les rues
//      (l'endpoint /nearest/ ne donne que la projection ponctuelle ; la ligne
//      entre deux projections coupe encore en diagonale entre les rues).
const OSRM_NEAREST_URL = "https://router.project-osrm.org/nearest/v1/foot";
const OSRM_ROUTE_URL   = "https://router.project-osrm.org/route/v1/foot";
const SNAP_MAX_DISTANCE_M = 50;
const SNAP_MIN_MOVE_M     = 3;
const SNAP_REQUEST_TIMEOUT_MS = 5000;

async function snapToRoad(lat, lng) {
  const url = `${OSRM_NEAREST_URL}/${lng},${lat}?number=1`;
  const ctrl = new AbortController();
  const t = setTimeout(() => ctrl.abort(), SNAP_REQUEST_TIMEOUT_MS);
  try {
    const resp = await fetch(url, { signal: ctrl.signal });
    if (!resp.ok) return null;
    const data = await resp.json();
    const wp = data.waypoints?.[0];
    if (!wp || !Array.isArray(wp.location)) return null;
    const [snapLng, snapLat] = wp.location;
    const dist = haversine({ lat, lng }, { lat: snapLat, lng: snapLng });
    if (dist > SNAP_MAX_DISTANCE_M) return null;
    return { lat: snapLat, lng: snapLng, dist };
  } catch {
    return null;
  } finally {
    clearTimeout(t);
  }
}

async function routeBetween(a, b) {
  const url = `${OSRM_ROUTE_URL}/${a.lng},${a.lat};${b.lng},${b.lat}?geometries=geojson&overview=full`;
  const ctrl = new AbortController();
  const t = setTimeout(() => ctrl.abort(), SNAP_REQUEST_TIMEOUT_MS);
  try {
    const resp = await fetch(url, { signal: ctrl.signal });
    if (!resp.ok) return null;
    const data = await resp.json();
    const route = data.routes?.[0];
    if (!route || !route.geometry || !Array.isArray(route.geometry.coordinates)) return null;
    const coords = route.geometry.coordinates.map(([lng, lat]) => [lat, lng]);
    return { coords, distance: route.distance };
  } catch {
    return null;
  } finally {
    clearTimeout(t);
  }
}

let snapChain = Promise.resolve();
let lastSnappedGps = null;

function onPosition(pos) {
  const { latitude, longitude, accuracy } = pos.coords;

  if (accuracy && accuracy > 100) {
    setStatus(`Signal GPS faible (±${Math.round(accuracy)} m)…`, "");
  } else {
    setStatus("Suivi actif — bonne balade !", "active");
  }

  // Marqueur live = position GPS réelle (immédiat, sans attendre OSRM).
  if (!liveMarker) {
    liveMarker = L.marker([latitude, longitude], { icon: liveIcon }).addTo(map);
  } else {
    liveMarker.setLatLng([latitude, longitude]);
  }
  map.panTo([latitude, longitude], { animate: true, duration: 0.4 });

  snapChain = snapChain
    .then(async () => {
      const t0 = performance.now();
      const snapped = await snapToRoad(latitude, longitude);
      const target = snapped
        ? { lat: snapped.lat, lng: snapped.lng }
        : { lat: latitude, lng: longitude };

      if (snapped) {
        console.log(
          `[snap] GPS (${latitude.toFixed(5)}, ${longitude.toFixed(5)}) ` +
          `→ rue (${snapped.lat.toFixed(5)}, ${snapped.lng.toFixed(5)}) ` +
          `Δ=${snapped.dist.toFixed(1)} m en ${(performance.now() - t0).toFixed(0)} ms`
        );
      } else {
        console.warn(
          `[snap] échec pour (${latitude.toFixed(5)}, ${longitude.toFixed(5)}) — point GPS brut conservé`
        );
      }

      if (!lastSnappedGps) {
        // 1er point : on initialise le tracé sur la projection.
        points = [{ lat: target.lat, lng: target.lng }];
        lastSnappedGps = target;
        map.setView([target.lat, target.lng], 16);
      } else {
        const moveDist = haversine(lastSnappedGps, target);
        if (moveDist < SNAP_MIN_MOVE_M) return; // sur place

        // /route/ entre les deux points : c'est ÇA qui fait que le tracé
        // épouse les rues, pas un segment droit.
        const t1 = performance.now();
        const route = await routeBetween(lastSnappedGps, target);
        if (route && route.coords.length >= 2) {
          for (let i = 1; i < route.coords.length; i++) {
            const [lat, lng] = route.coords[i];
            points.push({ lat, lng });
          }
          totalDistance += route.distance;
          console.log(
            `[route] ${lastSnappedGps.lat.toFixed(5)},${lastSnappedGps.lng.toFixed(5)} → ` +
            `${target.lat.toFixed(5)},${target.lng.toFixed(5)} : ` +
            `${route.coords.length} pts, +${route.distance.toFixed(0)} m ` +
            `en ${(performance.now() - t1).toFixed(0)} ms`
          );
        } else {
          // Fallback : segment droit
          points.push({ lat: target.lat, lng: target.lng });
          totalDistance += moveDist;
          console.warn(`[route] échec → segment droit, +${moveDist.toFixed(0)} m`);
        }
        lastSnappedGps = target;
      }

      const latlngs = points.map((p) => [p.lat, p.lng]);
      if (!trackPolyline) {
        trackPolyline = L.polyline(latlngs, {
          color: "#e85a4f", weight: 5, opacity: 0.9,
          lineCap: "round", lineJoin: "round",
        }).addTo(map);
      } else {
        trackPolyline.setLatLngs(latlngs);
      }

      updateStats();
      // Couverture des rues : on n'utilise que les points GPS snappés
      // (les vertices intermédiaires du routage ne représentent pas où on est passé).
      updateStreetCoverage(target);
    })
    .catch((err) => console.warn("[snap] erreur dans la chaîne :", err));
}

function onPositionError(err) {
  let msg = "Impossible d'obtenir votre position.";
  if (err.code === 1) msg = "Autorisation GPS refusée.";
  else if (err.code === 2) msg = "Position indisponible.";
  else if (err.code === 3) msg = "Signal GPS trop lent.";
  setStatus(msg, "error");
}

function startTracking() {
  if (!("geolocation" in navigator)) {
    setStatus("Géolocalisation non supportée par ce navigateur.", "error");
    return;
  }
  resetLiveStats();
  if (trackPolyline) { map.removeLayer(trackPolyline); trackPolyline = null; }
  if (liveMarker) { map.removeLayer(liveMarker); liveMarker = null; }
  activeStreets.clear();
  for (const s of streets) s.covered.clear();
  snapChain = Promise.resolve(); // Repart sur une chaîne propre
  lastSnappedGps = null;          // Aucune origine de routage encore

  startTime = Date.now();
  tracking = true;
  requestWakeLock();
  toggleBtn.dataset.state = "active";
  btnLabel.textContent = "Arrêter la balade";
  setStatus("Recherche du signal GPS…", "");
  durationTimer = setInterval(updateStats, 1000);
  // Autosave toutes les 30 s pour ne rien perdre en cas de crash / fermeture
  autosaveTimer = setInterval(autosaveCurrentWalk, AUTOSAVE_INTERVAL_MS);

  watchId = navigator.geolocation.watchPosition(onPosition, onPositionError, {
    enableHighAccuracy: true, maximumAge: 1000, timeout: 15000,
  });
}

function stopTracking() {
  tracking = false;
  releaseWakeLock();
  if (watchId !== null) { navigator.geolocation.clearWatch(watchId); watchId = null; }
  if (durationTimer) { clearInterval(durationTimer); durationTimer = null; }
  if (autosaveTimer) { clearInterval(autosaveTimer); autosaveTimer = null; }

  toggleBtn.dataset.state = "";
  btnLabel.textContent = "Démarrer la balade";

  // Évalue une dernière fois les rues touchées sans en être sorti
  finalizeActiveStreets();

  if (points.length > 1 && totalDistance > 5) {
    const walk = {
      id: String(startTime),
      startTime,
      duration: Date.now() - startTime,
      distance: totalDistance,
      points,
    };
    const walks = loadHistory();
    walks.push(walk);
    saveHistory(walks);
    setStatus(`Bravo ! ${formatDistance(totalDistance)} km parcourus.`, "active");
    renderHistory();
    updateProgress();
  } else {
    setStatus("Balade trop courte pour être sauvegardée.", "");
  }
  // Balade finalisée (ou écartée) : on nettoie l'autosave.
  clearCurrentWalk();
}

toggleBtn.addEventListener("click", () => {
  if (tracking) stopTracking();
  else startTracking();
});

// --- Initialisation : balades passées + rues de Paris ---
// 1) On récupère d'abord une éventuelle balade interrompue (crash, fermeture
//    brutale) pour ne perdre aucun point GPS.
recoverInterruptedWalk();
renderHistory();
updateProgress();

// Filet de sécurité : si l'utilisateur ferme l'onglet en plein suivi,
// on force une dernière sauvegarde immédiate.
window.addEventListener("pagehide", () => { if (tracking) autosaveCurrentWalk(); });
window.addEventListener("beforeunload", () => { if (tracking) autosaveCurrentWalk(); });

// Frontière Paris : charge en parallèle des rues, masque dès que prête.
(async function initBoundary() {
  try {
    const ring = await fetchParisBoundary();
    applyParisBoundary(ring);
  } catch (err) {
    console.warn("Frontière Paris indisponible — verrouillage par bbox uniquement.", err);
  }
})();

(async function initStreets() {
  progressDetailEl.textContent = "Chargement des rues de Paris…";
  setStatus("Chargement de la carte des rues…", "");
  try {
    const data = await fetchStreetsData();
    streets = data.map((d) => {
      const { samples, length } = makeSamplesForSegments(d.s);
      return {
        id: d.n,                    // une rue = un nom unique
        name: d.n,
        segments: d.s,
        samples,
        length,
        covered: new Set(),
        layer: null,
      };
    });
    const t1 = performance.now();
    buildStreetIndex();
    console.log(`[streets] index spatial construit en ${(performance.now() - t1).toFixed(0)} ms (${streetGrid.size} cellules)`);
    const t2 = performance.now();
    drawAllStreets();
    console.log(`[streets] ${streets.length} rues dessinées en ${(performance.now() - t2).toFixed(0)} ms`);
    // Le masque doit rester au-dessus des rues pour assombrir l'extérieur.
    if (parisMaskLayer) parisMaskLayer.bringToFront();
    updateProgress();
    const loadingScreen = document.getElementById("loading-screen");
    if (loadingScreen) {
      loadingScreen.classList.add("hidden");
      setTimeout(() => loadingScreen.remove(), 500);
    }
    setStatus("Appuyez pour commencer le suivi GPS.", "");
  } catch (err) {
    console.error(err);
    progressDetailEl.textContent = "Échec du chargement";
    setStatus("Impossible de charger les rues de Paris (réessayez plus tard).", "error");
  }
})();
// --- Wake Lock ---
let wakeLock = null;

async function requestWakeLock() {
  if ('wakeLock' in navigator) {
    try {
      wakeLock = await navigator.wakeLock.request('screen');
    } catch (err) {
      setStatus("Conseil : désactivez la mise en veille dans Réglages → Affichage pour éviter les coupures GPS.", "");
    }
  }
}

async function releaseWakeLock() {
  if (wakeLock) {
    await wakeLock.release();
    wakeLock = null;
  }
}

