// api/relay.js — Relais CORS durci pour l'outil DVF / DPE / BDNB / RNIC / OSM
module.exports = async (req, res) => {
  res.setHeader('Access-Control-Allow-Origin', '*');
  res.setHeader('Access-Control-Allow-Methods', 'GET, OPTIONS');
  res.setHeader('X-MDB-Relay', '1');
  if (req.method === 'OPTIONS') { res.status(204).end(); return; }
  if (req.method !== 'GET') { res.status(405).json({ error: 'Méthode non autorisée' }); return; }

  const target = req.query.url;
  if (!target || Array.isArray(target)) { res.status(400).json({ error: 'Paramètre url manquant ou invalide' }); return; }

  const ALLOWED = [
    'api.cquest.org',
    'files.data.gouv.fr',
    'apicarto.ign.fr',
    'api-adresse.data.gouv.fr',
    'data.geopf.fr',
    'data.ademe.fr',
    'api.bdnb.io',
    'www.data.gouv.fr',
    'tabular-api.data.gouv.fr',
    'overpass-api.de'
  ];

  let parsed;
  try { parsed = new URL(target); }
  catch { res.status(400).json({ error: 'URL invalide' }); return; }
  if (!['https:', 'http:'].includes(parsed.protocol)) { res.status(400).json({ error: 'Protocole non autorisé' }); return; }
  const host = parsed.hostname.toLowerCase();
  if (!ALLOWED.some(d => host === d || host.endsWith('.' + d))) {
    res.status(403).json({ error: 'Domaine non autorisé : ' + host });
    return;
  }

  const ctl = new AbortController();
  const timer = setTimeout(() => ctl.abort(), 15000);
  try {
    const upstream = await fetch(target, {
      signal: ctl.signal,
      headers: { 'User-Agent': 'MDB-DVF/1.1 (+demereenfils.fr)' }
    });
    const body = await upstream.text();
    res.setHeader('Content-Type', upstream.headers.get('content-type') || 'text/plain; charset=utf-8');
    if (upstream.ok) res.setHeader('Cache-Control', 's-maxage=3600, stale-while-revalidate=86400');
    else res.setHeader('Cache-Control', 'no-store');
    res.status(upstream.status).send(body);
  } catch (e) {
    res.setHeader('Cache-Control', 'no-store');
    const timeout = e && e.name === 'AbortError';
    res.status(timeout ? 504 : 502).json({ error: timeout ? 'Relais expiré (15 s)' : 'Relais en échec : ' + e.message });
  } finally {
    clearTimeout(timer);
  }
};
