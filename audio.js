// Procedural ambient soundscape (Web Audio, no samples): a faint breeze, bamboo rustle, spout drips,
// water stirred by the cursor, koi swirling, gritty sand under the tools, wind chime, birds, crickets at dusk.
export function createAudio() {
  let ctx = null, master, fx, analyser, white, brown;
  let wind, rustle, stir, stirLow, cricketBus, sandBus;
  // real recordings of water (see sounds/CREDITS.md): hand swirls + light ripples cut from a longer take
  const SWIRL_FILES = ['swirl_398700.mp3', 'swirl_398702.mp3', 'swirl_398713.mp3', 'swirl_398722.mp3'];
  const smp = { swirls: [], drops: [] };
  // sand under the tools: short overlapping pieces of a recording (or of soft noise) that follow each stroke.
  // Every quality of it is a number in SP so it can be tuned by ear from the page (the "Tune sand sound" panel).
  const SAND_SRC = { salt: 'sand_salt.mp3', friction: 'sand_friction.mp3', movement: 'sand_movement.mp3', drawing: 'sand_drawing.mp3' };
  // the default is what the user settled on by ear (2026-10-10): a soft, thin, even hiss that stops with the hand
  const SAND_DEFAULT = { src: 'noise', vol: 0.2, bright: 3774, low: 3000, pitch: 2.2, smooth: 1.4, vary: 0.56, follow: 1, tail: 0.03 };
  const SAND_RANGE = { vol: [0, 1], bright: [500, 12000], low: [40, 6000], pitch: [0.5, 2.2], smooth: [0.04, 2.5], vary: [0, 1], follow: [0, 1], tail: [0.01, 0.8] };
  const SP = { ...SAND_DEFAULT };
  const sandBufs = {};
  let sandIn, sandStroke, sHP, sLP1, sLP2, nextGrain = 0, puffUntil = 0, audition = false;
  // the pond's background sounds, each of which can be switched off on its own (the "Ambient sounds" panel)
  const AMB = { wind: true, rustle: true, birds: true, chime: true, crickets: true, drop: true, koi: true, leaves: true, water: true };
  let waterBus, waterPan, waterWet, nextSwirl = 0, nextDrop = 0, lastSwirl = -1, lastSwirlT = -9, swirlNow = false;
  let on = false, rippleAcc = 0, nextTouch = 0, lastFish = 0, stirLevel = 0;
  const R = (a, b) => a + Math.random() * (b - a);
  const clampPan = p => Math.max(-1, Math.min(1, p || 0));
  const timers = { drip: R(5, 10), bird: R(2, 5), chime: R(30, 60) };

  function noiseBuffer(kind) {
    const sr = ctx.sampleRate, n = sr * 4, buf = ctx.createBuffer(2, n, sr);
    for (let ch = 0; ch < 2; ch++) {
      const d = buf.getChannelData(ch); let b = 0;
      for (let i = 0; i < n; i++) {
        const w = Math.random() * 2 - 1;
        if (kind === 'brown') { b = (b + 0.02 * w) / 1.02; d[i] = b * 3.5; } else d[i] = w;
      }
    }
    return buf;
  }
  // looping noise → filters → (pan) → gain → destination
  function layer(buf, filters, dest, withPan) {
    const src = ctx.createBufferSource(); src.buffer = buf; src.loop = true;
    let node = src; const f = [];
    for (const [type, freq, Q] of filters) {
      const bq = ctx.createBiquadFilter(); bq.type = type; bq.frequency.value = freq; bq.Q.value = Q ?? 0.7;
      node.connect(bq); node = bq; f.push(bq);
    }
    const gain = ctx.createGain(); gain.gain.value = 0;
    let pan = null;
    if (withPan) { pan = ctx.createStereoPanner(); node.connect(pan); node = pan; }
    node.connect(gain); gain.connect(dest);
    src.start(0, Math.random() * 3);
    return { gain, f, pan };
  }

  // play a recorded clip with a soft fade in and out; returns how long it will sound
  function play(buf, t, o) {
    const src = ctx.createBufferSource(), g = ctx.createGain(), rate = o.rate || 1, off = o.offset || 0;
    src.buffer = buf; src.playbackRate.value = rate;
    const dur = Math.min(o.dur ?? 1e9, (buf.duration - off) / rate), a = Math.min(o.attack ?? 0.01, dur * 0.4), r = Math.min(o.release ?? 0.3, dur * 0.5);
    g.gain.setValueAtTime(0, t); g.gain.linearRampToValueAtTime(o.gain, t + a); g.gain.setValueAtTime(o.gain, t + dur - r); g.gain.linearRampToValueAtTime(0, t + dur);
    src.connect(g);
    if (o.pan !== undefined) { const p = ctx.createStereoPanner(); p.pan.value = clampPan(o.pan); g.connect(p); p.connect(o.dest || fx); } else g.connect(o.dest || fx);
    src.start(t, off); src.stop(t + dur + 0.03);
    return dur;
  }
  const anyOf = list => list[(Math.random() * list.length) | 0];
  // the long gentle take is mostly silence with small water movements dotted through it: cut the clearest of
  // them out as separate little ripple sounds
  function sliceEvents(A) {
    const sr = A.sampleRate, d0 = A.getChannelData(0), d1 = A.numberOfChannels > 1 ? A.getChannelData(1) : d0;
    const hop = Math.floor(sr * 0.01), n = Math.floor(d0.length / hop), env = new Float32Array(n);
    for (let k = 0; k < n; k++) { let sum = 0; for (let i = k * hop, e = i + hop; i < e; i++) sum += d0[i] * d0[i]; env[k] = Math.sqrt(sum / hop); }
    const order = Array.from(env.keys()).sort((a, b) => env[b] - env[a]), picked = [];
    for (const k of order) { if (env[k] < 0.004 || picked.length >= 18) break; if (picked.every(q => Math.abs(q - k) > 90)) picked.push(k); }
    return picked.map(k => {
      const start = Math.max(0, k * hop - Math.floor(sr * 0.05)), len = Math.min(Math.floor(sr * 0.8), d0.length - start);
      const b = ctx.createBuffer(2, len, sr); let pk = 1e-4;
      for (let i = 0; i < len; i++) pk = Math.max(pk, Math.abs(d0[start + i]), Math.abs(d1[start + i]));
      const gain = 0.3 / pk, fi = sr * 0.008, fo = sr * 0.25;
      [d0, d1].forEach((src, ch) => { const out = b.getChannelData(ch); for (let i = 0; i < len; i++) out[i] = src[start + i] * gain * Math.min(1, i / fi, (len - i) / fo); });
      return b;
    });
  }
  // turn a take of someone moving sand (strokes with pauses between) into one unbroken loop: keep only the
  // parts where sand is actually moving, cross-fade them together, and cross-fade the end back into the start
  function condense(A) {
    const sr = A.sampleRate, n = A.length, c0 = A.getChannelData(0), c1 = A.numberOfChannels > 1 ? A.getChannelData(1) : c0;
    const d = new Float32Array(n); for (let i = 0; i < n; i++) d[i] = (c0[i] + c1[i]) * 0.5;
    const hop = Math.floor(sr * 0.02), nf = Math.floor(n / hop), env = new Float32Array(nf);
    for (let k = 0; k < nf; k++) { let sum = 0; for (let i = k * hop, e = i + hop; i < e; i++) sum += d[i] * d[i]; env[k] = Math.sqrt(sum / hop); }
    const thr = Array.from(env).sort((a, b) => a - b)[Math.floor(nf * 0.8)] * 0.3;
    const on = new Uint8Array(nf); for (let k = 0; k < nf; k++) if (env[k] > thr) for (let j = Math.max(0, k - 2); j <= Math.min(nf - 1, k + 2); j++) on[j] = 1;
    const segs = []; let st = -1;
    for (let k = 0; k <= nf; k++) { if (k < nf && on[k]) { if (st < 0) st = k; } else if (st >= 0) { if (k - st >= 8) segs.push([st * hop, k * hop]); st = -1; } }
    const total = segs.reduce((a, g) => a + g[1] - g[0], 0);
    if (total < sr) { segs.length = 0; segs.push([0, n]); }
    const xf = Math.floor(sr * 0.03), out = new Float32Array(segs.reduce((a, g) => a + g[1] - g[0], 0)); let pos = 0;
    for (const [a, b] of segs) {
      let i = 0;
      if (pos > 0) { pos -= xf; for (; i < xf && a + i < b; i++) out[pos + i] = out[pos + i] * (1 - i / xf) + d[a + i] * (i / xf); }
      for (; a + i < b; i++) out[pos + i] = d[a + i];
      pos += b - a;
    }
    const X = Math.floor(Math.min(sr * 0.3, pos / 4)), len = pos - X;
    for (let i = 0; i < X; i++) out[i] = out[i] * (i / X) + out[len + i] * (1 - i / X);
    let sum = 0; for (let i = 0; i < len; i++) sum += out[i] * out[i];
    const g = 0.05 / (Math.sqrt(sum / len) || 1e-4), buf = ctx.createBuffer(1, len, sr), o = buf.getChannelData(0);
    for (let i = 0; i < len; i++) o[i] = Math.max(-0.9, Math.min(0.9, out[i] * g));
    return buf;
  }
  // soft pink noise at the same level as the condensed recordings: a source with no recorded character at all
  function softNoise() {
    const sr = ctx.sampleRate, n = sr * 6, buf = ctx.createBuffer(1, n, sr), d = buf.getChannelData(0);
    let b0 = 0, b1 = 0, b2 = 0, sum = 0;
    for (let i = 0; i < n; i++) {
      const w = Math.random() * 2 - 1;
      b0 = 0.99765 * b0 + w * 0.0990460; b1 = 0.96300 * b1 + w * 0.2965164; b2 = 0.57000 * b2 + w * 1.0526913;
      d[i] = b0 + b1 + b2 + w * 0.1848; sum += d[i] * d[i];
    }
    const g = 0.05 / Math.sqrt(sum / n); for (let i = 0; i < n; i++) d[i] *= g;
    return buf;
  }
  function loadSand() {
    sandBufs.noise = softNoise();
    for (const k in SAND_SRC) (async () => {
      try {
        const r = await fetch('./sounds/' + SAND_SRC[k]); if (!r.ok) throw new Error(SAND_SRC[k] + ' → ' + r.status);
        sandBufs[k] = condense(await ctx.decodeAudioData(await r.arrayBuffer()));
      } catch (e) { console.warn('[zen audio] sand recording unavailable: ' + k, e); }
    })();
  }
  const sandBuf = () => sandBufs[SP.src] || sandBufs.noise;
  function sandFilters(t = ctx.currentTime, tc = 0.03) {
    sHP.frequency.setTargetAtTime(SP.low, t, tc); sLP1.frequency.setTargetAtTime(SP.bright, t, tc);
    sLP2.frequency.setTargetAtTime(Math.min(18000, SP.bright * 1.55), t, tc);
  }
  // one soft-edged piece of the sand source, taken from a random spot so nothing ever repeats as a loop
  function sandGrain(t, gain, dur = SP.smooth * R(0.75, 1.25), attack = dur * 0.45) {
    const buf = sandBuf(), src = ctx.createBufferSource(), g = ctx.createGain(), rate = SP.pitch * R(0.92, 1.08);
    src.buffer = buf; src.playbackRate.value = rate;
    g.gain.setValueAtTime(0, t); g.gain.linearRampToValueAtTime(gain, t + attack); g.gain.linearRampToValueAtTime(0, t + dur);
    src.connect(g); g.connect(sandIn);
    src.start(t, R(0, Math.max(0.01, buf.duration - dur * rate - 0.02))); src.stop(t + dur + 0.02);
  }
  async function loadSamples() {
    try {
      const get = async f => { const r = await fetch('./sounds/' + f); if (!r.ok) throw new Error(f + ' → ' + r.status); return ctx.decodeAudioData(await r.arrayBuffer()); };
      const rmsOf = b => { const d = b.getChannelData(0); let sum = 0; for (let i = 0; i < d.length; i++) sum += d[i] * d[i]; return Math.sqrt(sum / d.length) || 1e-4; };
      const sw = await Promise.all(SWIRL_FILES.map(get));
      smp.swirls = sw.map(b => ({ buf: b, gain: 0.016 / rmsOf(b) }));      // even out how loud each take was recorded
      smp.drops = sliceEvents(await get('water_gentle.mp3'));
    } catch (e) { console.warn('[zen audio] water recordings unavailable — falling back to synthesized water', e); }
  }

  function build() {
    ctx = new (window.AudioContext || window.webkitAudioContext)();
    ctx.onstatechange = () => { if (api.onstate) api.onstate(ctx.state); };
    master = ctx.createGain(); master.gain.value = 0;
    const comp = ctx.createDynamicsCompressor(); comp.threshold.value = -16; comp.ratio.value = 3; comp.attack.value = 0.01; comp.release.value = 0.3;
    analyser = ctx.createAnalyser(); analyser.fftSize = 2048;
    master.connect(comp); comp.connect(analyser); analyser.connect(ctx.destination);

    white = noiseBuffer('white'); brown = noiseBuffer('brown');

    // small garden reverb for the one-shot sounds
    const sr = ctx.sampleRate, n = Math.floor(sr * 2.6), ir = ctx.createBuffer(2, n, sr);
    for (let ch = 0; ch < 2; ch++) { const d = ir.getChannelData(ch); for (let i = 0; i < n; i++) d[i] = (Math.random() * 2 - 1) * Math.pow(1 - i / n, 3.2); }
    const rev = ctx.createConvolver(); rev.buffer = ir;
    const revGain = ctx.createGain(); revGain.gain.value = 0.4; rev.connect(revGain); revGain.connect(master);
    fx = ctx.createGain(); fx.connect(master); fx.connect(rev);

    wind = layer(brown, [['lowpass', 300, 0.3]], master);
    rustle = layer(white, [['highpass', 3000, 0.5], ['bandpass', 5600, 0.6]], master);
    // water being stirred: a soft mid "shh" that small speakers can reproduce, over a deep slow body
    stir = layer(white, [['lowpass', 1200, 0.4], ['highpass', 260, 0.5]], fx, true);
    stirLow = layer(brown, [['lowpass', 520, 0.4], ['highpass', 90, 0.5]], fx, true);
    // recorded water under the cursor: everything goes through one bus that opens only while the hand is moving
    waterBus = ctx.createGain(); waterBus.gain.value = 0; waterPan = ctx.createStereoPanner();
    waterBus.connect(waterPan); waterPan.connect(master);
    waterWet = ctx.createGain(); waterWet.gain.value = 0.18; waterPan.connect(waterWet); waterWet.connect(rev);
    loadSamples();
    sandBus = ctx.createStereoPanner(); sandBus.connect(master);      // dry: sand is close and has no ring to it
    // fine dry sand has no grit in it: it is one smooth, airy 'ssshh'. Any flicker or ticking reads as gravel,
    // so this is plain steady hiss, high and soft, with only a trace of body underneath.
    // recorded sand goes through a softening chain first: no rumble, and the sharp hissy top rolled off
    sandIn = ctx.createGain(); sandStroke = ctx.createGain(); sandStroke.gain.value = 0;
    sHP = ctx.createBiquadFilter(); sHP.type = 'highpass'; sHP.frequency.value = SP.low; sHP.Q.value = 0.5;
    sLP1 = ctx.createBiquadFilter(); sLP1.type = 'lowpass'; sLP1.frequency.value = SP.bright; sLP1.Q.value = 0.5;
    sLP2 = ctx.createBiquadFilter(); sLP2.type = 'lowpass'; sLP2.frequency.value = Math.min(18000, SP.bright * 1.55); sLP2.Q.value = 0.5;
    sandIn.connect(sHP); sHP.connect(sLP1); sLP1.connect(sLP2); sLP2.connect(sandStroke); sandStroke.connect(sandBus);
    loadSand();

    // crickets: two steady tones, gated into chirps
    cricketBus = [];
    for (const [freq, pan] of [[4350, -0.6], [4720, 0.55]]) {
      const o = ctx.createOscillator(); o.type = 'sine'; o.frequency.value = freq;
      const g = ctx.createGain(); g.gain.value = 0;
      const p = ctx.createStereoPanner(); p.pan.value = pan;
      o.connect(g); g.connect(p); p.connect(fx); o.start();
      cricketBus.push({ g, next: 0, gap: R(0.4, 0.52) });
    }
  }

  // one water drop: a few milliseconds of noise ringing through a narrow filter. Softer and more natural than a
  // pitched tone — a "tk / plip" rather than a bubble.
  function drip(t, f, gain, pan = 0) {
    const src = ctx.createBufferSource(), bq = ctx.createBiquadFilter(), g = ctx.createGain(), p = ctx.createStereoPanner();
    const dur = R(0.035, 0.085);
    src.buffer = white; bq.type = 'bandpass'; bq.Q.value = R(8, 15);
    bq.frequency.setValueAtTime(f, t); bq.frequency.exponentialRampToValueAtTime(f * R(1.04, 1.2), t + dur);
    g.gain.setValueAtTime(0.0001, t); g.gain.exponentialRampToValueAtTime(Math.max(gain, 0.0002), t + 0.004); g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    p.pan.value = clampPan(pan);
    src.connect(bq); bq.connect(g); g.connect(p); p.connect(fx);
    src.start(t, Math.random() * 3.9); src.stop(t + dur + 0.02);
  }
  // one ripplet: the ring of a tiny air bubble pinched off as water folds over itself — a very short, very quiet,
  // high tone that dies away at once. Dozens a second fuse into the light liquid tinkle of fingers trailing
  // through still water. (Noise bursts sound like tapping on something hard; long low tones sound like cartoon
  // bubbles; slow noise swells sound like waves. This is deliberately none of those.)
  function ripplet(t, level, pan) {
    const o = ctx.createOscillator(), g = ctx.createGain(), p = ctx.createStereoPanner();
    const big = Math.random() < 0.07;                       // the odd slightly rounder one
    const f = big ? R(900, 1500) : 1500 * Math.pow(4.2, Math.random()), dur = big ? R(0.035, 0.06) : R(0.009, 0.028);
    const peak = (big ? R(0.02, 0.035) : R(0.012, 0.045) * Math.min(1, 2600 / f)) * (0.4 + 0.6 * level);
    o.type = 'sine'; o.frequency.setValueAtTime(f, t); o.frequency.exponentialRampToValueAtTime(f * R(1.04, 1.18), t + dur);
    g.gain.setValueAtTime(0, t); g.gain.linearRampToValueAtTime(peak, t + 0.0018); g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    p.pan.value = clampPan(pan + R(-0.3, 0.3));
    o.connect(g); g.connect(p); p.connect(fx);
    o.start(t); o.stop(t + dur + 0.01);
  }
  // a shaped swell of filtered noise: water moving (low, slow) or a puff of sand (high, short)
  function burst(t, { buf = white, f0 = 1200, f1 = 400, Q = 0.7, type = 'lowpass', gain = 0.1, attack = 0.01, dur = 0.3, pan = 0, dest = fx }) {
    const src = ctx.createBufferSource(), bq = ctx.createBiquadFilter(), g = ctx.createGain(), p = ctx.createStereoPanner();
    src.buffer = buf; bq.type = type; bq.Q.value = Q;
    bq.frequency.setValueAtTime(f0, t); bq.frequency.exponentialRampToValueAtTime(f1, t + dur);
    g.gain.setValueAtTime(0.0001, t); g.gain.exponentialRampToValueAtTime(gain, t + attack); g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    p.pan.value = clampPan(pan);
    src.connect(bq); bq.connect(g); g.connect(p); p.connect(dest);
    src.start(t, Math.random() * 3); src.stop(t + dur + 0.05);
  }
  function bird(t, vol = 1) {
    const p = ctx.createStereoPanner(); p.pan.value = R(-0.9, 0.9); p.connect(fx);
    const base = R(2600, 5200), n = Math.floor(R(2, 7)), gain = R(0.02, 0.05) * vol, up = Math.random() < 0.5;
    let tt = t;
    for (let i = 0; i < n; i++) {
      const d = R(0.05, 0.13), f0 = base * R(0.86, 1.2), f1 = f0 * (up ? R(1.15, 1.5) : R(0.7, 0.9));
      const o = ctx.createOscillator(), g = ctx.createGain();
      o.frequency.setValueAtTime(f0, tt); o.frequency.exponentialRampToValueAtTime(f1, tt + d);
      g.gain.setValueAtTime(0.0001, tt); g.gain.exponentialRampToValueAtTime(gain, tt + d * 0.25); g.gain.exponentialRampToValueAtTime(0.0001, tt + d);
      o.connect(g); g.connect(p); o.start(tt); o.stop(tt + d + 0.02);
      tt += d + R(0.03, 0.12);
    }
  }
  function chime(t, vol = 1) {
    const strikes = Math.floor(R(1, 2.6)), p = ctx.createStereoPanner(); p.pan.value = 0.45; p.connect(fx);
    let tt = t;
    for (let s = 0; s < strikes; s++) {
      const f = R(1250, 1900), amp = R(0.018, 0.036) * vol;
      [[1, 1, 3.2], [2.76, 0.45, 1.7], [5.4, 0.22, 0.9], [8.93, 0.1, 0.5]].forEach(([ratio, a, dec]) => {
        const o = ctx.createOscillator(), g = ctx.createGain();
        o.frequency.value = f * ratio;
        g.gain.setValueAtTime(0.0001, tt); g.gain.exponentialRampToValueAtTime(amp * a, tt + 0.004); g.gain.exponentialRampToValueAtTime(0.0001, tt + dec);
        o.connect(g); g.connect(p); o.start(tt); o.stop(tt + dec + 0.05);
      });
      tt += R(0.18, 0.7);
    }
  }

  const live = () => ctx && on;
  // iPhone / iPad: sound made by a web page counts as a "ringer" sound, so the silent switch mutes it, and it can
  // only be started from inside a real tap. Playing a silent, looping <audio> element (and asking for the
  // 'playback' audio session where the browser has one) makes the page count as media, which is always heard.
  const IOS = /iPad|iPhone|iPod/.test(navigator.userAgent) || (navigator.platform === 'MacIntel' && navigator.maxTouchPoints > 1);
  let keepAlive = null;
  function mediaChannel(play) {
    if (!IOS) return;
    try { if (navigator.audioSession) navigator.audioSession.type = play ? 'playback' : 'auto'; } catch {}
    if (!keepAlive) {
      const sr = 8000, n = sr / 2, b = new Uint8Array(44 + n), dv = new DataView(b.buffer);      // half a second of silence, as a WAV
      const put = (o, s) => { for (let i = 0; i < s.length; i++) b[o + i] = s.charCodeAt(i); };
      put(0, 'RIFF'); dv.setUint32(4, 36 + n, true); put(8, 'WAVEfmt '); dv.setUint32(16, 16, true); dv.setUint16(20, 1, true); dv.setUint16(22, 1, true);
      dv.setUint32(24, sr, true); dv.setUint32(28, sr, true); dv.setUint16(32, 1, true); dv.setUint16(34, 8, true); put(36, 'data'); dv.setUint32(40, n, true);
      b.fill(128, 44);
      keepAlive = new Audio(URL.createObjectURL(new Blob([b], { type: 'audio/wav' })));
      keepAlive.loop = true; keepAlive.setAttribute('playsinline', ''); keepAlive.preload = 'auto';
    }
    if (play) { const p = keepAlive.play(); if (p && p.catch) p.catch(() => {}); } else keepAlive.pause();
  }
  const api = {
    get on() { return on; },
    get started() { return !!ctx; },
    get running() { return !!ctx && ctx.state === 'running'; },
    onstate: null,
    // call from inside every tap / click / key press: wakes the sound if the browser has it held back
    unlock() {
      if (!ctx || !on) return;
      mediaChannel(true);
      if (ctx.state !== 'running') ctx.resume().catch(() => {});
    },
    setOn(v) {
      on = !!v;
      if (on && !ctx) build();
      if (!ctx) return;
      mediaChannel(on);
      if (on) ctx.resume().catch(() => {});
      master.gain.cancelScheduledValues(ctx.currentTime);
      master.gain.setTargetAtTime(on ? 1.6 : 0, ctx.currentTime, on ? 0.7 : 0.12);
    },
    // st: { env, gust 0..1, dusk 0..1, swish 0..1, swishPan, rake 0..1, rakePan, spoutPan, spoutGain }
    update(dt, st) {
      if (!live()) return;
      const t = ctx.currentTime, g = st.gust, pond = st.env === 'pond', lake = st.env === 'lake';
      let rk = Math.min(st.rake, 1);
      // "Listen" in the tuning panel: the sound of a slow stroke, over and over, with nobody raking
      if (audition) { const ph = t % 1.9; if (ph < 1.3) rk = Math.max(rk, 0.2 + 0.6 * Math.sin(Math.PI * ph / 1.3)); }
      // barely-there air: the pond should be about the water, the sand garden about the sand
      // the sand garden is the quiet one: its surroundings are turned right down so the sand is nearly all you hear
      const air = pond ? 1 : lake ? 0.7 : 0;      // sand garden: no wind, no rustle — nothing but the sand
      wind.gain.gain.setTargetAtTime(AMB.wind ? (0.006 + 0.022 * g) * air : 0, t, 0.6);
      wind.f[0].frequency.setTargetAtTime(200 + 260 * g, t, 0.7);
      rustle.gain.gain.setTargetAtTime(AMB.rustle && pond ? 0.002 + 0.014 * g * g : 0, t, 0.4);      // bamboo: pond only

      // a hand moving through the water
      const want = (pond || lake) && AMB.water ? Math.min(st.swish, 1) : 0;
      stirLevel += (want - stirLevel) * Math.min(1, dt * (want > stirLevel ? 7 : 2.6));
      if (smp.swirls.length) {
        // recorded hand swirls, overlapped end to end for as long as the hand keeps moving, with small ripples
        // from the gentle take sprinkled over them. The bus follows the hand: opens at once, closes softly.
        waterBus.gain.setTargetAtTime(stirLevel * 0.9 * (lake ? 0.36 : 1), t, stirLevel > 0.05 ? 0.08 : 0.3);      // the lake is wide and far: its water is heard softly
        waterPan.pan.setTargetAtTime(clampPan(st.swishPan), t, 0.25);
        waterWet.gain.setTargetAtTime(lake ? 0 : 0.18, t, 0.2);      // open water under open sky: no room around it, so no echo
        if (stirLevel > 0.06) {
          if (t >= nextSwirl) {
            let i; do { i = (Math.random() * smp.swirls.length) | 0; } while (i === lastSwirl && smp.swirls.length > 1);
            const sw = smp.swirls[lastSwirl = i];
            const dur = play(sw.buf, t + 0.01, { gain: sw.gain * R(0.8, 1.1), rate: R(0.88, 1.08), attack: swirlNow ? 0.04 : 0.3, release: 0.6, dest: waterBus });
            nextSwirl = t + dur * R(0.5, 0.68); lastSwirlT = t; swirlNow = false;
          }
          if (smp.drops.length && t >= nextDrop) {
            nextDrop = t + R(0.5, 1.5) / (0.5 + stirLevel);
            play(anyOf(smp.drops), t + 0.01, { gain: R(0.08, 0.2) * stirLevel, rate: R(0.9, 1.1), release: 0.25, dest: waterBus });
          }
        }
        stir.gain.gain.setTargetAtTime(0, t, 0.1); stirLow.gain.gain.setTargetAtTime(0, t, 0.1);
      } else {
        // fallback when the recordings could not be loaded: a synthesized stream of ripplets
        if (stirLevel > 0.03) {
          rippleAcc += dt * (14 + 62 * stirLevel);
          let guard = 0;
          while (rippleAcc >= 1 && guard++ < 14) { rippleAcc -= 1; ripplet(t + R(0, 0.05), stirLevel, st.swishPan); }
        } else rippleAcc = 0;
        stir.gain.gain.setTargetAtTime(stirLevel * 0.03, t, 0.15);
        stir.f[0].frequency.setTargetAtTime(2600, t, 0.3); stir.f[1].frequency.setTargetAtTime(800, t, 0.3);
        stir.pan.pan.setTargetAtTime(clampPan(st.swishPan), t, 0.25);
        stirLow.gain.gain.setTargetAtTime(0, t, 0.15);
      }

      // sand under the tool: nothing while still, swelling and thinning with the speed of the stroke, every
      // piece a little different in loudness and pitch — a hand moving, not a noise switched on
      const moving = rk > 0.03;
      // SP.tail is the time until it is as good as silent once the hand stops (a quarter of it per time-constant)
      const open = moving || t < puffUntil;
      sandStroke.gain.setTargetAtTime(open ? 1 : 0, t, open ? 0.04 : SP.tail / 4);
      if (!moving) nextGrain = 0;
      else {
        const lvl = SP.follow * rk + (1 - SP.follow) * 0.55;
        // the first piece of a stroke comes in at once, however long and slow-swelling the pieces are set to be
        if (nextGrain === 0) { sandGrain(t + 0.005, SP.vol * lvl, SP.smooth, 0.05); nextGrain = t + SP.smooth * 0.3; }
        else if (nextGrain < t) nextGrain = t + 0.005;
        // about three pieces sound at once whatever their length, so "smoother" does not also mean "louder"
        for (let n = 0; nextGrain < t + 0.06 && n < 8; n++) {
          sandGrain(nextGrain, SP.vol * lvl * (1 + SP.vary * R(-0.6, 0.4)));
          nextGrain += SP.smooth * R(0.26, 0.4);
        }
      }
      sandBus.pan.setTargetAtTime(clampPan(st.rakePan), t, 0.1);

      // no constant dripping — just a single quiet drop from the spout once in a long while
      if (pond) {
        timers.drip -= dt;
        if (timers.drip <= 0) {
          timers.drip = R(7, 16);
          if (!AMB.drop) { /* switched off */ }
          else if (smp.drops.length) play(anyOf(smp.drops), t + 0.02, { gain: 0.1 * st.spoutGain, release: 0.25, pan: st.spoutPan });
          else drip(t + 0.02, R(1100, 2000), 0.12 * st.spoutGain, st.spoutPan);
        }
      }
      // birds, chime and crickets belong to the pond only. In the sand garden they were turned down so far that
      // all that was left of them was a faint pure tone out of the silence — a beep — so there they are off.
      // The lake has birds too, further off and less often; the chime hangs in the garden only.
      if (pond || lake) {
        timers.bird -= dt;
        if (timers.bird <= 0) { timers.bird = R(4, 13) * (1 + 2 * st.dusk) * (lake ? 2.2 : 1); if (AMB.birds && Math.random() > st.dusk * 1.2) bird(t + 0.02, lake ? 0.5 : 1); }
      }
      if (pond) {
        timers.chime -= dt * (0.5 + g);
        if (timers.chime <= 0) { timers.chime = R(50, 120); if (AMB.chime) chime(t + 0.02); }      // rare: roughly once every minute or two
      }

      // crickets fade in toward dusk
      for (const c of cricketBus) {
        if (st.dusk < 0.3 || !pond || !AMB.crickets) { c.next = t; continue; }
        if (c.next < t) c.next = t + R(0, 0.3);
        const amp = 0.02 * (st.dusk - 0.3) / 0.7;
        while (c.next < t + 0.4) {
          for (let k = 0; k < 3; k++) {
            const a = c.next + k * 0.03;
            c.g.gain.setValueAtTime(0, a); c.g.gain.linearRampToValueAtTime(amp, a + 0.005); c.g.gain.linearRampToValueAtTime(0, a + 0.02);
          }
          c.next += Math.random() < 0.07 ? R(1.2, 3) : c.gap;
        }
      }
    },
    // a single small water sound (leaf landing, a koi mouthing the surface)
    plink(strength = 0.5, pan = 0, force = false) {
      if (!live() || !(AMB.leaves || force)) return;
      const t = ctx.currentTime + 0.01, k = Math.min(strength, 1);
      if (smp.drops.length) play(anyOf(smp.drops), t, { gain: 0.08 + 0.18 * k, rate: R(0.9, 1.1), release: 0.25, pan });
      else drip(t, R(700, 1700), 0.25 + 0.5 * k, pan);
    },
    // the cursor meeting the water: start a swirl straight away (recordings), or a flurry of ripplets (fallback)
    touch(speed = 0.5, pan = 0, first = false) {
      if (!live() || !first || !AMB.water) return;
      const t = ctx.currentTime;
      if (smp.swirls.length) { if (t - lastSwirlT > 0.6) { swirlNow = true; nextSwirl = t; } return; }
      if (t < nextTouch) return;
      nextTouch = t + 0.3;
      for (let i = 0; i < 12; i++) ripplet(t + R(0, 0.16), 0.9, pan);
    },
    // a koi turning, surfacing or darting: a short, slowed-down swirl of water
    fish(intensity = 0.5, pan = 0, force = false) {
      if (!live() || !(AMB.koi || force)) return;
      const t = ctx.currentTime, k = Math.min(intensity, 1);
      if (t - lastFish < 1.5 && !force) return;       // never more than one swirl at a time
      lastFish = t;
      if (smp.swirls.length) { const sw = anyOf(smp.swirls); play(sw.buf, t + 0.01, { gain: sw.gain * (0.1 + 0.35 * k), rate: R(0.72, 0.86), offset: R(0, 0.4), attack: 0.08, dur: 0.7 + 0.6 * k, release: 0.5, pan }); }
      else burst(t, { buf: brown, f0: 520 + 260 * k, f1: 200, Q: 0.4, gain: 0.08 + 0.18 * k, attack: 0.07, dur: 0.35 + 0.35 * k, pan });
    },
    // a skipped stone touching the water: a quick light 'tk' for each skip, a deeper 'plop' when it finally sinks
    skip(k = 1, pan = 0, sink = false) {
      if (!live() || !AMB.water) return;
      const t = ctx.currentTime + 0.005;
      // straight to the output, short and dry: out on a lake there is nothing for the sound to ring off
      if (smp.drops.length) play(anyOf(smp.drops), t, { gain: (sink ? 0.34 : 0.26) * k, rate: sink ? R(0.6, 0.74) : R(1.15, 1.5), dur: sink ? 0.5 : 0.22, release: sink ? 0.3 : 0.12, pan, dest: master });
      else drip(t, sink ? 520 : R(1200, 2000), 0.2 * k, pan);
    },
    splash(pan = 0, vol = 1) {
      if (!live() || !AMB.water) return;
      const t = ctx.currentTime + 0.01;
      if (smp.swirls.length) {
        const sw = smp.swirls[0];
        play(sw.buf, t, { gain: sw.gain * 2.6 * vol, rate: 1.12, attack: 0.008, release: 0.7, pan });
        for (let i = 0; i < 2 && smp.drops.length; i++) play(anyOf(smp.drops), t + R(0.1, 0.45), { gain: R(0.15, 0.3) * vol, release: 0.25, pan: pan + R(-0.2, 0.2) });
        return;
      }
      burst(t, { f0: 2000, f1: 380, gain: 0.16, attack: 0.015, dur: 0.4, pan });
      burst(t, { buf: brown, f0: 700, f1: 220, Q: 0.4, gain: 0.3, attack: 0.03, dur: 0.6, pan });
      for (let i = 0; i < 2; i++) drip(t + R(0.08, 0.35), R(600, 1300), R(0.12, 0.25), pan + R(-0.2, 0.2));
    },
    // sand pressed / stamped / a tool being set down: a short dry puff of grains
    sandPuff(strength = 1, pan = 0) {
      if (!live()) return;
      const t = ctx.currentTime;
      sandBus.pan.setTargetAtTime(clampPan(pan), t, 0.02);
      const hold = 0.12 + 0.2 * strength;      // a light touch is a short sound
      puffUntil = t + hold; sandStroke.gain.setTargetAtTime(1, t, 0.02);
      sandGrain(t + 0.005, SP.vol * 0.85 * strength, hold + 0.12); sandGrain(t + 0.04, SP.vol * 0.6 * strength, hold + 0.1);
    },
    chime() { if (live()) chime(ctx.currentTime + 0.02); },
    // RMS of the final output — used for testing that sound is actually being produced
    level() {
      if (!analyser) return 0;
      const d = new Float32Array(analyser.fftSize); analyser.getFloatTimeDomainData(d);
      let s = 0; for (let i = 0; i < d.length; i++) s += d[i] * d[i];
      return Math.sqrt(s / d.length);
    },
    get state() { return ctx ? ctx.state : 'none'; },
    get recordings() { return { swirls: smp.swirls.length, ripples: smp.drops.length, sand: Object.keys(sandBufs) }; },
    // the pond's background sounds, one switch each
    ambient: {
      get state() { return { ...AMB }; },
      set(o) { for (const k in o) if (k in AMB) AMB[k] = !!o[k]; },
      // play one of them now, so it can be told which sound is which
      hear(k) {
        if (!live()) return;
        const t = ctx.currentTime + 0.02;
        if (k === 'birds') bird(t); else if (k === 'chime') chime(t);
        else if (k === 'koi') api.fish(0.5, 0, true); else if (k === 'leaves') api.plink(0.08, 0, true);
        else if (k === 'drop') { if (smp.drops.length) play(anyOf(smp.drops), t, { gain: 0.1, release: 0.25 }); else drip(t, R(1100, 2000), 0.12); }
      },
    },
    // the tuning panel's handle on the sand sound
    sand: {
      get params() { return { ...SP }; },
      defaults: SAND_DEFAULT, range: SAND_RANGE, sources: ['salt', 'friction', 'movement', 'drawing', 'noise'],
      set(o) {
        for (const k in o) {
          if (k === 'src') { if (k in SP && (o.src === 'noise' || SAND_SRC[o.src])) SP.src = o.src; }
          else if (SAND_RANGE[k] && Number.isFinite(+o[k])) SP[k] = Math.max(SAND_RANGE[k][0], Math.min(SAND_RANGE[k][1], +o[k]));
        }
        if (ctx) sandFilters();
      },
      get listening() { return audition; },
      listen(v) { audition = !!v; },
    },
  };
  return api;
}
