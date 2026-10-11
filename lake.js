// Mountain lake environment: a still glacial lake under snow-streaked peaks, scree on one shore and spruce
// forest on the other, seen from a pile of boulders at the near end. Everything is procedural.
// Units are metres. The water surface is y = 0; the interactive water patch is centred on the world origin.
import * as THREE from 'three';

export const LAKE_S = 48;            // half-size of the interactive water patch
const Z0 = 24;                       // lake-local z = world z − Z0 (the near shore sits just inside the patch)
// near shoreline, mirrored in GLSL so the ripples stop where the bank does (negative = water)
// (a spit of boulders runs out into the water left of the viewpoint)
const spit = x => { const t = (x + 15) / 7.5; return 9.5 * Math.exp(-t * t); };
export const lakeShore = (x, z) => (z - Z0) - (19 + 2.2 * Math.sin(x * 0.11 + 0.6) + 0.9 * Math.sin(x * 0.31 + 2.0) - spit(x));
export const LAKE_GLSL = /* glsl */`float lakeD(vec2 p){ float t = (p.x + 15.) / 7.5;
  return (p.y - ${Z0}.) - (19. + 2.2 * sin(p.x * .11 + .6) + .9 * sin(p.x * .31 + 2.) - 9.5 * exp(-t * t)); }`;
export const LAKE_VIEW = { pos: [0, 6.2, 55], tgt: [0, 7.0, 32] };

export function createLake({ patch, NOISE, CAUSTIC, ROCK_COLOR, makeRockGeo, waterMat, U, helpers }) {
  const { vn2, fbm2, sstep, clamp, mulberry32 } = helpers;
  const V3 = THREE.Vector3;
  const rnd = mulberry32(4711), R = (a, b) => a + rnd() * (b - a);
  const group = new THREE.Group();
  const aboveWater = [];      // things that can never be seen through the water: left out of the refraction pass

  // ── the lie of the land ──
  const smax = (a, b, k) => { const h = clamp(0.5 + 0.5 * (a - b) / k, 0, 1); return b + (a - b) * h + k * h * (1 - h); };
  // signed distance to the shore in lake-local coordinates (positive on land)
  function shoreD(x, zl) {
    const u = -zl;
    const cx = -40 * sstep(150, 520, u);
    const wL = 95 + 25 * sstep(100, 300, u) - 60 * sstep(350, 520, u);
    const wR = 230 - 175 * sstep(60, 230, u) + 12 * Math.sin(u * 0.02);
    const wob = (fbm2(x * 0.012 + 3, zl * 0.012) - 0.5) * 30 * sstep(60, 130, Math.hypot(x, zl));
    const dN = lakeShore(x, zl + Z0), dL = (cx - wL) - x + wob, dR = x - (cx + wR) + wob, dF = u - 540 + wob;
    return smax(smax(dN, dF, 6), smax(dL, dR, 6), 6);
  }
  // peaks: x, z (local), height, base radius
  const PEAKS = [
    [-430, -150, 640, 560],      // the wall on the left, close by
    [-250, -480, 240, 380],      // its lower shoulder
    [-330, -820, 560, 520],      // the tower
    [-40, -1050, 470, 520], [190, -1150, 520, 560], [470, -1250, 560, 640], [820, -1250, 520, 700],
    [1250, -900, 480, 760], [430, -230, 150, 430],      // far right, and the forested ridge on the right shore
    [-900, -600, 600, 800], [-700, -1250, 560, 760], [100, -1900, 700, 1000],
    [1500, -200, 420, 800], [-1100, 200, 500, 800],
  ];
  function ridged(x, z) {
    let s = 0, a = 0.5, f = 1, w = 1, n = 0;
    for (let o = 0; o < 5; o++) {
      let v = 1 - Math.abs(2 * vn2(x * f + o * 17.1, z * f + o * 9.3) - 1); v *= v;
      s += a * v * w; n += a; w = clamp(v * 1.7, 0, 1); f *= 2.07; a *= 0.5;
    }
    return s / n;
  }
  const out = { h: 0, sd: 0, ridge: 0, m: 0 };
  function sample(x, zl) {
    const sd = shoreD(x, zl);
    out.sd = sd; out.ridge = 0.5; out.m = 0;
    if (sd <= 0) {
      const d = -sd;
      let h = -(1.5 * sstep(0, 5, d) + 0.11 * d);
      h += (fbm2(x * 0.9, zl * 0.9) - 0.5) * 0.5 * sstep(0.3, 3, d) * (1 - sstep(8, 22, d));
      out.h = Math.max(h, -26);
      return out;
    }
    // the bank: a pile of boulders under the viewpoint, a low stony rise everywhere else
    const near = sstep(130, 60, Math.hypot(x, zl - 31));
    let h = near * (3.4 * sstep(0.2, 7.5, sd) + (fbm2(x * 0.33 + 7, zl * 0.33) - 0.5) * 1.0 * sstep(0.5, 4, sd))
          + (1 - near) * (0.8 * sstep(0, 4, sd) + sd * 0.015);
    // mountains: cones, cut into ridges and gullies, stepped into cliff bands higher up
    let m = 0, s2 = 0;
    for (let i = 0; i < PEAKS.length; i++) {
      const p = PEAKS[i], px = x - p[0], pz = zl - p[1], f = 1 - Math.sqrt(px * px + pz * pz) / p[3];
      if (f <= 0) continue;
      const v = p[2] * 0.92 * Math.pow(f, 1.2);
      if (v > m) { s2 = m; m = v; } else if (v > s2) s2 = v;
    }
    m += 0.25 * s2;
    if (m > 0) {
      const rg = ridged(x / 380, zl / 380);
      out.ridge = rg;
      m *= 0.42 + 1.0 * rg;
      m += (ridged(x / 95 + 31, zl / 95) - 0.35) * 85 * sstep(150, 380, m);      // broken, toothed crests
      m += (fbm2(x / 55, zl / 55) - 0.5) * 34 * sstep(60, 260, m);
      const cliff = sstep(110, 300, m), t = (m + x * 0.05) / 70, ft = t - Math.floor(t);      // beds dip gently to one side
      m += ((Math.floor(t) + sstep(0.12, 0.42, ft)) * 70 - x * 0.05 - m) * 0.7 * cliff;
      m *= Math.pow(sstep(4, 170, sd), 1.1);
      m = Math.min(m, 3 + sd * 0.6 + sd * sd * 0.0011);      // scree lies no steeper than its angle of repose
      m *= 1 - near * sstep(110, 60, Math.hypot(x, zl - 31)) * 0.999;
    }
    out.m = m; out.h = h + m;
    return out;
  }
  const heightAt = (x, z) => sample(x, z - Z0).h;      // world coordinates

  // where forest grows: off the water, below the tree line, not on cliffs, not on the bare scree of the left shore
  function forestAt(x, zl, h, ny, sd) {
    const u = -zl;
    const line = 90 + 190 * sstep(-50, 480, x) + (fbm2(x * 0.004 + 9, zl * 0.004) - 0.5) * 120;
    let f = sstep(1.5, 8, sd) * (1 - sstep(line - 50, line, h)) * sstep(0.70, 0.84, ny);
    f *= 1 - 0.94 * sstep(-60, -125, x) * sstep(640, 480, u);
    f *= 0.3 + 0.7 * sstep(0.3, 0.46, fbm2(x * 0.007 + 5, zl * 0.007 + 1));
    f *= sstep(60, 110, Math.hypot(x, zl - 31));
    return f;
  }

  // ── terrain mesh: a fan of rings round the viewpoint, fine underfoot and coarse at the peaks ──
  {
    const NR = 420, NA = 640, CX = 0, CZ = 38, R0 = 2, R1 = 4400, HALF = 2.0;      // centre in local coords, just behind the viewer
    const pos = new Float32Array((NR + 1) * (NA + 1) * 3), info = new Float32Array((NR + 1) * (NA + 1) * 4);
    let k = 0, q = 0;
    for (let i = 0; i <= NR; i++) {
      const r = R0 * Math.pow(R1 / R0, i / NR);
      for (let j = 0; j <= NA; j++) {
        const a = (j / NA * 2 - 1) * HALF, x = CX + Math.sin(a) * r, zl = CZ - Math.cos(a) * r;
        const s = sample(x, zl);
        pos[k++] = x; pos[k++] = s.h; pos[k++] = zl + Z0;
        info[q++] = s.sd; info[q++] = s.ridge; info[q++] = 0; info[q++] = s.m;
      }
    }
    const idx = new Uint32Array(NR * NA * 6); k = 0;
    for (let i = 0; i < NR; i++) for (let j = 0; j < NA; j++) {
      const a = i * (NA + 1) + j, b = a + 1, c = a + NA + 1, d = c + 1;
      idx[k++] = a; idx[k++] = c; idx[k++] = b; idx[k++] = b; idx[k++] = c; idx[k++] = d;
    }
    const g = new THREE.BufferGeometry();
    g.setAttribute('position', new THREE.BufferAttribute(pos, 3));
    g.setIndex(new THREE.BufferAttribute(idx, 1));
    g.computeVertexNormals();
    const nrm = g.attributes.normal;
    if (nrm.getY(0) < 0) { for (let i = 0; i < idx.length; i += 3) { const t = idx[i + 1]; idx[i + 1] = idx[i + 2]; idx[i + 2] = t; } g.computeVertexNormals(); }
    for (let i = 0, n = pos.length / 3; i < n; i++) info[i * 4 + 2] = forestAt(pos[i * 3], pos[i * 3 + 2] - Z0, pos[i * 3 + 1], nrm.getY(i), info[i * 4]);
    g.setAttribute('aInfo', new THREE.BufferAttribute(info, 4));
    const LAND = /* glsl */`
      vec3 q3 = vWPos; float yy = q3.y; vec3 nW = normalize(vWNrm); float sl = 1. - nW.y;
      float sd = vInfo.x, rdg = vInfo.y, fst = vInfo.z, mh = vInfo.w;
      float dC = length(cameraPosition - q3), fine = 1. - smoothstep(40., 160., dC);
      // bedrock: level strata, bent a little, in greys and tans
      float warp = zfbm2(q3.xz * .004) * 90. + zfbm2(q3.xz * .03) * 14. + q3.x * .05;
      float st = (yy + warp) * .05;
      vec3 rock = mix(vec3(.17, .165, .17), vec3(.33, .29, .23), zn2(vec2(st, .5)));
      rock = mix(rock, vec3(.10, .095, .10), smoothstep(.45, .8, zn2(vec2(st * 3.7, 7.5))) * .75);
      rock = mix(rock, vec3(.36, .27, .19), smoothstep(.6, .85, zn2(vec2(st * .9 + 4., 2.5))) * .5);      // rusty beds
      rock *= .7 + .6 * zfbm2(q3.xz * .021 + 3.);
      rock *= .8 + .4 * zn2(vec2(q3.x * .09 + q3.z * .06, yy * .011));      // streaks running down the faces
      vec3 talus = mix(vec3(.36, .33, .29), vec3(.24, .225, .21), zfbm2(q3.xz * .045 + 8.));
      talus *= .9 + .2 * zn2(q3.xz * .9);
      vec3 col = mix(talus, rock, smoothstep(.2, .42, sl) * smoothstep(40., 150., mh));
      col *= mix(1., mix(.66, 1.1, smoothstep(.1, .55, rdg)), smoothstep(30., 160., mh));      // gullies sit in shade
      // snow: on ledges and in gullies, more of it the higher you look, never on the steepest faces
      float alt = smoothstep(40., 520., yy);
      float sn = zfbm2(q3.xz * .011 + 11.) * .62 + zfbm2(q3.xz * .07 + 2.) * .38;
      float hold = smoothstep(.56, .26, sl) + (1. - smoothstep(.1, .5, rdg)) * .35;
      float snow = smoothstep(.62, .69, sn * .55 + alt * .36 + hold * .22) * smoothstep(.6, .36, sl) * smoothstep(25., 70., mh);
      // forest floor (the trees themselves stand on top of this)
      vec3 duff = mix(vec3(.022, .042, .020), vec3(.05, .075, .03), zn2(q3.xz * .16)) * (.75 + .5 * zn2(q3.xz * .9));
      float fm = smoothstep(.12, .5, fst) * (1. - snow);
      // the stony bank and the lake bed: cobbles
      vec2 vv = zvor(q3.xz * 1.15); vec2 v2 = zvor(q3.xz * 3.4 + 9.);
      float cob = smoothstep(.62, .2, vv.x);
      vec3 stone = mix(vec3(.20, .195, .19), vec3(.50, .47, .42), fract(vv.y * 7.3)) * (.8 + .3 * zn2(q3.xz * 6.));
      vec3 grit = mix(vec3(.24, .22, .20), vec3(.42, .39, .34), fract(v2.y * 5.1));
      vec3 shore = mix(grit, stone, cob);
      float sh = (1. - smoothstep(18., 60., mh)) * (1. - smoothstep(5., 14., yy));
      col = mix(col, shore, sh * (1. - fm));
      col = mix(col, duff, fm);
      col = mix(col, vec3(.86, .89, .93), snow);
      // under water: pale silt settles between the stones
      float bed = smoothstep(.1, -1.2, yy);
      col = mix(col, vec3(.40, .43, .40) * (.8 + .3 * zn2(q3.xz * .7)), bed * .65);
      float wet = (1. - smoothstep(.0, .22, yy)) * (1. - bed);
      col *= mix(1., .5, wet);
      float hb = (cob * (1. - vv.x * vv.x * 2.) * .11 + smoothstep(.6, .2, v2.x) * .02) * sh * (1. - fm);
      hb += (zfbm2(q3.xz * .9) * .25 + zn2(q3.xz * 4.) * .05) * (1. - sh) * (1. - snow * .8);
      // the big relief the mesh is too coarse to carry: ledges along the beds, knobs and hollows across them
      float far = smoothstep(40., 140., mh) * (1. - snow * .7) * (1. - fm);
      float hf = (zfbm2(q3.xz * .03 + 5.) * 7. + zn2(q3.xz * .11) * 1.6 + zn2(vec2(st * 3.7, 7.5)) * 3.5 + zn2(vec2(st * 11., 3.5)) * 1.2) * far;
      // faces turned from the sun fall into blue shade (the peaks cast no real shadows at this distance)
      float ndl = dot(nW, uSunDirW);
      col *= mix(vec3(1.), mix(vec3(.5, .56, .7), vec3(1.), smoothstep(-.15, .4, ndl)), smoothstep(30., 120., mh));
      diffuseColor.rgb = col; pH = hb * fine + hf; pRough = mix(mix(.93, .6, snow), .28, wet);
    `;
    const mat = patch(new THREE.MeshStandardMaterial({ roughness: 0.93, metalness: 0 }), {
      vertPars: 'attribute vec4 aInfo; varying vec4 vInfo;', vert: 'vInfo = aInfo;', fragPars: 'varying vec4 vInfo;',
      color: LAND, bump: 1.2, afterLights: CAUSTIC,
    });
    const land = new THREE.Mesh(g, mat); land.receiveShadow = true; land.frustumCulled = false;
    group.add(land);
  }

  // ── conifers: three levels of detail, thousands of them ──
  function coniferGeo(tiers, sides, ragged, trunk) {
    const pos = [], col = [], idx = [];
    if (trunk) {
      const b = pos.length / 3;
      for (let j = 0; j < 5; j++) { const a = j / 5 * 6.2832; pos.push(Math.cos(a) * 0.016, 0, Math.sin(a) * 0.016, Math.cos(a) * 0.008, 0.5, Math.sin(a) * 0.008); col.push(0.42, 0.3, 0.22, 0.42, 0.3, 0.22); }
      for (let j = 0; j < 5; j++) { const a0 = b + j * 2, a1 = b + ((j + 1) % 5) * 2; idx.push(a0, a0 + 1, a1, a1, a0 + 1, a1 + 1); }
    }
    const y0 = trunk ? 0.13 : 0.04;
    for (let i = 0; i < tiers; i++) {
      const t = i / tiers, yb = y0 + (1 - y0) * t * 0.97, h = (1 - y0) / tiers * (tiers > 1 ? 2.2 : 1);
      const r = 0.17 * Math.pow(1 - t, 0.85) + 0.012, b = pos.length / 3;
      pos.push(0, Math.min(1, yb + h), 0); col.push(0.5, 0.56, 0.5);
      for (let j = 0; j < sides; j++) {
        // on the detailed trees every other point of a skirt is drawn in, so each tier reads as a whorl of boughs
        const star = ragged > 0.6 ? (j % 2 ? 0.5 : 1.08) : 1;
        const a = (j + (i % 2) * 0.5 + (ragged > 0.6 ? rnd() * 0.4 : 0)) / sides * 6.2832, rr = r * star * (1 + ragged * 0.6 * (rnd() - 0.5)), lit = (0.85 + 0.3 * rnd()) * (star < 1 ? 0.6 : 1.1);
        pos.push(Math.cos(a) * rr, yb - (star > 1 ? 0.012 + ragged * 0.02 * rnd() : -0.006), Math.sin(a) * rr); col.push(lit, lit * 1.05, lit * 0.9);
      }
      for (let j = 0; j < sides; j++) idx.push(b, b + 1 + (j + 1) % sides, b + 1 + j);
    }
    const g = new THREE.BufferGeometry();
    g.setAttribute('position', new THREE.Float32BufferAttribute(pos, 3));
    g.setAttribute('color', new THREE.Float32BufferAttribute(col, 3));
    g.setIndex(idx); g.computeVertexNormals();
    return g;
  }
  const NEEDLES = /* glsl */`
    float nn_ = zn3(vWPos * 9.) * .5 + zn3(vWPos * 31.) * .5;
    diffuseColor.rgb *= .7 + .6 * nn_; pH = nn_ * .02; pRough = .85;
  `;
  const treeMat = shadows => patch(new THREE.MeshStandardMaterial({ roughness: 0.85, vertexColors: true, side: shadows ? THREE.DoubleSide : THREE.FrontSide }), { color: NEEDLES, bump: 1 });
  {
    const tiers = [
      { geo: coniferGeo(15, 14, 0.9, true), step: 5.2, r0: 0, r1: 300, shadow: true, list: [] },
      { geo: coniferGeo(3, 6, 0.3, false), step: 8.5, r0: 300, r1: 1000, shadow: false, list: [] },
      { geo: coniferGeo(1, 5, 0.2, false), step: 15, r0: 1000, r1: 2500, shadow: false, list: [] },
    ];
    for (const T of tiers) {
      const x0 = -T.r1, x1 = T.r1, z0 = 31 - T.r1, z1 = 31 + Math.min(T.r1, 60);
      for (let gx = x0; gx < x1; gx += T.step) for (let gz = z0; gz < z1; gz += T.step) {
        const x = gx + rnd() * T.step, zl = gz + rnd() * T.step, d = Math.hypot(x, zl - 31);
        if (d < T.r0 || d >= T.r1 || zl > 31 + Math.abs(x) * 0.9 + 20) continue;
        const s = sample(x, zl), h = s.h, sd = s.sd;
        if (sd < 1.2 || h < 0.5) continue;
        const e = 3, hx = sample(x + e, zl).h, hz = sample(x, zl + e).h;
        const ny = 1 / Math.hypot((hx - h) / e, 1, (hz - h) / e);
        if (rnd() > forestAt(x, zl, h, ny, sd)) continue;
        T.list.push(x, h - 0.3, zl + Z0, R(9, 21) * (1 - 0.35 * sstep(120, 320, h)));
      }
    }
    // a few picked by hand: the lone spruce below the viewpoint, and others framing the view
    for (const [x, z, s] of [[-7.5, 40.6, 4.4], [-12.5, 39.5, 3.0], [-17.5, 41, 5.2], [-20, 45, 7.5], [-24, 50, 10], [21, 50.5, 7.5], [26, 53, 11], [-31, 51, 12], [33, 56, 13], [15, 47.5, 3.2]]) {
      tiers[0].list.push(x, heightAt(x, z) - 0.15, z, s);
    }
    const dummy = new THREE.Object3D(), c = new THREE.Color();
    for (const T of tiers) {
      const n = T.list.length / 4, im = new THREE.InstancedMesh(T.geo, treeMat(T.shadow), n);
      for (let i = 0; i < n; i++) {
        const s = T.list[i * 4 + 3];
        dummy.position.set(T.list[i * 4], T.list[i * 4 + 1], T.list[i * 4 + 2]);
        dummy.rotation.set(R(-0.03, 0.03), R(0, 6.28), R(-0.03, 0.03));
        dummy.scale.set(s * R(0.85, 1.25), s, s * R(0.85, 1.25)); dummy.updateMatrix();
        im.setMatrixAt(i, dummy.matrix);
        const v = R(0.7, 1.25); c.setRGB(0.013 * v, 0.03 * v * R(0.85, 1.15), 0.02 * v); im.setColorAt(i, c);
      }
      im.castShadow = T.shadow; im.receiveShadow = T.shadow;
      group.add(im); aboveWater.push(im);
    }
    group.userData.trees = tiers.map(T => T.list.length / 4);
  }

  // ── boulders: the pile under the viewpoint, and stones standing in the shallows ──
  {
    const geos = [5, 23, 47, 61].map(s => makeRockGeo(s, 5));
    const mat = patch(new THREE.MeshStandardMaterial({ roughness: 0.88 }), { color: ROCK_COLOR, bump: 1.4, fragPars: 'uniform float uMoss;', uniforms: { uMoss: { value: 0.12 } }, afterLights: CAUSTIC });
    const lists = geos.map(() => []);
    const put = (x, z, s, sink) => lists[(rnd() * geos.length) | 0].push(x, heightAt(x, z) + s * (0.18 - sink), z, s);
    for (let i = 0; i < 210; i++) {
      const x = R(-46, 46), z = R(38.5, 62), d = lakeShore(x, z);
      if (d < -3.5 || Math.hypot(x, z - 55) < 4.5) continue;      // not far out in the water, not where the viewer stands
      const big = rnd() < 0.16 && !(Math.abs(x) < 15 && z > 46);      // nothing tall where the viewer moves about
      put(x, z, big ? R(0.9, 1.9) : R(0.25, 0.75), d < 0 ? 0.25 : 0.1);
    }
    for (let i = 0; i < 40; i++) { const x = R(-26, -5), z = R(33, 46); if (lakeShore(x, z) > -2.5) put(x, z, R(0.4, 1.5), 0.15); }      // the spit
    const dummy = new THREE.Object3D();
    geos.forEach((geo, gi) => {
      const L = lists[gi], n = L.length / 4, im = new THREE.InstancedMesh(geo, mat, n);
      for (let i = 0; i < n; i++) {
        const s = L[i * 4 + 3];
        dummy.position.set(L[i * 4], L[i * 4 + 1], L[i * 4 + 2]);
        dummy.rotation.set(R(-0.3, 0.3), R(0, 6.28), R(-0.3, 0.3));
        dummy.scale.set(s * R(0.85, 1.3), s * R(0.5, 0.85), s * R(0.85, 1.25)); dummy.updateMatrix();
        im.setMatrixAt(i, dummy.matrix);
      }
      im.castShadow = im.receiveShadow = true; group.add(im);
    });
  }

  // ── fair-weather clouds on a dome ──
  const cloudMat = new THREE.ShaderMaterial({
    uniforms: { uTime: U.uTime, uSunDirW: U.uSunDirW, uSunCol: U.uSunCol, uAmb: { value: new THREE.Color(0.6, 0.66, 0.78) }, uCover: { value: 0.6 } },
    transparent: true, depthWrite: false, side: THREE.BackSide, fog: false,
    vertexShader: /* glsl */`varying vec3 vDir; void main(){ vDir = position; gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 1.0); }`,
    fragmentShader: /* glsl */`
      precision highp float;
      uniform float uTime, uCover; uniform vec3 uSunDirW, uSunCol, uAmb; varying vec3 vDir;
      ${NOISE}
      float cl(vec2 p){ return zfbm2(p * 1.1) * .72 + zfbm2(p * 4.3 + 9.) * .28; }
      void main(){
        vec3 d = normalize(vDir); if (d.y < .002) discard;
        // high, dry air: by day the sky is a deep clear blue right down to the peaks
        float day = smoothstep(.3, .62, uSunDirW.y);
        vec3 blue = mix(vec3(.50, .84, 1.45), vec3(.085, .33, 1.2), pow(d.y, .42));
        float as = day * .92 * smoothstep(.0, .04, d.y);
        vec2 p = d.xz / (d.y + .16) * 1.2 + uTime * vec2(.0026, .0011) + 3.7;
        float n = cl(p);
        float dens = smoothstep(uCover, uCover + .15, n);
        // lit from the sun's side, grey underneath where the cloud is thick
        float n2 = cl(p + normalize(uSunDirW.xz + 1e-4) * .1);
        float lit = clamp(.6 + (n - n2) * 4.5, 0., 1.);
        float core = smoothstep(uCover + .08, uCover + .38, n);
        vec3 col = uAmb * mix(1.1, .62, core) + uSunCol * .27 * lit * mix(1., .5, core);
        float ac = dens * smoothstep(.03, .26, d.y) * .97, a = ac + as * (1. - ac);
        if (a < .003) discard;
        gl_FragColor = vec4((col * ac + blue * as * (1. - ac)) / a, a);
      }`,
  });
  const clouds = new THREE.Mesh(new THREE.SphereGeometry(5200, 40, 14, 0, Math.PI * 2, 0, Math.PI / 2), cloudMat);
  clouds.frustumCulled = false; clouds.renderOrder = -1;
  group.add(clouds); aboveWater.push(clouds);

  // ── the water: the pond's surface shader on a sheet big enough for the whole valley ──
  const water = new THREE.Mesh(new THREE.PlaneGeometry(9000, 9000).rotateX(-Math.PI / 2), waterMat);
  water.position.set(0, 0, -1800); water.frustumCulled = false;
  group.add(water);

  return { group, water, clouds, cloudMat, heightAt, aboveWater };
}
