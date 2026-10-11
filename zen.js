import * as THREE from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';
import { Sky } from 'three/addons/objects/Sky.js';
import { EffectComposer } from 'three/addons/postprocessing/EffectComposer.js';
import { RenderPass } from 'three/addons/postprocessing/RenderPass.js';
import { ShaderPass } from 'three/addons/postprocessing/ShaderPass.js';
import { UnrealBloomPass } from 'three/addons/postprocessing/UnrealBloomPass.js';
import { OutputPass } from 'three/addons/postprocessing/OutputPass.js';
import { mergeGeometries, mergeVertices } from 'three/addons/utils/BufferGeometryUtils.js';
import { createAudio } from './audio.js?v=28';
import { createLake, lakeShore, LAKE_S, LAKE_GLSL, LAKE_VIEW } from './lake.js?v=27';

const V3 = THREE.Vector3;

// ───────────────────────────── constants & helpers ─────────────────────────────
const S = 6.2;          // half-size of the water simulation domain (metres)
const SIM = 512;        // water simulation resolution
const SAND_S = 11.7;    // half-size of the rake-able sand domain (reaches the garden walls)
const SAND_RES = 2560;
const GRAVEL_Y = 0.12;
// Moss islands: x, z, radius, environment. Index 3 = maple; the 'sand' ones are the dry-garden stone groups + lantern.
const ISL_ALL = [[-5.6, 6.0, 0.85, 'both'], [5.4, 6.4, 0.6, 'both'], [6.6, -5.4, 0.7, 'both'], [-6.0, -3.4, 0.55, 'both'],
  [-4.6, -1.6, 0.8, 'sand'], [4.4, -1.2, 0.6, 'sand'], [-3.0, 1.6, 0.5, 'sand'], [3.3, 1.9, 0.45, 'sand'], [5.2, -3.6, 0.45, 'sand']];
// (the dry garden keeps only two stone groups, set to the sides, so the middle is open sand; slots 6–7 are bonsai)
const ISL = { pond: ISL_ALL.filter(i => i[3] === 'both'), sand: ISL_ALL.filter(i => i[3] !== 'off'), lake: [] };
let ENV = 'pond';            // 'pond' | 'sand' | 'lake' — everything is built as 'pond', then setEnv() switches
let ISLANDS = ISL.pond;
const SHRUBS = [[-2.6, -6.3, 1.0], [0.9, -6.9, 1.25], [3.5, -6.1, 0.85], [-8.4, -5.2, 1.3], [-8.9, 1.2, 0.9], [-4.1, -7.4, 0.7], [8.0, 5.2, 0.8]];   // x, z, size
// places the sand tools cannot reach: under the bamboo (moss) and inside the shrubs
const BONSAI = [[-3.0, 1.6, 'pine', 0.5], [3.3, 1.9, 'maple', -2.2], [-1.4, -4.9, 'juniper', 2.6]];   // x, z, kind, facing
const sandBlocked = (x, z) => BONSAI.some(b => Math.hypot(x - b[0], z - b[1]) < 0.62) || (x > 0.7 && z < -7.2) || (x > 8.4 && z < 3.9) || (x < -9.2 && z > 6.3) || SHRUBS.some(s => Math.hypot(x - s[0], z - s[1]) < s[2] * 1.2);
const envObjs = { pond: [], sand: [] };   // objects that only exist in one environment

function mulberry32(a) {
  return function () {
    a |= 0; a = a + 0x6D2B79F5 | 0;
    let t = Math.imul(a ^ a >>> 15, 1 | a);
    t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
    return ((t ^ t >>> 14) >>> 0) / 4294967296;
  };
}
const rng = mulberry32(11);
const rand = (a, b) => a + rng() * (b - a);
const clamp = (x, a, b) => Math.min(b, Math.max(a, x));
const sstep = (a, b, x) => { const t = clamp((x - a) / (b - a), 0, 1); return t * t * (3 - 2 * t); };
const wrapPi = a => { while (a > Math.PI) a -= 2 * Math.PI; while (a < -Math.PI) a += 2 * Math.PI; return a; };

const fr = x => x - Math.floor(x);
const h2 = (x, y) => fr(Math.sin(x * 127.1 + y * 311.7) * 43758.5453);
const h3 = (x, y, z) => fr(Math.sin(x * 127.1 + y * 311.7 + z * 74.7) * 43758.5453);
function vn2(x, y) {
  const xi = Math.floor(x), yi = Math.floor(y); let fx = x - xi, fy = y - yi;
  fx = fx * fx * (3 - 2 * fx); fy = fy * fy * (3 - 2 * fy);
  const a = h2(xi, yi), b = h2(xi + 1, yi), c = h2(xi, yi + 1), d = h2(xi + 1, yi + 1);
  return a + (b - a) * fx + (c - a) * fy + (a - b - c + d) * fx * fy;
}
function fbm2(x, y, o = 4) { let s = 0, a = 0.5, n = 0; for (let i = 0; i < o; i++) { s += a * vn2(x, y); n += a; x = x * 2.03 + 17.3; y = y * 2.03 + 9.1; a *= 0.5; } return s / n; }
function vn3(x, y, z) {
  const xi = Math.floor(x), yi = Math.floor(y), zi = Math.floor(z); let fx = x - xi, fy = y - yi, fz = z - zi;
  fx = fx * fx * (3 - 2 * fx); fy = fy * fy * (3 - 2 * fy); fz = fz * fz * (3 - 2 * fz);
  const l = (a, b, t) => a + (b - a) * t;
  const a = l(l(h3(xi, yi, zi), h3(xi + 1, yi, zi), fx), l(h3(xi, yi + 1, zi), h3(xi + 1, yi + 1, zi), fx), fy);
  const b = l(l(h3(xi, yi, zi + 1), h3(xi + 1, yi, zi + 1), fx), l(h3(xi, yi + 1, zi + 1), h3(xi + 1, yi + 1, zi + 1), fx), fy);
  return l(a, b, fz);
}
function fbm3(x, y, z, o = 4) { let s = 0, a = 0.5, n = 0; for (let i = 0; i < o; i++) { s += a * vn3(x, y, z); n += a; x = x * 2.03 + 17.3; y = y * 2.03 + 9.1; z = z * 2.03 + 4.7; a *= 0.5; } return s / n; }

// Pond outline: a soft blob. Negative inside the water. Mirrored in GLSL (pondD).
const pondR = a => 3.5 + 0.5 * Math.sin(2 * a + 0.6) + 0.32 * Math.sin(3 * a + 2.1) + 0.16 * Math.sin(5 * a + 4.0);
function pondDist(x, z, env = ENV) { if (env !== 'pond') return 99; const qx = x * 0.8, qz = z * 1.15; return Math.hypot(qx, qz) - pondR(Math.atan2(qz, qx)); }
function pondPoint(a, off = 0) { const r = pondR(a) + off; return new V3(r * Math.cos(a) / 0.8, 0, r * Math.sin(a) / 1.15); }

function terrainH(x, z, env = ENV) {
  const d = pondDist(x, z, env);
  let y;
  if (d < 0) {
    y = -0.03 - 0.87 * sstep(0, 1.9, -d) + (fbm2(x * 1.7, z * 1.7) - 0.5) * 0.14 * sstep(0.2, 1.2, -d);
  } else {
    y = -0.03 + 0.15 * sstep(0, 0.45, d);
    y += 0.09 * sstep(0.08, 0.4, d) * (1 - sstep(0.55, 1.0, d)) * (0.4 + fbm2(x * 2.3 + 9, z * 2.3));
  }
  for (const [ix, iz, ir] of ISL[env]) y += 0.12 * (1 - sstep(ir * 0.3, ir + 0.35, Math.hypot(x - ix, z - iz)));
  return y;
}

// ───────────────────────────── renderer / scene / camera ─────────────────────────────
const canvas = document.getElementById('c');
const renderer = new THREE.WebGLRenderer({ canvas, antialias: false, powerPreference: 'high-performance' });
let PR = Math.min(window.devicePixelRatio || 1, 1.5);
renderer.setPixelRatio(PR);
renderer.setSize(innerWidth, innerHeight);
renderer.toneMapping = THREE.ACESFilmicToneMapping;
renderer.toneMappingExposure = 0.6;
renderer.shadowMap.enabled = true;
renderer.shadowMap.type = THREE.PCFSoftShadowMap;
renderer.shadowMap.autoUpdate = false;

const scene = new THREE.Scene();
scene.fog = new THREE.FogExp2(0xd0b090, 0.011);

const camera = new THREE.PerspectiveCamera(36, innerWidth / innerHeight, 0.1, 400);
camera.position.set(0.7, 2.05, 10.1);
camera.layers.enable(1);      // layer 1 = things floating on / above the water (kept out of the refraction pass)

const controls = new OrbitControls(camera, canvas);
controls.target.set(0, 0.62, -1.0);
controls.enableDamping = true; controls.dampingFactor = 0.06;
controls.enablePan = false;
controls.minDistance = 4.2; controls.maxDistance = 11;
controls.minPolarAngle = 0.32 * Math.PI; controls.maxPolarAngle = 0.492 * Math.PI;
controls.minAzimuthAngle = -1.25; controls.maxAzimuthAngle = 1.25;
controls.rotateSpeed = 0.45; controls.zoomSpeed = 0.6;
controls.update();
// the garden (pond + sand share it) and the lake are looked at from different places, through different lenses
const D2R = Math.PI / 180;
const VIEW = {
  garden: { pos: camera.position.clone(), tgt: controls.target.clone(), minD: 4.2, maxD: 11, minP: 0.32 * Math.PI, maxP: 0.492 * Math.PI, az: 1.25,
    near: 0.1, far: 400, fov: [36, 58], sunTgt: new V3(0, 0, 0), sunDist: 48, shBox: 15, shFar: 110 },
  lake: { pos: new V3(...LAKE_VIEW.pos), tgt: new V3(...LAKE_VIEW.tgt), minD: 17, maxD: 27, minP: 84 * D2R, maxP: 93.5 * D2R, az: 0.45,
    near: 0.4, far: 7000, fov: [54, 74], sunTgt: new V3(0, 0, 46), sunDist: 95, shBox: 30, shFar: 230 },
};
let viewKey = 'garden';
function applyView(key) {
  if (key !== viewKey) { VIEW[viewKey].pos.copy(camera.position); VIEW[viewKey].tgt.copy(controls.target); }      // each view is left as it was found
  viewKey = key; const v = VIEW[key];
  camera.position.copy(v.pos); controls.target.copy(v.tgt);
  controls.minDistance = v.minD; controls.maxDistance = v.maxD; controls.minPolarAngle = v.minP; controls.maxPolarAngle = v.maxP;
  controls.minAzimuthAngle = -v.az; controls.maxAzimuthAngle = v.az;
  camera.near = v.near; camera.far = v.far;
  waterMat.uniforms.uNear.value = v.near; waterMat.uniforms.uFar.value = v.far;
  Object.assign(sunLight.shadow.camera, { left: -v.shBox, right: v.shBox, top: v.shBox, bottom: -v.shBox, far: v.shFar });
  sunLight.shadow.camera.updateProjectionMatrix();
  resize(); controls.update();
}

// ───────────────────────────── shared uniforms & GLSL ─────────────────────────────
const U = {
  uTime: { value: 0 },
  uSim: { value: null },
  uSand: { value: null },
  uSimS: { value: S },
  uSandS: { value: SAND_S },
  uSunDirW: { value: new V3(0, 1, 0) },
  uSunCol: { value: new THREE.Color(1, 1, 1) },
  uIsl: { value: ISL_ALL.map(() => new V3(999, 999, 0.1)) },
  uPond: { value: 1 },
  uCaustK: { value: 110 },
};

const NOISE = /* glsl */`
float zh12(vec2 p){ vec3 p3=fract(vec3(p.xyx)*.1031); p3+=dot(p3,p3.yzx+33.33); return fract((p3.x+p3.y)*p3.z); }
float zh13(vec3 p3){ p3=fract(p3*.1031); p3+=dot(p3,p3.zyx+31.32); return fract((p3.x+p3.y)*p3.z); }
float zn2(vec2 p){ vec2 i=floor(p), f=fract(p); f=f*f*(3.-2.*f);
  return mix(mix(zh12(i),zh12(i+vec2(1.,0.)),f.x), mix(zh12(i+vec2(0.,1.)),zh12(i+vec2(1.,1.)),f.x), f.y); }
float zn3(vec3 p){ vec3 i=floor(p), f=fract(p); f=f*f*(3.-2.*f);
  float a=mix(mix(zh13(i),zh13(i+vec3(1.,0.,0.)),f.x), mix(zh13(i+vec3(0.,1.,0.)),zh13(i+vec3(1.,1.,0.)),f.x), f.y);
  float b=mix(mix(zh13(i+vec3(0.,0.,1.)),zh13(i+vec3(1.,0.,1.)),f.x), mix(zh13(i+vec3(0.,1.,1.)),zh13(i+vec3(1.,1.,1.)),f.x), f.y);
  return mix(a,b,f.z); }
vec2 zvor(vec2 p){ vec2 i=floor(p), f=fract(p); float md=8., id=0.;
  for(int y=-1;y<=1;y++) for(int x=-1;x<=1;x++){ vec2 g=vec2(float(x),float(y)); vec2 o=vec2(zh12(i+g), zh12(i+g+71.3));
    vec2 r=g+o-f; float d=dot(r,r); if(d<md){ md=d; id=zh12(i+g+13.7); } }
  return vec2(sqrt(md), id); }
float zfbm2(vec2 p){ float s=0.,a=.5; for(int i=0;i<4;i++){ s+=a*zn2(p); p=p*2.03+vec2(17.3,9.1); a*=.5; } return s/.9375; }
float zfbm3(vec3 p){ float s=0.,a=.5; for(int i=0;i<3;i++){ s+=a*zn3(p); p=p*2.03+vec3(17.3,9.1,4.7); a*=.5; } return s/.875; }
`;
const POND = /* glsl */`
uniform float uPond;
float pondD(vec2 p){ vec2 q=p*vec2(.8,1.15); float a=atan(q.y,q.x);
  float r=3.5+.5*sin(2.*a+.6)+.32*sin(3.*a+2.1)+.16*sin(5.*a+4.); return mix(99., length(q)-r, uPond); }
`;
const VERT_HEAD = /* glsl */`
uniform float uTime; uniform sampler2D uSim; uniform float uSimS;
vec2 zWind(vec2 root, float hh){ float ph=root.x*.35+root.y*.27;
  return vec2(sin(uTime*.7+ph)+.5*sin(uTime*1.31+ph*2.1), .7*cos(uTime*.53+ph*1.3))*.0032*hh*hh; }
`;
const FRAG_HEAD = /* glsl */`
varying vec3 vWPos; varying vec3 vWNrm;
uniform float uTime; uniform sampler2D uSim; uniform sampler2D uSand; uniform float uSimS; uniform float uSandS;
uniform vec3 uSunDirW; uniform vec3 uSunCol; uniform vec3 uIsl[9]; uniform float uCaustK;
${NOISE}
${POND}
vec3 zBump(vec3 N, vec3 p, float h){
  vec3 dpdx=dFdx(p), dpdy=dFdy(p); float dhx=dFdx(h), dhy=dFdy(h);
  vec3 r1=cross(dpdy,N), r2=cross(N,dpdx); float det=dot(dpdx,r1);
  vec3 g=sign(det)*(dhx*r1+dhy*r2);
  return normalize(abs(det)*N-g);
}
`;
const worldHook = (code, full) => `
vec4 wp = vec4(transformed, 1.0); vec4 ctr = vec4(0.0, 0.0, 0.0, 1.0);
#ifdef USE_INSTANCING
  wp = instanceMatrix * wp; ctr = instanceMatrix * ctr;
#endif
wp = modelMatrix * wp; ctr = modelMatrix * ctr;
${code}
${full ? `vWPos = wp.xyz;
{ vec3 wn_ = objectNormal;
#ifdef USE_INSTANCING
  wn_ = mat3(instanceMatrix) * wn_;
#endif
  vWNrm = normalize(mat3(modelMatrix) * wn_); }` : ''}
vec4 mvPosition = viewMatrix * wp;
gl_Position = projectionMatrix * mvPosition;
`;

let patchId = 0;
// Extends a built-in PBR material with procedural albedo / roughness / bump and vertex hooks, keeping lights + shadows.
function patch(mat, o = {}) {
  const key = o.key || ('zp' + (patchId++));
  mat.customProgramCacheKey = () => key;
  mat.onBeforeCompile = sh => {
    Object.assign(sh.uniforms, U, o.uniforms || {});
    sh.vertexShader = sh.vertexShader
      .replace('#include <common>', '#include <common>\n' + VERT_HEAD + 'varying vec3 vWPos; varying vec3 vWNrm;\n' + (o.vertPars || ''))
      .replace('#include <begin_vertex>', '#include <begin_vertex>\n' + (o.vert || ''))
      .replace('#include <project_vertex>', worldHook(o.world || '', true));
    sh.fragmentShader = sh.fragmentShader
      .replace('#include <common>', '#include <common>\n' + FRAG_HEAD + (o.fragPars || ''))
      .replace('#include <color_fragment>', '#include <color_fragment>\nfloat pH = 0.0; float pRough = roughness;\n' + (o.color || ''))
      .replace('#include <roughnessmap_fragment>', '#include <roughnessmap_fragment>\nroughnessFactor = clamp(pRough, 0.04, 1.0);')
      .replace('#include <normal_fragment_maps>', '#include <normal_fragment_maps>\n' + (o.color ? `normal = zBump(normal, -vViewPosition, pH * ${(o.bump ?? 1).toFixed(2)});` : ''))
      .replace('#include <lights_fragment_end>', '#include <lights_fragment_end>\n' + (o.afterLights || ''));
  };
  return mat;
}
function depthMat(world, vertPars = '', opts = {}) {
  const m = new THREE.MeshDepthMaterial({ depthPacking: THREE.RGBADepthPacking, ...opts });
  const key = 'zd' + (patchId++);
  m.customProgramCacheKey = () => key;
  m.onBeforeCompile = sh => {
    Object.assign(sh.uniforms, { uTime: U.uTime, uSim: U.uSim, uSimS: U.uSimS });
    sh.vertexShader = sh.vertexShader
      .replace('#include <common>', '#include <common>\n' + VERT_HEAD + vertPars)
      .replace('#include <project_vertex>', worldHook(world, false));
  };
  return m;
}

const CAUSTIC = /* glsl */`
if (vWPos.y < 0.0) {
  float dep_ = -vWPos.y;
  vec2 cp_ = vWPos.xz + uSunDirW.xz / max(uSunDirW.y, .25) * dep_ * .6;
  vec2 cuv_ = cp_ / (2. * uSimS) + .5; float e_ = 1.5 / ${SIM}.;
  float c0_ = texture2D(uSim, cuv_).r;
  float lap_ = texture2D(uSim, cuv_ + vec2(e_, 0.)).r + texture2D(uSim, cuv_ - vec2(e_, 0.)).r
             + texture2D(uSim, cuv_ + vec2(0., e_)).r + texture2D(uSim, cuv_ - vec2(0., e_)).r - 4. * c0_;
  float ca_ = 1. - lap_ * uCaustK * min(dep_ * 3., 1.);
  float a1_ = 1. - abs(zn2(cp_ * 2.6 + uTime * vec2(.21, .13)) * 2. - 1.);
  float a2_ = 1. - abs(zn2(cp_ * 3.7 - uTime * vec2(.17, .24) + 5.) * 2. - 1.);
  ca_ += (pow(a1_ * a2_, 3.) * 1.5 - .14) * smoothstep(0., .3, dep_);
  reflectedLight.directDiffuse *= clamp(ca_, .25, 3.5);
}
`;
const TRANSLUCENT = k => /* glsl */`
{ vec3 sv_ = normalize(mat3(viewMatrix) * uSunDirW);
  float tr_ = pow(saturate(dot(-normalize(vViewPosition), sv_)), 2.5) + .3 * saturate(dot(-normal, sv_));
  reflectedLight.directDiffuse += diffuseColor.rgb * uSunCol * tr_ * ${k.toFixed(3)}; }
`;
const FLOAT_HOOK = /* glsl */`
{ vec2 suv_ = ctr.xz / (2. * uSimS) + .5; float e_ = 3. / ${SIM}.;
  float h0_ = texture2D(uSim, suv_).r;
  vec2 g_ = vec2(texture2D(uSim, suv_ + vec2(e_, 0.)).r - texture2D(uSim, suv_ - vec2(e_, 0.)).r,
                 texture2D(uSim, suv_ + vec2(0., e_)).r - texture2D(uSim, suv_ - vec2(0., e_)).r) / (2. * e_ * 2. * uSimS);
  wp.y += (h0_ + dot(g_, wp.xz - ctr.xz)) * step(ctr.y, .08); }
`;

// ───────────────────────────── sky, sun, environment ─────────────────────────────
const sky = new Sky();
sky.scale.setScalar(1000);
sky.frustumCulled = false;
scene.add(sky);
const envScene = new THREE.Scene();
const skyEnv = new Sky(); skyEnv.material = sky.material; skyEnv.scale.setScalar(1000);
envScene.add(skyEnv);
const pmrem = new THREE.PMREMGenerator(renderer);
let envRT = null;

const sunDir = new V3();
const sunLight = new THREE.DirectionalLight(0xffffff, 4);
sunLight.castShadow = true;
sunLight.shadow.mapSize.set(4096, 4096);
Object.assign(sunLight.shadow.camera, { left: -15, right: 15, top: 15, bottom: -15, near: 1, far: 110 });
sunLight.shadow.bias = -0.0004; sunLight.shadow.normalBias = 0.035; sunLight.shadow.radius = 2.2;
scene.add(sunLight);

const lanternLight = new THREE.PointLight(0xffa24a, 3, 10, 2);
scene.add(lanternLight);
const windowMat = new THREE.MeshBasicMaterial({ color: 0xffffff });

const PRESETS = {
  morning: { elev: 30, theta: Math.PI - 0.95, sunCol: [1.0, 0.93, 0.83], sunI: 7.0, fog: [0.74, 0.80, 0.84], fogD: 0.020, exp: 0.52, envI: 0.8, lantern: 0.0, glow: 0.4, turb: 5, ray: 1.2, scatter: [0.020, 0.050, 0.038] },
  golden:  { elev: 17, theta: Math.PI + 0.62, sunCol: [1.0, 0.74, 0.47], sunI: 11.0, fog: [0.82, 0.66, 0.50], fogD: 0.017, exp: 0.5, envI: 0.7, lantern: 2.5, glow: 2.2, turb: 8, ray: 2.2, scatter: [0.026, 0.046, 0.026] },
  dusk:    { elev: 1.2, theta: Math.PI + 0.95, sunCol: [1.0, 0.45, 0.28], sunI: 0.5, fog: [0.42, 0.33, 0.38], fogD: 0.014, exp: 0.92, envI: 1.25, lantern: 16, glow: 7.0, turb: 10, ray: 3.0, scatter: [0.010, 0.016, 0.014] },
};
const cur = structuredClone(PRESETS.golden);
let tgt = null, todT = 1, todFrom = null, envDirty = 0;
const _lakeHaze = new THREE.Color(0.62, 0.74, 0.9);
let lake = null;                                      // the lake environment is built the first time it is visited
const todOf = { garden: 'golden', lake: 'morning' };      // the garden and the lake each keep their own time of day
let todName = 'golden';

function applySun(p, regenEnv = true) {
  // at the lake the sun stands higher and off to one side, so the peaks are modelled by light and shade
  const lakeOn = ENV === 'lake', elev = lakeOn ? p.elev * 1.3 + 2 : p.elev, theta = lakeOn ? (p.theta - Math.PI) * 1.42 : p.theta, V = VIEW[viewKey];
  sunDir.setFromSphericalCoords(1, THREE.MathUtils.degToRad(90 - elev), theta);
  const su = sky.material.uniforms;
  su.sunPosition.value.copy(sunDir); su.turbidity.value = lakeOn ? p.turb * 0.4 : p.turb; su.rayleigh.value = lakeOn ? p.ray * 1.8 : p.ray;      // thin, clear mountain air
  su.mieCoefficient.value = 0.006; su.mieDirectionalG.value = 0.82;
  sunLight.position.copy(sunDir).multiplyScalar(V.sunDist).add(V.sunTgt);
  sunLight.target.position.copy(V.sunTgt); sunLight.target.updateMatrixWorld();
  sunLight.color.setRGB(p.sunCol[0], p.sunCol[1], p.sunCol[2]); sunLight.intensity = p.sunI;
  U.uSunDirW.value.copy(sunDir);
  U.uSunCol.value.copy(sunLight.color).multiplyScalar(p.sunI);
  scene.fog.color.setRGB(p.fog[0], p.fog[1], p.fog[2]); scene.fog.density = p.fogD;
  if (lakeOn) { scene.fog.color.lerp(_lakeHaze, 0.45); scene.fog.density = p.fogD * 0.012; }      // mountain air: haze only over kilometres
  renderer.toneMappingExposure = p.exp;
  lanternLight.intensity = p.lantern;
  windowMat.color.setRGB(1.0 * p.glow, 0.55 * p.glow, 0.2 * p.glow);
  scene.environmentIntensity = p.envI;
  if (waterMat) {
    const wu = waterMat.uniforms;
    if (lakeOn) { wu.uScatter.value.set(0.016, 0.21, 0.205); wu.uAbsorb.value.set(1.1, 0.3, 0.34); wu.uFogCol.value.copy(scene.fog.color); wu.uFogD.value = scene.fog.density; }      // glacial rock-flour turquoise
    else { wu.uScatter.value.set(p.scatter[0], p.scatter[1], p.scatter[2]); wu.uAbsorb.value.set(2.1, 0.95, 1.5); wu.uFogD.value = 0; }
  }
  if (lake) lake.cloudMat.uniforms.uAmb.value.copy(scene.fog.color).multiplyScalar(0.85);
  if (regenEnv) {
    const old = envRT;
    envRT = pmrem.fromScene(envScene);
    scene.environment = envRT.texture;
    if (old) old.dispose();
  }
}
function setTimeOfDay(name, instant) {
  if (!PRESETS[name]) return;
  todName = name; todOf[viewKey] = name;
  if (instant) { Object.assign(cur, structuredClone(PRESETS[name])); tgt = null; todT = 1; applySun(cur); }
  else { todFrom = structuredClone(cur); tgt = PRESETS[name]; todT = 0; }
  document.querySelectorAll('#tod button').forEach(b => b.classList.toggle('on', b.dataset.tod === name));
}
function stepTimeOfDay(dt) {
  if (!tgt) return;
  todT = Math.min(1, todT + dt / 2.8);
  const k = todT * todT * (3 - 2 * todT);
  for (const key in tgt) {
    if (Array.isArray(tgt[key])) cur[key] = tgt[key].map((v, i) => todFrom[key][i] + (v - todFrom[key][i]) * k);
    else cur[key] = todFrom[key] + (tgt[key] - todFrom[key]) * k;
  }
  envDirty++;
  applySun(cur, todT >= 1 || envDirty % 5 === 0);
  if (todT >= 1) tgt = null;
}

// ───────────────────────────── water simulation (GPU heightfield) ─────────────────────────────
const fsCam = new THREE.OrthographicCamera(-1, 1, 1, -1, 0, 1);
const fsGeo = new THREE.PlaneGeometry(2, 2);
const FS_VERT = 'varying vec2 vUv; void main(){ vUv = uv; gl_Position = vec4(position.xy, 0.0, 1.0); }';
function fsPass(material) {
  const sc = new THREE.Scene(); sc.add(new THREE.Mesh(fsGeo, material));
  return target => { renderer.setRenderTarget(target); renderer.render(sc, fsCam); };
}
const rtOpts = { type: THREE.HalfFloatType, format: THREE.RGBAFormat, minFilter: THREE.LinearFilter, magFilter: THREE.LinearFilter, depthBuffer: false, stencilBuffer: false };
let simA = new THREE.WebGLRenderTarget(SIM, SIM, rtOpts), simB = new THREE.WebGLRenderTarget(SIM, SIM, rtOpts);
const MAXD = 8;
const simMat = new THREE.ShaderMaterial({
  uniforms: { tPrev: { value: null }, uDrops: { value: Array.from({ length: MAXD }, () => new THREE.Vector4()) }, uN: { value: 0 }, uS: { value: S }, uPond: U.uPond,
    uLake: { value: 0 }, uK: { value: 1 }, uDamp: { value: 0.9955 } },
  vertexShader: FS_VERT,
  fragmentShader: /* glsl */`
    precision highp float;
    uniform sampler2D tPrev; uniform vec4 uDrops[${MAXD}]; uniform int uN; uniform float uS, uLake, uK, uDamp; varying vec2 vUv;
    ${POND}
    ${LAKE_GLSL}
    float waterD(vec2 p){ return uLake > .5 ? lakeD(p) : pondD(p); }
    void main(){
      float e = 1. / ${SIM}.; float m = 2. * uS * e;
      vec2 P = (vUv - .5) * 2. * uS;
      if (waterD(P) > .05) { gl_FragColor = vec4(0.); return; }
      vec4 info = texture2D(tPrev, vUv);
      // banks reflect the waves (Neumann boundary)
      float hl = waterD(P - vec2(m, 0.)) > .05 ? info.r : texture2D(tPrev, vUv - vec2(e, 0.)).r;
      float hr = waterD(P + vec2(m, 0.)) > .05 ? info.r : texture2D(tPrev, vUv + vec2(e, 0.)).r;
      float hd = waterD(P - vec2(0., m)) > .05 ? info.r : texture2D(tPrev, vUv - vec2(0., e)).r;
      float hu = waterD(P + vec2(0., m)) > .05 ? info.r : texture2D(tPrev, vUv + vec2(0., e)).r;
      info.g += ((hl + hr + hd + hu) * .25 - info.r) * uK;
      info.g -= info.r * .0025;
      info.g *= uDamp;
      info.r += info.g;
      // the lake's patch of live water has open edges: waves reaching them die away instead of bouncing back
      float edge = min(min(vUv.x, 1. - vUv.x), min(vUv.y, 1. - vUv.y));
      info.rg *= mix(1., .86 + .14 * smoothstep(0., .07, edge), uLake);
      for (int i = 0; i < ${MAXD}; i++) { if (i >= uN) break;
        vec4 dr = uDrops[i]; float q = max(0., 1. - length(P - dr.xy) / dr.z);
        info.r += dr.w * (.5 - .5 * cos(q * 3.14159)); }
      gl_FragColor = info;
    }`,
});
const runSim = fsPass(simMat);
const dropQueue = [];
function addDrop(x, z, radius, strength) { if (dropQueue.length < 96) dropQueue.push(x, z, radius, strength); }
function stepSim() {
  const n = Math.min(MAXD, dropQueue.length / 4);
  for (let i = 0; i < n; i++) simMat.uniforms.uDrops.value[i].set(dropQueue[i * 4], dropQueue[i * 4 + 1], dropQueue[i * 4 + 2], dropQueue[i * 4 + 3]);
  dropQueue.splice(0, n * 4);
  simMat.uniforms.uN.value = n;
  simMat.uniforms.tPrev.value = simA.texture;
  runSim(simB);
  [simA, simB] = [simB, simA];
  U.uSim.value = simA.texture;
}
U.uSim.value = simA.texture;

// ───────────────────────────── sand surface (GPU): carved by whatever tool is dragged through it ─────────────────────────────
// r = groove height (0 valley … 1 ridge), g = how much this texel overrides the pristine pattern, b = freshly disturbed
// Tools: offs = where each tine / finger sits across the head (m), rG = furrow radius, foot = how much the head fills
// old furrows as it passes, depth = how deep it cuts. board = half-width of a flat blade that levels the sand.
const TOOLS = {
  rake:  { offs: [-0.24, -0.12, 0, 0.12, 0.24], rG: 0.03, foot: 0.8, depth: 1 },
  hand:  { offs: [-0.0825, -0.0275, 0.0275, 0.0825], rG: 0.02, foot: 0.45, depth: 0.85 },
  stick: { offs: [0], rG: 0.024, foot: 0.2, depth: 1 },
  board: { offs: [0], board: 0.3 },
};
const MAXT = 5;
let sandA = new THREE.WebGLRenderTarget(SAND_RES, SAND_RES, rtOpts), sandB = new THREE.WebGLRenderTarget(SAND_RES, SAND_RES, rtOpts);
const sandMat = new THREE.ShaderMaterial({
  uniforms: {
    tPrev: { value: null }, uMode: { value: 0 }, uFresh: { value: 0 }, uSeed: { value: 0 }, uSandS: { value: SAND_S },
    uN: { value: 5 }, uRG: { value: 0.03 }, uFoot: { value: 0.8 }, uDepth: { value: 1 }, uHalf: { value: 0.3 },
    uA: { value: Array.from({ length: MAXT }, () => new THREE.Vector2()) }, uB: { value: Array.from({ length: MAXT }, () => new THREE.Vector2()) },
    uIsl: U.uIsl, uPond: U.uPond,
  },
  vertexShader: FS_VERT,
  fragmentShader: /* glsl */`
    precision highp float;
    uniform sampler2D tPrev; uniform vec2 uA[${MAXT}], uB[${MAXT}];
    uniform float uMode, uFresh, uSeed, uSandS, uN, uRG, uFoot, uDepth, uHalf; uniform vec3 uIsl[9]; varying vec2 vUv;
    ${POND}
    float h12(vec2 p){ vec3 p3=fract(vec3(p.xyx)*.1031); p3+=dot(p3,p3.yzx+33.33); return fract((p3.x+p3.y)*p3.z); }
    // the gardener's original pattern (must match the terrain shader)
    float baseH(vec2 P){ float d = pondD(P), dIsl = 1e3;
      for (int i = 0; i < 9; i++) dIsl = min(dIsl, length(P - uIsl[i].xy) - uIsl[i].z);
      float df = min(d - 1.0, dIsl - .25); float c = df < 1.21 ? df : P.y;
      return .5 + .5 * cos(c * 6.28318 / .11); }
    void main(){
      vec4 prev = texture2D(tPrev, vUv);
      prev.b = max(0., prev.b - uFresh);
      if (uMode > 2.5) {              // levelling board: a flat blade wipes the sand smooth, spilling a little at each end
        vec2 P = (vUv - .5) * 2. * uSandS;
        vec2 ab = uB[0] - uA[0], ap = P - uA[0]; float L = length(ab);
        if (L > 1e-4) {
          vec2 dir = ab / L; float t = dot(ap, dir), sd = abs(dot(ap, vec2(-dir.y, dir.x)));
          if (t > -.04 && t < L + .002 && sd < uHalf + .06) {
            float eff = mix(baseH(P), prev.r, prev.g);
            float n = h12(floor(P * 85.) + uSeed) - .5;
            float lvl = 1. - smoothstep(uHalf - .025, uHalf, sd);
            float edge = smoothstep(uHalf - .03, uHalf, sd) * (1. - smoothstep(uHalf + .01, uHalf + .05, sd));
            prev.r = max(mix(eff, .5 + n * .07, lvl), edge * (.8 + n * .2));
            prev.g = max(prev.g, 1. - smoothstep(uHalf + .03, uHalf + .06, sd));
            prev.b = max(prev.b, lvl * .7);
          }
        }
      } else if (uMode > .5) {
        vec2 P = (vUv - .5) * 2. * uSandS;
        // dCap: distance to the tine's swept path (round ends) — where the furrow is cut.
        // dLat: sideways distance, only alongside the path — where sand is pushed aside. Keeping the heap off the
        // round ends stops each new step of the tool from burying the furrow it has just cut behind it.
        float dCap = 1e3, dLat = 1e3, rG = uRG;
        if (uMode > 1.5) {            // a press: dimple + concentric rings spreading from the touch point
          float dC = length(P - uA[0]);
          dCap = dLat = dC > .66 ? dC - .6 : abs(mod(dC + .06, .12) - .06);
        } else {
          for (int i = 0; i < ${MAXT}; i++) {
            if (float(i) >= uN) break;
            vec2 ab = uB[i] - uA[i], ap = P - uA[i]; float L = length(ab);
            if (L < 1e-4) { float d = length(ap); dCap = min(dCap, d); dLat = min(dLat, d); continue; }   // tool set down: a dent
            vec2 dir = ab / L; float t = dot(ap, dir), sd = abs(dot(ap, vec2(-dir.y, dir.x)));
            dCap = min(dCap, length(ap - dir * clamp(t, 0., L)));
            if (t > -.006 && t < L + .002) dLat = min(dLat, sd);
          }
        }
        if (min(dCap, dLat) < rG * 3.8) {
          float eff = mix(baseH(P), prev.r, prev.g);            // what the sand looks like right now
          float h = eff, w = 1. - smoothstep(rG, rG * 1.4, dCap);
          if (dLat < rG * 3.8) {
            float berm = smoothstep(rG * .8, rG * 1.6, dLat) * (1. - smoothstep(rG * 2., rG * 3., dLat));   // sand heaped beside the furrow
            float n = h12(floor(P * 85.) + uSeed) - .5;         // uneven, clumpy spill
            float foot = 1. - smoothstep(rG * 2., rG * 3., dLat);       // pushed sand fills the old furrows under the head
            h = max(mix(eff, .6, foot * uFoot), berm * (.9 + n * .2));
            w = max(w, 1. - smoothstep(rG * 2.8, rG * 3.6, dLat));
            prev.b = max(prev.b, 1. - smoothstep(rG * 1.7, rG * 3.3, dLat));
          }
          float groove = smoothstep(0., rG, dCap);              // the tine itself cuts down
          prev.r = min(h, 1. - uDepth + uDepth * groove * groove);
          prev.g = max(prev.g, w);
        }
      }
      gl_FragColor = prev;
    }`,
});
const runSand = fsPass(sandMat);
const sandQueue = [];     // { tool, a: Float32Array, b: Float32Array } path segments per tine, or { ring: [x, z] }
let sandIdle = 0, sandFreshAcc = 0;
function stepSand(dt) {
  sandFreshAcc += dt * 0.045;      // marks stay until "Reset sand"; only the damp, just-turned look fades (~20 s)
  if (!sandQueue.length && ++sandIdle % 4) return;
  const u = sandMat.uniforms; let n = 0;
  do {
    const s = sandQueue.shift();
    u.uMode.value = 0;
    if (s && s.ring) { u.uMode.value = 2; u.uRG.value = 0.03; u.uFoot.value = 0.8; u.uDepth.value = 1; u.uA.value[0].set(s.ring[0], s.ring[1]); }
    else if (s) {
      const T = TOOLS[s.tool], k = T.offs.length;
      u.uMode.value = T.board ? 3 : 1; u.uN.value = k;
      if (T.board) u.uHalf.value = T.board; else { u.uRG.value = T.rG; u.uFoot.value = T.foot; u.uDepth.value = T.depth; }
      for (let i = 0; i < k; i++) { u.uA.value[i].set(s.a[i * 2], s.a[i * 2 + 1]); u.uB.value[i].set(s.b[i * 2], s.b[i * 2 + 1]); }
    }
    u.uSeed.value = Math.random() * 100;
    u.uFresh.value = sandFreshAcc; sandFreshAcc = 0;
    u.tPrev.value = sandA.texture;
    runSand(sandB);
    [sandA, sandB] = [sandB, sandA];
  } while (sandQueue.length && ++n < 5);
  U.uSand.value = sandA.texture;
}
U.uSand.value = sandA.texture;
// back to the freshly raked garden
function resetSand() {
  sandQueue.length = 0;
  for (const rt of [sandA, sandB]) { renderer.setRenderTarget(rt); renderer.clear(); }
  renderer.setRenderTarget(null);
}

// ───────────────────────────── terrain: pond bed, mossy bank, raked gravel ─────────────────────────────
const TERRAIN_COLOR = /* glsl */`
  vec2 P = vWPos.xz; float vd = length(vViewPosition);
  float d = pondD(P);
  float nb = zfbm2(P * 1.9 + 3.1);
  float dIsl = 1e3;
  for (int i = 0; i < 9; i++) { dIsl = min(dIsl, length(P - uIsl[i].xy) - uIsl[i].z); }
  float mossM = max(1. - smoothstep(.62, .98, d + (nb - .5) * .55), 1. - smoothstep(.12, .42, dIsl + (nb - .5) * .3));
  float bam = max(step(.4, P.x) * (1. - smoothstep(-7.7, -7.1, P.y + (nb - .5) * 1.0)),
                  smoothstep(8.1, 8.7, P.x + (nb - .5) * 1.0) * (1. - smoothstep(3.6, 4.3, P.y)));
  mossM = max(mossM, bam);
  float bedM = 1. - smoothstep(-.10, .03, d + (nb - .5) * .08);
  float outM = smoothstep(12.1, 12.3, max(abs(P.x), abs(P.y)));

  // gravel + rake grooves
  float g1 = zn2(P * 150.), g2 = zn2(P * 67. + 7.);
  float gFade = 1. - smoothstep(4., 15., vd);
  vec3 gravel = mix(vec3(.36, .34, .30), vec3(.70, .67, .61), g1 * .55 + g2 * .45);
  gravel = mix(vec3(.53, .505, .455), gravel, .35 + .65 * gFade);
  gravel *= .88 + .24 * zfbm2(P * .55 + 11.);
  float df = min(d - 1.0, dIsl - .25);
  float coord = df < 1.21 ? df : P.y;
  float pitch = .11;
  float lfade = 1. - smoothstep(.16, .42, fwidth(coord) / pitch);
  float gr = .5 + .5 * cos(coord * 6.28318 / pitch);
  vec4 tr = texture2D(uSand, P / (2. * uSandS) + .5);
  float inS = step(abs(P.x), uSandS - .02) * step(abs(P.y), uSandS - .02);
  gr = mix(gr, tr.r, tr.g * inS);
  gr = smoothstep(0., 1., gr);
  float fresh = tr.b * inS;                        // just-turned sand: darker (damp underneath) and rougher
  float lf2 = max(lfade, tr.g * inS * (1. - smoothstep(6., 16., vd)));
  float hG = gr * .019 * lf2 + (g1 * .0035 + g2 * .003) * gFade + (g2 - .5) * .007 * fresh * gFade;
  gravel *= mix(1., .66 + .34 * gr, lf2);
  gravel *= 1. - .17 * fresh; gravel = mix(gravel, gravel * vec3(1.04, .99, .93), fresh);

  // moss
  float m1 = zfbm2(P * 7.), m2 = zn2(P * 95.);
  vec3 moss = mix(vec3(.050, .095, .018), vec3(.20, .30, .055), m1);
  moss *= .72 + .56 * m2;
  moss = mix(moss, vec3(.16, .13, .06), smoothstep(.62, .8, zfbm2(P * 2.6 + 40.)) * .35);
  float hM = m1 * .04 + m2 * .005 * gFade;

  // pond bed: silt + pebbles
  vec2 pv = zvor(P * 11.), pv2 = zvor(P * 27. + 5.); float pb2 = zfbm2(P * 4.5 + 2.);
  float peb = smoothstep(.5, .28, pv.x) * step(.42, pv.y), peb2 = smoothstep(.5, .25, pv2.x) * step(.5, pv2.y);
  vec3 bed = vec3(.075, .068, .045) * (.55 + .9 * pb2);
  bed = mix(bed, mix(vec3(.16, .15, .13), vec3(.42, .39, .33), pv2.y) * .8, peb2 * .8);
  bed = mix(bed, mix(vec3(.13, .125, .12), vec3(.46, .42, .35), fract(pv.y * 7.3)), peb);
  bed = mix(bed, vec3(.06, .09, .03), smoothstep(.55, .75, zfbm2(P * 3. + 30.)) * .5);
  float hB = peb * (1. - pv.x * pv.x * 3.) * .03 + peb2 * .008;

  vec3 col = mix(gravel, moss, mossM); float hh = mix(hG, hM, mossM); float rr = mix(.96, .9, mossM);
  col = mix(col, bed, bedM); hh = mix(hh, hB, bedM);
  col = mix(col, vec3(.045, .06, .025) * (.6 + .8 * nb), outM); hh *= 1. - outM;
  float wet = 1. - smoothstep(.0, .07, vWPos.y);
  col *= mix(1., .55, wet); rr = mix(rr, .3, wet * .85);
  diffuseColor.rgb = col; pH = hh; pRough = rr;
`;
const terrainMat = patch(new THREE.MeshStandardMaterial({ roughness: 0.95, metalness: 0 }), { color: TERRAIN_COLOR, bump: 1.3, afterLights: CAUSTIC });
{
  for (const env of ['pond', 'sand']) {
    const g = new THREE.PlaneGeometry(SAND_S * 2, SAND_S * 2, 460, 460);
    g.rotateX(-Math.PI / 2);
    const p = g.attributes.position;
    for (let i = 0; i < p.count; i++) p.setY(i, terrainH(p.getX(i), p.getZ(i), env));
    g.computeVertexNormals();
    const inner = new THREE.Mesh(g, terrainMat); inner.receiveShadow = true; scene.add(inner);
    envObjs[env].push(inner);
  }
  const sh = new THREE.Shape([new THREE.Vector2(-250, -250), new THREE.Vector2(250, -250), new THREE.Vector2(250, 250), new THREE.Vector2(-250, 250)]);
  const hs = SAND_S - 0.01;
  sh.holes.push(new THREE.Path([new THREE.Vector2(-hs, -hs), new THREE.Vector2(-hs, hs), new THREE.Vector2(hs, hs), new THREE.Vector2(hs, -hs)]));
  const og = new THREE.ShapeGeometry(sh); og.rotateX(-Math.PI / 2);
  const outer = new THREE.Mesh(og, terrainMat); outer.position.y = GRAVEL_Y; outer.receiveShadow = true; scene.add(outer);
}

// ───────────────────────────── rocks ─────────────────────────────
function makeRockGeo(seed, detail = 16) {
  let g = new THREE.IcosahedronGeometry(1, detail);
  g.deleteAttribute('normal'); g.deleteAttribute('uv');
  g = mergeVertices(g, 1e-4);
  const r = mulberry32(seed), cuts = [];
  for (let i = 0; i < 8; i++) {
    const d = new V3(r() * 2 - 1, (r() * 2 - 1) * 0.8, r() * 2 - 1).normalize();
    cuts.push([d, 0.5 + 0.32 * r()]);
  }
  const p = g.attributes.position, v = new V3();
  for (let i = 0; i < p.count; i++) {
    v.fromBufferAttribute(p, i);
    v.multiplyScalar(0.74 + 0.52 * fbm3(v.x * 1.3 + seed, v.y * 1.3, v.z * 1.3));
    for (const [d, off] of cuts) { const dd = v.dot(d) - off; if (dd > 0) v.addScaledVector(d, -dd * 0.86); }
    v.multiplyScalar(1 + (fbm3(v.x * 4.2 + seed * 3, v.y * 4.2, v.z * 4.2) - 0.5) * 0.13);
    p.setXYZ(i, v.x, v.y, v.z);
  }
  g.computeVertexNormals();
  return g;
}
const ROCK_COLOR = /* glsl */`
  vec3 q = vWPos;
  float n = zfbm3(q * 2.1), n2 = zfbm3(q * 9. + 4.), sp = zn3(q * 85.);
  vec3 base = mix(vec3(.12, .12, .125), vec3(.40, .385, .36), n);
  base *= .78 + .44 * n2;
  base = mix(base, base * 1.45, step(.8, sp) * .45);
  float cr = smoothstep(.016, .0, abs(zfbm3(q * 1.4 + 8.) - .5));
  base *= 1. - .28 * cr;
  float li = smoothstep(.6, .7, zfbm3(q * 3.3 + 20.));
  base = mix(base, vec3(.50, .51, .38), li * .4);
  float mm = smoothstep(.42, .78, vWNrm.y + (zfbm3(q * 4.5) - .5) * 1.0 - .12) * uMoss;
  vec3 mossc = mix(vec3(.045, .09, .015), vec3(.19, .29, .05), zfbm3(q * 15.));
  base = mix(base, mossc, mm);
  pH = n2 * .022 + sp * .0025 - cr * .008 + mm * zfbm3(q * 34.) * .014;
  float wet = 1. - smoothstep(.0, .08, vWPos.y);
  base *= mix(1., .48, wet);
  pRough = mix(mix(.82, .95, mm), .22, wet);
  diffuseColor.rgb = base;
`;
const rockMat = patch(new THREE.MeshStandardMaterial({ roughness: 0.85 }), { color: ROCK_COLOR, bump: 1.4, fragPars: 'uniform float uMoss;', uniforms: { uMoss: { value: 1 } }, afterLights: CAUSTIC });
const stoneMat = patch(new THREE.MeshStandardMaterial({ roughness: 0.85 }), { color: ROCK_COLOR, bump: 1.0, fragPars: 'uniform float uMoss;', uniforms: { uMoss: { value: 0.55 } } });
const rockGeos = [3, 17, 29, 41, 58, 73].map(makeRockGeo);
function addRock(x, z, s, o = {}) {
  const m = new THREE.Mesh(rockGeos[(rng() * rockGeos.length) | 0], rockMat);
  const sy = s * (o.sy ?? rand(0.5, 0.8));
  m.scale.set(s * rand(0.85, 1.25), sy, s * rand(0.85, 1.2));
  m.rotation.set(rand(-0.15, 0.15), rand(0, 6.28), rand(-0.12, 0.12));
  m.position.set(x, (o.y ?? terrainH(x, z)) + sy * (o.lift ?? 0.22), z);
  m.castShadow = m.receiveShadow = true;
  scene.add(m);
  if (o.env) envObjs[o.env].push(m);
  return m;
}
// stones edging the pond
for (let a = 0; a < Math.PI * 2;) {
  const big = rng() < 0.16;
  const s = big ? rand(0.5, 0.82) : rand(0.16, 0.36);
  if (rng() > 0.2) { const p = pondPoint(a, rand(0.0, 0.24) + (big ? 0.18 : 0)); addRock(p.x, p.z, s, { y: big ? -0.05 : undefined, env: 'pond' }); }
  a += (s * 1.15 + rand(0.02, 0.22)) / 4.2;
}
{ const p = pondPoint(1.32, -0.75); addRock(p.x, p.z, 0.55, { y: -0.3, sy: 0.5, lift: 0.5, env: 'pond' }); const p2 = pondPoint(1.18, -1.2); addRock(p2.x, p2.z, 0.26, { y: -0.2, sy: 0.24, lift: 0.5, env: 'pond' }); }
// island rock groups in the gravel
for (let i = 0; i < 3; i++) {
  const [ix, iz, ir] = ISLANDS[i];
  addRock(ix, iz, ir * 0.95, { sy: ir * rand(1.0, 1.35) / (ir * 0.95) * 0.8, lift: 0.35 });
  addRock(ix + ir * 0.9, iz + ir * 0.35, ir * 0.42);
  if (i !== 1) addRock(ix - ir * 0.75, iz + ir * 0.6, ir * 0.3);
}

// dry-garden stone groups (sand environment only): tall + low stones in odd-numbered clusters
{
  const R = (x, z, s, o = {}) => addRock(x, z, s, { y: terrainH(x, z, 'sand'), env: 'sand', ...o });
  R(-4.6, -1.6, 0.7, { sy: 1.35, lift: 0.36 }); R(-3.8, -1.15, 0.4, { sy: 0.6 }); R(-5.15, -0.95, 0.27);
  R(4.4, -1.2, 0.6, { sy: 0.66, lift: 0.3 }); R(4.95, -0.8, 0.3);
}

// ───────────────────────────── garden wall, far trees, hills ─────────────────────────────
const WALL_COLOR = /* glsl */`
  float s1_ = zfbm2(vec2(vWPos.x + vWPos.z, vWPos.y) * vec2(.7, 1.6));
  float s2_ = zfbm2(vec2((vWPos.x - vWPos.z) * 3., vWPos.y * .6) + 9.);
  vec3 c_ = mix(vec3(.56, .44, .29), vec3(.78, .68, .50), s1_);
  c_ = mix(c_, vec3(.36, .25, .16), smoothstep(.55, .8, s2_) * .5);
  c_ *= mix(.55, 1., smoothstep(.1, .7, vWPos.y));
  c_ *= mix(.7, 1., smoothstep(2.3, 1.9, vWPos.y));
  diffuseColor.rgb = c_; pH = zfbm2(vWPos.xy * 18. + vWPos.z * 18.) * .004; pRough = .93;
`;
const ROOF_COLOR = /* glsl */`
  float al_ = abs(vWNrm.x) > abs(vWNrm.z) ? vWPos.z : vWPos.x;
  float rib_ = .5 + .5 * cos(al_ * 6.28318 / .21);
  diffuseColor.rgb = vec3(.055, .058, .064) * (.7 + .5 * zfbm2(vWPos.xz * 3.)) * (.75 + .25 * rib_);
  pH = pow(rib_, .6) * .018; pRough = .55;
`;
{
  const wallMat = patch(new THREE.MeshStandardMaterial({ roughness: 0.93 }), { color: WALL_COLOR });
  const roofMat = patch(new THREE.MeshStandardMaterial({ roughness: 0.55 }), { color: ROOF_COLOR });
  const L = 24.6, H = 2.15, D = 12.15;
  const wg = new THREE.BoxGeometry(L, H, 0.32);
  const rg = new THREE.CylinderGeometry(0.52, 0.52, L + 0.5, 3, 1); rg.rotateZ(Math.PI / 2); rg.rotateX(Math.PI / 6); rg.scale(1, 0.55, 1);
  for (let i = 0; i < 4; i++) {
    const grp = new THREE.Group();
    const w = new THREE.Mesh(wg, wallMat); w.position.y = H / 2 + 0.05; w.castShadow = w.receiveShadow = true;
    const r = new THREE.Mesh(rg, roofMat); r.position.y = H + 0.2; r.castShadow = r.receiveShadow = true;
    grp.add(w, r);
    grp.position.set(Math.sin(i * Math.PI / 2) * D, 0, -Math.cos(i * Math.PI / 2) * D);
    grp.rotation.y = -i * Math.PI / 2;
    scene.add(grp);
  }
}
const FOLIAGE_COLOR = /* glsl */`
  float n_ = zfbm3(vWPos * 3.2), n2_ = zn3(vWPos * 24.);
  diffuseColor.rgb *= mix(vec3(.25, .4, .2), vec3(1.), n_) * (.65 + .7 * n2_);
  pH = n_ * .12 + n2_ * .03; pRough = .82;
`;
const foliageMat = patch(new THREE.MeshStandardMaterial({ roughness: 0.82 }), { color: FOLIAGE_COLOR, afterLights: TRANSLUCENT(0.03) });
{
  // rounded shrubs inside the garden
  let sg = new THREE.IcosahedronGeometry(1, 10); sg.deleteAttribute('normal'); sg.deleteAttribute('uv'); sg = mergeVertices(sg, 1e-4);
  const p = sg.attributes.position, v = new V3();
  for (let i = 0; i < p.count; i++) { v.fromBufferAttribute(p, i); v.multiplyScalar(0.82 + 0.36 * fbm3(v.x * 1.6 + 5, v.y * 1.6, v.z * 1.6) + 0.06 * fbm3(v.x * 9, v.y * 9, v.z * 9)); p.setXYZ(i, v.x, v.y, v.z); }
  sg.computeVertexNormals();
  const shrubs = SHRUBS;
  const sm = new THREE.InstancedMesh(sg, foliageMat, shrubs.length);
  const m4 = new THREE.Matrix4(), q = new THREE.Quaternion(), c = new THREE.Color();
  shrubs.forEach(([x, z, s], i) => {
    m4.compose(new V3(x, GRAVEL_Y + s * 0.28, z), q.setFromEuler(new THREE.Euler(0, rng() * 6, 0)), new V3(s * 1.15, s * 0.72, s * 1.1));
    sm.setMatrixAt(i, m4); sm.setColorAt(i, c.setRGB(rand(0.07, 0.11), rand(0.17, 0.24), rand(0.04, 0.06)));
  });
  sm.castShadow = sm.receiveShadow = true; scene.add(sm);

  // forest beyond the wall
  let cg = new THREE.ConeGeometry(1, 2.6, 11, 7); cg.translate(0, 1.3, 0); cg.deleteAttribute('normal'); cg.deleteAttribute('uv'); cg = mergeVertices(cg, 1e-4);
  const cp = cg.attributes.position;
  for (let i = 0; i < cp.count; i++) { v.fromBufferAttribute(cp, i); const k = 0.8 + 0.5 * fbm3(v.x * 2.2, v.y * 2.2, v.z * 2.2); cp.setXYZ(i, v.x * k, v.y, v.z * k); }
  cg.computeVertexNormals();
  const lumps = [];
  for (let i = 0; i < 9; i++) {
    let lg = new THREE.IcosahedronGeometry(rand(0.42, 0.7), 6); lg.deleteAttribute('normal'); lg.deleteAttribute('uv'); lg = mergeVertices(lg, 1e-4);
    const lp = lg.attributes.position, ox = rand(-0.62, 0.62), oy = rand(-0.3, 0.5), oz = rand(-0.62, 0.62);
    for (let j = 0; j < lp.count; j++) { v.fromBufferAttribute(lp, j); v.multiplyScalar(0.78 + 0.5 * fbm3(v.x * 3 + i * 7, v.y * 3, v.z * 3)); lp.setXYZ(j, v.x + ox, v.y + oy, v.z + oz); }
    lg.computeVertexNormals(); lumps.push(lg);
  }
  const crownGeo = mergeGeometries(lumps);
  const farMat = patch(new THREE.MeshStandardMaterial({ roughness: 0.9 }), { color: `
    float n_ = zfbm3(vWPos * 1.1), n2_ = zfbm3(vWPos * 5.);
    diffuseColor.rgb *= (.4 + .75 * n_) * (.55 + .8 * n2_);
    pH = n_ * .3 + n2_ * .1; pRough = .95;`, afterLights: TRANSLUCENT(0.02) });
  const N = 170;
  const cones = new THREE.InstancedMesh(cg, farMat, N), blobs = new THREE.InstancedMesh(crownGeo, farMat, N);
  for (let i = 0; i < N; i++) {
    for (const [mesh, tall] of [[cones, true], [blobs, false]]) {
      const a = rng() * Math.PI * 2, rad = rand(18, 44);
      const x = Math.cos(a) * rad, z = Math.sin(a) * rad;
      const h = tall ? rand(7, 14) : rand(2.0, 3.6);
      if (tall) m4.compose(new V3(x, 0, z), q.identity(), new V3(h * 0.22, h / 2.6, h * 0.22));
      else m4.compose(new V3(x, rand(3.2, 6.5), z), q.setFromEuler(new THREE.Euler(0, rng() * 6, 0)), new V3(h * 1.15, h, h * 1.15));
      mesh.setMatrixAt(i, m4);
      mesh.setColorAt(i, tall ? c.setRGB(rand(0.02, 0.035), rand(0.055, 0.085), rand(0.025, 0.04)) : c.setRGB(rand(0.045, 0.09), rand(0.10, 0.15), rand(0.02, 0.035)));
    }
  }
  cones.receiveShadow = blobs.receiveShadow = false;
  scene.add(cones, blobs);

  // hazy hills
  const hp = [], hi = [], M = 160, R = 150;
  for (let i = 0; i <= M; i++) { const a = i / M * Math.PI * 2; const top = 10 + 34 * fbm2(Math.cos(a) * 2.2 + 5, Math.sin(a) * 2.2 + 5); hp.push(Math.cos(a) * R, -2, Math.sin(a) * R, Math.cos(a) * R, top, Math.sin(a) * R); }
  for (let i = 0; i < M; i++) { const a = i * 2; hi.push(a, a + 1, a + 2, a + 1, a + 3, a + 2); }
  const hg = new THREE.BufferGeometry(); hg.setAttribute('position', new THREE.Float32BufferAttribute(hp, 3)); hg.setIndex(hi);
  scene.add(new THREE.Mesh(hg, new THREE.MeshBasicMaterial({ color: 0x1c2a26, side: THREE.DoubleSide })));
}

// ───────────────────────────── stone lantern (yukimi-dōrō) ─────────────────────────────
let lanternGroup; const lanternPos = {};
{
  const lp = pondPoint(-0.62, 0.62);
  const g = new THREE.Group();
  const add = (geo, y, mat = stoneMat) => { const m = new THREE.Mesh(geo, mat); m.position.y = y; m.castShadow = m.receiveShadow = true; g.add(m); return m; };
  for (let i = 0; i < 4; i++) {
    const a = i * Math.PI / 2 + Math.PI / 4;
    const leg = add(new THREE.BoxGeometry(0.075, 0.46, 0.075), 0.2);
    leg.position.x = Math.cos(a) * 0.23; leg.position.z = Math.sin(a) * 0.23;
    leg.rotation.set(Math.sin(a) * 0.3, 0, -Math.cos(a) * 0.3);
  }
  add(new THREE.CylinderGeometry(0.34, 0.3, 0.07, 6), 0.45);
  add(new THREE.CylinderGeometry(0.2, 0.2, 0.26, 6), 0.61);
  for (let i = 0; i < 6; i++) {
    const a = i * Math.PI / 3 + Math.PI / 6;
    const w = new THREE.Mesh(new THREE.PlaneGeometry(0.115, 0.15), windowMat);
    w.position.set(Math.sin(a) * 0.176, 0.61, Math.cos(a) * 0.176); w.rotation.y = a; g.add(w);
  }
  const prof = [[0.001, 0.3], [0.07, 0.27], [0.16, 0.17], [0.34, 0.07], [0.56, 0.0], [0.55, -0.035], [0.001, -0.035]].map(p => new THREE.Vector2(p[0], p[1]));
  const roof = add(new THREE.LatheGeometry(prof, 6), 0.775); roof.geometry.computeVertexNormals();
  add(new THREE.SphereGeometry(0.065, 12, 10), 1.11);
  g.position.set(lp.x, terrainH(lp.x, lp.z) - 0.02, lp.z);
  g.rotation.y = 0.4;
  scene.add(g);
  lanternLight.position.set(lp.x, g.position.y + 0.62, lp.z);
  lanternGroup = g; lanternPos.pond = g.position.clone();
  lanternPos.sand = new V3(ISL_ALL[8][0], terrainH(ISL_ALL[8][0], ISL_ALL[8][1], 'sand') - 0.02, ISL_ALL[8][1]);
}

// ───────────────────────────── bamboo grove ─────────────────────────────
const BAMBOO_GROUND = 0.1;
{
  const STALK_COLOR = /* glsl */`
    float hh_ = vWPos.y - ${BAMBOO_GROUND.toFixed(2)}; float nd_ = fract(hh_ / .36);
    float ring_ = 1. - smoothstep(0., .035, min(nd_, 1. - nd_));
    diffuseColor.rgb *= mix(1., .4, ring_);
    diffuseColor.rgb += vec3(.10, .11, .08) * smoothstep(.82, .96, nd_);
    diffuseColor.rgb *= .85 + .3 * zn2(vec2(vWPos.x * 40. + vWPos.z * 40., hh_ * 2.));
    pH = -ring_ * .004; pRough = .36;
  `;
  const stalkHook = 'wp.xz += zWind(ctr.xz, max(wp.y - ctr.y, 0.));';
  const leafHook = /* glsl */`wp.xz += zWind(aRoot.xz, aRoot.y);
    wp.y += sin(uTime * 2.6 + ctr.x * 9. + ctr.z * 7.) * length(wp.xyz - ctr.xyz) * .12 * aRoot.w;`;
  const stalkMat = patch(new THREE.MeshStandardMaterial({ roughness: 0.36 }), { color: STALK_COLOR, world: stalkHook });
  const leafMat = patch(new THREE.MeshStandardMaterial({ roughness: 0.5, side: THREE.DoubleSide }), { vertPars: 'attribute vec4 aRoot;', world: leafHook, afterLights: TRANSLUCENT(0.11) });
  const stalkDepth = depthMat(stalkHook), leafDepth = depthMat(leafHook, 'attribute vec4 aRoot;');

  const stalkGeo = new THREE.CylinderGeometry(0.55, 1, 1, 8, 14, true); stalkGeo.translate(0, 0.5, 0);
  const twigGeo = new THREE.CylinderGeometry(0.4, 1, 1, 4, 1, true); twigGeo.translate(0, 0.5, 0);
  // lanceolate leaf: base at origin, length +y
  const prof = [0, 0.55, 1, 0.85, 0.5, 0], lp = [], li = [];
  prof.forEach((w, i) => { const t = i / (prof.length - 1), dz = -0.14 * t * t; lp.push(-w / 2, t, dz, 0, t, dz + w * 0.12, w / 2, t, dz); });
  for (let i = 0; i < prof.length - 1; i++) { const a = i * 3; li.push(a, a + 1, a + 4, a, a + 4, a + 3, a + 1, a + 2, a + 5, a + 1, a + 5, a + 4); }
  const leafGeo = new THREE.BufferGeometry(); leafGeo.setAttribute('position', new THREE.Float32BufferAttribute(lp, 3)); leafGeo.setIndex(li); leafGeo.computeVertexNormals();

  const stalks = [];
  const put = (x, z) => stalks.push({ x, z, h: rand(4.6, 7.6), r: rand(0.026, 0.048) });
  for (let i = 0; i < 74; i++) put(rand(0.8, 11.4), rand(-11.5, -7.7));
  for (let i = 0; i < 34; i++) put(rand(8.7, 11.4), rand(-7.7, 3.6));
  for (let i = 0; i < 14; i++) put(rand(-11.4, -9.3), rand(6.5, 11.4));

  const CL = 12, LV = 9;
  const stalkMesh = new THREE.InstancedMesh(stalkGeo, stalkMat, stalks.length);
  const twigMesh = new THREE.InstancedMesh(twigGeo, leafMat, stalks.length * CL);
  const leafMesh = new THREE.InstancedMesh(leafGeo, leafMat, stalks.length * CL * LV);
  const twigRoot = new Float32Array(stalks.length * CL * 4), leafRoot = new Float32Array(stalks.length * CL * LV * 4);
  const m4 = new THREE.Matrix4(), q = new THREE.Quaternion(), q2 = new THREE.Quaternion(), c = new THREE.Color(), up = new V3(0, 1, 0), dir = new V3(), pos = new V3();
  let ti = 0, lfi = 0;
  stalks.forEach((s, i) => {
    q.setFromEuler(new THREE.Euler(rand(-0.04, 0.04), rng() * 6, rand(-0.04, 0.04)));
    m4.compose(new V3(s.x, BAMBOO_GROUND, s.z), q, new V3(s.r, s.h, s.r));
    stalkMesh.setMatrixAt(i, m4);
    const yel = rng();
    stalkMesh.setColorAt(i, c.setRGB(0.16 + yel * 0.22, 0.27 + yel * 0.13, 0.07 + yel * 0.03));
    for (let k = 0; k < CL; k++) {
      const hy = s.h * (0.42 + 0.58 * (k + rng()) / CL);
      const az = rng() * Math.PI * 2, len = rand(0.45, 1.0) * (1.15 - hy / s.h * 0.5);
      dir.set(Math.cos(az), rand(0.25, 0.75), Math.sin(az)).normalize();
      pos.set(s.x, BAMBOO_GROUND + hy, s.z);
      q.setFromUnitVectors(up, dir);
      m4.compose(pos, q, new V3(0.006, len, 0.006));
      twigMesh.setMatrixAt(ti, m4); twigMesh.setColorAt(ti, c.setRGB(0.2, 0.24, 0.08));
      twigRoot.set([s.x, hy, s.z, 0], ti * 4); ti++;
      for (let l = 0; l < LV; l++) {
        const t = 0.35 + 0.65 * rng();
        const lpz = pos.clone().addScaledVector(dir, len * t);
        const a2 = az + rand(-1.3, 1.3);
        const ld = new V3(Math.cos(a2), rand(-0.75, 0.05), Math.sin(a2)).normalize();
        q.setFromUnitVectors(up, ld); q2.setFromAxisAngle(up, rng() * 6.28); q.multiply(q2);
        const ll = rand(0.15, 0.25);
        m4.compose(lpz, q, new V3(ll * 0.17, ll, ll * 0.17));
        leafMesh.setMatrixAt(lfi, m4);
        const g = rng();
        leafMesh.setColorAt(lfi, c.setRGB(0.10 + g * 0.14, 0.22 + g * 0.17, 0.045 + g * 0.05));
        leafRoot.set([s.x, hy, s.z, 1], lfi * 4); lfi++;
      }
    }
  });
  twigGeo.setAttribute('aRoot', new THREE.InstancedBufferAttribute(twigRoot, 4));
  leafGeo.setAttribute('aRoot', new THREE.InstancedBufferAttribute(leafRoot, 4));
  stalkMesh.customDepthMaterial = stalkDepth; twigMesh.customDepthMaterial = leafDepth; leafMesh.customDepthMaterial = leafDepth;
  for (const m of [stalkMesh, twigMesh, leafMesh]) { m.castShadow = m.receiveShadow = true; m.frustumCulled = false; scene.add(m); }
}

// ───────────────────────────── Japanese maple ─────────────────────────────
function leafTexture() {
  const c = document.createElement('canvas'); c.width = c.height = 128; const g = c.getContext('2d');
  g.translate(64, 76);
  const lobes = [[0, 60], [0.72, 52], [-0.72, 52], [1.42, 40], [-1.42, 40], [2.15, 22], [-2.15, 22]];
  g.fillStyle = '#fff';
  for (const [a, L] of lobes) {
    g.save(); g.rotate(a); g.beginPath(); g.moveTo(0, 5);
    g.bezierCurveTo(L * 0.33, -L * 0.3, L * 0.14, -L * 0.75, 0, -L);
    g.bezierCurveTo(-L * 0.14, -L * 0.75, -L * 0.33, -L * 0.3, 0, 5); g.fill(); g.restore();
  }
  g.fillRect(-2, 0, 4, 44);
  g.strokeStyle = 'rgba(0,0,0,.22)'; g.lineWidth = 1.5;
  for (const [a, L] of lobes) { g.save(); g.rotate(a); g.beginPath(); g.moveTo(0, 0); g.lineTo(0, -L * 0.9); g.stroke(); g.restore(); }
  const t = new THREE.CanvasTexture(c); t.colorSpace = THREE.SRGBColorSpace; t.anisotropy = 4; return t;
}
const leafTex = leafTexture();
const leafPlane = new THREE.PlaneGeometry(1, 1); leafPlane.rotateX(-Math.PI / 2);
const MAPLE_BASE = new V3(ISLANDS[3][0], 0, ISLANDS[3][1]);
const mapleTips = [];
const leafColor = (c, r = rng()) => r < 0.5 ? c.setRGB(rand(0.42, 0.62), rand(0.025, 0.06), rand(0.015, 0.035)) : r < 0.86 ? c.setRGB(rand(0.62, 0.8), rand(0.13, 0.26), rand(0.02, 0.04)) : c.setRGB(rand(0.75, 0.85), rand(0.38, 0.5), rand(0.04, 0.07));
{
  const geos = [], up = new V3(0, 1, 0);
  const seg = (p, q, r0, r1) => {
    const d = q.clone().sub(p), len = d.length();
    const g = new THREE.CylinderGeometry(r1, r0, len * 1.08, 7, 1, true); g.translate(0, len / 2, 0);
    g.applyMatrix4(new THREE.Matrix4().compose(p, new THREE.Quaternion().setFromUnitVectors(up, d.normalize()), new V3(1, 1, 1)));
    geos.push(g);
  };
  const grow = (p0, dir, len, rad, depth) => {
    let p = p0.clone(); const d = dir.clone(), n = 3;
    for (let i = 0; i < n; i++) {
      d.x += rand(-0.17, 0.17); d.z += rand(-0.17, 0.17); d.y += rand(-0.1, 0.1) + (depth >= 2 ? -0.05 : 0.03); d.normalize();
      const q = p.clone().addScaledVector(d, len / n);
      seg(p, q, rad * (1 - 0.3 * i / n), rad * (1 - 0.3 * (i + 1) / n)); p = q;
      if (depth >= 3) mapleTips.push(q.clone());
    }
    if (depth >= 5) return;
    const k = depth === 0 ? 3 : (rng() < 0.45 ? 3 : 2), a0 = rng() * 6.28;
    for (let j = 0; j < k; j++) {
      const a = a0 + j * 6.28 / k + rand(-0.5, 0.5), spread = depth === 0 ? 0.8 : rand(0.5, 0.95);
      const nd = d.clone().multiplyScalar(1 - spread * 0.55).add(new V3(Math.cos(a) * spread, rand(-0.05, 0.3) * (depth < 2 ? 1.6 : 1), Math.sin(a) * spread)).normalize();
      grow(p, nd, len * rand(0.68, 0.82), rad * 0.62, depth + 1);
    }
  };
  const base = MAPLE_BASE.clone(); base.y = terrainH(base.x, base.z) - 0.1;
  grow(base, new V3(0.36, 1, 0.2).normalize(), 1.55, 0.19, 0);
  const BARK = /* glsl */`
    float b1_ = zfbm3(vWPos * vec3(14., 3., 14.)), b2_ = zfbm3(vWPos * 40.);
    diffuseColor.rgb = mix(vec3(.045, .036, .03), vec3(.20, .17, .145), b1_) * (.75 + .5 * b2_);
    float mo_ = smoothstep(.55, .75, zfbm3(vWPos * 5. + 3.)) * smoothstep(1.6, .2, vWPos.y);
    diffuseColor.rgb = mix(diffuseColor.rgb, vec3(.07, .12, .025), mo_ * .7);
    pH = b1_ * .012 + b2_ * .003; pRough = .9;
  `;
  const trunk = new THREE.Mesh(mergeGeometries(geos), patch(new THREE.MeshStandardMaterial({ roughness: 0.9 }), { color: BARK, bump: 1.5 }));
  trunk.castShadow = trunk.receiveShadow = true; scene.add(trunk);

  const mapleHook = /* glsl */`{ float ph_ = ctr.x * 3.1 + ctr.z * 2.3 + ctr.y * 1.7;
    wp.xyz += vec3(sin(uTime * 1.3 + ph_), .6 * sin(uTime * 2.1 + ph_ * 1.7), cos(uTime * 1.1 + ph_ * .8)) * .013; }`;
  const mapleMat = patch(new THREE.MeshStandardMaterial({ map: leafTex, alphaTest: 0.3, side: THREE.DoubleSide, roughness: 0.55 }), { world: mapleHook, afterLights: TRANSLUCENT(0.2) });
  const PER = 10, N = mapleTips.length * PER;
  const leaves = new THREE.InstancedMesh(leafPlane, mapleMat, N);
  const m4 = new THREE.Matrix4(), q = new THREE.Quaternion(), c = new THREE.Color(), e = new THREE.Euler();
  let i = 0;
  for (const t of mapleTips) for (let k = 0; k < PER; k++) {
    const s = rand(0.1, 0.16);
    q.setFromEuler(e.set(rand(-0.6, 0.6), rng() * 6.28, rand(-0.6, 0.6)));
    m4.compose(new V3(t.x + rand(-0.3, 0.3), t.y + rand(-0.14, 0.16), t.z + rand(-0.3, 0.3)), q, new V3(s, s, s));
    leaves.setMatrixAt(i, m4); leaves.setColorAt(i, leafColor(c)); i++;
  }
  leaves.customDepthMaterial = depthMat(mapleHook, '', { map: leafTex, alphaTest: 0.3 });
  leaves.castShadow = leaves.receiveShadow = true; leaves.frustumCulled = false;
  scene.add(leaves);

  // fallen leaves resting on the ground
  const groundMat = new THREE.MeshStandardMaterial({ map: leafTex, alphaTest: 0.3, side: THREE.DoubleSide, roughness: 0.6 });
  for (const env of ['pond', 'sand']) {
    const gm = new THREE.InstancedMesh(leafPlane, groundMat, 170);
    let n = 0, guard = 0;
    while (n < 170 && guard++ < 4000) {
      const t = mapleTips[(rng() * mapleTips.length) | 0];
      const x = t.x + rand(-1.6, 1.6), z = t.z + rand(-1.6, 1.6);
      if (pondDist(x, z, env) < 0.12 || Math.abs(x) > 11.5 || Math.abs(z) > 11.5) continue;
      const s = rand(0.1, 0.15);
      q.setFromEuler(e.set(rand(-0.25, 0.25), rng() * 6.28, rand(-0.25, 0.25)));
      m4.compose(new V3(x, terrainH(x, z, env) + 0.022, z), q, new V3(s, s, s));
      gm.setMatrixAt(n, m4); gm.setColorAt(n, leafColor(c)); n++;
    }
    gm.count = n; gm.receiveShadow = true; scene.add(gm); envObjs[env].push(gm);
  }
}

// ───────────────────────────── bonsai (sand garden) ─────────────────────────────
// Three potted trees on low display stands: an S-curved pine and a slanting juniper with layered foliage pads,
// and a small maple in autumn colour. Trunks are swept tubes with a flared root base; foliage is a soft core
// plus hundreds of little needle fans (or leaves) so the silhouette is feathery, not blobby.
{
  const V = (x, y, z) => new V3(x, y, z);
  const barkMat = patch(new THREE.MeshStandardMaterial({ roughness: 0.92, side: THREE.DoubleSide }), { color: `
    float b1_ = zfbm3(vWPos * vec3(55., 16., 55.)), b2_ = zfbm3(vWPos * 170.);
    diffuseColor.rgb = mix(vec3(.045, .032, .026), vec3(.27, .21, .165), b1_) * (.7 + .6 * b2_);
    pH = b1_ * .004 + b2_ * .0012; pRough = .93;`, bump: 1.6 });
  const padCode = `
    float n_ = zfbm3(vWPos * 42.), n2_ = zn3(vWPos * 260.);
    diffuseColor.rgb *= (.4 + .85 * n_) * (.6 + .7 * n2_);
    pH = n_ * .012 + n2_ * .004; pRough = .82;`;
  const soilMat = patch(new THREE.MeshStandardMaterial({ roughness: 0.95 }), { color: `
    float m_ = zfbm2(vWPos.xz * 28.), g_ = zn2(vWPos.xz * 320.);
    diffuseColor.rgb = mix(vec3(.05, .035, .022), vec3(.09, .16, .03), smoothstep(.38, .6, m_)) * (.65 + .7 * g_);
    pH = m_ * .008 + g_ * .0015; pRough = .96;`, bump: 1.4 });
  const standMat = new THREE.MeshStandardMaterial({ color: 0x24160d, roughness: 0.5 });

  // a tube swept along a curve, tapering from r0 to r1, with an optional flare at the root
  function tube(pts, r0, r1, flare = 0, sides = 8) {
    const curve = new THREE.CatmullRomCurve3(pts), N = Math.max(10, (pts.length - 1) * 8), pos = [], idx = [];
    const P = new V3(), T = new V3(), A = new V3(), B = new V3();
    for (let i = 0; i <= N; i++) {
      const t = i / N; curve.getPoint(t, P); curve.getTangent(t, T);
      const alongX = Math.abs(T.x) > 0.75;
      A.set(alongX ? 0 : 1, 0, alongX ? 1 : 0).cross(T).normalize(); B.crossVectors(T, A).normalize();
      const r = (r0 + (r1 - r0) * Math.pow(t, 0.8)) * (1 + flare * Math.exp(-t * 16));
      for (let j = 0; j < sides; j++) {
        const a = j / sides * 6.2832, k = r * (1 + 0.14 * Math.sin(a * 3 + t * 11) + 0.08 * Math.sin(a * 5 - t * 7));
        const ca = Math.cos(a) * k, sa = Math.sin(a) * k;
        pos.push(P.x + A.x * ca + B.x * sa, P.y + A.y * ca + B.y * sa, P.z + A.z * ca + B.z * sa);
      }
    }
    for (let i = 0; i < N; i++) for (let j = 0; j < sides; j++) { const a = i * sides + j, b = i * sides + (j + 1) % sides; idx.push(a, a + sides, b, b, a + sides, b + sides); }
    const g = new THREE.BufferGeometry(); g.setAttribute('position', new THREE.Float32BufferAttribute(pos, 3)); g.setIndex(idx); g.computeVertexNormals();
    return g;
  }
  function skeleton(kind) {
    const maple = kind === 'maple';
    const trunk = kind === 'juniper' ? [V(0, 0, 0), V(0.05, 0.1, 0.01), V(0.17, 0.2, -0.02), V(0.24, 0.33, 0.03), V(0.36, 0.4, 0), V(0.44, 0.5, -0.02)]
      : maple ? [V(0, 0, 0), V(0.04, 0.1, 0.01), V(-0.03, 0.2, -0.02), V(0.02, 0.3, 0.02), V(0, 0.38, 0)]
      : [V(0, 0, 0), V(0.075, 0.12, 0.02), V(-0.065, 0.27, -0.03), V(0.06, 0.42, 0.025), V(-0.02, 0.54, 0), V(0.012, 0.62, 0)];
    const r0 = maple ? 0.04 : 0.05, rTop = 0.011, wood = [tube(trunk, r0, rTop, 1.15, 10)], ends = [];
    const curve = new THREE.CatmullRomCurve3(trunk), P = new V3(), nb = maple ? 8 : 6;
    for (let i = 0; i < nb; i++) {
      const u = i / (nb - 1), t = 0.3 + 0.62 * u; curve.getPoint(t, P);
      const ang = i * 2.4 + rand(-0.4, 0.4), dx = Math.cos(ang), dz = Math.sin(ang);
      const len = (maple ? 0.2 : 0.3) * (1.05 - 0.6 * u) * rand(0.85, 1.1);
      // pine / juniper branches dip and level out (weighted-down look); maple branches reach upward
      const mid = V(P.x + dx * len * 0.5, P.y + (maple ? 0.14 : -0.07) * len, P.z + dz * len * 0.5);
      const end = V(P.x + dx * len, P.y + (maple ? 0.45 : -0.04) * len, P.z + dz * len);
      wood.push(tube([P.clone(), mid, end], (r0 + (rTop - r0) * Math.pow(t, 0.8)) * 0.55, 0.005, 0, 6));
      ends.push({ p: end.add(V(0, maple ? 0.02 : 0.03, 0)), r: len * (maple ? 0.78 : 0.52) });
    }
    ends.push({ p: trunk[trunk.length - 1].clone().add(V(0, 0.02, 0)), r: maple ? 0.13 : 0.115 });
    return { wood: mergeGeometries(wood), ends };
  }

  // soft core of a foliage pad: a lumpy, flat-bottomed cushion
  let blob = new THREE.IcosahedronGeometry(1, 4); blob.deleteAttribute('normal'); blob.deleteAttribute('uv'); blob = mergeVertices(blob, 1e-4);
  { const p = blob.attributes.position, v = new V3();
    for (let i = 0; i < p.count; i++) { v.fromBufferAttribute(p, i); v.multiplyScalar(0.8 + 0.4 * fbm3(v.x * 2.2 + 3, v.y * 2.2, v.z * 2.2)); p.setXYZ(i, v.x, v.y < 0 ? v.y * 0.35 : v.y, v.z); } }
  // a fan of needles
  const needleTex = (() => {
    const c = document.createElement('canvas'); c.width = c.height = 64; const g = c.getContext('2d');
    g.lineCap = 'round';
    for (let i = 0; i < 30; i++) {
      const a = (rng() * 2 - 1) * 1.25, L = 34 + rng() * 26, k = 200 + (rng() * 55 | 0);
      g.strokeStyle = `rgb(${k},${k},${k})`; g.lineWidth = 1.6 + rng() * 1.2;
      g.beginPath(); g.moveTo(32, 63); g.lineTo(32 + Math.sin(a) * L, 63 - Math.cos(a) * L); g.stroke();
    }
    const t = new THREE.CanvasTexture(c); t.colorSpace = THREE.SRGBColorSpace; t.anisotropy = 4; return t;
  })();
  const fanGeo = new THREE.PlaneGeometry(1, 1); fanGeo.translate(0, 0.5, 0);
  const sway = `{ float ph_ = ctr.x * 31. + ctr.z * 23. + ctr.y * 17.; wp.xyz += vec3(sin(uTime * 1.6 + ph_), .5 * sin(uTime * 2.3 + ph_ * 1.7), cos(uTime * 1.3 + ph_ * .8)) * .0025; }`;
  const fanMat = patch(new THREE.MeshStandardMaterial({ map: needleTex, alphaTest: 0.35, side: THREE.DoubleSide, roughness: 0.6 }), { world: sway, afterLights: TRANSLUCENT(0.1) });
  const fanDepth = depthMat(sway, '', { map: needleTex, alphaTest: 0.35 });
  const leafMat = patch(new THREE.MeshStandardMaterial({ map: leafTex, alphaTest: 0.3, side: THREE.DoubleSide, roughness: 0.55 }), { world: sway, afterLights: TRANSLUCENT(0.2) });
  const leafDepth = depthMat(sway, '', { map: leafTex, alphaTest: 0.3 });

  const potGeo = new THREE.LatheGeometry([[0.001, 0], [0.2, 0], [0.214, 0.014], [0.238, 0.084], [0.254, 0.1], [0.236, 0.1], [0.224, 0.088], [0.001, 0.088]].map(q => new THREE.Vector2(q[0], q[1])), 36);
  potGeo.scale(1.28, 1, 0.86); potGeo.computeVertexNormals();
  const soilGeo = new THREE.CircleGeometry(0.224, 28); soilGeo.rotateX(-Math.PI / 2); soilGeo.scale(1.28, 1, 0.86);
  const STYLE = {
    pine:    { pot: [0x3b2a20, 0.75, 0],   pad: [0.03, 0.085, 0.028], fan: [[0.05, 0.14, 0.04], [0.09, 0.22, 0.06]] },
    juniper: { pot: [0x60735f, 0.3, 0.5],  pad: [0.045, 0.105, 0.065], fan: [[0.08, 0.19, 0.11], [0.13, 0.27, 0.16]] },
    maple:   { pot: [0x27425e, 0.28, 0.6] },
  };
  const m4 = new THREE.Matrix4(), q = new THREE.Quaternion(), q2 = new THREE.Quaternion(), c = new THREE.Color(), e = new THREE.Euler(), up = V(0, 1, 0), d = new V3();

  for (const [x, z, kind, facing] of BONSAI) {
    const st = STYLE[kind], g = new THREE.Group(), put = m => { m.castShadow = m.receiveShadow = true; g.add(m); return m; };
    // display stand
    put(new THREE.Mesh(new THREE.BoxGeometry(0.66, 0.035, 0.42), standMat)).position.y = 0.325;
    put(new THREE.Mesh(new THREE.BoxGeometry(0.58, 0.05, 0.34), standMat)).position.y = 0.285;
    for (const sx of [-1, 1]) for (const sz of [-1, 1]) put(new THREE.Mesh(new THREE.BoxGeometry(0.04, 0.3, 0.04), standMat)).position.set(sx * 0.27, 0.15, sz * 0.15);
    // pot + mossy soil
    const TOP = 0.3425;
    const potMat = new THREE.MeshPhysicalMaterial({ color: st.pot[0], roughness: st.pot[1], clearcoat: st.pot[2], clearcoatRoughness: 0.3 });
    put(new THREE.Mesh(potGeo, potMat)).position.y = TOP;
    put(new THREE.Mesh(soilGeo, soilMat)).position.y = TOP + 0.089;
    // tree
    const { wood, ends } = skeleton(kind);
    const tree = new THREE.Group(); tree.position.y = TOP + 0.084; g.add(tree);
    const trunk = new THREE.Mesh(wood, barkMat); trunk.castShadow = trunk.receiveShadow = true; tree.add(trunk);
    if (kind === 'maple') {
      const PER = 125, leaves = new THREE.InstancedMesh(leafPlane, leafMat, ends.length * PER); let i = 0;
      for (const en of ends) for (let k = 0; k < PER; k++) {
        const a = rng() * 6.283, rr = Math.cbrt(rng()) * en.r, yy = (rng() * 2 - 1) * 0.6, hr = Math.sqrt(1 - yy * yy * 0.8), sz = rand(0.034, 0.055);
        q.setFromEuler(e.set(rand(-0.7, 0.7), rng() * 6.283, rand(-0.7, 0.7)));
        m4.compose(V(en.p.x + Math.cos(a) * rr * hr, en.p.y + yy * rr * 0.7, en.p.z + Math.sin(a) * rr * hr), q, V(sz, sz, sz));
        leaves.setMatrixAt(i, m4); leaves.setColorAt(i, leafColor(c)); i++;
      }
      leaves.customDepthMaterial = leafDepth; leaves.castShadow = leaves.receiveShadow = true; leaves.frustumCulled = false; tree.add(leaves);
    } else {
      const padMat = patch(new THREE.MeshStandardMaterial({ roughness: 0.82 }), { color: padCode, afterLights: TRANSLUCENT(0.04) });
      padMat.color.setRGB(st.pad[0], st.pad[1], st.pad[2]);
      const cores = ends.map(en => { const b = blob.clone(); b.scale(en.r * 0.9, en.r * 0.42, en.r * 0.9); b.translate(en.p.x, en.p.y, en.p.z); return b; });
      const pads = new THREE.Mesh(mergeGeometries(cores), padMat); pads.geometry.computeVertexNormals(); pads.castShadow = pads.receiveShadow = true; tree.add(pads);
      const PER = 85, fans = new THREE.InstancedMesh(fanGeo, fanMat, ends.length * PER); let i = 0;
      for (const en of ends) for (let k = 0; k < PER; k++) {
        // needle fans sit on the upper surface of the pad and point up and outward
        const a = rng() * 6.283, yy = rand(-0.15, 1), hr = Math.sqrt(Math.max(0, 1 - yy * yy));
        d.set(Math.cos(a) * hr, yy, Math.sin(a) * hr);
        const pos = V(en.p.x + d.x * en.r * 0.82, en.p.y + d.y * en.r * 0.36, en.p.z + d.z * en.r * 0.82);
        d.y = d.y * 0.6 + 0.75; d.normalize();
        q.setFromUnitVectors(up, d); q2.setFromAxisAngle(up, rng() * 6.283); q.multiply(q2);
        const sz = en.r * rand(0.45, 0.75);
        m4.compose(pos, q, V(sz, sz, sz));
        fans.setMatrixAt(i, m4);
        const t = rng(); fans.setColorAt(i, c.setRGB(st.fan[0][0] + (st.fan[1][0] - st.fan[0][0]) * t, st.fan[0][1] + (st.fan[1][1] - st.fan[0][1]) * t, st.fan[0][2] + (st.fan[1][2] - st.fan[0][2]) * t)); i++;
      }
      fans.customDepthMaterial = fanDepth; fans.castShadow = fans.receiveShadow = true; fans.frustumCulled = false; tree.add(fans);
    }
    g.position.set(x, terrainH(x, z, 'sand') - 0.01, z); g.rotation.y = facing;
    g.visible = false; scene.add(g); envObjs.sand.push(g);
  }
}

// ───────────────────────────── lily pads & water lilies ─────────────────────────────
function padTexture() {
  const c = document.createElement('canvas'); c.width = c.height = 256; const g = c.getContext('2d');
  const gr = g.createRadialGradient(128, 128, 4, 128, 128, 128);
  gr.addColorStop(0, '#6f9a35'); gr.addColorStop(0.55, '#487d27'); gr.addColorStop(1, '#2d5c1e');
  g.fillStyle = gr; g.fillRect(0, 0, 256, 256);
  g.strokeStyle = 'rgba(190,220,120,.33)'; g.lineWidth = 1.6;
  for (let i = 0; i < 20; i++) {
    const a = i / 20 * 6.283 + rng() * 0.1; g.beginPath(); g.moveTo(128, 128);
    const mx = 128 + Math.cos(a) * 80, my = 128 + Math.sin(a) * 80; g.lineTo(mx, my);
    g.lineTo(128 + Math.cos(a + 0.09) * 127, 128 + Math.sin(a + 0.09) * 127); g.moveTo(mx, my);
    g.lineTo(128 + Math.cos(a - 0.09) * 127, 128 + Math.sin(a - 0.09) * 127); g.stroke();
  }
  for (let i = 0; i < 46; i++) {
    const a = rng() * 6.283, r = Math.sqrt(rng()) * 122;
    g.fillStyle = rng() < 0.6 ? 'rgba(35,60,15,.22)' : 'rgba(190,175,70,.2)';
    g.beginPath(); g.arc(128 + Math.cos(a) * r, 128 + Math.sin(a) * r, 2 + rng() * 7, 0, 6.3); g.fill();
  }
  g.strokeStyle = 'rgba(95,65,25,.4)'; g.lineWidth = 7; g.beginPath(); g.arc(128, 128, 125, 0, 6.3); g.stroke();
  const t = new THREE.CanvasTexture(c); t.colorSpace = THREE.SRGBColorSpace; t.anisotropy = 8; return t;
}
const pads = [];
let padMesh, flowerMesh;
{
  const N = 44, notch = 0.17, pos = [0, 0.004, 0], uv = [0.5, 0.5], idx = [];
  for (let i = 0; i <= N; i++) {
    const a = notch + (i / N) * (Math.PI * 2 - 2 * notch), r = 1 + 0.035 * Math.sin(a * 7) + 0.02 * Math.sin(a * 13 + 1);
    pos.push(Math.cos(a) * r, 0.012 * Math.sin(a * 5) + 0.012, Math.sin(a) * r); uv.push(0.5 + Math.cos(a) * 0.49, 0.5 + Math.sin(a) * 0.49);
  }
  for (let i = 0; i < N; i++) idx.push(0, i + 2, i + 1);
  const pg = new THREE.BufferGeometry();
  pg.setAttribute('position', new THREE.Float32BufferAttribute(pos, 3)); pg.setAttribute('uv', new THREE.Float32BufferAttribute(uv, 2)); pg.setIndex(idx); pg.computeVertexNormals();

  const clusters = [pondPoint(2.25, -1.5), pondPoint(-0.95, -1.45), pondPoint(0.55, -1.35), pondPoint(-2.35, -1.6), pondPoint(3.5, -1.3)];
  let guard = 0;
  while (pads.length < 30 && guard++ < 3000) {
    const c = clusters[pads.length % clusters.length], a = rng() * 6.283, rr = Math.sqrt(rng()) * 1.25;
    const x = c.x + Math.cos(a) * rr, z = c.z + Math.sin(a) * rr, r = rand(0.15, 0.34);
    if (pondDist(x, z) > -0.3 - r) continue;
    if (pads.some(p => Math.hypot(p.ax - x, p.az - z) < (p.r + r) * 0.98)) continue;
    pads.push({ ax: x, az: z, x, z, vx: 0, vz: 0, r, rot: rng() * 6.28, vr: 0 });
  }
  const padMat = patch(new THREE.MeshPhysicalMaterial({ map: padTexture(), roughness: 0.5, clearcoat: 0.35, clearcoatRoughness: 0.35, side: THREE.DoubleSide }), { world: FLOAT_HOOK });
  padMesh = new THREE.InstancedMesh(pg, padMat, pads.length);
  padMesh.instanceMatrix.setUsage(THREE.DynamicDrawUsage);
  const c = new THREE.Color();
  pads.forEach((p, i) => { const k = rand(0.78, 1.08); padMesh.setColorAt(i, c.setRGB(k, k * rand(0.94, 1.04), k * rand(0.8, 1))); });
  padMesh.castShadow = padMesh.receiveShadow = true; padMesh.frustumCulled = false; padMesh.layers.set(1);
  scene.add(padMesh); envObjs.pond.push(padMesh);

  // water lily: three rings of cupped petals + golden centre
  const petal = (len, wid, curl, tilt, yaw, tip) => {
    const nu = 4, nv = 6, P = [], C = [], I = [];
    for (let v = 0; v <= nv; v++) {
      const tv = v / nv, w = wid * Math.pow(Math.sin(Math.PI * Math.pow(tv, 0.7)) || 0, 0.8);
      for (let u = 0; u <= nu; u++) {
        const tu = u / nu * 2 - 1;
        P.push(tu * w, curl * tv * tv * len + tu * tu * w * 0.5, tv * len);
        const k = Math.pow(tv, 1.3);
        C.push(0.95 + (tip[0] - 0.95) * k, 0.9 + (tip[1] - 0.9) * k, 0.8 + (tip[2] - 0.8) * k);
      }
    }
    for (let v = 0; v < nv; v++) for (let u = 0; u < nu; u++) { const a = v * (nu + 1) + u, b = a + nu + 1; I.push(a, b, a + 1, b, b + 1, a + 1); }
    const g = new THREE.BufferGeometry();
    g.setAttribute('position', new THREE.Float32BufferAttribute(P, 3)); g.setAttribute('color', new THREE.Float32BufferAttribute(C, 3)); g.setIndex(I);
    g.rotateX(-tilt); g.rotateY(yaw); return g;
  };
  const parts = [];
  [[10, 0.2, 0.185, 0.05, 0.25, [0.92, 0.42, 0.56]], [8, 0.62, 0.16, 0.047, 0.35, [0.95, 0.5, 0.62]], [7, 1.02, 0.125, 0.04, 0.4, [0.97, 0.62, 0.7]]]
    .forEach(([n, tilt, len, wid, curl, tip], ri) => { for (let i = 0; i < n; i++) parts.push(petal(len, wid, curl, tilt, i / n * 6.283 + ri * 0.4, tip)); });
  const core = new THREE.SphereGeometry(0.034, 10, 8); core.deleteAttribute('uv'); core.deleteAttribute('normal'); core.translate(0, 0.03, 0);
  core.setAttribute('color', new THREE.Float32BufferAttribute(new Array(core.attributes.position.count).fill(0).flatMap(() => [0.95, 0.62, 0.08]), 3));
  parts.push(core);
  const fg = mergeGeometries(parts); fg.computeVertexNormals();
  const flowerMat = patch(new THREE.MeshStandardMaterial({ vertexColors: true, roughness: 0.55, side: THREE.DoubleSide }), { world: FLOAT_HOOK, afterLights: TRANSLUCENT(0.1) });
  const spots = [0, 1, 2, 3, 6, 9].map(i => pads[i]).filter(Boolean);
  flowerMesh = new THREE.InstancedMesh(fg, flowerMat, spots.length);
  const m4 = new THREE.Matrix4(), q = new THREE.Quaternion();
  spots.forEach((p, i) => {
    const a = rng() * 6.28, s = rand(0.95, 1.35);
    m4.compose(new V3(p.ax + Math.cos(a) * (p.r + 0.1), 0.02, p.az + Math.sin(a) * (p.r + 0.1)), q.setFromEuler(new THREE.Euler(rand(-0.08, 0.08), rng() * 6, rand(-0.08, 0.08))), new V3(s, s, s));
    flowerMesh.setMatrixAt(i, m4);
  });
  flowerMesh.castShadow = true; flowerMesh.frustumCulled = false; flowerMesh.layers.set(1);
  scene.add(flowerMesh); envObjs.pond.push(flowerMesh);
}

// ───────────────────────────── bamboo water spout (kakei) ─────────────────────────────
let spoutTip;
{
  const A = 2.72, bambooMat = new THREE.MeshStandardMaterial({ color: 0x77763a, roughness: 0.45 });
  const back = pondPoint(A, 1.0), tip = pondPoint(A, -0.34), post = pondPoint(A, 0.34);
  back.y = 0.66; tip.y = 0.42;
  const d = tip.clone().sub(back), len = d.length();
  const pipe = new THREE.Mesh(new THREE.CylinderGeometry(0.03, 0.034, len, 10), bambooMat);
  pipe.position.copy(back).addScaledVector(d, 0.5); pipe.quaternion.setFromUnitVectors(new V3(0, 1, 0), d.clone().normalize());
  const pm = new THREE.Mesh(new THREE.CylinderGeometry(0.04, 0.045, 0.75, 10), bambooMat); pm.position.set(post.x, 0.33, post.z);
  const stream = new THREE.Mesh(new THREE.CylinderGeometry(0.006, 0.009, tip.y, 6), new THREE.MeshStandardMaterial({ color: 0xdfeef2, roughness: 0.05, transparent: true, opacity: 0.55 }));
  stream.position.set(tip.x, tip.y / 2 - 0.01, tip.z); stream.layers.set(1);
  for (const m of [pipe, pm]) { m.castShadow = m.receiveShadow = true; }
  scene.add(pipe, pm, stream); envObjs.pond.push(pipe, pm, stream);
  spoutTip = tip;
}

// ───────────────────────────── koi ─────────────────────────────
function koiGeometry() {
  const NS = 30, NR = 14, pos = [], uv = [], idx = [];
  for (let i = 0; i <= NS; i++) {
    const t = i / NS, x = 0.5 - t * 0.86, f = Math.pow(Math.sin(Math.PI * Math.pow(t, 0.55)), 0.75) || 0;
    const w = 0.098 * f + 0.016 * t, hg = 0.115 * f + 0.034 * t;
    for (let j = 0; j <= NR; j++) {
      const ph = -Math.PI / 2 + j / NR * Math.PI * 2, cy = Math.sin(ph), cz = Math.cos(ph);
      pos.push(x, hg * cy * (cy < 0 ? 0.8 : 1), w * cz); uv.push(t * 0.94, j / NR);
    }
  }
  for (let i = 0; i < NS; i++) for (let j = 0; j < NR; j++) { const a = i * (NR + 1) + j, b = a + NR + 1; idx.push(a, b, a + 1, b, b + 1, a + 1); }
  const tri = (...v) => { const n = pos.length / 3; for (let i = 0; i < 9; i += 3) { pos.push(v[i], v[i + 1], v[i + 2]); uv.push(0.978, 0.5); } idx.push(n, n + 1, n + 2); };
  tri(-0.34, 0.036, 0, -0.63, 0.155, 0, -0.53, 0, 0); tri(-0.34, 0.036, 0, -0.53, 0, 0, -0.34, -0.03, 0); tri(-0.34, -0.03, 0, -0.53, 0, 0, -0.63, -0.135, 0);
  for (const s of [-1, 1]) tri(0.2, -0.03, s * 0.075, 0.01, -0.07, s * 0.22, 0.08, -0.035, s * 0.07);
  tri(0.14, 0.116, 0, -0.14, 0.088, 0, -0.04, 0.178, 0);
  const g = new THREE.BufferGeometry();
  g.setAttribute('position', new THREE.Float32BufferAttribute(pos, 3)); g.setAttribute('uv', new THREE.Float32BufferAttribute(uv, 2)); g.setIndex(idx); g.computeVertexNormals();
  return g;
}
const KOI_PAL = {
  kohaku: { base: '#f3eee4', blobs: [['#d9461f', 5, 0.07]], fin: '#f1ece2' },
  sanke: { base: '#f3eee4', blobs: [['#d9461f', 4, 0.07], ['#151515', 5, 0.03]], fin: '#f1ece2' },
  showa: { base: '#19181b', blobs: [['#d13f1c', 4, 0.07], ['#efe9df', 4, 0.05]], fin: '#2b2a2d' },
  ogon: { base: '#e2a231', blobs: [['#f0c05a', 3, 0.05]], fin: '#eec367' },
  tancho: { base: '#f4f0e8', blobs: [], head: '#d43a1a', fin: '#f4f0e8' },
  benigoi: { base: '#d4501f', blobs: [['#e8742d', 3, 0.06]], fin: '#e0703a' },
  utsuri: { base: '#f0ebe2', blobs: [['#161616', 6, 0.05]], fin: '#e9e4da' },
};
function koiTexture(kind) {
  const W = 256, H = 128, c = document.createElement('canvas'); c.width = W; c.height = H; const g = c.getContext('2d'), pal = KOI_PAL[kind];
  g.fillStyle = pal.base; g.fillRect(0, 0, W, H);
  const blob = (u, v, ru, rv, col) => { g.fillStyle = col; g.beginPath(); g.ellipse(u * W, v * H, ru * W, rv * H, rand(-0.4, 0.4), 0, 6.283); g.fill(); };
  for (const [col, n, size] of pal.blobs) for (let i = 0; i < n; i++) blob(rand(0.1, 0.85), 0.5 + rand(-0.16, 0.16), size * rand(0.6, 1.3), size * rand(1.2, 2.6), col);
  if (pal.head) blob(0.1, 0.5, 0.055, 0.17, pal.head);
  g.globalAlpha = 0.08; g.strokeStyle = '#000';
  for (let x = 22; x < W * 0.9; x += 5) for (let y = ((x / 5) % 2) * 3; y < H; y += 6) { g.beginPath(); g.arc(x, y, 3.2, -1.2, 1.2); g.stroke(); }
  g.globalAlpha = 1; g.fillStyle = '#0b0b0b';
  for (const v of [0.33, 0.67]) { g.beginPath(); g.arc(0.085 * W, v * H, 2.6, 0, 6.3); g.fill(); }
  g.fillStyle = pal.fin; g.fillRect(W * 0.955, 0, W * 0.045, H);
  const t = new THREE.CanvasTexture(c); t.colorSpace = THREE.SRGBColorSpace; return t;
}
const koi = [];
{
  const geo = koiGeometry(), kinds = ['kohaku', 'sanke', 'showa', 'ogon', 'tancho', 'benigoi', 'utsuri', 'kohaku', 'sanke', 'ogon'];
  const KOI_VERT = /* glsl */`{ float bx_ = .5 - position.x; float w_ = sin(uPh - bx_ * 5.5);
    transformed.z += uAmp * (.012 + .11 * bx_ * bx_) * w_ + uBend * bx_ * bx_ * .35; }`;
  kinds.forEach((kind, i) => {
    const uni = { uPh: { value: rng() * 6 }, uAmp: { value: 1 }, uBend: { value: 0 } };
    const mat = patch(new THREE.MeshStandardMaterial({ map: koiTexture(kind), roughness: 0.32, side: THREE.DoubleSide }),
      { key: 'koi', vertPars: 'uniform float uPh, uAmp, uBend;', vert: KOI_VERT, uniforms: uni, afterLights: CAUSTIC });
    const mesh = new THREE.Mesh(geo, mat);
    const sc = rand(0.5, 0.82); mesh.scale.setScalar(sc);
    mesh.castShadow = true; mesh.frustumCulled = false;
    let x, z; do { x = rand(-4, 4); z = rand(-3, 3); } while (pondDist(x, z) > -1.3);
    const baseY = rand(-0.4, -0.2);
    koi.push({ mesh, uni, x, z, y: baseY, baseY, ang: rng() * 6.28, wander: rng() * 6.28, speed: 0.25, cruise: rand(0.17, 0.36), turn: 0, scare: 0, wake: 0, sc, seed: rng() * 100 });
    scene.add(mesh); envObjs.pond.push(mesh);
  });
}

// ───────────────────────────── drifting leaves ─────────────────────────────
const NLEAF = 36;
const dynLeaves = [];
const dynMesh = new THREE.InstancedMesh(leafPlane, patch(new THREE.MeshStandardMaterial({ map: leafTex, alphaTest: 0.3, side: THREE.DoubleSide, roughness: 0.5 }), { world: FLOAT_HOOK, afterLights: TRANSLUCENT(0.2) }), NLEAF);
{
  dynMesh.instanceMatrix.setUsage(THREE.DynamicDrawUsage);
  dynMesh.castShadow = true; dynMesh.frustumCulled = false; dynMesh.layers.set(1);
  const c = new THREE.Color();
  for (let i = 0; i < NLEAF; i++) {
    dynMesh.setColorAt(i, leafColor(c));
    const L = { mode: 'wait', t: rand(0, 26), x: 0, y: -5, z: 0, vx: 0, vz: 0, rx: 0, ry: rng() * 6.28, rz: 0, s: rand(0.11, 0.16), ph: rng() * 6.28, life: 0, k: 1 };
    if (i < 12) { // some already afloat
      do { L.x = rand(-5, 3.5); L.z = rand(-3.5, 2.5); } while (pondDist(L.x, L.z) > -0.4);
      L.mode = 'float'; L.y = 0.009; L.life = rand(20, 70);
    }
    dynLeaves.push(L);
  }
  scene.add(dynMesh);
}
function spawnLeaf(L) {
  const t = mapleTips[(rng() * mapleTips.length) | 0];
  L.x = t.x + rand(-0.3, 0.3); L.y = t.y - 0.1; L.z = t.z + rand(-0.3, 0.3);
  L.vx = rand(0.05, 0.3); L.vz = rand(0.0, 0.22); L.mode = 'fall'; L.k = 1; L.ph = rng() * 6.28;
}

// dust motes catching the light
let motes;
{
  const c = document.createElement('canvas'); c.width = c.height = 32; const g = c.getContext('2d');
  const gr = g.createRadialGradient(16, 16, 0, 16, 16, 16); gr.addColorStop(0, 'rgba(255,255,255,1)'); gr.addColorStop(0.4, 'rgba(255,255,255,.35)'); gr.addColorStop(1, 'rgba(255,255,255,0)');
  g.fillStyle = gr; g.fillRect(0, 0, 32, 32);
  const N = 260, p = new Float32Array(N * 3);
  for (let i = 0; i < N; i++) { p[i * 3] = rand(-8, 8); p[i * 3 + 1] = rand(0.2, 4.2); p[i * 3 + 2] = rand(-7, 8); }
  const geo = new THREE.BufferGeometry(); geo.setAttribute('position', new THREE.BufferAttribute(p, 3));
  motes = new THREE.Points(geo, new THREE.PointsMaterial({ map: new THREE.CanvasTexture(c), size: 0.03, transparent: true, opacity: 0.55, depthWrite: false, blending: THREE.AdditiveBlending, color: 0xffe2b0 }));
  motes.frustumCulled = false; motes.layers.set(1);
  scene.add(motes);
}

// ───────────────────────────── water surface ─────────────────────────────
const reflRT = new THREE.WebGLRenderTarget(4, 4, { type: THREE.HalfFloatType, minFilter: THREE.LinearFilter, magFilter: THREE.LinearFilter });
const refrRT = new THREE.WebGLRenderTarget(4, 4, { type: THREE.HalfFloatType, minFilter: THREE.LinearFilter, magFilter: THREE.LinearFilter });
refrRT.depthTexture = new THREE.DepthTexture(4, 4); refrRT.depthTexture.type = THREE.UnsignedIntType;
var waterMat = new THREE.ShaderMaterial({
  uniforms: {
    uSim: U.uSim, uTime: U.uTime, uSimS: U.uSimS, uSunDirW: U.uSunDirW, uSunCol: U.uSunCol,
    uRefl: { value: reflRT.texture }, uRefr: { value: refrRT.texture }, uRefrDepth: { value: refrRT.depthTexture },
    uRes: { value: new THREE.Vector2(1, 1) }, uNear: { value: camera.near }, uFar: { value: camera.far },
    uAbsorb: { value: new V3(2.1, 0.95, 1.5) }, uScatter: { value: new V3(0.026, 0.046, 0.026) },
    uLake: { value: 0 }, uFogCol: { value: new THREE.Color() }, uFogD: { value: 0 },
  },
  vertexShader: /* glsl */`varying vec3 vW; void main(){ vec4 w = modelMatrix * vec4(position, 1.0); vW = w.xyz; gl_Position = projectionMatrix * viewMatrix * w; }`,
  fragmentShader: /* glsl */`
    precision highp float;
    uniform sampler2D uSim, uRefl, uRefr, uRefrDepth;
    uniform vec2 uRes; uniform float uSimS, uTime, uNear, uFar, uLake, uFogD;
    uniform vec3 uSunDirW, uSunCol, uAbsorb, uScatter, uFogCol;
    varying vec3 vW;
    ${NOISE}
    float lin(float z){ return uNear * uFar / (uFar - z * (uFar - uNear)); }
    float wn(vec2 p){ return zn2(p * 5.5 + uTime * vec2(.33, .21)) * .55 + zn2(p * 12. - uTime * vec2(.28, .4)) * .28 + zn2(p * 27. + uTime * vec2(.5, -.3)) * .12; }
    // a still lake is never quite glass: long, slow, barely-there undulations
    float lk(vec2 p){ return zn2(p * .33 + uTime * vec2(.03, .017)) * .6 + zn2(p * 1.05 - uTime * vec2(.04, .05)) * .4; }
    void main(){
      vec2 suv = vW.xz / (2. * uSimS) + .5; float e = 1. / ${SIM}.; float tm = 2. * uSimS * e;
      float hl = texture2D(uSim, suv - vec2(e, 0.)).r, hr = texture2D(uSim, suv + vec2(e, 0.)).r;
      float hd = texture2D(uSim, suv - vec2(0., e)).r, hu = texture2D(uSim, suv + vec2(0., e)).r;
      vec2 g = vec2(hr - hl, hu - hd) / (2. * tm);
      g *= step(abs(suv.x - .5), .5) * step(abs(suv.y - .5), .5);      // nothing stirs outside the simulated patch
      float dist = length(cameraPosition - vW);
      if (uLake > .5) {
        float gust = smoothstep(.45, .85, zn2(vW.xz * .02 + uTime * .012));
        float l0 = lk(vW.xz);
        g += vec2(lk(vW.xz + vec2(.3, 0.)) - l0, lk(vW.xz + vec2(0., .3)) - l0) / .3 * (.004 + .01 * gust);
      } else {
        // faint breeze: drifting patches of fine ripples
        float gust = smoothstep(.3, .75, zn2(vW.xz * .32 + uTime * .045));
        float w0 = wn(vW.xz);
        g += vec2(wn(vW.xz + vec2(.025, 0.)) - w0, wn(vW.xz + vec2(0., .025)) - w0) / .025 * .0045 * (.2 + gust) / (1. + dist * .06);
      }
      vec3 N = normalize(vec3(-g.x, 1., -g.y));
      vec3 V = normalize(cameraPosition - vW);
      float F = .02 + .98 * pow(1. - max(dot(N, V), 0.), 5.);
      vec2 sc = gl_FragCoord.xy / uRes;
      vec3 nv = mat3(viewMatrix) * (N - vec3(0., 1., 0.));

      // planar reflection (mirrored camera renders flipped in x)
      vec2 ruv = vec2(1. - sc.x, sc.y) + vec2(-nv.x * .55, nv.y * 1.1);
      vec3 refl = min(texture2D(uRefl, clamp(ruv, .002, .998)).rgb, vec3(4.5));

      // refraction through the surface with depth-based absorption
      float zW = lin(gl_FragCoord.z);
      float z0 = lin(texture2D(uRefrDepth, sc).x);
      float th0 = max(z0 - zW, 0.);
      vec2 fuv = sc + nv.xy * .22 * min(th0 * 2.5, 1.);
      float zS = lin(texture2D(uRefrDepth, fuv).x);
      if (zS < zW) { fuv = sc; zS = z0; }
      vec3 refr = texture2D(uRefr, fuv).rgb;
      float thick = max(zS - zW, 0.) * dist / zW;
      vec3 tr = exp(-thick * uAbsorb);
      vec3 sunTint = uSunCol * max(uSunDirW.y, .05) + vec3(.35, .45, .6);
      vec3 body = refr * tr + uScatter * sunTint * (1. - tr);
      // milky glacial water glows by scattered sunlight, so a ripple's sunward slope is brighter than its far one:
      // that is what makes a disturbance show on water too cloudy to see into
      if (uLake > .5) body *= clamp(1. + (dot(N, uSunDirW) / max(uSunDirW.y, .2) - 1.) * 2.2, .5, 1.7);

      vec3 col = mix(body, refl, F);
      vec3 R = reflect(-V, N);
      col += uSunCol * pow(max(dot(R, uSunDirW), 0.), 900.) * 14.;
      float fg = dist * uFogD; col = mix(uFogCol, col, exp(-fg * fg));      // distance haze (the lake only; zero elsewhere)
      gl_FragColor = vec4(col, 1.);
    }`,
});
const pondWater = new THREE.Mesh(new THREE.PlaneGeometry(S * 2, S * 2).rotateX(-Math.PI / 2), waterMat);
scene.add(pondWater); envObjs.pond.push(pondWater);

const reflCam = new THREE.PerspectiveCamera();
reflCam.matrixAutoUpdate = false; reflCam.matrixWorldAutoUpdate = false; reflCam.layers.enable(1);
const MIRROR = new THREE.Matrix4().makeScale(1, -1, 1), FLIPX = new THREE.Matrix4().makeScale(-1, 1, 1);
const reflPlane = new THREE.Plane(), clipV = new THREE.Vector4(), qV = new THREE.Vector4();
function updateReflCam() {
  reflCam.matrixWorld.copy(MIRROR).multiply(camera.matrixWorld).multiply(FLIPX);
  reflCam.matrixWorldInverse.copy(reflCam.matrixWorld).invert();
  const pm = reflCam.projectionMatrix.copy(camera.projectionMatrix), e = pm.elements;
  // oblique near plane at the water line so nothing below the surface leaks into the mirror image
  reflPlane.set(new V3(0, 1, 0), 0.012).applyMatrix4(reflCam.matrixWorldInverse);
  clipV.set(reflPlane.normal.x, reflPlane.normal.y, reflPlane.normal.z, reflPlane.constant);
  qV.x = (Math.sign(clipV.x) + e[8]) / e[0]; qV.y = (Math.sign(clipV.y) + e[9]) / e[5]; qV.z = -1; qV.w = (1 + e[10]) / e[14];
  clipV.multiplyScalar(2 / clipV.dot(qV));
  e[2] = clipV.x; e[6] = clipV.y; e[10] = clipV.z + 1 - 0.003; e[14] = clipV.w;
  reflCam.projectionMatrixInverse.copy(pm).invert();
}

// ───────────────────────────── post-processing ─────────────────────────────
const composer = new EffectComposer(renderer, new THREE.WebGLRenderTarget(4, 4, { type: THREE.HalfFloatType, samples: 4 }));
composer.addPass(new RenderPass(scene, camera));
const bloom = new UnrealBloomPass(new THREE.Vector2(256, 256), 0.26, 0.6, 1.25);
composer.addPass(bloom);
const finish = new ShaderPass({
  uniforms: { tDiffuse: { value: null }, uTime: U.uTime },
  vertexShader: 'varying vec2 vUv; void main(){ vUv = uv; gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 1.0); }',
  fragmentShader: /* glsl */`
    uniform sampler2D tDiffuse; uniform float uTime; varying vec2 vUv;
    void main(){
      vec3 c = texture2D(tDiffuse, vUv).rgb; vec2 q = vUv - .5;
      c *= mix(.6, 1., smoothstep(.98, .28, length(q * vec2(1., .84))));
      float l = dot(c, vec3(.2126, .7152, .0722)); c = max(mix(vec3(l), c, 1.1), 0.);
      float n = fract(sin(dot(gl_FragCoord.xy + fract(uTime) * 61., vec2(12.9898, 78.233))) * 43758.5453);
      c *= 1. + (n - .5) * .04;
      gl_FragColor = vec4(c, 1.);
    }`,
});
composer.addPass(finish);
composer.addPass(new OutputPass());

function resize() {
  const w = innerWidth, h = innerHeight;
  renderer.setPixelRatio(PR); renderer.setSize(w, h);
  composer.setPixelRatio(PR); composer.setSize(w, h);
  const db = renderer.getDrawingBufferSize(new THREE.Vector2());
  reflRT.setSize(Math.max(2, db.x >> 1), Math.max(2, db.y >> 1));
  refrRT.setSize(db.x, db.y);
  waterMat.uniforms.uRes.value.copy(db);
  camera.aspect = w / h;
  camera.fov = VIEW[viewKey].fov[w / h < 1 ? 1 : 0];      // widen for portrait screens
  camera.updateProjectionMatrix();
}
addEventListener('resize', resize);

// ───────────────────────────── pointer interaction ─────────────────────────────
const raycaster = new THREE.Raycaster(), ndc = new THREE.Vector2();
const sfx = { swish: 0, rake: 0 };
const audio = createAudio();
const cursor = { kind: null, sx: 0, x: 0, z: 0, vx: 0, vz: 0, speed: 0, still: 0, t: 0, lastWater: null, lastSand: null };
function pick(cx, cy) {
  ndc.set(cx / innerWidth * 2 - 1, -(cy / innerHeight) * 2 + 1);
  raycaster.setFromCamera(ndc, camera);
  const o = raycaster.ray.origin, d = raycaster.ray.direction;
  if (d.y > -1e-3) return null;
  let t = -o.y / d.y, x = o.x + d.x * t, z = o.z + d.z * t;
  if (ENV === 'lake') return Math.abs(x) < LAKE_S - 1.5 && Math.abs(z) < LAKE_S - 1.5 && lakeShore(x, z) < -0.3 ? { kind: 'water', x, z } : null;
  if (pondDist(x, z) < -0.03) return { kind: 'water', x, z };
  t = (GRAVEL_Y - o.y) / d.y; x = o.x + d.x * t; z = o.z + d.z * t;
  if (Math.abs(x) < SAND_S - 0.35 && Math.abs(z) < SAND_S - 0.35 && pondDist(x, z) > 1.0 && !sandBlocked(x, z) && ISLANDS.every(i => Math.hypot(x - i[0], z - i[1]) > i[2] + 0.3)) return { kind: 'sand', x, z };
  return null;
}
function onPointer(cx, cy) {
  const now = performance.now() / 1000, hit = pick(cx, cy);
  if (!hit) { cursor.kind = null; cursor.lastWater = cursor.lastSand = null; return; }
  const dtE = Math.max(now - cursor.t, 1 / 240);
  if (cursor.kind === hit.kind && dtE < 0.25) {
    const vx = (hit.x - cursor.x) / dtE, vz = (hit.z - cursor.z) / dtE;
    cursor.vx += (vx - cursor.vx) * 0.5; cursor.vz += (vz - cursor.vz) * 0.5;
  } else { cursor.vx = cursor.vz = 0; }
  cursor.speed = Math.hypot(cursor.vx, cursor.vz);
  cursor.kind = hit.kind; cursor.x = hit.x; cursor.z = hit.z; cursor.t = now;

  if (hit.kind === 'water') {
    cursor.lastSand = null;
    // the lake is the pond's water on a bigger scale: same strokes, same sounds, everything WS times larger
    const WS = ENV === 'lake' ? LAKE_S / S : 1, sp = cursor.speed / WS, K = WS * (ENV === 'lake' ? 1.8 : 1);      // K: wave height
    const lakeOn = ENV === 'lake';
    // pond: any movement in the water is heard, however slow. Lake: a slow glide is all but silent, a sweep is heard
    if (sp > 0.03) sfx.swish = Math.max(sfx.swish, lakeOn ? Math.min(1, sp / 2.2) : Math.min(1, 0.45 + sp / 1.8));
    const L = cursor.lastWater;
    if (!L) { cursor.lastWater = { x: hit.x, z: hit.z }; addDrop(hit.x, hit.z, 0.1 * WS, -0.004 * K); if (!lakeOn) { audio.touch(1.2, ndc.x * 0.7, true); sfx.swish = Math.max(sfx.swish, 0.45); } }
    else {
      const dx = hit.x - L.x, dz = hit.z - L.z, dist = Math.hypot(dx, dz);
      if (dist > 0.06 * WS) {
        const n = Math.min(14, Math.floor(dist / (0.06 * WS))), str = -(0.0022 + Math.min(sp, 3.5) * 0.0011) * K;
        for (let i = 1; i <= n; i++) addDrop(L.x + dx * i / n, L.z + dz * i / n, 0.1 * WS, str);
        L.x = hit.x; L.z = hit.z; sfx.swish = Math.max(sfx.swish, lakeOn ? Math.min(1, sp / 2.2) : Math.min(1, 0.35 + sp / 1.8)); audio.touch(sp, ndc.x * 0.7);
      }
    }
  } else { cursor.lastWater = null; }      // on sand the rake (updateRake) follows the cursor and does the carving
  cursor.sx = ndc.x;
}
addEventListener('pointermove', e => {
  if (e.pointerType === 'mouse' && e.buttons !== 0) return;
  // over the tuning panel the tool lifts off the sand, so moving a slider does not rake what is behind it
  // over the buttons and panels the hand is off the scene: nothing behind them is stirred or raked
  if (e.target !== canvas) { cursor.kind = null; cursor.lastWater = cursor.lastSand = null; return; }
  onPointer(e.clientX, e.clientY);
});
// a click (not an orbit drag): splash in the water, or a ripple of rings stamped in the sand
function clickAt(cx, cy) {
  if (ENV === 'lake') { throwStone(cx, cy, 0.5); return; }
  const h = pick(cx, cy);
  if (!h) return;
  if (h.kind === 'water') {
    const WS = ENV === 'lake' ? LAKE_S / S : 1;
    addDrop(h.x, h.z, 0.16 * WS, -0.022 * WS * (WS > 1 ? 1.6 : 1)); audio.splash(ndc.x * 0.6, WS > 1 ? 0.15 : 1);
    for (const k of koi) if (Math.hypot(k.x - h.x, k.z - h.z) < 1.5) k.scare = 1;
  } else { sandQueue.push({ ring: [h.x, h.z] }); audio.sandPuff(1, ndc.x * 0.7); puffGrains(h.x, h.z); }
}
let downAt = null;
canvas.addEventListener('pointerdown', e => { downAt = { x: e.clientX, y: e.clientY, t: performance.now(), cancel: false }; });
// a press that turns into a drag is a look around, not a throw
addEventListener('pointermove', e => { if (downAt && Math.hypot(e.clientX - downAt.x, e.clientY - downAt.y) >= 6) downAt.cancel = true; });
addEventListener('pointerup', e => {
  if (downAt && !downAt.cancel && Math.hypot(e.clientX - downAt.x, e.clientY - downAt.y) < 6) {
    const held = performance.now() - downAt.t;
    // the lake: the longer the press, the harder the throw. Elsewhere: a click is a quick press
    if (ENV === 'lake') throwStone(downAt.x, downAt.y, throwPower(held / 1000));
    else if (held < 400) clickAt(e.clientX, e.clientY);
  }
  downAt = null;
});
document.addEventListener('pointerleave', () => { cursor.kind = null; cursor.lastWater = cursor.lastSand = null; });
document.querySelectorAll('#tod button').forEach(b => b.addEventListener('click', () => setTimeOfDay(b.dataset.tod)));

// ───────────────────────────── sand tools ─────────────────────────────
// The chosen tool follows the cursor over the sand. Its head lags and swings round like something being pulled,
// and every tine / finger carves its own furrow, so grooves fan out on turns and cross older lines.
let tool = 'rake';
const rake = { groups: {}, x: 0, z: 0, dx: 0, dz: 1, active: false, lift: 1, tines: null, acc: 0, speed: 0, get group() { return this.groups[tool]; } };
{
  const wood = new THREE.MeshStandardMaterial({ color: 0x7a5630, roughness: 0.72 });
  const bamboo = new THREE.MeshStandardMaterial({ color: 0x9a8c4a, roughness: 0.45 });
  const skin = new THREE.MeshStandardMaterial({ color: 0xc98f6b, roughness: 0.62 });
  const cloth = new THREE.MeshStandardMaterial({ color: 0x232a3a, roughness: 0.9 });
  const mk = name => { const g = new THREE.Group(); g.visible = false; scene.add(g); rake.groups[name] = g; return g; };
  const put = (g, m) => { m.castShadow = true; m.receiveShadow = true; g.add(m); return m; };
  // a rounded limb between two points (local space; +z is the direction of pull)
  const limb = (g, a, b, r0, r1, mat) => {
    const A = new V3(...a), B = new V3(...b), d = B.clone().sub(A), len = d.length();
    const m = put(g, new THREE.Mesh(new THREE.CylinderGeometry(r1, r0, len, 10), mat));
    m.position.copy(A).addScaledVector(d, 0.5); m.quaternion.setFromUnitVectors(new V3(0, 1, 0), d.normalize());
    for (const [P, r] of [[A, r0], [B, r1]]) put(g, new THREE.Mesh(new THREE.SphereGeometry(r, 10, 8), mat)).position.copy(P);
    return m;
  };
  const HANDLE = [0, 0.112 + 1.75 * Math.cos(1.02), 1.75 * Math.sin(1.02)];     // long handle leaning toward the pull

  // rake: bar + five teeth
  let g = mk('rake');
  put(g, new THREE.Mesh(new THREE.BoxGeometry(0.57, 0.042, 0.058), wood)).position.y = 0.112;
  for (const o of TOOLS.rake.offs) { const t = put(g, new THREE.Mesh(new THREE.CylinderGeometry(0.013, 0.006, 0.13, 7), wood)); t.position.set(o, 0.052, -0.012); t.rotation.x = -0.2; }
  limb(g, [0, 0.112, 0], HANDLE, 0.018, 0.014, wood);

  // levelling board: a flat blade on the same kind of handle
  g = mk('board');
  const blade = put(g, new THREE.Mesh(new THREE.BoxGeometry(0.6, 0.15, 0.022), wood)); blade.position.set(0, 0.072, 0); blade.rotation.x = -0.18;
  limb(g, [0, 0.12, 0.01], HANDLE, 0.018, 0.014, wood);

  // stick: a bamboo cane, tip in the sand
  g = mk('stick');
  limb(g, [0, -0.01, 0], [0, 0.95, 0.78], 0.011, 0.016, bamboo);

  // hand: four fingertips drawn through the sand (drawn larger than life so the furrows read from across the garden)
  g = mk('hand');
  const offs = TOOLS.hand.offs, lens = [0.92, 1.05, 1.0, 0.82];
  offs.forEach((o, i) => {
    const k = lens[i], tip = [o, 0.006, 0], mid = [o * 0.97, 0.05 * k, 0.05 * k], kn = [o * 0.92, 0.085, 0.118];
    limb(g, tip, mid, 0.017, 0.019, skin); limb(g, mid, kn, 0.019, 0.022, skin);
  });
  const palm = put(g, new THREE.Mesh(new THREE.SphereGeometry(1, 16, 12), skin)); palm.scale.set(0.108, 0.034, 0.105); palm.position.set(0, 0.112, 0.205); palm.rotation.x = -0.3;
  limb(g, [-0.1, 0.1, 0.2], [-0.15, 0.06, 0.12], 0.024, 0.019, skin); limb(g, [-0.15, 0.06, 0.12], [-0.165, 0.035, 0.05], 0.019, 0.016, skin);   // thumb
  limb(g, [0, 0.15, 0.3], [0, 0.42, 0.72], 0.05, 0.062, skin);                    // forearm
  limb(g, [0, 0.27, 0.49], [0, 0.5, 0.85], 0.075, 0.09, cloth);                   // sleeve
}
// grains kicked up by the tines
const NGR = 280, grainPos = new Float32Array(NGR * 3).fill(-10), grainVel = new Float32Array(NGR * 3), grainLife = new Float32Array(NGR);
let grainPts, grainI = 0;
{
  const c = document.createElement('canvas'); c.width = c.height = 16; const g = c.getContext('2d');
  const gr = g.createRadialGradient(8, 8, 0, 8, 8, 8); gr.addColorStop(0, 'rgba(255,255,255,1)'); gr.addColorStop(0.6, 'rgba(255,255,255,.8)'); gr.addColorStop(1, 'rgba(255,255,255,0)');
  g.fillStyle = gr; g.fillRect(0, 0, 16, 16);
  const geo = new THREE.BufferGeometry(); geo.setAttribute('position', new THREE.BufferAttribute(grainPos, 3));
  grainPts = new THREE.Points(geo, new THREE.PointsMaterial({ map: new THREE.CanvasTexture(c), size: 0.017, color: 0xb9b0a0, transparent: true, alphaTest: 0.3, depthWrite: false }));
  grainPts.frustumCulled = false; scene.add(grainPts);
}
function emitGrain(x, z, vx, vy, vz) {
  const i = grainI = (grainI + 1) % NGR;
  grainPos[i * 3] = x; grainPos[i * 3 + 1] = GRAVEL_Y + 0.02; grainPos[i * 3 + 2] = z;
  grainVel[i * 3] = vx; grainVel[i * 3 + 1] = vy; grainVel[i * 3 + 2] = vz; grainLife[i] = 0.7;
}
function puffGrains(x, z) { for (let i = 0; i < 46; i++) { const a = Math.random() * 6.283, r = Math.random() * 0.6, v = 0.2 + Math.random() * 0.5; emitGrain(x + Math.cos(a) * r, z + Math.sin(a) * r, Math.cos(a) * v, 0.5 + Math.random() * 0.9, Math.sin(a) * v); } }
function tinePositions() {
  const offs = TOOLS[tool].offs, out = new Float32Array(offs.length * 2), px = rake.dz, pz = -rake.dx;   // head runs perpendicular to the pull
  offs.forEach((o, i) => { out[i * 2] = rake.x + px * o; out[i * 2 + 1] = rake.z + pz * o; });
  return out;
}
function setTool(name) {
  if (!TOOLS[name]) return;
  for (const k in rake.groups) rake.groups[k].visible = false;
  tool = name; rake.active = false; rake.lift = 1;
  document.querySelectorAll('#tools button').forEach(b => b.classList.toggle('on', b.dataset.tool === name));
  store.set('zen_tool', name);
}
function updateRake(dt) {
  const r = rake, on = cursor.kind === 'sand';
  if (on) {
    if (!r.active) {       // set the tool down: a dent under each tine / fingertip
      r.active = true; r.x = cursor.x; r.z = cursor.z; r.acc = 0; r.tines = tinePositions();
      if (!TOOLS[tool].board) sandQueue.push({ tool, a: r.tines, b: r.tines });
      audio.sandPuff(0.35, cursor.sx * 0.7);
    }
    const k = Math.min(1, dt * 12), px = r.x, pz = r.z;
    r.x += (cursor.x - r.x) * k; r.z += (cursor.z - r.z) * k;
    const mx = r.x - px, mz = r.z - pz, md = Math.hypot(mx, mz);
    r.speed += (md / Math.max(dt, 1e-4) - r.speed) * Math.min(1, dt * 14);
    if (md > 1e-5) {       // the head swings round to trail the pull over ~12 cm of travel
      const t = Math.min(1, md / 0.12), nx = r.dx + (mx / md - r.dx) * t, nz = r.dz + (mz / md - r.dz) * t, nl = Math.hypot(nx, nz);
      if (nl > 1e-3) { r.dx = nx / nl; r.dz = nz / nl; }
    }
    r.acc += md;
    if (r.acc > 0.012) {
      const now = tinePositions();
      if (sandQueue.length < 10) sandQueue.push({ tool, a: r.tines, b: now });
      const sp = Math.min(r.speed, 3), half = TOOLS[tool].board || 0;
      for (let i = 0, n = half ? 5 : now.length / 2; i < n; i++) if (Math.random() < sp * 0.55) { const j = half ? 0 : i, o = half ? (Math.random() * 2 - 1) * half : 0; emitGrain(now[j * 2] + r.dz * o, now[j * 2 + 1] - r.dx * o, r.dx * sp * (0.1 + Math.random() * 0.3) + (Math.random() - 0.5) * 0.5, (0.25 + Math.random() * 0.8) * Math.min(1, sp), r.dz * sp * (0.1 + Math.random() * 0.3) + (Math.random() - 0.5) * 0.5); }
      r.tines = now; r.acc = 0;
    }
    // loudness follows the stroke: slow = faint, a sweep swells. It is heard only while the pointer itself is
    // moving — the tool glides on a moment to catch up, but the sound stops with the hand
    const handMoving = performance.now() / 1000 - cursor.t < 0.12;
    sfx.rake = handMoving && r.speed > 0.03 ? Math.min(1, 0.12 + r.speed / 1.2) : 0;
  } else { r.active = false; r.speed = 0; sfx.rake = 0; }
  r.lift += ((on ? 0 : 1) - r.lift) * Math.min(1, dt * (on ? 12 : 4));
  r.group.visible = r.lift < 0.97;
  r.group.position.set(r.x, GRAVEL_Y - 0.004 + r.lift * 0.35, r.z);
  r.group.rotation.y = Math.atan2(r.dx, r.dz);

  let any = false;
  for (let i = 0; i < NGR; i++) {
    if (grainLife[i] <= 0) continue;
    any = true; grainLife[i] -= dt;
    grainVel[i * 3 + 1] -= 7.5 * dt;
    grainPos[i * 3] += grainVel[i * 3] * dt; grainPos[i * 3 + 1] += grainVel[i * 3 + 1] * dt; grainPos[i * 3 + 2] += grainVel[i * 3 + 2] * dt;
    if (grainLife[i] <= 0 || grainPos[i * 3 + 1] < GRAVEL_Y) { grainLife[i] = 0; grainPos[i * 3 + 1] = -10; }
  }
  if (any) grainPts.geometry.attributes.position.needsUpdate = true;
}

// ───────────────────────────── per-frame updates ─────────────────────────────
const _m4 = new THREE.Matrix4(), _q = new THREE.Quaternion(), _e = new THREE.Euler(), _p = new V3(), _s = new V3();

const panOf = (x, z) => clamp(_p.set(x, 0, z).project(camera).x * 0.8, -1, 1);
let gulpT = 3;
function updateKoi(dt, time) {
  // now and then a koi rises and mouths the surface
  gulpT -= dt;
  if (gulpT <= 0) {
    gulpT = rand(9, 22);
    const k = koi[(rng() * koi.length) | 0];
    addDrop(k.x + Math.cos(k.ang) * 0.3 * k.sc, k.z + Math.sin(k.ang) * 0.3 * k.sc, 0.07, 0.008);
    k.y = Math.min(k.y + 0.1, -0.1); audio.fish(0.2, panOf(k.x, k.z));
  }
  const onWater = cursor.kind === 'water';
  for (const k of koi) {
    let sx = Math.cos(k.wander), sz = Math.sin(k.wander);
    k.wander += (vn2(time * 0.25 + k.seed, k.seed) - 0.5) * 2.4 * dt;
    const d = pondDist(k.x, k.z);
    if (d > -1.15) { const w = (d + 1.15) * 2.6, l = Math.hypot(k.x, k.z) || 1; sx -= k.x / l * w; sz -= k.z / l * w; }
    for (const o of koi) if (o !== k) { const dx = k.x - o.x, dz = k.z - o.z, dd = Math.hypot(dx, dz); if (dd < 0.7 && dd > 1e-4) { const w = (0.7 - dd) * 1.6 / dd; sx += dx * w; sz += dz * w; } }
    let target = k.cruise * (1 + 0.3 * Math.sin(time * 0.3 + k.seed)), targetY = k.baseY, curious = false;
    if (onWater) {
      const dx = cursor.x - k.x, dz = cursor.z - k.z, dd = Math.hypot(dx, dz) || 1e-3;
      if ((cursor.speed > 2.2 && dd < 1.3) || (cursor.speed > 0.8 && dd < 0.3)) { if (k.scare < 0.4) audio.fish(0.6, panOf(k.x, k.z)); k.scare = 1; }
      else if (cursor.still > 0.6 && dd < 3.6 && k.scare < 0.1) {
        curious = true;
        if (dd > 0.42) { sx += dx / dd * 2.4; sz += dz / dd * 2.4; target = 0.55; }
        else { sx += -dz / dd * 1.5 + dx / dd * 0.3; sz += dx / dd * 1.5 + dz / dd * 0.3; target = 0.2; if (rng() < dt * 0.7) { addDrop(k.x + Math.cos(k.ang) * 0.3 * k.sc, k.z + Math.sin(k.ang) * 0.3 * k.sc, 0.05, 0.0045); if (rng() < 0.05) audio.fish(0.12, panOf(k.x, k.z)); } }
        targetY = -0.12;
      }
      if (k.scare > 0.1) { sx -= dx / dd * 4 * k.scare; sz -= dz / dd * 4 * k.scare; }
    }
    if (k.scare > 0.05) target = k.cruise + 1.9 * k.scare;
    k.scare *= Math.exp(-dt * 1.3);
    const diff = wrapPi(Math.atan2(sz, sx) - k.ang), maxTurn = 1.3 + k.scare * 6;
    k.turn += (clamp(diff * 2.5, -maxTurn, maxTurn) - k.turn) * Math.min(1, dt * 5);
    k.ang += k.turn * dt;
    k.speed += (target - k.speed) * Math.min(1, dt * (k.scare > 0.1 ? 7 : 1.5));
    k.x += Math.cos(k.ang) * k.speed * dt; k.z += Math.sin(k.ang) * k.speed * dt;
    const bed = terrainH(k.x, k.z) + 0.14;
    k.y += (Math.min(-0.1, Math.max(targetY, bed)) - k.y) * Math.min(1, dt * (curious ? 1.2 : 0.8));
    k.wake += k.speed * dt;
    if (k.speed > 0.8 && k.wake > 0.13) { k.wake = 0; addDrop(k.x, k.z, 0.1, 0.0032 * k.speed); if (rng() < 0.1) audio.fish(0.2 * k.speed, panOf(k.x, k.z)); }
    // sharp turns swirl the water
    if (Math.abs(k.turn) > 1.1 && k.speed > 0.3 && rng() < dt * 1.5) { addDrop(k.x, k.z, 0.09, 0.004); if (rng() < 0.25) audio.fish(0.2, panOf(k.x, k.z)); }
    k.uni.uPh.value += dt * (2.6 + k.speed * 10);
    k.uni.uAmp.value = clamp(0.45 + k.speed * 1.3, 0.4, 2.2);
    k.uni.uBend.value += (-k.turn * 0.35 - k.uni.uBend.value) * Math.min(1, dt * 4);
    k.mesh.position.set(k.x, k.y, k.z); k.mesh.rotation.y = -k.ang;
  }
}

function pushByCursor(o, radius, gain, dt) {
  if (cursor.kind !== 'water') return;
  const dx = o.x - cursor.x, dz = o.z - cursor.z, dd = Math.hypot(dx, dz);
  if (dd > radius) return;
  const f = (1 - dd / radius) * gain * dt, sp = Math.min(cursor.speed, 3);
  o.vx += cursor.vx * f * 0.6 + dx / (dd + 0.05) * f * (0.25 + sp * 0.35);
  o.vz += cursor.vz * f * 0.6 + dz / (dd + 0.05) * f * (0.25 + sp * 0.35);
  if (o.vr !== undefined) o.vr += (cursor.vx * dz - cursor.vz * dx) * f * 0.8;
}
function updatePads(dt, time) {
  const damp = Math.exp(-dt * 1.6);
  pads.forEach((p, i) => {
    pushByCursor(p, p.r + 0.45, 1.6, dt);
    p.vx += (p.ax - p.x) * 1.4 * dt; p.vz += (p.az - p.z) * 1.4 * dt;
    p.vx *= damp; p.vz *= damp; p.vr *= damp;
    p.x += p.vx * dt; p.z += p.vz * dt; p.rot += p.vr * dt + Math.sin(time * 0.2 + i) * 0.0006;
    _m4.compose(_p.set(p.x, 0.014, p.z), _q.setFromAxisAngle(V3_UP, p.rot), _s.set(p.r, p.r, p.r));
    padMesh.setMatrixAt(i, _m4);
  });
  padMesh.instanceMatrix.needsUpdate = true;
}
const V3_UP = new V3(0, 1, 0);

function updateLeaves(dt, time) {
  dynLeaves.forEach((L, i) => {
    if (L.mode === 'wait') { L.t -= dt; if (L.t <= 0) spawnLeaf(L); }
    else if (L.mode === 'fall') {
      const sw = Math.sin(time * 2.1 + L.ph);
      L.x += (L.vx + sw * 0.35) * dt; L.z += (L.vz + Math.cos(time * 1.7 + L.ph) * 0.25) * dt;
      L.y -= (0.42 + 0.22 * Math.abs(sw)) * dt;
      L.rx = sw * 0.9; L.rz = Math.cos(time * 1.7 + L.ph) * 0.7; L.ry += dt * 1.2;
      const overWater = pondDist(L.x, L.z) < -0.05;
      const floor = overWater ? 0.009 : terrainH(L.x, L.z) + 0.022;
      if (L.y <= floor) {
        L.y = floor; L.rx = rand(-0.06, 0.06); L.rz = rand(-0.06, 0.06);
        if (overWater) { L.mode = 'float'; L.life = rand(35, 70); L.vx *= 0.25; L.vz *= 0.25; addDrop(L.x, L.z, 0.075, 0.007); audio.plink(0.08); }
        else { L.mode = 'rest'; L.life = rand(25, 60); }
      }
    } else if (L.mode === 'float') {
      pushByCursor(L, 0.5, 2.6, dt);
      L.vx += (vn2(L.x * 0.6 + time * 0.03, L.z * 0.6) - 0.5) * 0.02 * dt + 0.004 * dt;
      L.vz += (vn2(L.x * 0.6, L.z * 0.6 + time * 0.03) - 0.5) * 0.02 * dt;
      const dmp = Math.exp(-dt * 0.9); L.vx *= dmp; L.vz *= dmp;
      const nx = L.x + L.vx * dt, nz = L.z + L.vz * dt;
      if (pondDist(nx, nz) < -0.22) { L.x = nx; L.z = nz; } else { L.vx *= -0.3; L.vz *= -0.3; }
      L.ry += (L.vx - L.vz) * dt * 1.5;
      L.life -= dt; if (L.life < 0) L.mode = 'fade';
    } else if (L.mode === 'rest') { L.life -= dt; if (L.life < 0) L.mode = 'fade'; }
    else if (L.mode === 'fade') { L.k -= dt * 0.5; if (L.k <= 0) { L.mode = 'wait'; L.t = rand(2, 22); L.y = -5; L.k = 1; } }
    const s = L.s * (L.mode === 'fade' ? Math.max(L.k, 0.001) : 1);
    _m4.compose(_p.set(L.x, L.y, L.z), _q.setFromEuler(_e.set(L.rx, L.ry, L.rz)), _s.set(s, s, s));
    dynMesh.setMatrixAt(i, _m4);
  });
  dynMesh.instanceMatrix.needsUpdate = true;
}

function updateMotes(dt, time) {
  const p = motes.geometry.attributes.position;
  for (let i = 0; i < p.count; i++) {
    let x = p.getX(i) + (0.05 + 0.04 * Math.sin(time * 0.3 + i)) * dt, y = p.getY(i) + Math.sin(time * 0.5 + i * 1.7) * 0.03 * dt, z = p.getZ(i) + Math.cos(time * 0.23 + i * 0.6) * 0.03 * dt;
    if (x > 8) x -= 16;
    p.setXYZ(i, x, y, z);
  }
  p.needsUpdate = true;
}

// everything built so far is the garden; it steps aside as one when the lake is shown
const garden = new THREE.Group();
for (const c of [...scene.children]) if (c !== sky && c !== sunLight && c !== lanternLight) garden.add(c);
scene.add(garden);
// ───────────────────────────── lake: skipping stones ─────────────────────────────
// A click throws a flat stone toward the pointer. It touches down there and skips on: each hop shorter and
// lower than the last, drifting to one side as the spin takes over, a ring left at every touch, then it sinks.
const stones = [];
{
  const g = new THREE.SphereGeometry(0.17, 12, 8); g.scale(1, 0.3, 0.85);
  const m = new THREE.MeshStandardMaterial({ color: 0x4a4744, roughness: 0.7 });
  for (let i = 0; i < 6; i++) { const mesh = new THREE.Mesh(g, m); mesh.visible = false; scene.add(mesh); stones.push({ mesh, on: false, v: new V3(), hop: 0, spin: 20 }); }
}
const NSPR = 180, sprPos = new Float32Array(NSPR * 3).fill(-50), sprVel = new Float32Array(NSPR * 3), sprLife = new Float32Array(NSPR);
let sprI = 0;
const sprayPts = new THREE.Points(new THREE.BufferGeometry().setAttribute('position', new THREE.BufferAttribute(sprPos, 3)),
  new THREE.PointsMaterial({ color: 0xeaf6f8, size: 0.085, transparent: true, opacity: 0.85, depthWrite: false }));
sprayPts.frustumCulled = false; sprayPts.visible = false; scene.add(sprayPts);
function spray(x, z, n, vx, vz) {
  for (let i = 0; i < n; i++) {
    const j = sprI = (sprI + 1) % NSPR, a = Math.random() * 6.283, r = 0.4 + Math.random() * 1.1;
    sprPos[j * 3] = x; sprPos[j * 3 + 1] = 0.03; sprPos[j * 3 + 2] = z;
    sprVel[j * 3] = vx * 0.22 + Math.cos(a) * r; sprVel[j * 3 + 1] = 1.3 + Math.random() * 2.2; sprVel[j * 3 + 2] = vz * 0.22 + Math.sin(a) * r;
    sprLife[j] = 0.4 + Math.random() * 0.35;
  }
}
// How a throw of a given strength (0…1) aimed at a point on screen will go: where it leaves the hand, how fast,
// and every place it is expected to touch the water. Used both to throw and to show the path while aiming.
const POWER_TIME = 1.4;                              // seconds of holding for a full-strength throw
const throwPower = held => clamp(0.12 + 0.88 * held / POWER_TIME, 0.12, 1);
function planThrow(cx, cy, pw) {
  ndc.set(cx / innerWidth * 2 - 1, -(cy / innerHeight) * 2 + 1);
  raycaster.setFromCamera(ndc, camera);
  const o = raycaster.ray.origin, d = raycaster.ray.direction, hx = Math.hypot(d.x, d.z);
  if (hx < 1e-3) return null;
  // first touch where the pointer meets the water — but a gentle throw cannot reach far
  const dist = clamp(d.y < -1e-3 ? -o.y / d.y * hx : 99, 6, 9 + 21 * pw);
  _s.setFromMatrixColumn(camera.matrixWorld, 0);
  const from = new V3().copy(o).addScaledVector(_s, 0.45); from.y -= 0.9;      // it leaves the hand low, to the right of the eye
  let x = o.x + d.x / hx * dist, z = o.z + d.z / hx * dist;
  const dx = x - from.x, dz = z - from.z, dd = Math.hypot(dx, dz);
  let ux = dx / dd, uz = dz / dd, hs = 9 + 21 * pw;
  const T0 = 0.34 + 0.3 * pw, touches = [[x, z]];
  for (let n = 0; n < 12; n++) {
    const nhs = hs * 0.84, T = T0 * Math.pow(0.8, n);
    if (nhs * T < 1.0 || lake.heightAt(x, z) > -0.03) break;
    const a = 0.035 * (n + 1), c = Math.cos(a), sn = Math.sin(a), nx = ux * c - uz * sn, nz = ux * sn + uz * c;
    ux = nx; uz = nz; x += ux * nhs * T; z += uz * nhs * T; hs = nhs; touches.push([x, z]);
  }
  return { from, ux: dx / dd, uz: dz / dd, dd, hs: 9 + 21 * pw, T0, touches, reach: Math.hypot(x - o.x, z - o.z) };
}
function throwStone(cx, cy, pw = 0.5) {
  const pl = planThrow(cx, cy, pw);
  if (!pl) return;
  const st = stones.find(s => !s.on) || stones[0], p = st.mesh.position;
  p.copy(pl.from);
  const fly = Math.max(pl.hs, 13), T = pl.dd / fly;      // through the air to the first touch
  st.v.set(pl.ux * fly, (0.5 * 9.8 * T * T - p.y) / T, pl.uz * fly);
  st.on = true; st.hop = 0; st.hs = pl.hs; st.T0 = pl.T0; st.spin = 14 + 20 * pw; st.mesh.visible = true;
}
// while the button is held: rings on the water where the stone is expected to touch, and a strength bar by the pointer
const aimMarks = [];
{
  const g = new THREE.RingGeometry(0.17, 0.46, 24).rotateX(-Math.PI / 2);
  for (let i = 0; i < 13; i++) {
    const m = new THREE.Mesh(g, new THREE.MeshBasicMaterial({ color: 0xffffff, transparent: true, opacity: 0.6, depthWrite: false, fog: false }));
    m.visible = false; m.renderOrder = 2; scene.add(m); aimMarks.push(m);
  }
}
const powerEl = document.getElementById('power');
function hideAim() { for (const m of aimMarks) m.visible = false; powerEl.hidden = true; }
function updateAim() {
  if (ENV !== 'lake' || !downAt || downAt.cancel) { if (!powerEl.hidden) hideAim(); return; }
  const pw = throwPower((performance.now() - downAt.t) / 1000), pl = planThrow(downAt.x, downAt.y, pw);
  if (!pl) { hideAim(); return; }
  aimMarks.forEach((m, i) => {
    const t = pl.touches[i]; m.visible = !!t; if (!t) return;
    // rings grow with distance so the far ones can still be made out; the first touch and the last are the bold ones
    const s = (i === 0 ? 1.25 : 0.8) * (1 + Math.hypot(t[0] - camera.position.x, t[1] - camera.position.z) * 0.045);
    m.position.set(t[0], 0.04, t[1]); m.scale.set(s, 1, s); m.material.opacity = i === 0 || i === pl.touches.length - 1 ? 0.9 : 0.6;
  });
  powerEl.hidden = false;
  powerEl.style.left = Math.min(innerWidth - 200, downAt.x + 22) + 'px'; powerEl.style.top = Math.min(innerHeight - 70, downAt.y + 30) + 'px';      // below the pointer: the stone's path runs up the screen
  powerEl.firstElementChild.firstElementChild.style.width = Math.round(pw * 100) + '%';
  powerEl.lastElementChild.textContent = `Strength ${Math.round(pw * 100)}% · ${pl.touches.length - 1} skips · about ${Math.round(pl.reach)} m`;
}
function updateStones(dt) {
  for (const st of stones) {
    if (!st.on) continue;
    const p = st.mesh.position, v = st.v;
    v.y -= 9.8 * dt; p.addScaledVector(v, dt);
    st.mesh.rotation.set(0, st.mesh.rotation.y + st.spin * dt, 0.14);
    if (p.y > 0.03 || v.y >= 0) continue;
    if (lake.heightAt(p.x, p.z) > -0.03) { st.on = false; st.mesh.visible = false; continue; }      // came down on the shore
    const hs = Math.hypot(v.x, v.z), n = st.hop++, k = Math.pow(0.8, n);
    // (the first touch takes the strength of the throw, not the speed it happened to arrive at)
    const nhs = (n === 0 ? st.hs : hs) * 0.84, T = st.T0 * Math.pow(0.8, n) * (0.95 + Math.random() * 0.1);
    const sink = nhs * T < 1.0 || n >= 12;
    addDrop(p.x, p.z, sink ? 1.0 : 0.62, -(sink ? 0.2 : 0.13) * (0.45 + 0.55 * k));
    spray(p.x, p.z, sink ? 14 : 9, v.x, v.z);
    _p.copy(p).sub(camera.position);
    audio.skip(0.35 + 0.65 * k, clamp(_p.dot(_s.setFromMatrixColumn(camera.matrixWorld, 0)) / Math.max(_p.length(), 1) * 1.6, -1, 1), sink);
    if (sink) { st.on = false; st.mesh.visible = false; continue; }
    const a = 0.035 * (n + 1), c = Math.cos(a), s = Math.sin(a);      // the spin walks it off to one side
    v.set((v.x * c - v.z * s) / hs * nhs, 9.8 * T / 2, (v.x * s + v.z * c) / hs * nhs); p.y = 0.03;
  }
  let any = false;
  for (let j = 0; j < NSPR; j++) {
    if (sprLife[j] <= 0) continue;
    any = true; sprLife[j] -= dt; sprVel[j * 3 + 1] -= 9.8 * dt;
    sprPos[j * 3] += sprVel[j * 3] * dt; sprPos[j * 3 + 1] += sprVel[j * 3 + 1] * dt; sprPos[j * 3 + 2] += sprVel[j * 3 + 2] * dt;
    if (sprLife[j] <= 0 || sprPos[j * 3 + 1] < 0) { sprLife[j] = 0; sprPos[j * 3 + 1] = -50; }
  }
  if (any) sprayPts.geometry.attributes.position.needsUpdate = true;
}

function clearSim() { for (const rt of [simA, simB]) { renderer.setRenderTarget(rt); renderer.clear(); } renderer.setRenderTarget(null); }

// ───────────────────────────── environments & sound UI ─────────────────────────────
const store = { get: k => { try { return localStorage.getItem(k); } catch { return null; } }, set: (k, v) => { try { localStorage.setItem(k, v); } catch {} } };
const HINTS = {
  pond: 'Glide over the water · hold still and the koi come · sweep the sand to rake it · drag to look around',
  sand: 'Pick rake, hand, stick or board and draw in the sand · click to press rings · drag to look around',
  lake: 'Glide over the still lake to stir it · click to skip a stone — hold longer to throw harder · drag to look around',
};
const ENV_NAME = { pond: ['静', 'Shizuka · tranquil pond'], sand: ['枯', 'Karesansui · dry garden'], lake: ['湖', 'Mizuumi · mountain lake'] };
let hintTimer = 0;
function showHint() {
  const h = document.getElementById('hint'); h.textContent = HINTS[ENV]; h.classList.remove('gone');
  clearTimeout(hintTimer); hintTimer = setTimeout(() => h.classList.add('gone'), 10000);
}
function applyEnv(env) {
  const prev = ENV, lakeOn = env === 'lake';
  ENV = env; ISLANDS = ISL[env];
  if (lakeOn && !lake) {
    lake = createLake({ patch, NOISE, CAUSTIC, ROCK_COLOR, makeRockGeo, waterMat, U, helpers: { vn2, fbm2, sstep, clamp, mulberry32 } });
    scene.add(lake.group);
  }
  garden.visible = !lakeOn; if (lake) lake.group.visible = lakeOn;
  sprayPts.visible = lakeOn; if (!lakeOn) { hideAim(); for (const st of stones) { st.on = false; st.mesh.visible = false; } }
  // the lake's live water is a much bigger patch of the same simulation, with slower, longer-lived ripples
  U.uSimS.value = simMat.uniforms.uS.value = lakeOn ? LAKE_S : S;
  simMat.uniforms.uLake.value = waterMat.uniforms.uLake.value = lakeOn ? 1 : 0;
  simMat.uniforms.uK.value = lakeOn ? 0.22 : 1; simMat.uniforms.uDamp.value = lakeOn ? 0.997 : 0.9955;
  if (prev !== env && (lakeOn || prev === 'lake')) clearSim();
  applyView(lakeOn ? 'lake' : 'garden');
  if (todOf[viewKey] !== todName) setTimeOfDay(todOf[viewKey], true); else applySun(cur);
  U.uPond.value = env === 'pond' ? 1 : 0;
  ISL_ALL.forEach((i, n) => { if (i[3] === 'both' || i[3] === env) U.uIsl.value[n].set(i[0], i[1], i[2]); else U.uIsl.value[n].set(999, 999, 0.1); });
  for (const k in envObjs) for (const o of envObjs[k]) o.visible = k === env;
  if (!lakeOn) {
    lanternGroup.position.copy(lanternPos[env]);
    lanternLight.position.set(lanternPos[env].x, lanternPos[env].y + 0.62, lanternPos[env].z);
  }
  // leaves already lying about settle onto whatever is under them now
  for (const L of lakeOn ? [] : dynLeaves) {
    if (L.mode !== 'float' && L.mode !== 'rest') continue;
    if (pondDist(L.x, L.z) < -0.05) { L.mode = 'float'; L.y = 0.009; if (!(L.life > 0)) L.life = 30; }
    else { L.mode = 'rest'; L.y = terrainH(L.x, L.z) + 0.022; }
  }
  cursor.kind = null; cursor.lastWater = cursor.lastSand = null; dropQueue.length = 0;
  document.querySelectorAll('#envs button').forEach(b => b.classList.toggle('on', b.dataset.env === env));
  document.getElementById('kanji').textContent = ENV_NAME[env][0];
  document.getElementById('name').textContent = ENV_NAME[env][1];
  document.querySelectorAll('#tod button').forEach(b => b.classList.toggle('on', b.dataset.tod === todName));
  document.getElementById('tools').style.display = document.getElementById('resetPill').style.display = lakeOn ? 'none' : '';
  store.set('zen_env', env);
  document.getElementById('labPill').style.display = env === 'sand' ? '' : 'none';
  if (env !== 'sand') { document.getElementById('sandLab').hidden = true; audio.sand.listen(false); }
  document.getElementById('ambPill').style.display = env === 'sand' ? 'none' : '';
  if (env === 'sand') { document.getElementById('ambLab').hidden = true; document.getElementById('ambBtn').classList.remove('on'); }
  document.querySelectorAll('#ambList .amb').forEach(r => { r.style.display = lakeOn && !r.dataset.lake ? 'none' : ''; });      // the lake has only breeze and birds
}
let envBusy = false;
function setEnv(env, instant) {
  if (!ISL[env] || (env === ENV && !instant) || envBusy) return;
  if (instant) { applyEnv(env); return; }
  envBusy = true;
  const veil = document.getElementById('veil'); veil.classList.add('show');
  setTimeout(() => { applyEnv(env); showHint(); veil.classList.remove('show'); envBusy = false; }, 700);
}
document.querySelectorAll('#envs button').forEach(b => b.addEventListener('click', () => setEnv(b.dataset.env)));

document.querySelectorAll('#tools button').forEach(b => b.addEventListener('click', () => setTool(b.dataset.tool)));
document.getElementById('resetSand').addEventListener('click', () => { resetSand(); audio.sandPuff(0.8, 0); });
setTool(TOOLS[store.get('zen_tool')] ? store.get('zen_tool') : 'rake');

// sound: browsers only allow audio after a gesture, so it starts on the first click/tap/key unless switched off
const soundBtn = document.getElementById('sound');
let soundWanted = store.get('zen_sound') !== 'off';
function refreshSound() { soundBtn.textContent = audio.on ? 'Sound on' : (soundWanted ? 'Sound: click to start' : 'Sound off'); soundBtn.classList.toggle('on', audio.on); }
soundBtn.addEventListener('click', e => { e.stopPropagation(); soundWanted = !audio.on; audio.setOn(soundWanted); store.set('zen_sound', soundWanted ? 'on' : 'off'); refreshSound(); });
const firstGesture = e => { if (e.target === soundBtn) return; if (soundWanted && !audio.on) { audio.setOn(true); refreshSound(); } };   // the button handles its own click
addEventListener('pointerdown', firstGesture); addEventListener('keydown', firstGesture);
refreshSound();

// ── pond ambient sounds: one switch each, plus all on / all off ──
{
  const lab = document.getElementById('ambLab'), list = document.getElementById('ambList'), A = audio.ambient;
  // [key, name, what it sounds like, can be played on demand?]
  const AMBS = [
    ['wind', 'Breeze', 'Soft, steady air in the background', false],
    ['rustle', 'Bamboo rustle', 'Leaves stirring when the breeze picks up', false],
    ['birds', 'Birds', 'Short high chirps, every few seconds', true],
    ['chime', 'Wind chime', 'One ringing tone, 2–3 seconds, every minute or two', true],
    ['crickets', 'Crickets', 'High trills — only at dusk', false],
    ['drop', 'Water spout drop', 'A single drop now and then', true],
    ['koi', 'Koi', 'A swirl of water when a fish turns or surfaces', true],
    ['leaves', 'Falling leaves', 'A tiny plip when a leaf lands on the water', true],
    ['water', 'Water under your hand', 'Swirling water whenever the pointer moves across the water', false],
  ];
  const rows = {};
  function refresh() {
    const s = A.state;
    for (const k in rows) { rows[k].row.classList.toggle('off', !s[k]); rows[k].sw.classList.toggle('on', s[k]); rows[k].sw.textContent = s[k] ? 'On' : 'Off'; rows[k].sw.setAttribute('aria-pressed', s[k]); }
    store.set('zen_amb', JSON.stringify(s));
  }
  const startSound = () => { if (!audio.on) { soundWanted = true; audio.setOn(true); store.set('zen_sound', 'on'); refreshSound(); } };
  for (const [k, name, desc, playable] of AMBS) {
    const row = document.createElement('div'); row.className = 'amb'; if (k === 'wind' || k === 'birds' || k === 'water') row.dataset.lake = '1';
    row.innerHTML = `<div class="txt"><b>${name}</b><span>${desc}</span></div>${playable ? '<button class="hear">Hear</button>' : ''}<button class="sw" aria-label="${name}"></button>`;
    const sw = row.querySelector('.sw'); rows[k] = { row, sw };
    sw.onclick = () => { A.set({ [k]: !A.state[k] }); refresh(); };
    if (playable) row.querySelector('.hear').onclick = () => { startSound(); A.hear(k); };
    list.append(row);
  }
  const all = v => { A.set(Object.fromEntries(AMBS.map(a => [a[0], v]))); refresh(); };
  document.getElementById('ambAllOn').onclick = () => all(true);
  document.getElementById('ambAllOff').onclick = () => all(false);
  try { const saved = JSON.parse(store.get('zen_amb') || 'null'); if (saved) A.set(saved); } catch {}
  const show = v => { lab.hidden = !v; document.getElementById('ambBtn').classList.toggle('on', v); };
  document.getElementById('ambBtn').onclick = () => show(lab.hidden);
  document.getElementById('ambClose').onclick = () => show(false);
  lab.addEventListener('keydown', e => e.stopPropagation());
  refresh();
}

// ── sand-sound tuning panel: every quality of the sand sound on a slider, so it can be set by ear ──
{
  const lab = document.getElementById('sandLab'), A = audio.sand, RG = A.range;
  const SRC_NAME = { salt: 'Salt', friction: 'Friction', movement: 'Movement', drawing: 'Drawing', noise: 'Soft hiss' };
  // [key, name, left end, right end, log scale?, how the value reads]
  const SL = [
    ['vol', 'Loudness', 'quiet', 'loud', false, v => Math.round(v * 100) + '%'],
    ['bright', 'Brightness', 'dull, muffled', 'crisp, hissy', true, v => Math.round(v) + ' Hz'],
    ['low', 'Body', 'full, deep', 'thin, airy', true, v => Math.round(v) + ' Hz'],
    ['pitch', 'Grain size', 'coarse', 'fine', false, v => v.toFixed(2) + '×'],
    ['smooth', 'Smoothness', 'flickery', 'one even shhh', true, v => v.toFixed(2) + ' s'],
    ['vary', 'Unevenness', 'steady', 'uneven', false, v => Math.round(v * 100) + '%'],
    ['follow', 'Follows speed', 'same at any speed', 'louder when fast', false, v => Math.round(v * 100) + '%'],
    ['tail', 'Fade out', 'stops at once', 'lingers', true, v => v.toFixed(2) + ' s'],
  ];
  const PRE = {
    'Yours': A.defaults,
    'Silk': { src: 'salt', vol: 0.2, bright: 3000, low: 500, pitch: 1.35, smooth: 0.9, vary: 0.15, follow: 0.8, tail: 0.3 },
    'Whisper': { src: 'noise', vol: 0.22, bright: 2600, low: 700, pitch: 1, smooth: 1.0, vary: 0.1, follow: 0.9, tail: 0.35 },
    'Powder': { src: 'noise', vol: 0.3, bright: 7000, low: 2200, pitch: 1, smooth: 0.7, vary: 0.2, follow: 0.9, tail: 0.25 },
    'Dry brush': { src: 'friction', vol: 0.2, bright: 6000, low: 400, pitch: 1.1, smooth: 0.3, vary: 0.4, follow: 1, tail: 0.15 },
    'Deep drag': { src: 'movement', vol: 0.26, bright: 2200, low: 150, pitch: 0.85, smooth: 0.5, vary: 0.3, follow: 1, tail: 0.2 },
    'Finger trace': { src: 'drawing', vol: 0.22, bright: 5000, low: 300, pitch: 1, smooth: 0.4, vary: 0.3, follow: 1, tail: 0.18 },
  };
  const toPos = (k, v, log) => { const [a, b] = RG[k]; return log ? Math.log(Math.max(v, a) / a) / Math.log(b / a) : (v - a) / (b - a); };
  const toVal = (k, p, log) => { const [a, b] = RG[k]; return log ? a * Math.pow(b / a, p) : a + (b - a) * p; };
  const srcBox = document.getElementById('labSrc'), preBox = document.getElementById('labPresets'), box = document.getElementById('labSliders');
  const out = document.getElementById('labOut'), listenBtn = document.getElementById('labListen'), rows = {};
  const summary = () => { const p = A.params; return SRC_NAME[p.src] + ' · ' + SL.map(([k, n, , , , f]) => n + ' ' + f(p[k])).join(' · '); };
  function refresh() {
    const p = A.params;
    for (const b of srcBox.children) b.classList.toggle('on', b.dataset.src === p.src);
    for (const [k, , , , log, fmt] of SL) { rows[k].input.value = Math.round(toPos(k, p[k], log) * 1000); rows[k].val.textContent = fmt(p[k]); }
    out.textContent = summary();
    listenBtn.classList.toggle('on', A.listening); listenBtn.textContent = A.listening ? 'Listening… (stop)' : 'Listen';
    store.set('zen_sand_snd', JSON.stringify(p));
  }
  for (const k of A.sources) { const b = document.createElement('button'); b.textContent = SRC_NAME[k]; b.dataset.src = k; b.onclick = () => { A.set({ src: k }); refresh(); }; srcBox.append(b); }
  for (const n in PRE) { const b = document.createElement('button'); b.textContent = n; b.onclick = () => { A.set(PRE[n]); refresh(); }; preBox.append(b); }
  for (const [k, name, lo, hi, log] of SL) {
    const d = document.createElement('div'); d.className = 'sl';
    d.innerHTML = `<div class="top"><b>${name}</b><span></span></div><input type="range" min="0" max="1000" step="1" aria-label="${name}"><div class="ends"><span>${lo}</span><span>${hi}</span></div>`;
    const input = d.querySelector('input'); rows[k] = { input, val: d.querySelector('.top span') };
    input.addEventListener('input', () => { A.set({ [k]: toVal(k, input.value / 1000, log) }); refresh(); });
    box.append(d);
  }
  try { const saved = JSON.parse(store.get('zen_sand_snd') || 'null'); if (saved) A.set(saved); } catch {}
  const startSound = () => { if (!audio.on) { soundWanted = true; audio.setOn(true); store.set('zen_sound', 'on'); refreshSound(); } };
  listenBtn.onclick = () => { startSound(); A.listen(!A.listening); refresh(); };
  document.getElementById('labReset').onclick = () => { A.set(A.defaults); refresh(); };
  document.getElementById('labCopy').onclick = async e => {
    const b = e.currentTarget, txt = summary();
    try { await navigator.clipboard.writeText(txt); b.textContent = 'Copied'; } catch { b.textContent = 'Select the text below'; }
    setTimeout(() => { b.textContent = 'Copy settings'; }, 1800);
  };
  const show = v => { lab.hidden = !v; document.getElementById('labBtn').classList.toggle('on', v); if (!v) A.listen(false); refresh(); };
  document.getElementById('labBtn').onclick = () => show(lab.hidden);
  document.getElementById('labClose').onclick = () => show(false);
  lab.addEventListener('keydown', e => e.stopPropagation());      // arrow keys on a slider stay with the slider
  refresh();
}

// ───────────────────────────── main loop ─────────────────────────────
applySun(cur);
resize();
// prime the pond so it is not dead flat on the first frame
for (let i = 0; i < 5; i++) { let x, z; do { x = rand(-4, 4); z = rand(-3, 3); } while (pondDist(x, z) > -0.6); addDrop(x, z, 0.09, 0.006); }
applyEnv(ISL[store.get('zen_env')] ? store.get('zen_env') : 'pond');
showHint();

const clock = new THREE.Clock();
let simAcc = 0, dripT = 0, ambT = 2, frames = 0, perfT = 0, perfN = 0;
let simTime = 0;
function frame() {
  requestAnimationFrame(frame);
  tick(Math.min(clock.getDelta(), 0.05));
}
function tick(dt) {
  const time = (simTime += dt);
  U.uTime.value = time;

  // cursor idle tracking
  if (performance.now() / 1000 - cursor.t > 0.08) { cursor.vx *= Math.exp(-dt * 8); cursor.vz *= Math.exp(-dt * 8); cursor.speed = Math.hypot(cursor.vx, cursor.vz); }
  cursor.still = (cursor.kind === 'water' && cursor.speed < 0.35) ? cursor.still + dt : 0;

  // ambient life: spout drip + the odd insect touching the surface
  const pond = ENV === 'pond', lakeOn = ENV === 'lake', wet = pond || lakeOn;
  dripT -= dt; if (pond && dripT <= 0) { dripT = rand(0.09, 0.16); addDrop(spoutTip.x + rand(-0.01, 0.01), spoutTip.z + rand(-0.01, 0.01), 0.055, rand(-0.004, 0.006)); }
  ambT -= dt; if (pond && ambT <= 0) { ambT = rand(1.5, 5); let x, z; do { x = rand(-5, 5); z = rand(-3.6, 3.6); } while (pondDist(x, z) > -0.4); addDrop(x, z, 0.05, 0.006); }

  stepTimeOfDay(dt);
  if (pond) { updateKoi(dt, time); updatePads(dt, time); }
  if (!lakeOn) { updateLeaves(dt, time); updateMotes(dt, time); updateRake(dt); } else { updateStones(dt); updateAim(); }
  lanternLight.intensity = lakeOn ? 0 : cur.lantern * (0.9 + 0.1 * Math.sin(time * 9) * Math.sin(time * 5.3));

  simAcc += dt * 60; let steps = Math.min(3, Math.floor(simAcc)); simAcc -= steps; if (simAcc > 3) simAcc = 0;
  if (wet) { while (steps-- > 0 || dropQueue.length > MAXD * 4) stepSim(); } else dropQueue.length = 0;
  if (!lakeOn) stepSand(dt);

  controls.update();
  camera.updateMatrixWorld();
  renderer.shadowMap.needsUpdate = true;

  if (wet) {
    const water = lakeOn ? lake.water : pondWater;
    water.visible = false;
    updateReflCam();
    renderer.setRenderTarget(reflRT); renderer.render(scene, reflCam);
    camera.layers.set(0);
    if (lakeOn) for (const o of lake.aboveWater) o.visible = false;
    renderer.setRenderTarget(refrRT); renderer.render(scene, camera);
    if (lakeOn) for (const o of lake.aboveWater) o.visible = true;
    camera.layers.enable(1);
    renderer.setRenderTarget(null);
    water.visible = true;
  }
  composer.render();

  // soundscape follows the scene: gusts, where the spout is relative to the camera, what the cursor is doing
  sfx.swish *= Math.exp(-dt * 5);
  _p.copy(spoutTip).sub(camera.position); const sd = _p.length(); _s.setFromMatrixColumn(camera.matrixWorld, 0);
  audio.update(dt, { env: ENV, gust: sstep(0.25, 0.8, vn2(time * 0.11, 7.3)), dusk: clamp((cur.lantern - 2.5) / 13.5, 0, 1),
    swish: sfx.swish, swishPan: cursor.sx * 0.7, rake: sfx.rake, rakePan: cursor.sx * 0.7, spoutPan: clamp(_p.dot(_s) / sd * 1.3, -1, 1), spoutGain: clamp(7 / (2 + sd), 0.3, 1.3) });

  if (++frames === 3) document.getElementById('loading').classList.add('gone');
  // adaptive resolution: drop the pixel ratio if the machine can't hold ~45 fps
  if (time > 4) { perfT += dt; perfN++; if (perfN >= 90) { if (perfT / perfN > 1 / 42 && PR > 1) { PR = Math.max(1, PR - 0.25); resize(); } perfT = perfN = 0; } }
}
frame();

window.__zen = { get lake() { return lake; }, stones, throwStone, planThrow, aimMarks, canvas, VIEW, garden, tick, rake, setTool, resetSand, get tool() { return tool; }, audio, setEnv, clickAt, get env() { return ENV; }, THREE, renderer, scene, camera, controls, koi, pads, cursor, addDrop, setTimeOfDay, onPointer, sandQueue, PRESETS, cur, get pixelRatio() { return PR; } };
