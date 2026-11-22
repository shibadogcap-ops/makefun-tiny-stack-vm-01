// make.fun tiny stack VM: a from-scratch implementation of generator/subject/ISA.md.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const IL = new Int8Array(256).fill(-1), PK = new Uint8Array(256);
const def = (o, im, po, pu) => { IL[o] = im; PK[o] = (po << 2) | pu; };
def(0x00,0,0,0); def(0x01,1,0,1); def(0x02,4,0,1);
def(0x03,0,1,0); def(0x04,0,1,2); def(0x05,0,2,2); def(0x06,0,2,3); def(0x07,0,3,3);
for (const o of [0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x18,0x19,0x1a,0x1c,0x1d,0x1e,0x20,0x21,0x22]) def(o,0,2,1);
def(0x17,0,1,1); def(0x1b,0,1,1);
def(0x30,2,0,0); def(0x31,2,1,0); def(0x32,2,1,0); def(0x33,2,0,0);
def(0x34,0,0,0); def(0x40,0,1,1); def(0x41,0,2,0);
def(0x50,0,1,0); def(0x51,0,1,0); def(0x52,0,0,1); def(0x53,0,1,0);

const T = new Uint8Array(16);

function run(p, input) {
  const n = p.length;
  const D = new Int32Array(256), C = new Int32Array(64), M = new Int32Array(256);
  const out = new Uint8Array(65536);
  const R = c => ({ exit: c, out: out.subarray(0, olen) });
  let sp = 0, csp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  for (;;) {
    if (steps === 1000000) return R(10);
    if (pc < 0 || pc >= n) return R(9);
    const op = p[pc], im = IL[op];
    if (im < 0) return R(5);
    if (pc + im >= n) return R(9);
    steps++;
    const nx = pc + 1 + im, pk = PK[op], pops = pk >> 2, pushes = pk & 3;
    if (sp < pops) return R(2);
    if (sp - pops + pushes > 256) return R(3);
    pc = nx;
    switch (op) {
      case 0x00: return R(0);
      case 0x01: D[sp++] = (p[nx - 1] << 24) >> 24; break;
      case 0x02: D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp - 1]; sp++; break;
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 0x06: D[sp] = D[sp - 2]; sp++; break;
      case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1], a = D[sp - 2]; let r;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break;
          case 0x13: if (b === 0) return R(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; break;
          case 0x14: if (b === 0) return R(4); r = a % b | 0; break;
          case 0x15: if (b === 0) return R(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break;
          case 0x16: if (b === 0) return R(4); r = (a >>> 0) % (b >>> 0) | 0; break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break;
          case 0x1d: r = a >> (b & 31); break;
          case 0x1e: r = (a >>> (b & 31)) | 0; break;
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        }
        sp -= 2; D[sp++] = r; break;
      }
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break;
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break;
      case 0x30: pc = nx + (((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16); break;
      case 0x31: case 0x32: {
        const v = D[--sp], rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        if ((op === 0x31 && v === 0) || (op === 0x32 && v !== 0)) pc = nx + rel;
        break;
      }
      case 0x33: if (csp === 64) return R(7); C[csp++] = nx; pc = p[nx - 2] | (p[nx - 1] << 8); break;
      case 0x34: if (csp === 0) return R(8); pc = C[--csp]; break;
      case 0x40: { const a = D[sp - 1]; if (a < 0 || a > 255) return R(6); D[sp - 1] = M[a]; break; }
      case 0x41: { const a = D[sp - 1], v = D[sp - 2]; if (a < 0 || a > 255) return R(6); sp -= 2; M[a] = v; break; }
      case 0x50: {
        const v = D[sp - 1]; let x = v < 0 ? -v : v, m = 0, s = 0;
        if (v < 0) T[m++] = 45;
        s = m;
        do { T[m++] = 48 + (x % 10); x = Math.floor(x / 10); } while (x > 0);
        for (let a = s, b = m - 1; a < b; a++, b--) { const c = T[a]; T[a] = T[b]; T[b] = c; }
        if (olen + m > 65536) return R(11);
        sp--;
        for (let i = 0; i < m; i++) out[olen + i] = T[i];
        olen += m; break;
      }
      case 0x51: if (olen >= 65536) return R(11); out[olen++] = D[--sp] & 255; break;
      case 0x52: D[sp++] = ip < input.length ? input[ip++] : -1; break;
      case 0x53: return R(D[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  let out = new Uint8Array(0), exit = 0;
  try {
    const r = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
    out = r.out; exit = r.exit;
  } catch (e) {}
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), out);
  writeFileSync(join(O, id, 'exit.txt'), exit + '\n');
}
