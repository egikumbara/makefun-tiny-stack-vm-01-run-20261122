// Tiny stack VM: 32-bit wrapping ints, 256-value stack, 64-deep call stack,
// 256 words of memory, byte I/O, ten traps. One run answers every instance
// in /input/<id>/ (program.bin + input.bin) into /output/<id>/.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
// Opcode table: [immediate bytes, popped, pushed]; absent = unknown (trap 5).
const MT = new Array(256).fill(null);
for (const [o, i, po, pu] of [
  [0, 0, 0, 0], [1, 1, 0, 1], [2, 4, 0, 1], [3, 0, 1, 0], [4, 0, 1, 2],
  [5, 0, 2, 2], [6, 0, 2, 3], [7, 0, 3, 3], [16, 0, 2, 1], [17, 0, 2, 1],
  [18, 0, 2, 1], [19, 0, 2, 1], [20, 0, 2, 1], [21, 0, 2, 1], [22, 0, 2, 1],
  [23, 0, 1, 1], [24, 0, 2, 1], [25, 0, 2, 1], [26, 0, 2, 1], [27, 0, 1, 1],
  [28, 0, 2, 1], [29, 0, 2, 1], [30, 0, 2, 1], [32, 0, 2, 1], [33, 0, 2, 1],
  [34, 0, 2, 1], [48, 2, 0, 0], [49, 2, 1, 0], [50, 2, 1, 0], [51, 2, 0, 0],
  [52, 0, 0, 0], [64, 0, 1, 1], [65, 0, 2, 0], [80, 0, 1, 0], [81, 0, 1, 0],
  [82, 0, 0, 1], [83, 0, 1, 0],
]) MT[o] = [i, po, pu];
// Runs one program on its input bytes; returns [stdout, exit code].
function run(p, inp) {
  const n = p.length, S = new Int32Array(256), C = new Int32Array(64);
  const M = new Int32Array(256), O = new Uint8Array(65536);
  let sp = 0, cp = 0, pc = 0, steps = 0, ol = 0, ip = 0;
  const out = (c) => [O.subarray(0, ol), c];
  for (;;) {
    if (steps === 1000000) return out(10);
    if (pc < 0 || pc >= n) return out(9);
    const op = p[pc], m = MT[op];
    if (!m) return out(5);
    if (pc + m[0] >= n) return out(9);
    steps++;
    const nx = pc + 1 + m[0];
    if (sp < m[1]) return out(2);
    if (sp - m[1] + m[2] > 256) return out(3);
    pc = nx;
    switch (op) {
      case 0: return out(0);
      case 1: S[sp++] = (p[nx - 1] << 24) >> 24; break;
      case 2: S[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break;
      case 3: sp--; break;
      case 4: S[sp] = S[sp - 1]; sp++; break;
      case 5: { const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; break; }
      case 6: S[sp] = S[sp - 2]; sp++; break;
      case 7: { const t = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = t; break; }
      case 23: S[sp - 1] = -S[sp - 1] | 0; break;
      case 27: S[sp - 1] = ~S[sp - 1]; break;
      case 16: case 17: case 18: case 19: case 20: case 21: case 22: case 24:
      case 25: case 26: case 28: case 29: case 30: case 32: case 33: case 34: {
        const b = S[sp - 1], a = S[sp - 2];
        let r = 0;
        if (op === 16) r = (a + b) | 0;
        else if (op === 17) r = (a - b) | 0;
        else if (op === 18) r = Math.imul(a, b);
        else if (op === 19) { if (!b) return out(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
        else if (op === 20) { if (!b) return out(4); r = b === -1 ? 0 : (a % b) | 0; }
        else if (op === 21) { if (!b) return out(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 22) { if (!b) return out(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
        else if (op === 24) r = a & b;
        else if (op === 25) r = a | b;
        else if (op === 26) r = a ^ b;
        else if (op === 28) r = a << (b & 31);
        else if (op === 29) r = a >> (b & 31);
        else if (op === 30) r = (a >>> (b & 31)) | 0;
        else if (op === 32) r = a === b ? 1 : 0;
        else if (op === 33) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2; S[sp++] = r;
        break;
      }
      case 48: case 49: case 50: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = op === 48;
        if (!take) { const v = S[--sp]; take = op === 49 ? v === 0 : v !== 0; }
        if (take) pc = nx + rel;
        break;
      }
      case 51:
        if (cp === 64) return out(7);
        C[cp++] = nx; pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 52:
        if (!cp) return out(8);
        pc = C[--cp];
        break;
      case 64: {
        const a = S[sp - 1];
        if (a < 0 || a > 255) return out(6);
        S[sp - 1] = M[a];
        break;
      }
      case 65: {
        const a = S[sp - 1], v = S[sp - 2];
        if (a < 0 || a > 255) return out(6);
        M[a] = v; sp -= 2;
        break;
      }
      case 80: {
        const t = Buffer.from(String(S[sp - 1]));
        if (ol + t.length > 65536) return out(11);
        O.set(t, ol); ol += t.length; sp--;
        break;
      }
      case 81:
        if (ol + 1 > 65536) return out(11);
        O[ol++] = S[--sp] & 255;
        break;
      case 82: S[sp++] = ip < inp.length ? inp[ip++] : -1; break;
      case 83: return out(S[--sp] & 255);
    }
  }
}
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  let prog, inp;
  try {
    prog = readFileSync(join(I, id, 'program.bin'));
    inp = readFileSync(join(I, id, 'input.bin'));
  } catch {
    prog = Buffer.alloc(0); inp = Buffer.alloc(0);
  }
  const [stdout, code] = run(prog, inp);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), stdout);
  writeFileSync(join(O, id, 'exit.txt'), String(code) + '\n');
}
