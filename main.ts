// Tiny stack VM, ISA v1 — from-scratch interpreter for tiny-stack-vm-01.
// Reads /input/<id>/{program,input}.bin, writes /output/<id>/{stdout.bin,exit.txt}.
// Deterministic: no clock, no environment reads, no randomness.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Opcode metadata: [immediate bytes, pops, pushes]; gaps are not opcodes.
const META: Array<[number, number, number, number]> = [
  [0x00, 0, 0, 0], [0x01, 1, 0, 1], [0x02, 4, 0, 1], [0x03, 0, 1, 0],
  [0x04, 0, 1, 2], [0x05, 0, 2, 2], [0x06, 0, 2, 3], [0x07, 0, 3, 3],
  [0x10, 0, 2, 1], [0x11, 0, 2, 1], [0x12, 0, 2, 1], [0x13, 0, 2, 1],
  [0x14, 0, 2, 1], [0x15, 0, 2, 1], [0x16, 0, 2, 1], [0x17, 0, 1, 1],
  [0x18, 0, 2, 1], [0x19, 0, 2, 1], [0x1a, 0, 2, 1], [0x1b, 0, 1, 1],
  [0x1c, 0, 2, 1], [0x1d, 0, 2, 1], [0x1e, 0, 2, 1],
  [0x20, 0, 2, 1], [0x21, 0, 2, 1], [0x22, 0, 2, 1],
  [0x30, 2, 0, 0], [0x31, 2, 1, 0], [0x32, 2, 1, 0], [0x33, 2, 0, 0],
  [0x34, 0, 0, 0], [0x40, 0, 1, 1], [0x41, 0, 2, 0],
  [0x50, 0, 1, 0], [0x51, 0, 1, 0], [0x52, 0, 0, 1], [0x53, 0, 1, 0],
];
const IMM = new Uint8Array(256);
const POPS = new Uint8Array(256);
const PUSH = new Uint8Array(256);
const KNOWN = new Uint8Array(256);
for (const [b, i, a, c] of META) {
  KNOWN[b] = 1;
  IMM[b] = i;
  POPS[b] = a;
  PUSH[b] = c;
}

const STACK_MAX = 256;
const CALLS_MAX = 64;
const MEM_WORDS = 256;
const STEP_LIMIT = 1000000;
const OUT_MAX = 65536;

function run(p: Uint8Array, inp: Uint8Array): { out: Uint8Array; code: number } {
  const st = new Int32Array(STACK_MAX);
  let sp = 0;
  const cs = new Int32Array(CALLS_MAX);
  let cp = 0;
  const mem = new Int32Array(MEM_WORDS);
  const out = new Uint8Array(OUT_MAX);
  let ol = 0;
  let pc = 0;
  let ip = 0;
  let steps = 0;
  const end = (code: number): { out: Uint8Array; code: number } => ({
    out: out.subarray(0, ol),
    code,
  });
  for (;;) {
    // ISA step order: step limit, pc range, opcode, immediate, stack bounds.
    if (steps === STEP_LIMIT) return end(10);
    if (pc < 0 || pc >= p.length) return end(9);
    const op = p[pc];
    if (!KNOWN[op]) return end(5);
    const imm = IMM[op];
    if (pc + imm >= p.length) return end(9);
    steps++;
    const nx = pc + 1 + imm;
    if (sp < POPS[op]) return end(2);
    if (sp - POPS[op] + PUSH[op] > STACK_MAX) return end(3);
    pc = nx;
    switch (op) {
      case 0x00:
        return end(0);
      case 0x01: // PUSH8: sign-extend the byte
        st[sp++] = (p[nx - 1] << 24) >> 24;
        break;
      case 0x02: // PUSH32: little-endian signed word
        st[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24);
        break;
      case 0x03:
        sp--;
        break;
      case 0x04:
        st[sp] = st[sp - 1];
        sp++;
        break;
      case 0x05: {
        const t = st[sp - 1];
        st[sp - 1] = st[sp - 2];
        st[sp - 2] = t;
        break;
      }
      case 0x06:
        st[sp] = st[sp - 2];
        sp++;
        break;
      case 0x07: {
        const a = st[sp - 3];
        st[sp - 3] = st[sp - 2];
        st[sp - 2] = st[sp - 1];
        st[sp - 1] = a;
        break;
      }
      case 0x17: // NEG: -INT_MIN wraps to INT_MIN
        st[sp - 1] = -st[sp - 1] | 0;
        break;
      case 0x1b:
        st[sp - 1] = ~st[sp - 1];
        break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15:
      case 0x16: case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d:
      case 0x1e: case 0x20: case 0x21: case 0x22: {
        const b = st[sp - 1];
        const a = st[sp - 2];
        let r: number;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) {
          if (b === 0) return end(4);
          // (a / b) | 0 truncates toward zero; INT_MIN / -1 wraps to INT_MIN.
          r = (a / b) | 0;
        } else if (op === 0x14) {
          if (b === 0) return end(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 0x15) {
          if (b === 0) return end(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return end(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // 0x22 LTU
        sp -= 2;
        st[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = op === 0x30;
        if (op !== 0x30) {
          const v = st[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33: // CALL: unsigned 16-bit target
        if (cp === CALLS_MAX) return end(7);
        cs[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) return end(8);
        pc = cs[--cp];
        break;
      case 0x40: {
        const addr = st[sp - 1];
        if (addr < 0 || addr >= MEM_WORDS) return end(6);
        st[sp - 1] = mem[addr];
        break;
      }
      case 0x41: {
        const addr = st[sp - 1];
        if (addr < 0 || addr >= MEM_WORDS) return end(6);
        mem[addr] = st[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: {
        const v = st[sp - 1];
        if (v >= 0 && v < 10) { // single digit: no String allocation
          if (ol + 1 > OUT_MAX) return end(11);
          sp--;
          out[ol++] = 48 + v;
          break;
        }
        const s = String(v);
        if (ol + s.length > OUT_MAX) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        break;
      }
      case 0x51:
        if (ol + 1 > OUT_MAX) return end(11);
        out[ol++] = st[--sp] & 255;
        break;
      case 0x52:
        st[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 0x53:
        return end(st[--sp] & 255);
      default:
        return end(5);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(
    new Uint8Array(readFileSync(join(I, id, 'program.bin'))),
    new Uint8Array(readFileSync(join(I, id, 'input.bin'))),
  );
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
