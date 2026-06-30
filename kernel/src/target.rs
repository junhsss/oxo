use crate::compile::{self, Branch, Expr, Func, Op, Program, Shape};
use std::collections::HashMap;

pub const ZERO: u32 = 0;
pub const RA: u32 = 1;
pub const SP: u32 = 2;
pub const T0: u32 = 5;
pub const T1: u32 = 6;
pub const T2: u32 = 7;
pub const A0: u32 = 10;
pub const A1: u32 = 11;

const STACK_TOP: u64 = 0x10_0000;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Instr {
    Addi(u32, u32, i32),
    Add(u32, u32, u32),
    Sub(u32, u32, u32),
    Lui(u32, i32),
    Beq(u32, u32, i32),
    Bne(u32, u32, i32),
    Blt(u32, u32, i32),
    Jal(u32, i32),
    Jalr(u32, u32, i32),
    Ld(u32, u32, i32),
    Sd(u32, u32, i32),
    Ecall,
    Unknown(u32),
}

fn itype(op: u32, f3: u32, rd: u32, rs1: u32, imm: i32) -> u32 {
    assert!((-(1 << 11)..(1 << 11)).contains(&imm));
    (((imm as u32) & 0xfff) << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | op
}

fn rtype(op: u32, f3: u32, f7: u32, rd: u32, rs1: u32, rs2: u32) -> u32 {
    (f7 << 25) | (rs2 << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | op
}

fn stype(op: u32, f3: u32, rs1: u32, rs2: u32, imm: i32) -> u32 {
    assert!((-(1 << 11)..(1 << 11)).contains(&imm));
    let i = (imm as u32) & 0xfff;
    ((i >> 5) << 25) | (rs2 << 20) | (rs1 << 15) | (f3 << 12) | ((i & 0x1f) << 7) | op
}

fn btype(op: u32, f3: u32, rs1: u32, rs2: u32, off: i32) -> u32 {
    assert!(off % 2 == 0 && (-(1 << 12)..(1 << 12)).contains(&off));
    let o = off as u32;
    (((o >> 12) & 1) << 31)
        | (((o >> 5) & 0x3f) << 25)
        | (rs2 << 20)
        | (rs1 << 15)
        | (f3 << 12)
        | (((o >> 1) & 0xf) << 8)
        | (((o >> 11) & 1) << 7)
        | op
}

fn jtype(op: u32, rd: u32, off: i32) -> u32 {
    assert!(off % 2 == 0 && (-(1 << 20)..(1 << 20)).contains(&off));
    let o = off as u32;
    (((o >> 20) & 1) << 31)
        | (((o >> 1) & 0x3ff) << 21)
        | (((o >> 11) & 1) << 20)
        | (((o >> 12) & 0xff) << 12)
        | (rd << 7)
        | op
}

pub fn encode(i: Instr) -> u32 {
    match i {
        Instr::Addi(rd, rs1, imm) => itype(0x13, 0, rd, rs1, imm),
        Instr::Add(rd, rs1, rs2) => rtype(0x33, 0, 0x00, rd, rs1, rs2),
        Instr::Sub(rd, rs1, rs2) => rtype(0x33, 0, 0x20, rd, rs1, rs2),
        Instr::Lui(rd, imm) => {
            assert!((-(1 << 19)..(1 << 19)).contains(&imm));
            (((imm as u32) & 0xf_ffff) << 12) | (rd << 7) | 0x37
        }
        Instr::Beq(rs1, rs2, off) => btype(0x63, 0, rs1, rs2, off),
        Instr::Bne(rs1, rs2, off) => btype(0x63, 1, rs1, rs2, off),
        Instr::Blt(rs1, rs2, off) => btype(0x63, 4, rs1, rs2, off),
        Instr::Jal(rd, off) => jtype(0x6f, rd, off),
        Instr::Jalr(rd, rs1, imm) => itype(0x67, 0, rd, rs1, imm),
        Instr::Ld(rd, rs1, off) => itype(0x03, 3, rd, rs1, off),
        Instr::Sd(rs2, rs1, off) => stype(0x23, 3, rs1, rs2, off),
        Instr::Ecall => 0x73,
        Instr::Unknown(w) => w,
    }
}

fn sext(v: u32, bits: u32) -> i32 {
    let s = 32 - bits;
    ((v << s) as i32) >> s
}

fn imm_i(w: u32) -> i32 {
    (w as i32) >> 20
}

fn imm_s(w: u32) -> i32 {
    sext((((w >> 25) & 0x7f) << 5) | ((w >> 7) & 0x1f), 12)
}

fn imm_b(w: u32) -> i32 {
    sext(
        (((w >> 31) & 1) << 12)
            | (((w >> 7) & 1) << 11)
            | (((w >> 25) & 0x3f) << 5)
            | (((w >> 8) & 0xf) << 1),
        13,
    )
}

fn imm_j(w: u32) -> i32 {
    sext(
        (((w >> 31) & 1) << 20)
            | (((w >> 12) & 0xff) << 12)
            | (((w >> 20) & 1) << 11)
            | (((w >> 21) & 0x3ff) << 1),
        21,
    )
}

fn imm_u(w: u32) -> i32 {
    sext((w >> 12) & 0xf_ffff, 20)
}

pub fn decode(w: u32) -> Instr {
    let op = w & 0x7f;
    let rd = (w >> 7) & 0x1f;
    let f3 = (w >> 12) & 0x7;
    let rs1 = (w >> 15) & 0x1f;
    let rs2 = (w >> 20) & 0x1f;
    let f7 = (w >> 25) & 0x7f;
    match (op, f3, f7) {
        (0x13, 0, _) => Instr::Addi(rd, rs1, imm_i(w)),
        (0x33, 0, 0x00) => Instr::Add(rd, rs1, rs2),
        (0x33, 0, 0x20) => Instr::Sub(rd, rs1, rs2),
        (0x37, _, _) => Instr::Lui(rd, imm_u(w)),
        (0x63, 0, _) => Instr::Beq(rs1, rs2, imm_b(w)),
        (0x63, 1, _) => Instr::Bne(rs1, rs2, imm_b(w)),
        (0x63, 4, _) => Instr::Blt(rs1, rs2, imm_b(w)),
        (0x6f, _, _) => Instr::Jal(rd, imm_j(w)),
        (0x67, 0, _) => Instr::Jalr(rd, rs1, imm_i(w)),
        (0x03, 3, _) => Instr::Ld(rd, rs1, imm_i(w)),
        (0x23, 3, _) => Instr::Sd(rs2, rs1, imm_s(w)),
        _ if w == 0x73 => Instr::Ecall,
        _ => Instr::Unknown(w),
    }
}

pub fn assemble(code: &[Instr]) -> Vec<u8> {
    let mut out = Vec::with_capacity(code.len() * 4);
    for &i in code {
        out.extend_from_slice(&encode(i).to_le_bytes());
    }
    out
}

#[derive(Debug, PartialEq, Eq)]
pub enum HaltError {
    Stuck,
    OutOfResources,
}

pub struct Cpu {
    pub regs: [i64; 32],
    pub pc: u64,
    mem: HashMap<u64, u8>,
}

impl Cpu {
    fn new() -> Cpu {
        Cpu {
            regs: [0; 32],
            pc: 0,
            mem: HashMap::new(),
        }
    }

    pub fn reg(&self, r: u32) -> i64 {
        if r == 0 {
            0
        } else {
            self.regs[r as usize]
        }
    }

    fn set(&mut self, r: u32, v: i64) {
        if r != 0 {
            self.regs[r as usize] = v;
        }
    }

    fn load8(&self, a: u64) -> u8 {
        *self.mem.get(&a).unwrap_or(&0)
    }

    fn store8(&mut self, a: u64, b: u8) {
        self.mem.insert(a, b);
    }

    fn load32(&self, a: u64) -> u32 {
        (self.load8(a) as u32)
            | ((self.load8(a + 1) as u32) << 8)
            | ((self.load8(a + 2) as u32) << 16)
            | ((self.load8(a + 3) as u32) << 24)
    }

    pub fn load64(&self, a: u64) -> i64 {
        let v = (self.load8(a) as u64)
            | ((self.load8(a + 1) as u64) << 8)
            | ((self.load8(a + 2) as u64) << 16)
            | ((self.load8(a + 3) as u64) << 24)
            | ((self.load8(a + 4) as u64) << 32)
            | ((self.load8(a + 5) as u64) << 40)
            | ((self.load8(a + 6) as u64) << 48)
            | ((self.load8(a + 7) as u64) << 56);
        v as i64
    }

    pub fn store64(&mut self, a: u64, val: i64) {
        let v = val as u64;
        self.store8(a, (v & 0xff) as u8);
        self.store8(a + 1, ((v >> 8) & 0xff) as u8);
        self.store8(a + 2, ((v >> 16) & 0xff) as u8);
        self.store8(a + 3, ((v >> 24) & 0xff) as u8);
        self.store8(a + 4, ((v >> 32) & 0xff) as u8);
        self.store8(a + 5, ((v >> 40) & 0xff) as u8);
        self.store8(a + 6, ((v >> 48) & 0xff) as u8);
        self.store8(a + 7, ((v >> 56) & 0xff) as u8);
    }

    fn exec(&mut self, i: Instr) {
        match i {
            Instr::Addi(rd, rs1, imm) => {
                self.set(rd, self.reg(rs1).wrapping_add(imm as i64));
                self.pc += 4;
            }
            Instr::Add(rd, rs1, rs2) => {
                self.set(rd, self.reg(rs1).wrapping_add(self.reg(rs2)));
                self.pc += 4;
            }
            Instr::Sub(rd, rs1, rs2) => {
                self.set(rd, self.reg(rs1).wrapping_sub(self.reg(rs2)));
                self.pc += 4;
            }
            Instr::Lui(rd, imm) => {
                self.set(rd, (imm as i64) << 12);
                self.pc += 4;
            }
            Instr::Beq(rs1, rs2, off) => {
                if self.reg(rs1) == self.reg(rs2) {
                    self.pc = self.pc.wrapping_add(off as i64 as u64);
                } else {
                    self.pc += 4;
                }
            }
            Instr::Bne(rs1, rs2, off) => {
                if self.reg(rs1) != self.reg(rs2) {
                    self.pc = self.pc.wrapping_add(off as i64 as u64);
                } else {
                    self.pc += 4;
                }
            }
            Instr::Blt(rs1, rs2, off) => {
                if self.reg(rs1) < self.reg(rs2) {
                    self.pc = self.pc.wrapping_add(off as i64 as u64);
                } else {
                    self.pc += 4;
                }
            }
            Instr::Jal(rd, off) => {
                let ret = self.pc.wrapping_add(4);
                self.set(rd, ret as i64);
                self.pc = self.pc.wrapping_add(off as i64 as u64);
            }
            Instr::Jalr(rd, rs1, imm) => {
                let ret = self.pc.wrapping_add(4);
                let t = (self.reg(rs1).wrapping_add(imm as i64) as u64) & !1u64;
                self.set(rd, ret as i64);
                self.pc = t;
            }
            Instr::Ld(rd, rs1, off) => {
                let a = self.reg(rs1).wrapping_add(off as i64) as u64;
                self.set(rd, self.load64(a));
                self.pc += 4;
            }
            Instr::Sd(rs2, rs1, off) => {
                let a = self.reg(rs1).wrapping_add(off as i64) as u64;
                self.store64(a, self.reg(rs2));
                self.pc += 4;
            }
            Instr::Ecall => {}
            Instr::Unknown(_) => {}
        }
    }
}

pub fn run(code: &[u8], fuel: usize) -> Result<Cpu, HaltError> {
    run_at(code, fuel, 0)
}

pub fn run_at(code: &[u8], fuel: usize, base: u64) -> Result<Cpu, HaltError> {
    let mut cpu = Cpu::new();
    for (k, b) in code.iter().enumerate() {
        cpu.mem.insert(base + k as u64, *b);
    }
    cpu.pc = base;
    cpu.regs[SP as usize] = STACK_TOP as i64;
    for _ in 0..fuel {
        let inst = decode(cpu.load32(cpu.pc));
        match inst {
            Instr::Ecall => return Ok(cpu),
            Instr::Unknown(_) => return Err(HaltError::Stuck),
            other => cpu.exec(other),
        }
    }
    Err(HaltError::OutOfResources)
}

enum AItem {
    Raw(Instr),
    Mark(usize),
    Beq(u32, u32, usize),
    Bne(u32, u32, usize),
    Jal(u32, usize),
}

fn round16(x: i64) -> i64 {
    (x + 15) & !15
}

fn max_len(e: &Expr, cur: usize) -> usize {
    match e {
        Expr::Ret(_) => cur,
        Expr::Let(_, rest) => max_len(rest, cur + 1),
        Expr::Case(_, _, branches) => branches
            .iter()
            .map(|b| max_len(&b.body, cur + b.nbind))
            .max()
            .unwrap_or(cur),
    }
}

fn flocals(f: &Func) -> usize {
    max_len(&f.body, f.nparams)
}

fn frame_bytes(f: &Func) -> i64 {
    round16(8 * (flocals(f) as i64 + 1))
}

fn slot_off(s: usize) -> i32 {
    let o = 8 * s as i64;
    assert!(o < 2048);
    o as i32
}

fn fits_imm12(x: i64) -> bool {
    (-2048..2048).contains(&x)
}

struct Lower<'a> {
    prog: &'a Program,
    frames: Vec<i64>,
    items: Vec<AItem>,
    next_label: usize,
}

impl Lower<'_> {
    fn fresh(&mut self) -> usize {
        let l = self.next_label;
        self.next_label += 1;
        l
    }

    fn raw(&mut self, i: Instr) {
        self.items.push(AItem::Raw(i));
    }

    fn li(&mut self, rd: u32, v: i64) {
        if fits_imm12(v) {
            self.raw(Instr::Addi(rd, ZERO, v as i32));
        } else {
            let v = v as i32;
            let hi = v.wrapping_add(0x800) >> 12;
            let lo = v - (hi << 12);
            self.raw(Instr::Lui(rd, hi));
            self.raw(Instr::Addi(rd, rd, lo));
        }
    }

    fn lower_expr(&mut self, e: &Expr, cur: usize, floc: usize) {
        match e {
            Expr::Ret(slot) => {
                self.raw(Instr::Ld(A0, SP, slot_off(*slot)));
                self.raw(Instr::Ld(RA, SP, slot_off(floc)));
                self.raw(Instr::Jalr(ZERO, RA, 0));
            }
            Expr::Let(Op::Constr(i, j, fs), rest) => {
                self.emit_constr(*i, *j, fs, cur);
                self.lower_expr(rest, cur + 1, floc);
            }
            Expr::Let(Op::Call(f, args), rest) => {
                self.emit_call(*f, args, cur);
                self.lower_expr(rest, cur + 1, floc);
            }
            Expr::Case(i, scrut, branches) => {
                self.emit_case(*i, *scrut, branches, cur, floc);
            }
        }
    }

    fn emit_constr(&mut self, i: usize, j: usize, fs: &[usize], cur: usize) {
        match compile::shape(&self.prog.sig, i) {
            Shape::EnumLike => {
                self.li(T0, j as i64);
                self.raw(Instr::Sd(T0, SP, slot_off(cur)));
            }
            Shape::NatLike => {
                if j == 0 {
                    self.raw(Instr::Sd(ZERO, SP, slot_off(cur)));
                } else {
                    self.raw(Instr::Ld(T0, SP, slot_off(fs[0])));
                    self.raw(Instr::Addi(T0, T0, 1));
                    self.raw(Instr::Sd(T0, SP, slot_off(cur)));
                }
            }
        }
    }

    fn emit_call(&mut self, f: usize, args: &[usize], cur: usize) {
        let fr = self.frames[f];
        assert_eq!(args.len(), self.prog.funcs[f].nparams);
        for (r, &a) in args.iter().enumerate() {
            self.raw(Instr::Ld(T0, SP, slot_off(a)));
            let off = -fr + 8 * r as i64;
            assert!(fits_imm12(off));
            self.raw(Instr::Sd(T0, SP, off as i32));
        }
        assert!(fits_imm12(fr));
        self.raw(Instr::Addi(SP, SP, (-fr) as i32));
        self.items.push(AItem::Jal(RA, f));
        self.raw(Instr::Addi(SP, SP, fr as i32));
        self.raw(Instr::Sd(A0, SP, slot_off(cur)));
    }

    fn emit_case(&mut self, i: usize, scrut: usize, branches: &[Branch], cur: usize, floc: usize) {
        self.raw(Instr::Ld(T1, SP, slot_off(scrut)));
        match compile::shape(&self.prog.sig, i) {
            Shape::NatLike => {
                let l1 = self.fresh();
                self.items.push(AItem::Bne(T1, ZERO, l1));
                self.lower_expr(&branches[0].body, cur, floc);
                self.items.push(AItem::Mark(l1));
                self.raw(Instr::Addi(T0, T1, -1));
                self.raw(Instr::Sd(T0, SP, slot_off(cur)));
                self.lower_expr(&branches[1].body, cur + 1, floc);
            }
            Shape::EnumLike => {
                let k = branches.len();
                let labels: Vec<usize> = (0..k - 1).map(|_| self.fresh()).collect();
                for (j, &lab) in labels.iter().enumerate() {
                    self.li(T0, j as i64);
                    self.items.push(AItem::Beq(T1, T0, lab));
                }
                self.lower_expr(&branches[k - 1].body, cur, floc);
                for (j, &lab) in labels.iter().enumerate() {
                    self.items.push(AItem::Mark(lab));
                    self.lower_expr(&branches[j].body, cur, floc);
                }
            }
        }
    }
}

fn resolve(items: Vec<AItem>) -> Vec<Instr> {
    let mut label_addr: HashMap<usize, i64> = HashMap::new();
    let mut addr = 0i64;
    for it in &items {
        match it {
            AItem::Mark(l) => {
                label_addr.insert(*l, addr);
            }
            _ => addr += 4,
        }
    }
    let mut out = Vec::new();
    let mut here = 0i64;
    for it in items {
        match it {
            AItem::Mark(_) => {}
            AItem::Raw(i) => {
                out.push(i);
                here += 4;
            }
            AItem::Beq(rs1, rs2, l) => {
                out.push(Instr::Beq(rs1, rs2, (label_addr[&l] - here) as i32));
                here += 4;
            }
            AItem::Bne(rs1, rs2, l) => {
                out.push(Instr::Bne(rs1, rs2, (label_addr[&l] - here) as i32));
                here += 4;
            }
            AItem::Jal(rd, l) => {
                out.push(Instr::Jal(rd, (label_addr[&l] - here) as i32));
                here += 4;
            }
        }
    }
    out
}

pub fn lower(prog: &Program, entry: usize, args: &[i64]) -> Vec<Instr> {
    let n = prog.funcs.len();
    let frames: Vec<i64> = prog.funcs.iter().map(frame_bytes).collect();
    let mut lo = Lower {
        prog,
        frames,
        items: Vec::new(),
        next_label: n,
    };
    let fe = lo.frames[entry];
    assert_eq!(args.len(), prog.funcs[entry].nparams);
    for (r, &v) in args.iter().enumerate() {
        lo.li(T0, v);
        let off = -fe + 8 * r as i64;
        assert!(fits_imm12(off));
        lo.raw(Instr::Sd(T0, SP, off as i32));
    }
    assert!(fits_imm12(fe));
    lo.raw(Instr::Addi(SP, SP, (-fe) as i32));
    lo.items.push(AItem::Jal(RA, entry));
    lo.raw(Instr::Ecall);
    for f in 0..n {
        lo.items.push(AItem::Mark(f));
        let floc = flocals(&prog.funcs[f]);
        lo.raw(Instr::Sd(RA, SP, slot_off(floc)));
        lo.lower_expr(&prog.funcs[f].body, prog.funcs[f].nparams, floc);
    }
    resolve(lo.items)
}

pub fn run_native(
    prog: &Program,
    entry: usize,
    args: &[i64],
    fuel: usize,
) -> Result<i64, HaltError> {
    let code = assemble(&lower(prog, entry, args));
    let cpu = run(&code, fuel)?;
    Ok(cpu.reg(A0))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encode_matches_worked_examples() {
        assert_eq!(encode(Instr::Addi(ZERO, ZERO, 0)), 0x0000_0013);
        assert_eq!(encode(Instr::Ecall), 0x0000_0073);
        assert_eq!(encode(Instr::Jal(ZERO, 0)), 0x0000_006f);
        assert_eq!(encode(Instr::Jal(RA, 0)), 0x0000_00ef);
        assert_eq!(encode(Instr::Beq(ZERO, ZERO, 0)), 0x0000_0063);
        assert_eq!(encode(Instr::Beq(A0, A1, 48)), 0x02b5_0863);
        assert_eq!(encode(Instr::Jal(RA, -32)), 0xfe1f_f0ef);
    }

    #[test]
    fn decode_inverts_worked_examples() {
        assert_eq!(decode(0x02b5_0863), Instr::Beq(A0, A1, 48));
        assert_eq!(decode(0xfe1f_f0ef), Instr::Jal(RA, -32));
        assert_eq!(decode(0x0000_0073), Instr::Ecall);
        assert_eq!(decode(0x0000_0013), Instr::Addi(ZERO, ZERO, 0));
    }

    #[test]
    fn decode_encode_round_trip() {
        let prog = [
            Instr::Addi(A0, SP, -2048),
            Instr::Addi(T0, ZERO, 2047),
            Instr::Add(A0, T1, T2),
            Instr::Sub(RA, A0, A1),
            Instr::Lui(T0, 0x1_2345),
            Instr::Lui(A0, -1),
            Instr::Beq(T0, T1, 48),
            Instr::Bne(A0, A1, -16),
            Instr::Blt(T1, T2, 4094),
            Instr::Blt(SP, RA, -4096),
            Instr::Jal(RA, -32),
            Instr::Jal(ZERO, 1048574),
            Instr::Jalr(ZERO, RA, 0),
            Instr::Jalr(A0, T0, -1),
            Instr::Ld(T0, SP, 0),
            Instr::Ld(A0, T1, -8),
            Instr::Sd(RA, SP, 16),
            Instr::Sd(T0, SP, -24),
            Instr::Ecall,
        ];
        for i in prog {
            assert_eq!(decode(encode(i)), i);
        }
    }

    #[test]
    fn emulator_runs_countdown_loop() {
        let code = assemble(&[
            Instr::Addi(A0, ZERO, 0),
            Instr::Addi(T0, ZERO, 5),
            Instr::Beq(T0, ZERO, 16),
            Instr::Add(A0, A0, T0),
            Instr::Addi(T0, T0, -1),
            Instr::Jal(ZERO, -12),
            Instr::Ecall,
        ]);
        let cpu = run(&code, 1000).unwrap();
        assert_eq!(cpu.reg(A0), 15);
    }

    #[test]
    fn emulator_runs_all_stack_call() {
        let code = assemble(&[
            Instr::Addi(T0, ZERO, 3),
            Instr::Sd(T0, SP, -24),
            Instr::Addi(T0, ZERO, 4),
            Instr::Sd(T0, SP, -16),
            Instr::Addi(SP, SP, -24),
            Instr::Jal(RA, 12),
            Instr::Addi(SP, SP, 24),
            Instr::Ecall,
            Instr::Sd(RA, SP, 16),
            Instr::Ld(T0, SP, 0),
            Instr::Ld(T1, SP, 8),
            Instr::Add(A0, T0, T1),
            Instr::Ld(RA, SP, 16),
            Instr::Jalr(ZERO, RA, 0),
        ]);
        let cpu = run(&code, 1000).unwrap();
        assert_eq!(cpu.reg(A0), 7);
        assert_eq!(cpu.reg(SP), STACK_TOP as i64);
    }

    #[test]
    fn emulator_out_of_fuel() {
        let code = assemble(&[Instr::Jal(ZERO, 0)]);
        assert!(matches!(run(&code, 1000), Err(HaltError::OutOfResources)));
    }

    use crate::compile::{compile, decode_to_eterm};
    use crate::{enorm, erase, Constructor, Context, Inductive, Sig, Term};
    use std::rc::Rc;

    fn v(i: usize) -> Term {
        Term::Var(i)
    }
    fn lam(a: Term, t: Term) -> Term {
        Term::Lam(Box::new(a), Box::new(t))
    }
    fn app(f: Term, x: Term) -> Term {
        Term::App(Box::new(f), Box::new(x))
    }

    fn nat_sig() -> Rc<Sig> {
        Rc::new(vec![Inductive {
            params: vec![],
            indices: vec![],
            sort: 1,
            constructors: vec![
                Constructor {
                    args: vec![],
                    index_values: vec![],
                },
                Constructor {
                    args: vec![Term::Ind(0)],
                    index_values: vec![],
                },
            ],
        }])
    }

    fn bool_sig() -> Rc<Sig> {
        Rc::new(vec![Inductive {
            params: vec![],
            indices: vec![],
            sort: 1,
            constructors: vec![
                Constructor {
                    args: vec![],
                    index_values: vec![],
                },
                Constructor {
                    args: vec![],
                    index_values: vec![],
                },
            ],
        }])
    }

    fn nat_bool_sig() -> Rc<Sig> {
        Rc::new(vec![
            Inductive {
                params: vec![],
                indices: vec![],
                sort: 1,
                constructors: vec![
                    Constructor {
                        args: vec![],
                        index_values: vec![],
                    },
                    Constructor {
                        args: vec![Term::Ind(0)],
                        index_values: vec![],
                    },
                ],
            },
            Inductive {
                params: vec![],
                indices: vec![],
                sort: 1,
                constructors: vec![
                    Constructor {
                        args: vec![],
                        index_values: vec![],
                    },
                    Constructor {
                        args: vec![],
                        index_values: vec![],
                    },
                ],
            },
        ])
    }

    fn nat_lit(mut k: usize) -> Term {
        let mut t = Term::Constr(0, 0);
        while k > 0 {
            t = app(Term::Constr(0, 1), t);
            k -= 1;
        }
        t
    }

    #[test]
    fn compiles_nat_plus_through_rv64i() {
        let sig = nat_sig();
        let ctx = Context::with_sig(sig.clone());
        let plus_src = lam(
            Term::Ind(0),
            lam(
                Term::Ind(0),
                app(
                    app(
                        app(app(Term::Rec(0, 1), lam(Term::Ind(0), Term::Ind(0))), v(0)),
                        lam(
                            Term::Ind(0),
                            lam(Term::Ind(0), app(Term::Constr(0, 1), v(0))),
                        ),
                    ),
                    v(1),
                ),
            ),
        );
        let (prog, entry) = compile(sig.clone(), &erase(&ctx, &plus_src).unwrap());
        let got = run_native(&prog, entry, &[2, 1], 1_000_000).unwrap();
        let applied = app(app(plus_src, nat_lit(2)), nat_lit(1));
        let want = enorm(&sig, &erase(&ctx, &applied).unwrap());
        assert_eq!(decode_to_eterm(&sig, 0, got), want);
    }

    #[test]
    fn compiles_bool_not_through_rv64i() {
        let sig = bool_sig();
        let ctx = Context::with_sig(sig.clone());
        let not_src = lam(
            Term::Ind(0),
            app(
                app(
                    app(
                        app(Term::Rec(0, 1), lam(Term::Ind(0), Term::Ind(0))),
                        Term::Constr(0, 1),
                    ),
                    Term::Constr(0, 0),
                ),
                v(0),
            ),
        );
        let (prog, entry) = compile(sig.clone(), &erase(&ctx, &not_src).unwrap());
        let tru = compile::encode(&sig, 0, 1, &[]);
        let fls = compile::encode(&sig, 0, 0, &[]);
        let got_t = run_native(&prog, entry, &[tru], 1000).unwrap();
        let got_f = run_native(&prog, entry, &[fls], 1000).unwrap();
        assert_eq!(
            decode_to_eterm(&sig, 0, got_t),
            enorm(
                &sig,
                &erase(&ctx, &app(not_src.clone(), Term::Constr(0, 1))).unwrap()
            )
        );
        assert_eq!(
            decode_to_eterm(&sig, 0, got_f),
            enorm(
                &sig,
                &erase(&ctx, &app(not_src, Term::Constr(0, 0))).unwrap()
            )
        );
    }

    #[test]
    fn compiles_even_through_rv64i() {
        let sig = nat_bool_sig();
        let ctx = Context::with_sig(sig.clone());
        let not1 = lam(
            Term::Ind(1),
            app(
                app(
                    app(
                        app(Term::Rec(1, 1), lam(Term::Ind(1), Term::Ind(1))),
                        Term::Constr(1, 1),
                    ),
                    Term::Constr(1, 0),
                ),
                v(0),
            ),
        );
        let even_src = lam(
            Term::Ind(0),
            app(
                app(
                    app(
                        app(Term::Rec(0, 1), lam(Term::Ind(0), Term::Ind(1))),
                        Term::Constr(1, 1),
                    ),
                    lam(Term::Ind(0), lam(Term::Ind(1), app(not1, v(0)))),
                ),
                v(0),
            ),
        );
        let (prog, entry) = compile(sig.clone(), &erase(&ctx, &even_src).unwrap());
        let got4 = run_native(&prog, entry, &[4], 1_000_000).unwrap();
        let got3 = run_native(&prog, entry, &[3], 1_000_000).unwrap();
        assert_eq!(
            decode_to_eterm(&sig, 1, got4),
            enorm(
                &sig,
                &erase(&ctx, &app(even_src.clone(), nat_lit(4))).unwrap()
            )
        );
        assert_eq!(
            decode_to_eterm(&sig, 1, got3),
            enorm(&sig, &erase(&ctx, &app(even_src, nat_lit(3))).unwrap())
        );
        assert_eq!(decode_to_eterm(&sig, 1, got4), crate::ETerm::Constr(1, 1));
        assert_eq!(decode_to_eterm(&sig, 1, got3), crate::ETerm::Constr(1, 0));
    }

    struct Rng(u64);

    impl Rng {
        fn bits(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
        fn below(&mut self, n: u64) -> u64 {
            self.bits() % n
        }
    }

    #[derive(Clone, Copy, PartialEq)]
    enum Ty {
        Nat,
        Bool,
    }

    fn ty_term(t: Ty) -> Term {
        match t {
            Ty::Nat => Term::Ind(0),
            Ty::Bool => Term::Ind(1),
        }
    }

    fn pick_var(ty: Ty, ctx: &[Ty], rng: &mut Rng) -> Option<Term> {
        let cands: Vec<usize> = (0..ctx.len())
            .filter(|&i| ctx[ctx.len() - 1 - i] == ty)
            .collect();
        if cands.is_empty() {
            None
        } else {
            Some(Term::Var(cands[rng.below(cands.len() as u64) as usize]))
        }
    }

    fn leaf(ty: Ty, ctx: &[Ty], rng: &mut Rng) -> Term {
        if rng.below(2) == 0 {
            if let Some(v) = pick_var(ty, ctx, rng) {
                return v;
            }
        }
        match ty {
            Ty::Nat => nat_lit(rng.below(3) as usize),
            Ty::Bool => Term::Constr(1, rng.below(2) as usize),
        }
    }

    fn gen_nat_rec(ty: Ty, ctx: &mut Vec<Ty>, depth: usize, rng: &mut Rng) -> Term {
        let base = gen(ty, ctx, depth - 1, rng);
        ctx.push(Ty::Nat);
        ctx.push(ty);
        let step = gen(ty, ctx, depth - 1, rng);
        ctx.pop();
        ctx.pop();
        let major = nat_lit(rng.below(3) as usize);
        app(
            app(
                app(app(Term::Rec(0, 1), lam(Term::Ind(0), ty_term(ty))), base),
                lam(Term::Ind(0), lam(ty_term(ty), step)),
            ),
            major,
        )
    }

    fn gen_bool_rec(ty: Ty, ctx: &mut Vec<Ty>, depth: usize, rng: &mut Rng) -> Term {
        let ef = gen(ty, ctx, depth - 1, rng);
        let et = gen(ty, ctx, depth - 1, rng);
        let major = gen(Ty::Bool, ctx, depth - 1, rng);
        app(
            app(
                app(app(Term::Rec(1, 1), lam(Term::Ind(1), ty_term(ty))), ef),
                et,
            ),
            major,
        )
    }

    fn gen(ty: Ty, ctx: &mut Vec<Ty>, depth: usize, rng: &mut Rng) -> Term {
        if depth == 0 || rng.below(3) == 0 {
            return leaf(ty, ctx, rng);
        }
        match ty {
            Ty::Nat => match rng.below(3) {
                0 => app(Term::Constr(0, 1), gen(Ty::Nat, ctx, depth - 1, rng)),
                1 => gen_nat_rec(ty, ctx, depth, rng),
                _ => gen_bool_rec(ty, ctx, depth, rng),
            },
            Ty::Bool => match rng.below(2) {
                0 => gen_nat_rec(ty, ctx, depth, rng),
                _ => gen_bool_rec(ty, ctx, depth, rng),
            },
        }
    }

    #[test]
    fn compiler_matches_evaluator_through_rv64i() {
        let sig = nat_bool_sig();
        let ctx = Context::with_sig(sig.clone());
        let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
        for _ in 0..2000 {
            let ty = if rng.below(2) == 0 { Ty::Nat } else { Ty::Bool };
            let mut tctx = Vec::new();
            let t = gen(ty, &mut tctx, 4, &mut rng);
            let e = erase(&ctx, &t).unwrap();
            let (prog, entry) = compile(sig.clone(), &e);
            let i = if ty == Ty::Nat { 0 } else { 1 };
            let got = run_native(&prog, entry, &[], 20_000_000).unwrap();
            assert_eq!(decode_to_eterm(&sig, i, got), enorm(&sig, &e));
        }
    }
}
