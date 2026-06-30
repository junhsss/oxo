use oxo_kernel::logic::countdown_bytes;
use oxo_kernel::target::{assemble, run, run_at, Instr, A0, RA, T0, ZERO};
use std::path::PathBuf;
use std::process::Command;

const BASE: u64 = 0x8000_0000;
const CODE_OFF: u64 = 0x78;

fn emit_elf(code: &[u8]) -> Vec<u8> {
    let total = CODE_OFF + code.len() as u64;
    let entry = BASE + CODE_OFF;
    let mut e = Vec::new();
    e.extend_from_slice(b"\x7fELF");
    e.extend_from_slice(&[2, 1, 1, 0]);
    e.extend_from_slice(&[0u8; 8]);
    e.extend_from_slice(&2u16.to_le_bytes());
    e.extend_from_slice(&243u16.to_le_bytes());
    e.extend_from_slice(&1u32.to_le_bytes());
    e.extend_from_slice(&entry.to_le_bytes());
    e.extend_from_slice(&64u64.to_le_bytes());
    e.extend_from_slice(&0u64.to_le_bytes());
    e.extend_from_slice(&0u32.to_le_bytes());
    e.extend_from_slice(&64u16.to_le_bytes());
    e.extend_from_slice(&56u16.to_le_bytes());
    e.extend_from_slice(&1u16.to_le_bytes());
    e.extend_from_slice(&0u16.to_le_bytes());
    e.extend_from_slice(&0u16.to_le_bytes());
    e.extend_from_slice(&0u16.to_le_bytes());
    e.extend_from_slice(&1u32.to_le_bytes());
    e.extend_from_slice(&7u32.to_le_bytes());
    e.extend_from_slice(&0u64.to_le_bytes());
    e.extend_from_slice(&BASE.to_le_bytes());
    e.extend_from_slice(&BASE.to_le_bytes());
    e.extend_from_slice(&total.to_le_bytes());
    e.extend_from_slice(&total.to_le_bytes());
    e.extend_from_slice(&0x1000u64.to_le_bytes());
    assert_eq!(e.len() as u64, CODE_OFF);
    e.extend_from_slice(code);
    e
}

fn sail_bin() -> PathBuf {
    if let Ok(p) = std::env::var("OXO_SAIL") {
        return PathBuf::from(p);
    }
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../target/m3-sail/sail-riscv-Mac-arm64/bin/sail_riscv_sim")
}

fn sail_regs(code: &[u8], inst_limit: u32) -> [i64; 32] {
    let bin = sail_bin();
    assert!(
        bin.exists(),
        "Sail oracle not found at {bin:?} — set OXO_SAIL or download sail-riscv 0.12"
    );
    let elf = emit_elf(code);
    let dir = std::env::temp_dir();
    let path = dir.join(format!("oxo_m3_{}.elf", std::process::id()));
    std::fs::write(&path, &elf).unwrap();
    let out = Command::new(&bin)
        .args(["--trace-instr", "--trace-gpr", "--inst-limit"])
        .arg(inst_limit.to_string())
        .arg(&path)
        .output()
        .expect("failed to run sail_riscv_sim");
    let _ = std::fs::remove_file(&path);
    let text = String::from_utf8_lossy(&out.stdout);
    let mut regs = [0i64; 32];
    for line in text.lines() {
        let l = line.trim();
        if l.starts_with('[') && l.contains("ecall") {
            break;
        }
        if let Some(rest) = l.strip_prefix('x') {
            if let Some((idx, val)) = rest.split_once(" <- 0x") {
                if let (Ok(i), Ok(v)) = (idx.parse::<usize>(), u64::from_str_radix(val.trim(), 16))
                {
                    if i < 32 {
                        regs[i] = v as i64;
                    }
                }
            }
        }
    }
    regs
}

fn oxo_regs(code: &[u8], fuel: usize) -> [i64; 32] {
    run(code, fuel).expect("oxo machine halts").regs
}

fn oxo_regs_at(code: &[u8], fuel: usize, base: u64) -> [i64; 32] {
    run_at(code, fuel, base).expect("oxo machine halts").regs
}

#[test]
#[ignore]
fn differential_countdown_against_sail() {
    let code = countdown_bytes();
    let sail = sail_regs(&code, 300);
    let oxo = oxo_regs(&code, 300);
    let sum_to_5 = 15i64;
    assert_eq!(
        sail[A0 as usize], sum_to_5,
        "Sail must compute a0 = sum_to(5) = 15"
    );
    assert_eq!(
        oxo[A0 as usize], sail[A0 as usize],
        "oxo a0 must agree with authoritative Sail a0"
    );
    assert_eq!(
        oxo[T0 as usize], sail[T0 as usize],
        "oxo t0 must agree with Sail t0"
    );
    eprintln!(
        "M3 countdown: Sail a0={} t0={} | oxo a0={} t0={} — AGREE",
        sail[A0 as usize], sail[T0 as usize], oxo[A0 as usize], oxo[T0 as usize]
    );
}

#[test]
#[ignore]
fn differential_subset_vectors_against_sail() {
    let safe = [5u32, 6, 7, 28, 29, 30, 10, 11, 12];
    let progs: Vec<Vec<Instr>> = vec![
        vec![
            Instr::Addi(7, ZERO, 123),
            Instr::Addi(28, ZERO, -45),
            Instr::Add(6, 7, 28),
        ],
        vec![
            Instr::Addi(5, ZERO, 1000),
            Instr::Addi(6, ZERO, 337),
            Instr::Sub(29, 5, 6),
        ],
        vec![Instr::Lui(30, 0x12345), Instr::Addi(30, 30, 0x678)],
        vec![
            Instr::Addi(7, ZERO, -1),
            Instr::Addi(28, ZERO, 1),
            Instr::Add(29, 7, 28),
        ],
        vec![
            Instr::Addi(5, ZERO, 7),
            Instr::Addi(6, ZERO, 7),
            Instr::Beq(5, 6, 8),
            Instr::Addi(10, ZERO, 111),
            Instr::Addi(11, ZERO, 222),
        ],
        vec![
            Instr::Addi(5, ZERO, 3),
            Instr::Addi(6, ZERO, 9),
            Instr::Blt(5, 6, 8),
            Instr::Addi(12, ZERO, 1),
            Instr::Addi(12, ZERO, 2),
        ],
        vec![
            Instr::Addi(7, ZERO, 5),
            Instr::Bne(7, ZERO, 8),
            Instr::Addi(28, ZERO, 99),
            Instr::Addi(29, ZERO, 88),
        ],
        vec![
            Instr::Addi(10, ZERO, 41),
            Instr::Jal(ZERO, 8),
            Instr::Addi(10, ZERO, 0),
            Instr::Addi(11, ZERO, 42),
        ],
    ];
    for (n, prog) in progs.iter().enumerate() {
        let mut code = assemble(prog);
        code.extend_from_slice(&assemble(&[Instr::Ecall]));
        let sail = sail_regs(&code, 200);
        let oxo = oxo_regs(&code, 200);
        for &r in &safe {
            assert_eq!(
                oxo[r as usize] as u64, sail[r as usize] as u64,
                "prog#{n}: x{r} disagrees — oxo={:#x} sail={:#x}",
                oxo[r as usize], sail[r as usize]
            );
        }
        eprintln!("M3 subset prog#{n}: oxo == Sail on {{x5,x6,x7,x28,x29,x30,x10,x11,x12}}");
    }
}

struct Rng(u64);
impl Rng {
    fn step(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        (self.step() >> 33) % n
    }
}

const POOL: [u32; 28] = [
    1, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
    29, 30, 31,
];

fn rand_reg(r: &mut Rng) -> u32 {
    POOL[r.below(POOL.len() as u64) as usize]
}

fn rand_src(r: &mut Rng) -> u32 {
    if r.below(8) == 0 {
        ZERO
    } else {
        rand_reg(r)
    }
}

fn rand_imm12(r: &mut Rng) -> i32 {
    let edges = [-2048i32, -1, 0, 1, 2047, -1024, 1023, 5];
    if r.below(3) == 0 {
        edges[r.below(edges.len() as u64) as usize]
    } else {
        (r.below(4096) as i32) - 2048
    }
}

fn rand_imm20(r: &mut Rng) -> i32 {
    let edges = [-524288i32, -1, 0, 1, 524287, -262144, 262143, 0x12345];
    if r.below(3) == 0 {
        edges[r.below(edges.len() as u64) as usize]
    } else {
        (r.below(0x100000) as i32) - 0x80000
    }
}

fn gen_alu_prog(r: &mut Rng) -> Vec<Instr> {
    let len = 1 + r.below(12);
    let mut p = Vec::new();
    for _ in 0..len {
        let i = match r.below(4) {
            0 => Instr::Addi(rand_reg(r), rand_src(r), rand_imm12(r)),
            1 => Instr::Add(rand_reg(r), rand_src(r), rand_src(r)),
            2 => Instr::Sub(rand_reg(r), rand_src(r), rand_src(r)),
            _ => Instr::Lui(rand_reg(r), rand_imm20(r)),
        };
        p.push(i);
    }
    p
}

#[test]
#[ignore]
fn differential_fuzz_alu_against_sail() {
    let mut r = Rng(0x6f78_6f5f_6d33_5f31);
    let k = 600;
    for n in 0..k {
        let prog = gen_alu_prog(&mut r);
        let mut full: Vec<Instr> = POOL.iter().map(|&rg| Instr::Addi(rg, ZERO, 0)).collect();
        full.extend(prog.iter().cloned());
        full.push(Instr::Ecall);
        let code = assemble(&full);
        let sail = sail_regs(&code, 96);
        let oxo = oxo_regs(&code, 96);
        let mut bad = Vec::new();
        for &reg in &POOL {
            if oxo[reg as usize] as u64 != sail[reg as usize] as u64 {
                bad.push((reg, oxo[reg as usize], sail[reg as usize]));
            }
        }
        assert!(
            bad.is_empty(),
            "fuzz#{n} DIVERGENCE prog={prog:?} diffs={bad:?}"
        );
    }
    eprintln!("M3 fuzz: {k} random ALU programs — oxo == Sail on all of x{{1,5..=31}}");
}

fn gen_cf_prog(r: &mut Rng) -> Vec<Instr> {
    let body_len = 3 + r.below(10);
    let mut body = Vec::new();
    for i in 0..body_len {
        let remaining = body_len - i;
        let off = (1 + r.below(remaining)) as i32 * 4;
        let instr = match r.below(8) {
            0..=2 => Instr::Addi(rand_reg(r), rand_src(r), rand_imm12(r)),
            3 => Instr::Add(rand_reg(r), rand_src(r), rand_src(r)),
            4 => Instr::Sub(rand_reg(r), rand_src(r), rand_src(r)),
            5 => Instr::Beq(rand_reg(r), rand_src(r), off),
            6 => Instr::Bne(rand_reg(r), rand_src(r), off),
            _ => {
                if r.below(2) == 0 {
                    Instr::Blt(rand_reg(r), rand_src(r), off)
                } else {
                    Instr::Jal(ZERO, off)
                }
            }
        };
        body.push(instr);
    }
    body
}

#[test]
#[ignore]
fn differential_fuzz_controlflow_against_sail() {
    let mut r = Rng(0xc0ff_ee5f_6366_5f31);
    let k = 600;
    for n in 0..k {
        let prog = gen_cf_prog(&mut r);
        let mut full: Vec<Instr> = POOL.iter().map(|&rg| Instr::Addi(rg, ZERO, 0)).collect();
        full.extend(prog.iter().cloned());
        full.push(Instr::Ecall);
        let code = assemble(&full);
        let sail = sail_regs(&code, 96);
        let oxo = oxo_regs(&code, 96);
        let mut bad = Vec::new();
        for &reg in &POOL {
            if oxo[reg as usize] as u64 != sail[reg as usize] as u64 {
                bad.push((reg, oxo[reg as usize], sail[reg as usize]));
            }
        }
        assert!(
            bad.is_empty(),
            "cf-fuzz#{n} DIVERGENCE prog={prog:?} diffs={bad:?}"
        );
    }
    eprintln!("M3 cf-fuzz: {k} random control-flow programs — oxo == Sail on x{{1,5..=31}}");
}

const MEM_POOL: [u32; 27] = [
    1, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
    29, 30,
];

fn rand_mem_reg(r: &mut Rng) -> u32 {
    MEM_POOL[r.below(MEM_POOL.len() as u64) as usize]
}

fn rand_mem_src(r: &mut Rng) -> u32 {
    if r.below(8) == 0 {
        ZERO
    } else {
        rand_mem_reg(r)
    }
}

fn gen_mem_prog(r: &mut Rng) -> Vec<Instr> {
    let n = 3 + r.below(12);
    let mut body = Vec::new();
    for _ in 0..n {
        let off = (r.below(16) * 8) as i32;
        let instr = match r.below(5) {
            0 => Instr::Sd(rand_mem_src(r), 31, off),
            1 => Instr::Ld(rand_mem_reg(r), 31, off),
            2 => Instr::Addi(rand_mem_reg(r), rand_mem_src(r), rand_imm12(r)),
            3 => Instr::Add(rand_mem_reg(r), rand_mem_src(r), rand_mem_src(r)),
            _ => Instr::Sub(rand_mem_reg(r), rand_mem_src(r), rand_mem_src(r)),
        };
        body.push(instr);
    }
    body
}

#[test]
#[ignore]
fn differential_fuzz_memory_against_sail() {
    let mut r = Rng(0x6d65_6d5f_6d33_5f31);
    let k = 400;
    for n in 0..k {
        let body = gen_mem_prog(&mut r);
        let mut full: Vec<Instr> = POOL.iter().map(|&rg| Instr::Addi(rg, ZERO, 0)).collect();
        full.push(Instr::Lui(31, 0x40040));
        full.push(Instr::Add(31, 31, 31));
        for slot in 0..16 {
            full.push(Instr::Sd(ZERO, 31, slot * 8));
        }
        full.extend(body.iter().cloned());
        full.push(Instr::Ecall);
        let code = assemble(&full);
        let sail = sail_regs(&code, 160);
        let oxo = oxo_regs(&code, 160);
        let mut bad = Vec::new();
        for &reg in &POOL {
            if oxo[reg as usize] as u64 != sail[reg as usize] as u64 {
                bad.push((reg, oxo[reg as usize], sail[reg as usize]));
            }
        }
        assert!(
            bad.is_empty(),
            "mem-fuzz#{n} DIVERGENCE prog={body:?} diffs={bad:?}"
        );
    }
    eprintln!("M3 mem-fuzz: {k} random load/store programs — oxo == Sail on x{{1,5..=30}}, base x31=0x80080000");
}

#[test]
#[ignore]
fn differential_jalr_against_sail() {
    let entry = BASE + CODE_OFF;
    let progs: Vec<Vec<Instr>> = vec![
        vec![
            Instr::Jal(RA, 12),
            Instr::Addi(5, ZERO, 100),
            Instr::Ecall,
            Instr::Addi(6, ZERO, 200),
            Instr::Jalr(ZERO, RA, 0),
        ],
        vec![
            Instr::Jal(RA, 12),
            Instr::Addi(7, ZERO, 111),
            Instr::Ecall,
            Instr::Addi(8, ZERO, 222),
            Instr::Jalr(9, RA, 0),
        ],
        vec![
            Instr::Jal(RA, 16),
            Instr::Addi(5, ZERO, 7),
            Instr::Addi(6, ZERO, 7),
            Instr::Ecall,
            Instr::Addi(10, ZERO, 55),
            Instr::Addi(11, ZERO, 66),
            Instr::Jalr(ZERO, RA, 0),
        ],
        vec![
            Instr::Jal(RA, 16),
            Instr::Addi(5, ZERO, 1),
            Instr::Addi(6, ZERO, 2),
            Instr::Ecall,
            Instr::Jalr(ZERO, RA, 8),
        ],
    ];
    for (n, prog) in progs.iter().enumerate() {
        let mut full: Vec<Instr> = POOL.iter().map(|&rg| Instr::Addi(rg, ZERO, 0)).collect();
        full.extend(prog.iter().cloned());
        let code = assemble(&full);
        let sail = sail_regs(&code, 96);
        let oxo = oxo_regs_at(&code, 96, entry);
        for &reg in &POOL {
            assert_eq!(
                oxo[reg as usize] as u64, sail[reg as usize] as u64,
                "jalr#{n}: x{reg} oxo={:#x} sail={:#x}",
                oxo[reg as usize], sail[reg as usize]
            );
        }
        eprintln!("M3 jalr#{n}: oxo(@{entry:#x}) == Sail on x{{1,5..=31}} incl RA + Jalr-rd");
    }
}
