// Bigint macro-rule simulator for TM 1RB0RC_0LC0LB_0LD1LC_0LE1LA_0LF---_1RF1RA.
//
// State A(n,m) = 0^inf <F 0^n 1^m 0^inf, simulated under the macro rules
// documented in previous-work/wiki.txt:
//
//   A(4n,   m) -> A(9n+11, m-3)        (R0)
//   A(4n+1, m) -> A(9n+15, m-3)        (R1)
//   A(4n+2, m) -> A(9n+12, m-2)        (R2)
//   A(4n+3, m) -> A(9n+16, m-2)        (R3)
//   A(n, 0)    -> translated cycler    (terminal)
//   A(n, 1)    -> A(3, n+3)            (reset / cycle boundary)
//   A(n, 2)    -> halt                 (terminal)
//
// Start state: A(3, 1).

use rug::integer::Order;
use rug::{Assign, Integer};
use std::io::{Read, Write};
use std::time::Instant;

// Checkpoint format (little-endian throughout):
//   magic    : 8 bytes b"MACROSIM"
//   version  : u32     = 1
//   step     : u64
//   cycle    : u64
//   n_limbs  : u32     (number of u64 little-endian limbs of n)
//   m_limbs  : u32     (same, for m)
//   n_data   : n_limbs * 8 bytes, u64 LE limbs (least significant first)
//   m_data   : m_limbs * 8 bytes, u64 LE limbs
// File is written to "<path>.new", fsync'd, then atomically renamed onto <path>.
const CKPT_MAGIC: &[u8; 8] = b"MACROSIM";
const CKPT_VERSION: u32 = 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Rule {
    R0,
    R1,
    R2,
    R3,
    Reset,
    Halt,
    Cycler,
}

impl Rule {
    fn tag(self) -> &'static str {
        match self {
            Rule::R0 => "R0",
            Rule::R1 => "R1",
            Rule::R2 => "R2",
            Rule::R3 => "R3",
            Rule::Reset => "reset",
            Rule::Halt => "halt",
            Rule::Cycler => "cycler",
        }
    }
}

// Apply one macro step in place. Returns which rule fired.
// Precondition: n >= 0, m >= 0.
fn macro_step(n: &mut Integer, m: &mut Integer) -> Rule {
    // Terminal / reset dispatch comes first.
    if *m == 0u32 {
        return Rule::Cycler;
    }
    if *m == 1u32 {
        // (n, 1) -> (3, n + 3). Use swap to avoid an Integer clone.
        std::mem::swap(n, m); // n <- 1, m <- old_n
        *m += 3u32;
        n.assign(3);
        return Rule::Reset;
    }
    if *m == 2u32 {
        return Rule::Halt;
    }
    // m >= 3: dispatch by n mod 4.
    //
    // Fused form n := (9*n + a) >> 2 with a chosen so the result is
    // 9*floor(n/4) + c for the original c in {11,15,12,16}:
    //   r=0: 9*4q                 + 44 = 36q + 44, >>2 = 9q + 11
    //   r=1: 9*(4q+1) = 36q +  9, + 51 = 36q + 60, >>2 = 9q + 15
    //   r=2: 9*(4q+2) = 36q + 18, + 30 = 36q + 48, >>2 = 9q + 12
    //   r=3: 9*(4q+3) = 36q + 27, + 37 = 36q + 64, >>2 = 9q + 16
    // Win: `>>= 2` is a bit-shift (mpz_fdiv_q_2exp) whereas the old `/= 4`
    // went through mpz_tdiv_q_ui's 128/64 div-per-limb path. ~1.48x on this machine.
    let r = n.mod_u(4);
    let (a, dec): (u32, u32) = match r {
        0 => (44, 3),
        1 => (51, 3),
        2 => (30, 2),
        3 => (37, 2),
        _ => unreachable!(),
    };
    *n *= 9u32;
    *n += a;
    *n >>= 2u32;
    *m -= dec;
    match r {
        0 => Rule::R0,
        1 => Rule::R1,
        2 => Rule::R2,
        3 => Rule::R3,
        _ => unreachable!(),
    }
}

struct Args {
    milestone_every: u64,
    max_steps: Option<u64>,
    quiet: bool,
    checkpoint_every: u64,
    checkpoint_path: String,
    resume: Option<String>,
}

fn parse_args() -> Args {
    let mut a = Args {
        milestone_every: 1_000_000,
        max_steps: None,
        quiet: false,
        checkpoint_every: 0,
        checkpoint_path: "checkpoint.bin".to_string(),
        resume: None,
    };
    let argv: Vec<String> = std::env::args().skip(1).collect();
    let mut i = 0;
    while i < argv.len() {
        match argv[i].as_str() {
            "--milestone-every" => {
                i += 1;
                a.milestone_every = argv
                    .get(i)
                    .expect("--milestone-every needs a value")
                    .parse()
                    .expect("--milestone-every: invalid u64");
            }
            "--max-steps" => {
                i += 1;
                a.max_steps = Some(
                    argv.get(i)
                        .expect("--max-steps needs a value")
                        .parse()
                        .expect("--max-steps: invalid u64"),
                );
            }
            "--quiet" => {
                a.quiet = true;
            }
            "--checkpoint-every" => {
                i += 1;
                a.checkpoint_every = argv
                    .get(i)
                    .expect("--checkpoint-every needs a value")
                    .parse()
                    .expect("--checkpoint-every: invalid u64");
            }
            "--checkpoint-path" => {
                i += 1;
                a.checkpoint_path = argv
                    .get(i)
                    .expect("--checkpoint-path needs a value")
                    .to_string();
            }
            "--resume" => {
                i += 1;
                a.resume = Some(
                    argv.get(i)
                        .expect("--resume needs a value")
                        .to_string(),
                );
            }
            "-h" | "--help" => {
                print_usage();
                std::process::exit(0);
            }
            other => {
                eprintln!("unknown argument: {other}");
                print_usage();
                std::process::exit(2);
            }
        }
        i += 1;
    }
    a
}

fn print_usage() {
    eprintln!(
        "usage: macro-sim [--milestone-every N] [--max-steps N] [--quiet]\n\
         \x20               [--checkpoint-every N] [--checkpoint-path PATH] [--resume PATH]\n\
         \n\
         Simulates the A(n,m) macro rules for TM\n\
         1RB0RC_0LC0LB_0LD1LC_0LE1LA_0LF---_1RF1RA, starting from A(3,1).\n\
         \n\
         --milestone-every N    intra-cycle progress line every N macro steps (default 1000000)\n\
         --max-steps N          stop after N macro steps even if not terminal (default: unbounded)\n\
         --quiet                suppress intra-cycle progress lines (still prints cycle boundaries and terminal)\n\
         --checkpoint-every N   write a checkpoint every N macro steps (default 0 = disabled)\n\
         --checkpoint-path P    file path for the checkpoint (default \"checkpoint.bin\")\n\
         --resume P             resume from a previously written checkpoint at path P"
    );
}

fn write_checkpoint(
    path: &str,
    step: u64,
    cycle: u64,
    n: &Integer,
    m: &Integer,
) -> std::io::Result<()> {
    let tmp = format!("{path}.new");
    let f = std::fs::File::create(&tmp)?;
    let mut w = std::io::BufWriter::new(f);
    w.write_all(CKPT_MAGIC)?;
    w.write_all(&CKPT_VERSION.to_le_bytes())?;
    w.write_all(&step.to_le_bytes())?;
    w.write_all(&cycle.to_le_bytes())?;
    let n_digits: Vec<u64> = n.to_digits(Order::Lsf);
    let m_digits: Vec<u64> = m.to_digits(Order::Lsf);
    let n_len: u32 = n_digits
        .len()
        .try_into()
        .map_err(|_| std::io::Error::new(std::io::ErrorKind::InvalidData, "n too large"))?;
    let m_len: u32 = m_digits
        .len()
        .try_into()
        .map_err(|_| std::io::Error::new(std::io::ErrorKind::InvalidData, "m too large"))?;
    w.write_all(&n_len.to_le_bytes())?;
    w.write_all(&m_len.to_le_bytes())?;
    for d in &n_digits {
        w.write_all(&d.to_le_bytes())?;
    }
    for d in &m_digits {
        w.write_all(&d.to_le_bytes())?;
    }
    w.flush()?;
    let f = w.into_inner().map_err(|e| e.into_error())?;
    f.sync_all()?;
    std::fs::rename(&tmp, path)?;
    Ok(())
}

fn read_checkpoint(path: &str) -> std::io::Result<(u64, u64, Integer, Integer)> {
    let f = std::fs::File::open(path)?;
    let mut r = std::io::BufReader::new(f);
    let mut magic = [0u8; 8];
    r.read_exact(&mut magic)?;
    if &magic != CKPT_MAGIC {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "checkpoint: bad magic",
        ));
    }
    let mut b4 = [0u8; 4];
    let mut b8 = [0u8; 8];
    r.read_exact(&mut b4)?;
    let version = u32::from_le_bytes(b4);
    if version != CKPT_VERSION {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            format!("checkpoint: unsupported version {version}"),
        ));
    }
    r.read_exact(&mut b8)?;
    let step = u64::from_le_bytes(b8);
    r.read_exact(&mut b8)?;
    let cycle = u64::from_le_bytes(b8);
    r.read_exact(&mut b4)?;
    let n_len = u32::from_le_bytes(b4) as usize;
    r.read_exact(&mut b4)?;
    let m_len = u32::from_le_bytes(b4) as usize;
    let mut n_data = vec![0u64; n_len];
    for slot in n_data.iter_mut() {
        r.read_exact(&mut b8)?;
        *slot = u64::from_le_bytes(b8);
    }
    let mut m_data = vec![0u64; m_len];
    for slot in m_data.iter_mut() {
        r.read_exact(&mut b8)?;
        *slot = u64::from_le_bytes(b8);
    }
    let n = Integer::from_digits(&n_data, Order::Lsf);
    let m = Integer::from_digits(&m_data, Order::Lsf);
    Ok((step, cycle, n, m))
}

#[inline]
fn decimal_digits_estimate(bits: u32) -> u64 {
    // log10(2) ~ 0.30102999566. Floor-rounded; +1 when n == 0 is irrelevant here.
    ((bits as f64) * 0.30102999566398114).floor() as u64 + 1
}

fn write_witness(path: &str, n: &Integer) -> std::io::Result<()> {
    let f = std::fs::File::create(path)?;
    let mut w = std::io::BufWriter::new(f);
    let s = n.to_string_radix(10);
    w.write_all(s.as_bytes())?;
    w.write_all(b"\n")?;
    w.flush()?;
    Ok(())
}

fn print_milestone(t0: Instant, step: u64, cycle: u64, m: &Integer, n: &Integer, rule: Rule) {
    let bits = n.significant_bits();
    let dec = decimal_digits_estimate(bits);
    let elapsed = t0.elapsed().as_secs_f64();
    // m is small in our scenarios; print it directly.
    println!(
        "[{:>10.3}s] step={:>12} cycle={:>4} m={} n.bits={} n.digits~{} rule={}",
        elapsed,
        step,
        cycle,
        m,
        bits,
        dec,
        rule.tag()
    );
}

fn ends_excerpt(s: &str, k: usize) -> (String, String) {
    if s.len() <= 2 * k {
        (s.to_string(), String::new())
    } else {
        (s[..k].to_string(), s[s.len() - k..].to_string())
    }
}

fn run(args: &Args) {
    let t0 = Instant::now();
    let mut n: Integer;
    let mut m: Integer;
    let mut step: u64;
    let mut cycle: u64;

    println!("== macro-sim ==");
    println!("TM     : 1RB0RC_0LC0LB_0LD1LC_0LE1LA_0LF---_1RF1RA");

    if let Some(path) = &args.resume {
        match read_checkpoint(path) {
            Ok((s, c, nn, mm)) => {
                step = s;
                cycle = c;
                n = nn;
                m = mm;
                println!(
                    "resume : from {path} at step={step} cycle={cycle} n.bits={} m.bits={}",
                    n.significant_bits(),
                    m.significant_bits()
                );
            }
            Err(e) => {
                eprintln!("error: failed to read checkpoint {path}: {e}");
                std::process::exit(1);
            }
        }
    } else {
        n = Integer::from(3);
        m = Integer::from(1);
        step = 0;
        cycle = 0;
        println!("start  : A(3, 1)");
    }
    println!(
        "config : milestone_every={} max_steps={:?} quiet={} checkpoint_every={} checkpoint_path={:?}",
        args.milestone_every,
        args.max_steps,
        args.quiet,
        args.checkpoint_every,
        args.checkpoint_path
    );
    println!();

    loop {
        if let Some(cap) = args.max_steps {
            if step >= cap {
                println!(
                    "*** STOP (max-steps reached) at step {step}, cycle {cycle}: n.bits={} n.digits~{} m={} ***",
                    n.significant_bits(),
                    decimal_digits_estimate(n.significant_bits()),
                    m
                );
                return;
            }
        }
        let rule = macro_step(&mut n, &mut m);
        step += 1;

        match rule {
            Rule::Halt => {
                let bits = n.significant_bits();
                let dec_full = n.to_string_radix(10);
                let (head, tail) = ends_excerpt(&dec_full, 50);
                println!(
                    "*** HALT at step {step}, cycle {cycle}: n.bits={bits} n.digits={} ***",
                    dec_full.len()
                );
                if tail.is_empty() {
                    println!("    n = {head}");
                } else {
                    println!("    n head50 = {head}");
                    println!("    n tail50 = {tail}");
                }
                let elapsed = t0.elapsed().as_secs_f64();
                println!("    elapsed = {elapsed:.3}s, total macro steps = {step}");
                if let Err(e) = write_witness("halt_witness.txt", &n) {
                    eprintln!("warning: failed to write halt_witness.txt: {e}");
                } else {
                    println!("    witness written to halt_witness.txt");
                }
                return;
            }
            Rule::Cycler => {
                let bits = n.significant_bits();
                let dec_full = n.to_string_radix(10);
                let (head, tail) = ends_excerpt(&dec_full, 50);
                println!(
                    "*** CYCLER at step {step}, cycle {cycle}: n.bits={bits} n.digits={} ***",
                    dec_full.len()
                );
                if tail.is_empty() {
                    println!("    n = {head}");
                } else {
                    println!("    n head50 = {head}");
                    println!("    n tail50 = {tail}");
                }
                let elapsed = t0.elapsed().as_secs_f64();
                println!("    elapsed = {elapsed:.3}s, total macro steps = {step}");
                if let Err(e) = write_witness("cycler_witness.txt", &n) {
                    eprintln!("warning: failed to write cycler_witness.txt: {e}");
                } else {
                    println!("    witness written to cycler_witness.txt");
                }
                return;
            }
            Rule::Reset => {
                cycle += 1;
                let bits = m.significant_bits(); // after swap, m holds new_m = old_n + 3
                let dec = decimal_digits_estimate(bits);
                println!(
                    "*** cycle {cycle} open at step {step}: state = (3, m) with m.bits={bits} m.digits~{dec} ***"
                );
                if bits <= 200 {
                    println!("    m = {m}");
                }
            }
            _ => {
                if !args.quiet && step % args.milestone_every == 0 {
                    print_milestone(t0, step, cycle, &m, &n, rule);
                }
            }
        }
        if args.checkpoint_every != 0 && step % args.checkpoint_every == 0 {
            match write_checkpoint(&args.checkpoint_path, step, cycle, &n, &m) {
                Ok(()) => {
                    let elapsed = t0.elapsed().as_secs_f64();
                    println!(
                        "[{:>10.3}s] checkpoint -> {} at step={} cycle={} n.bits={}",
                        elapsed,
                        args.checkpoint_path,
                        step,
                        cycle,
                        n.significant_bits()
                    );
                }
                Err(e) => {
                    eprintln!("warning: checkpoint write failed: {e}");
                }
            }
        }
    }
}

fn main() {
    let args = parse_args();
    run(&args);
}

#[cfg(test)]
mod tests {
    use super::*;

    // Run one macro step and return (rule, n, m).
    fn step(n: i64, m: i64) -> (Rule, Integer, Integer) {
        let mut nn = Integer::from(n);
        let mut mm = Integer::from(m);
        let r = macro_step(&mut nn, &mut mm);
        (r, nn, mm)
    }

    // Exact prefix from wiki:
    //   (3,1) -> (3,6) -> (16,4) -> (47,1) -> (3,50) -> (16,48) -> (47,45) -> (115,43)
    #[test]
    fn prefix_matches_wiki() {
        let expected: &[(Rule, i64, i64)] = &[
            (Rule::Reset, 3, 6),
            (Rule::R3, 16, 4),
            (Rule::R0, 47, 1),
            (Rule::Reset, 3, 50),
            (Rule::R3, 16, 48),
            (Rule::R0, 47, 45),
            (Rule::R3, 115, 43),
        ];
        let mut n = Integer::from(3);
        let mut m = Integer::from(1);
        for (i, (er, en, em)) in expected.iter().enumerate() {
            let r = macro_step(&mut n, &mut m);
            assert_eq!(r, *er, "step {i}: wrong rule");
            assert_eq!(n, Integer::from(*en), "step {i}: wrong n");
            assert_eq!(m, Integer::from(*em), "step {i}: wrong m");
        }
    }

    // Starting from (3, 50), running until the next Reset must land at
    // (n_before_reset, m_before_reset) = (119114448, 1), then reset to (3, 119114451).
    #[test]
    fn cycle_2_ends_at_119114448() {
        let mut n = Integer::from(3);
        let mut m = Integer::from(50);
        let mut steps = 0u64;
        loop {
            // Snapshot before the step; we want the state at the moment m hits 1.
            if m == 1u32 {
                assert_eq!(n, Integer::from(119114448), "wrong terminal n for cycle 2");
                // Now apply the reset and check post-state.
                let r = macro_step(&mut n, &mut m);
                assert_eq!(r, Rule::Reset);
                assert_eq!(n, Integer::from(3));
                assert_eq!(m, Integer::from(119114451));
                return;
            }
            let r = macro_step(&mut n, &mut m);
            steps += 1;
            assert!(matches!(r, Rule::R0 | Rule::R1 | Rule::R2 | Rule::R3));
            assert!(steps < 100, "cycle 2 ran way longer than expected ({steps})");
        }
    }

    // Checkpoint roundtrip: write a state, read it back, continue simulation,
    // and verify the same trajectory as running uninterrupted.
    #[test]
    fn checkpoint_roundtrip() {
        // Reach a non-trivial state by stepping 25 times from (3, 1):
        // this lands at cycle 3 open, i.e. (3, 119114451).
        let mut n = Integer::from(3);
        let mut m = Integer::from(1);
        let mut cycle = 0u64;
        for _ in 0..25 {
            if macro_step(&mut n, &mut m) == Rule::Reset {
                cycle += 1;
            }
        }
        assert_eq!(n, Integer::from(3));
        assert_eq!(m, Integer::from(119114451u64));
        assert_eq!(cycle, 3);
        // Now run 50 more steps from there in a "reference" copy.
        let (mut ref_n, mut ref_m) = (n.clone(), m.clone());
        for _ in 0..50 {
            macro_step(&mut ref_n, &mut ref_m);
        }
        // Write checkpoint at step 25, cycle 3.
        let path = std::env::temp_dir().join("macro-sim-ckpt-test.bin");
        let path_s = path.to_string_lossy().to_string();
        write_checkpoint(&path_s, 25, 3, &n, &m).expect("write checkpoint");
        // Read back.
        let (rs, rc, mut rn, mut rm) = read_checkpoint(&path_s).expect("read checkpoint");
        assert_eq!(rs, 25);
        assert_eq!(rc, 3);
        assert_eq!(rn, Integer::from(3));
        assert_eq!(rm, Integer::from(119114451u64));
        // Continue from the read-back state and check trajectory equality.
        for _ in 0..50 {
            macro_step(&mut rn, &mut rm);
        }
        assert_eq!(rn, ref_n, "checkpoint-resumed n diverged");
        assert_eq!(rm, ref_m, "checkpoint-resumed m diverged");
        let _ = std::fs::remove_file(&path);
    }

    // Sanity on the individual rule arithmetic.
    #[test]
    fn rule_arithmetic_units() {
        // R0: A(4n, m) -> A(9n+11, m-3); take n=4, m=4 -> (47, 1)
        assert_eq!(step(16, 4), (Rule::R0, Integer::from(47), Integer::from(1)));
        // R1: A(4n+1, m) -> A(9n+15, m-3); take n=4 -> 4n+1 = 17, m=5 -> (9*4+15, 2) = (51, 2)
        assert_eq!(step(17, 5), (Rule::R1, Integer::from(51), Integer::from(2)));
        // R2: A(4n+2, m) -> A(9n+12, m-2); take n=4 -> 4n+2 = 18, m=5 -> (9*4+12, 3) = (48, 3)
        assert_eq!(step(18, 5), (Rule::R2, Integer::from(48), Integer::from(3)));
        // R3: A(4n+3, m) -> A(9n+16, m-2); take n=4 -> 4n+3 = 19, m=5 -> (9*4+16, 3) = (52, 3)
        assert_eq!(step(19, 5), (Rule::R3, Integer::from(52), Integer::from(3)));
        // Reset: A(n, 1) -> A(3, n+3); take n=10, m=1 -> (3, 13)
        assert_eq!(step(10, 1), (Rule::Reset, Integer::from(3), Integer::from(13)));
        // Halt at m=2.
        let (r, _, _) = step(7, 2);
        assert_eq!(r, Rule::Halt);
        // Cycler at m=0.
        let (r, _, _) = step(7, 0);
        assert_eq!(r, Rule::Cycler);
    }
}
