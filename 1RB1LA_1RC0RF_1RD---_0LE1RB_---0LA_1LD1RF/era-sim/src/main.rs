// era-sim: native Rust port of macro_sim.py.
//
// 1:1 port of the macro_step dispatch. Bridge axioms via raw TM simulation.
// Output: JSONL of era-boundary states (and optional axiom log).

use std::collections::HashMap;
use std::fs::File;
use std::io::{BufWriter, Write};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    M,
    M0,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Macro {
    kind: Kind,
    c: u64,
    l: Vec<u64>,
    r: Vec<u64>,
}

impl Macro {
    fn fmt_inline(&self) -> String {
        match self.kind {
            Kind::M => format!("M({:?},{},{:?})", self.l, self.c, self.r),
            Kind::M0 => format!("M0({:?},{:?})", self.l, self.r),
        }
    }
}

enum AxiomKind { R1, R2, R3 }

enum StepResult {
    Step(u64, &'static str),
    Axiom(AxiomKind),
    Halt,
    Stuck(&'static str),
}

// Macro-step dispatch. Mirrors macro_sim.py::macro_step exactly, but mutates
// `m` in place to avoid allocating fresh Vecs each step (97% sweep).
fn macro_step(m: &mut Macro) -> StepResult {
    use Kind::*;
    use StepResult::*;
    match m.kind {
        M => {
            let c = m.c;
            if m.r.is_empty() { return Stuck("M_R_empty"); }
            if c == 1 {
                if m.l.is_empty() { return Stuck("M_c1_no_L"); }
                let new_c = m.l.remove(0);
                m.c = new_c;
                m.r.insert(0, 1);
                return Step(6, "shift");
            }
            if c == 0 { return Stuck("M_c0"); }
            if c == 2 {
                if m.l.is_empty() {
                    m.l.push(1);
                } else {
                    m.l[0] += 1;
                }
                m.r[0] += 1;
                m.c = 0;
                m.kind = M0;
                let rule = if m.l.len() == 1 && m.l[0] == 1 { "sweep_to_zero_left_empty" } else { "sweep_to_zero" };
                // Need correct rule label even if l[0] was non-empty originally: use a flag.
                // Fall through: handle via separate branch below.
                let _ = rule;
                return Step(11, "sweep_to_zero"); // safe — rule name only used for era detection
            }
            if c == 3 {
                if m.l.is_empty() { return Axiom(AxiomKind::R1); }
                let new_c = m.l.remove(0) + 1;
                m.c = new_c;
                m.r[0] += 1;
                m.r.insert(0, 1);
                return Step(19, "sweep_and_shift");
            }
            // c >= 4
            let steps = 2 * c + 7;
            if m.l.is_empty() {
                m.l.push(1);
            } else {
                m.l[0] += 1;
            }
            m.r[0] += 1;
            m.c = c - 2;
            Step(steps, "sweep")
        }
        M0 => {
            if m.l.is_empty() { return Stuck("M0_L_empty"); }
            if m.r.is_empty() { return Stuck("M0_R_empty"); }
            let a = m.l[0];
            if m.r.len() >= 2 && m.r[0] == 1 && m.r[1] >= 1 { return Halt; }
            if m.r.len() == 1 {
                let rval = m.r[0];
                if rval == 1 {
                    // era_and_sweep / era_and_sweep_solo
                    let steps = 2 * (a - 1) + 27;
                    if m.l.len() >= 2 {
                        m.l.remove(0);
                        m.l[0] += 1;
                        m.c = a + 3;
                        m.kind = M;
                        return Step(steps, "era_and_sweep");
                    }
                    m.l[0] = 1;
                    m.c = a + 3;
                    m.kind = M;
                    return Step(steps, "era_and_sweep_solo");
                }
                if rval == 2 {
                    m.l.remove(0);
                    m.c = a + 3;
                    m.kind = M;
                    m.r[0] = 1;
                    return Step(8, "zero_two_solo");
                }
                if rval == 3 {
                    m.l[0] = a + 4;
                    m.c = 0;
                    m.r[0] = 1;
                    return Step(12, "zero_bounce_to_zero");
                }
                if rval == 4 {
                    m.l.remove(0);
                    m.c = a + 4;
                    m.kind = M;
                    m.r[0] = 1;
                    m.r.push(1);
                    return Step(19, "zero_bounce_and_shift");
                }
                let z = rval - 5;
                m.l[0] = a + 4;
                m.c = z + 2;
                m.kind = M;
                m.r[0] = 1;
                return Step(z + 14, "zero_bounce");
            }
            if m.r[0] == 0 { return Stuck("M0_R_starts_0"); }
            if m.r[0] == 1 { return Stuck("M0_R_starts_1_invalid"); }
            if m.r[0] == 2 {
                m.l.remove(0);
                m.c = a + 3;
                m.kind = M;
                m.r.remove(0);
                m.r[0] += 1;
                return Step(8, "zero_two");
            }
            // r[0] >= 3
            let r_len = m.r.len();
            let last = *m.r.last().unwrap();
            if last == 2 {
                if r_len == 2 {
                    if m.r[0] == 3 {
                        m.l.remove(0);
                        m.c = a + 4;
                        m.kind = M;
                        m.r.clear();
                        m.r.extend_from_slice(&[1, 1, 1]);
                        return Step(22, "multi_bounce_2_double_shift");
                    }
                    let r2 = m.r[0] - 4;
                    m.l[0] = a + 4;
                    m.c = r2 + 2;
                    m.kind = M;
                    m.r.clear();
                    m.r.extend_from_slice(&[1, 1]);
                    return Step(r2 + 24, "multi_bounce_2_and_shift");
                }
                if r_len == 3 {
                    let e = m.r[1];
                    if e == 1 { return Axiom(AxiomKind::R2); }
                    let r_prime = m.r[0] - 3;
                    let steps = r_prime + 3 + e + 17 + 6;
                    m.l[0] = a + 4;
                    m.l.insert(0, r_prime + 1);
                    m.c = e;
                    m.kind = M;
                    m.r.clear();
                    m.r.extend_from_slice(&[1, 1]);
                    return Step(steps, "multi_bounce_3run_last_2");
                }
                return Axiom(AxiomKind::R3);
            }
            if last == 1 {
                let r_prime = m.r[0] - 3;
                let n = (r_len - 2) as u64;
                let mid_sum: u64 = m.r[1..r_len-1].iter().sum();
                let steps = r_prime + 3 * n + mid_sum + 16;
                // new L = reverse(R_mid) ++ [r'+1, a+4] ++ L[1..]
                let mut new_l: Vec<u64> = Vec::with_capacity((r_len - 2) + 2 + m.l.len() - 1);
                for &x in m.r[1..r_len-1].iter().rev() { new_l.push(x); }
                new_l.push(r_prime + 1);
                new_l.push(a + 4);
                new_l.extend_from_slice(&m.l[1..]);
                m.l = new_l;
                m.c = 0;
                m.kind = M0;
                m.r.clear();
                m.r.push(1);
                return Step(steps, "multi_bounce_general_to_zero");
            }
            // last >= 3
            let r_prime = m.r[0] - 3;
            let z = last - 2;
            let n = (r_len - 2) as u64;
            let mid_sum: u64 = m.r[1..r_len-1].iter().sum();
            let steps = r_prime + z + 3 * n + mid_sum + 17;
            let mut new_l: Vec<u64> = Vec::with_capacity((r_len - 2) + 2 + m.l.len() - 1);
            for &x in m.r[1..r_len-1].iter().rev() { new_l.push(x); }
            new_l.push(r_prime + 1);
            new_l.push(a + 4);
            new_l.extend_from_slice(&m.l[1..]);
            m.l = new_l;
            m.c = z + 1;
            m.kind = M;
            m.r.clear();
            m.r.push(1);
            Step(steps, "multi_bounce_general")
        }
    }
}

// Raw TM transition table: index = state*2 + sym.
const RULES: [Option<(u8, i8, u8)>; 12] = {
    let mut t = [None; 12];
    t[0] = Some((1, 1, 1));   // A,0 -> 1RB
    t[1] = Some((1, -1, 0));  // A,1 -> 1LA
    t[2] = Some((1, 1, 2));   // B,0 -> 1RC
    t[3] = Some((0, 1, 5));   // B,1 -> 0RF
    t[4] = Some((1, 1, 3));   // C,0 -> 1RD (C,1 halt)
    t[6] = Some((0, -1, 4));  // D,0 -> 0LE
    t[7] = Some((1, 1, 1));   // D,1 -> 1RB (E,0 halt)
    t[9] = Some((0, -1, 0));  // E,1 -> 0LA
    t[10] = Some((1, -1, 3)); // F,0 -> 1LD
    t[11] = Some((1, 1, 5));  // F,1 -> 1RF
    t
};

fn bridge_axiom(m: &Macro, max_steps: u64) -> (Option<Macro>, u64, bool) {
    let (mut tape, mut head, mut state, mut leftmost, mut rightmost) = render_to_tape(m);
    if tape.is_empty() { return (None, 0, false); }

    for i in 1..=max_steps {
        let sym = *tape.get(&head).unwrap_or(&0);
        let key = (state as usize) * 2 + sym as usize;
        let Some((write, mv, new_state)) = RULES[key] else {
            return (None, i, true);
        };
        if write != sym {
            if write == 1 {
                tape.insert(head, 1);
                if head < leftmost { leftmost = head; }
                if head > rightmost { rightmost = head; }
            } else {
                tape.remove(&head);
                if tape.is_empty() { return (None, i, false); }
                if head == leftmost { leftmost = *tape.keys().min().unwrap(); }
                if head == rightmost { rightmost = *tape.keys().max().unwrap(); }
            }
        }
        head += mv as i64;
        state = new_state;

        if state != 0 { continue; }
        if let Some(mn) = detect_macro(&tape, head, state, leftmost, rightmost) {
            if check_invariant(&mn)
                && !(mn.kind == m.kind && mn.l == m.l && mn.c == m.c && mn.r == m.r)
            {
                return (Some(mn), i, false);
            }
        }
    }
    (None, max_steps, false)
}

fn render_to_tape(m: &Macro) -> (HashMap<i64, u8>, i64, u8, i64, i64) {
    let mut tape: HashMap<i64, u8> = HashMap::new();
    let head: i64 = 0;
    match m.kind {
        Kind::M => {
            tape.insert(head, 1);
            for i in 1..(m.c as i64) { tape.insert(head - i, 1); }
            let mut pos: i64 = head - (m.c as i64) - 1;
            for (j, &run_len) in m.l.iter().enumerate() {
                for _ in 0..run_len { tape.insert(pos, 1); pos -= 1; }
                if j + 1 < m.l.len() { pos -= 1; }
            }
            let mut pos: i64 = head + 3;
            for (j, &run_len) in m.r.iter().enumerate() {
                for _ in 0..run_len { tape.insert(pos, 1); pos += 1; }
                if j + 1 < m.r.len() { pos += 1; }
            }
        }
        Kind::M0 => {
            let mut pos: i64 = head - 1;
            for (j, &run_len) in m.l.iter().enumerate() {
                for _ in 0..run_len { tape.insert(pos, 1); pos -= 1; }
                if j + 1 < m.l.len() { pos -= 1; }
            }
            let mut pos: i64 = head + 3;
            for (j, &run_len) in m.r.iter().enumerate() {
                for _ in 0..run_len { tape.insert(pos, 1); pos += 1; }
                if j + 1 < m.r.len() { pos += 1; }
            }
        }
    }
    let leftmost = *tape.keys().min().unwrap();
    let rightmost = *tape.keys().max().unwrap();
    (tape, head, 0, leftmost, rightmost)
}

fn check_invariant(m: &Macro) -> bool {
    match m.kind {
        Kind::M => {
            if m.r.is_empty() { return false; }
            if m.c < 2 { return false; }
            if !m.l.iter().all(|&x| x >= 1) { return false; }
            if !m.r.iter().all(|&x| x >= 1) { return false; }
            true
        }
        Kind::M0 => {
            if m.l.is_empty() || m.r.is_empty() { return false; }
            if !m.l.iter().all(|&x| x >= 1) { return false; }
            if !m.r.iter().all(|&x| x >= 1) { return false; }
            if m.r.len() >= 2 && m.r[0] == 1 && m.r[1] >= 1 { return false; }
            true
        }
    }
}

fn detect_macro(tape: &HashMap<i64, u8>, head: i64, state: u8, leftmost: i64, rightmost: i64) -> Option<Macro> {
    if state != 0 { return None; }
    if tape.is_empty() { return None; }
    let sym = *tape.get(&head).unwrap_or(&0);
    if *tape.get(&(head + 1)).unwrap_or(&0) != 0 { return None; }
    if *tape.get(&(head + 2)).unwrap_or(&0) != 0 { return None; }

    if sym == 1 {
        let mut c: u64 = 1;
        let mut p = head - 1;
        while *tape.get(&p).unwrap_or(&0) == 1 { c += 1; p -= 1; }
        let mut l: Vec<u64> = Vec::new();
        if p - 1 >= leftmost {
            let mut pos = p - 1;
            loop {
                if *tape.get(&pos).unwrap_or(&0) != 1 { return None; }
                let mut run_len: u64 = 0;
                while pos >= leftmost && *tape.get(&pos).unwrap_or(&0) == 1 {
                    run_len += 1; pos -= 1;
                }
                l.push(run_len);
                if pos < leftmost { break; }
                if leftmost >= pos { break; }
                pos -= 1;
            }
        }
        let mut r: Vec<u64> = Vec::new();
        if head + 3 <= rightmost {
            let mut pos = head + 3;
            loop {
                if *tape.get(&pos).unwrap_or(&0) != 1 { return None; }
                let mut run_len: u64 = 0;
                while pos <= rightmost && *tape.get(&pos).unwrap_or(&0) == 1 {
                    run_len += 1; pos += 1;
                }
                r.push(run_len);
                if pos > rightmost { break; }
                if rightmost <= pos { break; }
                pos += 1;
            }
        }
        Some(Macro { kind: Kind::M, l, c, r })
    } else {
        if *tape.get(&(head - 1)).unwrap_or(&0) != 1 { return None; }
        let mut l: Vec<u64> = Vec::new();
        let mut pos = head - 1;
        loop {
            if *tape.get(&pos).unwrap_or(&0) != 1 { return None; }
            let mut run_len: u64 = 0;
            while pos >= leftmost && *tape.get(&pos).unwrap_or(&0) == 1 {
                run_len += 1; pos -= 1;
            }
            l.push(run_len);
            if pos < leftmost { break; }
            if leftmost >= pos { break; }
            pos -= 1;
        }
        let mut r: Vec<u64> = Vec::new();
        if head + 3 <= rightmost {
            let mut pos = head + 3;
            loop {
                if *tape.get(&pos).unwrap_or(&0) != 1 { return None; }
                let mut run_len: u64 = 0;
                while pos <= rightmost && *tape.get(&pos).unwrap_or(&0) == 1 {
                    run_len += 1; pos += 1;
                }
                r.push(run_len);
                if pos > rightmost { break; }
                if rightmost <= pos { break; }
                pos += 1;
            }
        }
        Some(Macro { kind: Kind::M0, l, c: 0, r })
    }
}

struct Args {
    max_macro: u64,
    max_eras: Option<u64>,
    era_log: Option<String>,
    axiom_log: Option<String>,
    verbose: Option<u64>,
}

fn parse_args() -> Args {
    let mut max_macro: u64 = 100_000;
    let mut max_eras: Option<u64> = None;
    let mut era_log: Option<String> = None;
    let mut axiom_log: Option<String> = None;
    let mut verbose: Option<u64> = None;

    let argv: Vec<String> = std::env::args().collect();
    let mut i = 1;
    while i < argv.len() {
        match argv[i].as_str() {
            "-n" | "--macro-steps" => { i += 1; max_macro = argv[i].parse().expect("-n"); }
            "-E" | "--max-eras" => { i += 1; max_eras = Some(argv[i].parse().expect("-E")); }
            "-e" | "--era-log" => { i += 1; era_log = Some(argv[i].clone()); }
            "-l" | "--log" => { i += 1; axiom_log = Some(argv[i].clone()); }
            "-v" | "--verbose" => { i += 1; verbose = Some(argv[i].parse().expect("-v")); }
            other => panic!("unknown arg: {}", other),
        }
        i += 1;
    }
    Args { max_macro, max_eras, era_log, axiom_log, verbose }
}

fn write_era_record(fp: &mut BufWriter<File>, era: u64, macro_count: u64, raw_steps: u128, m: &Macro) {
    write!(fp,
        "{{\"era\":{},\"macro_step\":{},\"raw_step\":{},\"kind\":\"{}\",\"c\":{},\"L\":[",
        era, macro_count, raw_steps,
        if m.kind == Kind::M { "M" } else { "M0" }, m.c
    ).unwrap();
    for (i, x) in m.l.iter().enumerate() {
        if i > 0 { write!(fp, ",").unwrap(); }
        write!(fp, "{}", x).unwrap();
    }
    write!(fp, "],\"R\":[").unwrap();
    for (i, x) in m.r.iter().enumerate() {
        if i > 0 { write!(fp, ",").unwrap(); }
        write!(fp, "{}", x).unwrap();
    }
    let l_sum: u64 = m.l.iter().sum();
    let r_sum: u64 = m.r.iter().sum();
    let l_head = if m.l.is_empty() { 0 } else { m.l[0] };
    let l_last = if m.l.is_empty() { 0 } else { *m.l.last().unwrap() };
    let r_head = if m.r.is_empty() { 0 } else { m.r[0] };
    let r_last = if m.r.is_empty() { 0 } else { *m.r.last().unwrap() };
    writeln!(fp,
        "],\"L_len\":{},\"L_sum\":{},\"R_len\":{},\"R_sum\":{},\"L_head\":{},\"L_last\":{},\"R_head\":{},\"R_last\":{}}}",
        m.l.len(), l_sum, m.r.len(), r_sum, l_head, l_last, r_head, r_last
    ).unwrap();
}

fn classify_axiom(m: &Macro) -> (&'static str, String) {
    match m.kind {
        Kind::M => {
            if m.l.is_empty() && m.c == 3 && !m.r.is_empty() {
                return ("R1", format!("d={}", m.r[0]));
            }
        }
        Kind::M0 => {
            if !m.l.is_empty() && !m.r.is_empty() && m.r[0] >= 3 && *m.r.last().unwrap() == 2 {
                if m.r.len() == 3 && m.r[1] == 1 {
                    return ("R2", format!("r={},a={}", m.r[0] - 3, m.l[0]));
                }
                if m.r.len() >= 4 {
                    return ("R3", format!("r={},a={}", m.r[0] - 3, m.l[0]));
                }
            }
        }
    }
    ("?", String::new())
}

fn main() {
    let args = parse_args();

    let mut m = Macro { kind: Kind::M, l: vec![1], c: 4, r: vec![1] };
    let mut raw_steps: u128 = 43;
    let mut macro_count: u64 = 0;
    let mut era: u64 = 0;
    let mut halted = false;
    let mut stuck: Option<&'static str> = None;

    let mut era_fp = args.era_log.as_ref().map(|p| BufWriter::new(File::create(p).expect("era log")));
    let mut ax_fp = args.axiom_log.as_ref().map(|p| BufWriter::new(File::create(p).expect("axiom log")));

    if let Some(fp) = era_fp.as_mut() {
        write_era_record(fp, 0, 0, raw_steps, &m);
    }

    let start = std::time::Instant::now();

    while macro_count < args.max_macro {
        macro_count += 1;
        if let Some(period) = args.verbose {
            if macro_count % period == 0 {
                eprintln!("  [m={} era={} raw~{} elapsed={}.{:03}s] {}",
                    macro_count, era, raw_steps,
                    start.elapsed().as_secs(),
                    start.elapsed().subsec_millis(),
                    m.fmt_inline());
            }
        }
        match macro_step(&mut m) {
            StepResult::Step(steps, rule) => {
                raw_steps += steps as u128;
                let is_era = rule == "era_and_sweep" || rule == "era_and_sweep_solo";
                if is_era {
                    era += 1;
                    if let Some(fp) = era_fp.as_mut() {
                        write_era_record(fp, era, macro_count, raw_steps, &m);
                    }
                    if let Some(max_e) = args.max_eras {
                        if era >= max_e { break; }
                    }
                }
            }
            StepResult::Axiom(_) => {
                let (ax_class, params) = classify_axiom(&m);
                if let Some(fp) = ax_fp.as_mut() {
                    writeln!(fp,
                        "{{\"macro_step\":{},\"raw_step\":{},\"axiom\":\"{}\",\"params\":\"{}\",\"config_in\":\"{}\"}}",
                        macro_count, raw_steps, ax_class, params, m.fmt_inline()
                    ).unwrap();
                }
                let (m_new, bridge_k, did_halt) = bridge_axiom(&m, 100_000_000);
                if did_halt {
                    halted = true;
                    eprintln!("HALT during bridge of {} at raw~{}", ax_class, raw_steps);
                    break;
                }
                let Some(m_new) = m_new else {
                    stuck = Some("bridge_failed");
                    eprintln!("BRIDGE FAILED for {} at raw~{}: {}", ax_class, raw_steps, m.fmt_inline());
                    break;
                };
                raw_steps += bridge_k as u128;
                m = m_new;
            }
            StepResult::Halt => {
                halted = true;
                eprintln!("HALT at macro={} raw~{}: {}", macro_count, raw_steps, m.fmt_inline());
                break;
            }
            StepResult::Stuck(why) => {
                stuck = Some(why);
                eprintln!("STUCK at macro={} raw~{}: {} ({})", macro_count, raw_steps, m.fmt_inline(), why);
                break;
            }
        }
    }

    if let Some(mut fp) = era_fp { fp.flush().unwrap(); }
    if let Some(mut fp) = ax_fp { fp.flush().unwrap(); }

    let dt = start.elapsed();
    eprintln!("=== Run summary ===");
    eprintln!("Halted: {}", halted);
    if let Some(s) = stuck { eprintln!("Stuck: {}", s); }
    eprintln!("Macro steps: {}", macro_count);
    eprintln!("Raw steps: ~{}", raw_steps);
    eprintln!("Era count: {}", era);
    eprintln!("Final config: {}", m.fmt_inline());
    eprintln!("Wall: {}.{:03}s", dt.as_secs(), dt.subsec_millis());
}
