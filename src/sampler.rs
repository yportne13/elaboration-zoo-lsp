use std::collections::HashMap;
use std::sync::Mutex;

/// Tiny IP-capture sampling profiler. Lazy symbol resolution at the end.

#[derive(Clone)]
struct RawStack {
    ips: Vec<usize>,
}

unsafe impl Send for RawStack {}
unsafe impl Sync for RawStack {}

struct SamplerState {
    raw: Vec<RawStack>,
    skip_counter: u32,
    active: bool,
}

static SAMPLER: Sampler = Sampler {
    state: Mutex::new(SamplerState {
        raw: Vec::new(),
        skip_counter: 0,
        active: false,
    }),
};

struct Sampler {
    state: Mutex<SamplerState>,
}

impl Sampler {
    fn enable(&self) {
        let mut s = self.state.lock().unwrap();
        s.raw.clear();
        s.skip_counter = 0;
        s.active = true;
    }

    fn tick(&self) {
        let mut s = self.state.lock().unwrap();
        if !s.active {
            return;
        }
        s.skip_counter += 1;
        if s.skip_counter < 200 {
            return;
        }
        s.skip_counter = 0;
        drop(s);
        self.capture_raw();
    }

    fn capture_raw(&self) {
        let mut ips = Vec::new();
        backtrace::trace(|frame| {
            ips.push(frame.ip() as usize);
            true
        });
        if ips.len() < 3 {
            return;
        }
        let trimmed: Vec<_> = ips.into_iter().skip(2).collect();
        if trimmed.is_empty() {
            return;
        }
        let mut s = self.state.lock().unwrap();
        s.raw.push(RawStack { ips: trimmed });
    }

    fn write_folded(&self, path: &str) -> std::io::Result<()> {
        use std::collections::HashSet;
        let raw = {
            let s = self.state.lock().unwrap();
            s.raw.clone()
        };

        let mut all_ips: HashSet<usize> = HashSet::new();
        for stack in &raw {
            for &ip in &stack.ips {
                all_ips.insert(ip);
            }
        }

        use std::sync::OnceLock;
        static CACHE: OnceLock<Mutex<HashMap<usize, String>>> = OnceLock::new();
        let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));
        {
            let mut cache = cache.lock().unwrap();
            for &ip in &all_ips {
                if cache.contains_key(&ip) {
                    continue;
                }
                let mut name = String::new();
                backtrace::resolve(ip as *mut std::ffi::c_void, |sym| {
                    if let Some(n) = sym.name() {
                        name = n.to_string();
                    }
                });
                if name.is_empty() {
                    name = format!("0x{:x}", ip);
                }
                cache.insert(ip, name);
            }
        }

        let cache = cache.lock().unwrap();
        let mut folded: HashMap<String, u64> = HashMap::new();
        for stack in &raw {
            let mut line = String::new();
            for &ip in stack.ips.iter().rev() {
                if let Some(name) = cache.get(&ip) {
                    line.push_str(name);
                    line.push(';');
                }
            }
            *folded.entry(line).or_insert(0) += 1;
        }

        let mut out = String::new();
        for (stack, count) in &folded {
            out.push_str(&format!("{} {}\n", stack, count));
        }
        std::fs::write(path, out)
    }

    fn has_active(&self) -> bool {
        self.state.lock().map(|s| s.active).unwrap_or(false)
    }
}

pub fn enable() { SAMPLER.enable() }
pub fn tick() { SAMPLER.tick() }
pub fn write_folded(path: &str) -> std::io::Result<()> { SAMPLER.write_folded(path) }
pub fn has_active() -> bool { SAMPLER.has_active() }
