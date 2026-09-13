use rustc_hash::FxHashMap;

// 双向映射的两个方向都用 FxHashMap：BiMap 只做查找/插入（src_names 等
// 热路径），不依赖迭代序（唯一的迭代用途 iter_all/values 在内存画像的
// visited 集合收集里，序无关）；FxHashMap 省去 SipHash，与仓库其他热表
// 一致（perf-debt 剩余机会 14）。
#[derive(Clone, Default)]
pub struct BiMap<K1, K2, V> {
    map1: FxHashMap<K1, K2>,
    map2: FxHashMap<K2, V>,
}

impl<K1, K2, V> std::fmt::Debug for BiMap<K1, K2, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BiMap")
            .finish()
    }
}

impl<K1, K2, V> BiMap<K1, K2, V>
where
    K1: std::hash::Hash + Eq + Clone,
    K2: std::hash::Hash + Eq + Clone,
    V: Clone,
{
    pub fn new() -> Self {
        BiMap {
            map1: FxHashMap::default(),
            map2: FxHashMap::default(),
        }
    }

    pub fn len(&self) -> usize {
        self.map1.len()
    }

    pub fn insert(&mut self, key1: K1, (key2, value): (K2, V)) {
        self.map2.insert(key2.clone(), value);
        self.map1.insert(key1, key2);
    }

    pub fn get(&self, key1: &K1) -> Option<(&K2, &V)> {
        self.map1.get(key1)
            .and_then(|k2| self.map2.get(k2).map(|v| (k2, v)))
    }

    pub fn get_by_key2(&self, key2: &K2) -> Option<&V> {
        self.map2.get(key2)
    }

    pub fn get_by_key2_mut(&mut self, key2: &K2) -> Option<&mut V> {
        self.map2.get_mut(key2)
    }

    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.map2.values()
    }

    pub fn iter_all(&self) -> impl Iterator<Item = (&K1, &K2, &V)> {
        self.map1.iter().filter_map(move |(k1, k2)| {
            self.map2.get(k2).map(|v| (k1, k2, v))
        })
    }
}