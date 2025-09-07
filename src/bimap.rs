use std::collections::HashMap;

#[derive(Debug, Clone, Default)]
pub struct BiMap<K1, K2, V> {
    map1: HashMap<K1, K2>,
    map2: HashMap<K2, V>,
}

impl<K1, K2, V> BiMap<K1, K2, V>
where
    K1: std::hash::Hash + Eq + Clone,
    K2: std::hash::Hash + Eq + Clone,
    V: Clone,
{
    pub fn new() -> Self {
        BiMap {
            map1: HashMap::new(),
            map2: HashMap::new(),
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
}