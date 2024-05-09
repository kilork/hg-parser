use std::sync::{Arc, Mutex};

use lru_cache::LruCache;

use crate::types::NodeHash;

pub struct Cache {
    inner: Mutex<LruCache<NodeHash, CacheEntry<[u8]>>>,
}

impl Cachable<NodeHash, [u8]> for Cache {
    fn new(capacity: usize) -> Self {
        Self {
            inner: Mutex::new(LruCache::new(capacity)),
        }
    }

    fn put(&self, key: NodeHash, value: Arc<[u8]>) -> Arc<[u8]> {
        self.inner
            .lock()
            .unwrap()
            .insert(key, CacheEntry::Normal(value.clone()));
        value
    }

    fn get(&self, key: &NodeHash) -> Option<Arc<[u8]>> {
        self.inner.lock().unwrap().get_mut(key).map(|x| match x {
            CacheEntry::Normal(x) => x.clone(),
        })
    }
}

pub enum CacheEntry<K: ?Sized> {
    Normal(Arc<K>),
}

pub trait Cachable<K, V: ?Sized> {
    fn new(capacity: usize) -> Self;
    fn get(&self, key: &K) -> Option<Arc<V>>;
    fn put(&self, key: K, value: Arc<V>) -> Arc<V>;
}
