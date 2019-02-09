use std::io::{Read, Write};
use std::sync::{Arc, Mutex};

use lru_cache::LruCache;
use snap::{Reader, Writer};

use crate::types::NodeHash;

pub struct Cache {
    inner: Mutex<LruCache<NodeHash, CacheEntry<Vec<u8>>>>,
}

const THRESHOLD: usize = 50000;

impl Cachable<NodeHash, Vec<u8>> for Cache {
    fn new(capacity: usize) -> Self {
        eprintln!("cache: {}", capacity);
        Self {
            inner: Mutex::new(LruCache::new(capacity)),
        }
    }

    fn put(&self, key: NodeHash, value: Arc<Vec<u8>>) -> Arc<Vec<u8>> {
        if value.len() > THRESHOLD {
            let data = Vec::new();
            let mut snap_writer = Writer::new(data);
            snap_writer.write_all(&value).unwrap();
            self.inner
                .lock()
                .unwrap()
                .insert(key, CacheEntry::Snap(snap_writer.into_inner().unwrap()));
            value
        } else {
            self.inner
                .lock()
                .unwrap()
                .insert(key, CacheEntry::Normal(value.clone()));
            value
        }
    }

    fn get(&self, key: &NodeHash) -> Option<Arc<Vec<u8>>> {
        self.inner.lock().unwrap().get_mut(key).map(|x| match x {
            CacheEntry::Normal(x) => x.clone(),
            CacheEntry::Snap(x) => {
                let mut buf = vec![];
                Reader::new(x.as_slice()).read_to_end(&mut buf).unwrap();
                Arc::new(buf)
            }
        })
    }
}

pub enum CacheEntry<K> {
    Normal(Arc<K>),
    Snap(K),
}

pub trait Cachable<K, V> {
    fn new(capacity: usize) -> Self;
    fn get(&self, key: &K) -> Option<Arc<V>>;
    fn put(&self, key: K, value: Arc<V>) -> Arc<V>;
}
