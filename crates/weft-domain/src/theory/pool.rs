use std::{collections::HashMap, hash::Hash, sync::Arc};

// The arena and equality index share one owned payload. Large natural/text
// arguments are not cloned for each occurrence or quantified substitution.
#[derive(Debug)]
pub(super) struct Pool<T> {
    pub values: Vec<Arc<T>>,
    index: HashMap<Arc<T>, usize>,
}
impl<T: Eq + Hash> Default for Pool<T> {
    fn default() -> Self {
        Self {
            values: Vec::new(),
            index: HashMap::new(),
        }
    }
}
impl<T: Eq + Hash> Pool<T> {
    pub fn intern(&mut self, value: T) -> usize {
        if let Some(index) = self.index.get(&value) {
            return *index;
        }
        let index = self.values.len();
        let value = Arc::new(value);
        self.index.insert(Arc::clone(&value), index);
        self.values.push(value);
        index
    }
}
