struct Vector<const K: usize> {
    len: i32,
}

impl<const K: usize> Vector<K> {
    fn len(&self) -> i32 {
        self.len
    }
}

fn main() {
    let v = Vector::<2> { len: 2 };
    assert!(v.len() == 2);
}
