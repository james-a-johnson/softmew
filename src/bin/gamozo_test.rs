// Test empty reset 100 million times.
//
// Gamozo was able to get this down to about 125 milliseconds.

use softmew::MMU;
use softmew::map::Perm;

pub fn main() {
    let mut mew = MMU::new();
    mew.map_memory(0x0, 1024 * 1024, Perm::default()).unwrap();
    let data = mew.get_mapping_mut(0x100).unwrap();
    data.data_mut()[0..4].copy_from_slice(b"asdf");

    let forked = mew.clone();
    for _ in 0..100_000_000 {
        mew.reset(&forked);
    }
}
