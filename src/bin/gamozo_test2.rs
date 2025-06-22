// Test writing and resetting a memory mapping 100 million times
//
// Gamozo was ble to get this down to about 900 milliseconds.

use softmew::MMU;
use softmew::permission::Perm;

pub fn main() {
    let mut mew = MMU::new();
    mew.map_memory(0x0, 1024 * 1024, Perm::default()).unwrap();
    let data = mew.get_mapping_mut(0x100).unwrap();
    data.data_mut()[0..4].copy_from_slice(b"asdf");

    let forked = mew.snapshot();
    for _ in 0..100_000_000 {
        mew.write_perm(0x100, b"hello").unwrap();
        mew.reset(&forked);
    }
}
