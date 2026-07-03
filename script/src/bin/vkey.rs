//! Print the VK hash for a bb verification key file.
//! Usage: cargo run --bin vkey -- path/to/vk/vk_hash

fn main() {
    let path = std::env::args().nth(1).expect("usage: vkey <path-to-vk_hash>");
    let raw = std::fs::read(&path).expect("read vk_hash");
    if raw.len() == 32 {
        println!("0x{}", hex::encode(&raw));
    } else {
        println!("{}", String::from_utf8_lossy(&raw).trim());
    }
}
