fn main() {
    let cfg = autocfg::new();
    if cfg.probe_rustc_version(1, 34) {
        println!("cargo:rustc-cfg=has_sized_atomics");
    }
}
