fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    // `target_feature = "atomics"` is an unstable wasm target feature, so stable
    // rustc never puts it in the cfg set, even for wasm32-wasip1-threads whose
    // std is fully threaded. Detect the threaded wasi targets from the triple so
    // the wasi_threads parker can be selected on stable. See
    // rust-lang/rust#77839.
    println!("cargo:rustc-check-cfg=cfg(parking_lot_core_wasi_threads)");
    let target = std::env::var("TARGET").unwrap_or_default();
    if matches!(
        target.as_str(),
        "wasm32-wasip1-threads" | "wasm32-wasi-preview1-threads" | "wasm32-wasip2-threads"
    ) {
        println!("cargo:rustc-cfg=parking_lot_core_wasi_threads");
    }
}
