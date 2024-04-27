fn main() {
    cc::Build::new()
        .file("src/ot/utils/transpose.c")
        .flag("-msse4.1")
        .compile("libtranspose.a");
}
