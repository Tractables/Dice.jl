wd = pwd()

cmd = `cargo build --manifest-path=$wd/dicegg/Cargo.toml --target=x86_64-apple-darwin --release`
run(cmd)
Libc.Libdl.dlopen("$(wd)/dicegg/target/x86_64-apple-darwin/release/libmain")


function printhello()
    ccall(:rustdylib_printhello, Cvoid, ())
end

# Creates new dice expr and returns id
function new_expr()
    ccall(:new_expr, Cuint, ())
end

expr = new_expr()

