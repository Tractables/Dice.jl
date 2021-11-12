export has_dice_binary

function has_dice_binary()
    !isnothing(Sys.which("dice"))
end

function run_dice(code::String; 
            showinternal=false, skiptable=false, 
            determinism=true, showsize=false,
            printstatebdd=false)
    dice = Sys.which("dice")
    isnothing(dice) && error("Ocaml dice binary not found in path")
    mktemp() do path, io 
        write(io, code)
        close(io)
        flags = String[]
        if showinternal
            push!(flags, "-show-internal")
        end
        if skiptable
            push!(flags, "-skip-table")
        end
        if determinism
            push!(flags, "-determinism")
        end
        if showsize
            push!(flags, "-show-size")
        end
        if printstatebdd
            push!(flags, "-print-state-bdd")
        end
        cmd = `$dice $path $flags`
        Base.read(cmd, String)
    end    
end

function num_nodes_ocml(code)
    out = run_dice(code; skiptable=true, showsize=true)
    regex = r"================.*================\n(.+)\n"
    size_str = match(regex, out)
    @assert size_str !== nothing "$out did not match expected pattern"
    Base.parse(Int, size_str[1])
end