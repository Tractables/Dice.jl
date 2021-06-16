
function run_dice(code; 
            showinternal=false, skiptable=false, 
            determinism=true, showsize=false,
            printstatebdd=false)
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
        cmd = `$(homedir())/.opam/4.09.0/bin/dice $path $flags`
        # println(cmd)
        run(cmd)
        nothing
    end    
end