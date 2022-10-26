mutable struct X end

function test()
    x = X()
    finalizer(x) do finalizee
        ccall(:jl_safe_printf, Cvoid, (Cstring, Cstring), "finalizing %s\n", repr(finalizee))
    end
end

test()
println("end of program")

#==
Prints:

end of program
finalizing X()
==#