export Monad, liftM

struct Monad
    bind # (m a) * (a -> m b) -> m b
    ret  # a -> m a
end

# Variadic liftM
function liftM(m::Monad, f)
    f_vec(args) = f(args...)
    function g(mas...)
        liftM_helper(m, f_vec)(collect(mas))
    end
end

# liftM but takes in vector input for efficiency
function liftM_helper(m::Monad, f)
    function g(mas)
        if isempty(mas)
            m.ret(f([]))
        else
            ma = pop!(mas)
            m.bind(ma,
                a -> liftM_helper(m, as -> f(push!(as, a)))(mas)
            )
        end
    end
end

# Specialized versions
#==

function liftM1(m::Monad, f)
    function g(ma)
        m.bind(ma, a -> m.ret(f(a)))
    end
end

function liftM2(m::Monad, f)
    function g(ma, mb)
        m.bind(ma,
            a -> m.bind(mb,
                b -> m.ret(f(a, b))
            )
        )
    end
end

function liftM3(m::Monad, f)
    function g(ma, mb, mc)
        m.bind(ma,
            a -> m.bind(mb,
                b -> m.bind(mc,
                    c -> m.ret(f(a, b, c))
                )
            )
        )
    end
end
==#
