export Monad, liftM, liftM2, liftM3

struct Monad
    bind # (m a) * (a -> m b) -> m b
    ret  # a -> m a
end

function liftM(m::Monad, f)
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
