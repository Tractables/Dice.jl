    function visit(x::L.Var)
    end

    function visit(x::L.Nat)
    end

    function visit(x::L.Z)
    end

    function visit(x::L.Bool)
    end

    function visit(x::L.NatAdd)
        for x in x.xs
            visit(x)
        end
    end

    function visit(x::L.ZAdd)
        for x in x.xs
            visit(x)
        end
    end

    function visit(x::L.Eq)
        visit(x.x)
        visit(x.y)
    end

    function visit(x::L.If)
        visit(x.c)
        visit(x.t)
        visit(x.e)
    end

    function visit(x::L.Construct)
        for arg in x.args
            visit(arg)
        end
    end

    function visit(x::L.Match)
        visit(x.scrutinee)
        for ((ctor, args), body) in x.branches
            visit(body)
        end
    end

    function visit(x::L.Call)
        for arg in x.args
            visit(arg)
        end
    end

    function visit(x::L.Lambda)
        visit(x.body)
    end

    function visit(x::L.Map)
        visit(x.f)
        visit(x.l)
    end

    function visit(x::L.BindGen)
        visit(x.gen)
        visit(x.body)
    end

    function visit(x::L.ReturnGen)
        visit(x.x)
    end

    function visit(x::L.OneOf)
        visit(x.default)
        visit(x.x)
    end

    function visit(x::L.Frequency)
        for (name, body) in x.branches
            visit(body)
        end
    end

    function visit(x::L.Backtrack)
        for (name, body) in x.branches
            visit(body)
        end
    end

    function visit(x::L.GenNat)
    end

    function visit(x::L.GenZ)
    end

    function visit(x::L.GenBool)
    end

    function visit(x::L.Function)
        visit(x.body)
    end

    function visit(x::L.Program)
        for f in x.functions
            visit(f)
        end
        visit(x.res)
    end