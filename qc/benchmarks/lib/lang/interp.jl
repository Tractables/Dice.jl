Env = Dict{Symbol, Any}

# Interpret to a Dice dist
function interp(rs::RunState, prog::L.Program)
    prim_map, loc_map, tuple_tys, enums = check_tree(prog)

    function with_binding(env, from, to)
        env2 = copy(env)
        env2[from] = to
        env2
    end

    functions = Dict(
        f.name => f
        for f in prog.functions
    )

    function_results = Dict(
        f.name => []
        for f in prog.functions
    )

    function interp(env::Env, x::L.Var)
        env[x.s]
    end

    function interp(env::Env, x::L.Loc)
        DistUInt32(loc_map[x])
    end

    function interp(env::Env, x::L.Nat)
        DistUInt32(x.x)
    end

    function interp(env::Env, x::L.Z)
        DistInt32(x.x)
    end

    function interp(env::Env, x::L.Bool)
        x.x
    end

    function interp(env::Env, x::L.NatAdd)
        sum(
            interp(env, y)
            for y in x.xs
        )
    end

    function interp(env::Env, x::L.ZAdd)
        sum(
            interp(env, y)
            for y in x.xs
        )
    end

    function interp(env::Env, x::L.Eq)
        prob_equals(
            interp(env, x.x),
            interp(env, x.y),
        )
    end

    function interp(env::Env, x::L.If)
        @alea_ite if interp(env, x.c)
            interp(env, x.t)
        else
            interp(env, x.e)
        end
    end

    function interp(env::Env, x::L.Construct)
        x.ctor([interp(env, arg) for arg in x.args]...)
    end

    function interp(env::Env, x::L.Tuple)
        Tuple([interp(env, component) for component in x.components])
    end

    function interp(env::Env, x::L.UnpackTuple)
        tup = interp(env, x.e)
        env1 = copy(env)
        @assert length(x.bindings) == length(tup)
        for (param, v) in zip(x.bindings, tup)
            env1[param.name] = v
        end

        interp(env1, x.body)
    end

    function interp(env::Env, x::L.Match)
        Dice.match(interp(env, x.scrutinee), [
            ctor => (args...) -> begin
                @assert length(args) == length(vars)
                env1 = copy(env)
                for (var, arg) in zip(vars, args)
                    env1[var] = arg
                end
                interp(env1, body)
            end
            for ((ctor, vars), body) in x.branches
        ])
    end

    function interp(env::Env, x::L.ConstructEnum)
        DistUInt32(findfirst(==(x.s), x.enum.ctors))
    end

    function interp(env::Env, x::L.MatchEnum)
        scrutinee = interp(env, x.scrutinee)
        branches = Any[Dice.getunset() for _ in x.enum.ctors]

        for (ctor, body) in x.branches
            branches[findfirst(==(ctor), x.enum.ctors)] = interp(env, body)
        end

        res = Dice.getunset()
        for (i, v) in enumerate(branches)
            if Dice.isunset(res)
                res = v
            else
                res = @alea_ite if prob_equals(DistUInt32(i), scrutinee)
                    v
                else
                    res
                end
            end
        end
        res
    end

    function interp(env::Env, x::L.Call)
        f = functions[x.f]
        @assert length(f.params) == length(x.args) "$(f.name), $(f.params), $(x.args)"
        res = interp(
            Env(
                param.name => interp(env, arg)
                for (param, arg) in zip(f.params, x.args)
            ),
            f.body
        )
        push!(function_results[x.f], res)
        res
    end

    function interp(env::Env, x::L.Lambda)
        error("Lambdas should be interped by Map.")
    end

    function interp(env::Env, x::L.Map)
        @assert length(x.f.params) == 1
        prob_map(
            x.dest_module,
            y -> begin
                interp(with_binding(env, x.f.params[1], y), x.f.body)
            end,
            interp(env, x.l)
        )
    end

    function interp(env::Env, x::L.BindGen)
        # we're always in the monad. this is just a let
        interp(
            with_binding(env, x.var, interp(env, x.gen)),
            x.body
        )
    end

    function interp(env::Env, x::L.ReturnGen)
        # always already in the monad
        interp(env, x.x)
    end

    function interp(env::Env, x::L.OneOf)
        one_of(
            interp(env, x.default),
            interp(env, x.x),
        )
    end

    function interp(env::Env, x::L.Frequency)
        dependents = [interp(env, dependent) for dependent in x.dependents]
        frequency_for(rs, prim_map[x], dependents, [
            name => interp(env, body)
            for (name, body) in x.branches
        ])
    end

    function interp(env::Env, x::L.Backtrack)
        dependents = [interp(env, dependent) for dependent in x.dependents]
        backtrack_for(rs, prim_map[x], dependents, [
                name => interp(env, body)
                for (name, body) in x.branches
            ],
            interp(env, x.none)
        )
    end

    function interp(env::Env, x::L.GenNat)
        name = prim_map[x]
        dependents = [interp(env, dependent) for dependent in x.dependents]
        sum(
            @alea_ite if flip_for(rs, "$(name)_num$(n)", dependents)
                DistUInt32(n)
            else
                DistUInt32(0)
            end
            for n in twopowers(x.width)
        )
    end

    function interp(env::Env, x::L.GenZ)
        name = prim_map[x]
        dependents = [interp(env, dependent) for dependent in x.dependents]
        sum(
            @alea_ite if flip_for(rs, "$(name)_num$(n)", dependents)
                DistInt32(n)
            else
                DistInt32(0)
            end
            for n in twopowers(x.width)
        )
    end

    function interp(env::Env, x::L.GenBool)
        name = prim_map[x]
        dependents = [interp(env, dependent) for dependent in x.dependents]
        flip_for(rs, "$(name)_true", dependents)
    end

    function interp(env::Env, x::L.ArbitraryBool)
        true
    end

    function interp(env::Env, x::L.ArbitraryNat)
        DistUInt32(0)
    end

    function interp(env::Env, x::L.ArbitraryZ)
        DistInt32(0)
    end

    res = interp(Env(), prog.res)

    res, prim_map, function_results
end