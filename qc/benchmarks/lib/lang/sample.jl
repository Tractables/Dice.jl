Env = Dict{Symbol, Any}

# sampleret to a Dice dist
function sample_from_lang(rs::RunState, prog::L.Program)
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

    function sample(env::Env, x::L.Var)
        env[x.s]
    end

    function sample(env::Env, x::L.Loc)
        DistUInt32(loc_map[x])
    end

    function sample(env::Env, x::L.Nat)
        DistUInt32(x.x)
    end

    function sample(env::Env, x::L.Z)
        DistInt32(x.x)
    end

    function sample(env::Env, x::L.Bool)
        x.x
    end

    function sample(env::Env, x::L.NatAdd)
        sum(
            sample(env, y)
            for y in x.xs
        )
    end

    function sample(env::Env, x::L.ZAdd)
        sum(
            sample(env, y)
            for y in x.xs
        )
    end

    function sample(env::Env, x::L.Eq)
        prob_equals(
            sample(env, x.x),
            sample(env, x.y),
        )
    end

    function sample(env::Env, x::L.If)
        if sample(env, x.c)
            sample(env, x.t)
        else
            sample(env, x.e)
        end
    end

    function sample(env::Env, x::L.Construct)
        x.ctor([sample(env, arg) for arg in x.args]...)
    end

    function sample(env::Env, x::L.Tuple)
        Tuple([sample(env, component) for component in x.components])
    end

    function sample(env::Env, x::L.UnpackTuple)
        tup = sample(env, x.e)
        env1 = copy(env)
        @assert length(x.bindings) == length(tup)
        for (param, v) in zip(x.bindings, tup)
            env1[param.name] = v
        end

        sample(env1, x.body)
    end

    function sample(env::Env, x::L.Match)
        Dice.match(sample(env, x.scrutinee), [
            ctor => (args...) -> begin
                @assert length(args) == length(vars)
                env1 = copy(env)
                for (var, arg) in zip(vars, args)
                    env1[var] = arg
                end
                sample(env1, body)
            end
            for ((ctor, vars), body) in x.branches
        ])

        # @infiltrate
        # scrutinee = sample(env, x.scrutinee)
        # if scrutinee isa Integer

        # end
        # which = scrutinee.which
        # @assert isdeterministic(which)
        # (ctor, vars), body = x.branches[which]
        # args = scrutinee.dist[which]
        # @assert length(args) == length(vars)
        # env1 = copy(env)
        # for (var, arg) in zip(vars, args)
        #     env1[var] = arg
        # end
        # sample(env1, body)
    end

    function sample(env::Env, x::L.ConstructEnum)
        DistUInt32(findfirst(==(x.s), x.enum.ctors))
    end

    function sample(env::Env, x::L.MatchEnum)
        scrutinee = sample(env, x.scrutinee)
        branches = Any[Dice.getunset() for _ in x.enum.ctors]

        for (ctor, body) in x.branches
            branches[findfirst(==(ctor), x.enum.ctors)] = sample(env, body)
        end

        res = Dice.getunset()
        for (i, v) in enumerate(branches)
            if Dice.isunset(res)
                res = v
            else
                res = if prob_equals(DistUInt32(i), scrutinee)
                    v
                else
                    res
                end
            end
        end
        res
    end

    function sample(env::Env, x::L.Call)
        f = functions[x.f]
        @assert length(f.params) == length(x.args)
        res = sample(
            Env(
                param.name => sample(env, arg)
                for (param, arg) in zip(f.params, x.args)
            ),
            f.body
        )
        push!(function_results[x.f], res)
        res
    end

    function sample(env::Env, x::L.Lambda)
        error("Lambdas should be sampleed by Map.")
    end

    function sample(env::Env, x::L.Map)
        @assert length(x.f.params) == 1
        prob_map(
            x.dest_module,
            y -> begin
                sample(with_binding(env, x.f.params[1], y), x.f.body)
            end,
            sample(env, x.l)
        )
    end

    function sample(env::Env, x::L.BindGen)
        # we're always in the monad. this is just a let
        sample(
            with_binding(env, x.var, sample(env, x.gen)),
            x.body
        )
    end

    function sample(env::Env, x::L.ReturnGen)
        # always already in the monad
        sample(env, x.x)
    end

    function sample(env::Env, x::L.OneOf)
        one_of_sample(
            sample(env, x.default),
            sample(env, x.x),
        )
    end


    function sample(env::Env, x::L.Frequency)
        dependents = [sample(env, dependent) for dependent in x.dependents]
        frequency_for_sample(rs, a, prim_map[x], dependents, [
            name => sample(env, body)
            for (name, body) in x.branches
        ])
    end

    function sample(env::Env, x::L.Backtrack)
        @assert false
        dependents = [sample(env, dependent) for dependent in x.dependents]
        backtrack_for_sample(rs, prim_map[x], dependents, [
                name => sample(env, body)
                for (name, body) in x.branches
            ],
            sample(env, x.none)
        )
    end

    function sample(env::Env, x::L.GenNat)
        name = prim_map[x]
        dependents = [sample(env, dependent) for dependent in x.dependents]
        sum(
            begin
                if flip_for_sample(rs, a, "$(name)_num$(n)", dependents)
                    DistUInt32(n)
                else
                    DistUInt32(0)
                end
            end
            for n in twopowers(x.width)
        )
    end

    function sample(env::Env, x::L.GenZ)
        name = prim_map[x]
        dependents = [sample(env, dependent) for dependent in x.dependents]
        sum(
            begin
                if flip_for_sample(rs, a, "$(name)_num$(n)", dependents)
                    DistInt32(n)
                else
                    DistInt32(0)
                end
            end
            for n in twopowers(x.width)
        )
    end

    function sample(env::Env, x::L.GenBool)
        name = prim_map[x]
        dependents = [sample(env, dependent) for dependent in x.dependents]
        flip_for_sample(rs, a, "$(name)_true", dependents)
    end

    function sample(env::Env, x::L.ArbitraryBool)
        true
    end

    function sample(env::Env, x::L.ArbitraryNat)
        DistUInt32(0)
    end

    function sample(env::Env, x::L.ArbitraryZ)
        DistInt32(0)
    end

    # register var_vals
    # @infiltrate
    # pre_register(rs, prim_map)
    a = ADComputer(rs.var_vals)
    rs.coupled_ad_computer = a
    sampler() = sample(Env(), prog.res)
    sampler, prim_map, function_results
end

function pre_register(rs, prim_map)
    function reg_flip_for!(rs, name, dependents)
        support = support_mixed(dependents; as_dist=true)
        @assert !isempty(support)
        for dependents_vals in support
            t = join([string(x) for x in dependents_vals], "%")
            register_weight!(rs, "$(name)%%$(t)")
        end
    end

    function f(_::L.GenBool, name)
        reg_flip_for!(rs, "$(name)_true", dependents)
    end

    function f(x::L.GenNat, name)
        for n in twopowers(x.width)
            reg_flip_for!(rs, "$(name)_num$(n)", dependents)
        end
    end

    function f(e::L.Frequency, name)
        support = support_mixed(e.dependents; as_dist=true)
        @assert !isempty(support)
        for dependents_vals in support
            t = join([string(x) for x in dependents_vals], "%")
            for casename in casenames
                register_weight!(rs, "$(name)_$(casename)%%$(t)")
            end
        end
    end
    for (e, id) in prim_map
        f(e, id)
    end
end