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
        loc_map[x]
    end

    function sample(env::Env, x::L.Nat)
        x.x
    end

    function sample(env::Env, x::L.Z)
        x.x
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
        sample(env, x.x) == sample(env, x.y)
    end

    function sample(env::Env, x::L.If)
        if sample(env, x.c)
            sample(env, x.t)
        else
            sample(env, x.e)
        end
    end

    function sample(env::Env, x::L.Construct)
        (x.ctor, [sample(env, arg) for arg in x.args])
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
        scrutinee = sample(env, x.scrutinee)
        if scrutinee isa Integer
            branches = x.branches
            @assert length(branches) == 2
            o, s = if branches[1][1][1] == :O && branches[2][1][1] == :S
                branches[1], branches[2]
            else
                @assert branches[2][1][1] == :O && branches[2][1][1] == :S
                branches[2], branches[1]
            end
            if scrutinee > 0
                env1 = copy(env)
                (_ctor, vars), body = s
                var, = vars
                env1[var] = scrutinee - 1
                return sample(env1, body)
            else
                _, body = o
                return sample(env, body)
            end
        else
            which, args = scrutinee
            for ((ctor, vars), body) in x.branches
                if ctor == Symbol(which)
                    env1 = copy(env)
                    for (var, arg) in zip(vars, args)
                        env1[var] = arg
                    end
                    return sample(env1, body)
                end
            end
            println(env)
            println(which)
            println(x.branches)
            error()
        end
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
        findfirst(==(x.s), x.enum.ctors)
    end

    function sample(env::Env, x::L.MatchEnum)
        scrutinee = sample(env, x.scrutinee)
        for (ctor, body) in x.branches
            i = findfirst(==(ctor), x.enum.ctors)
            if i == scrutinee
                return sample(env, body)
            end
        end
        error()
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
        # println("$(f.name) returned $(res)")
        res
    end

    function sample(env::Env, x::L.Lambda)
        error("Lambdas should be sampleed by Map.")
    end

    function sample(env::Env, x::L.Map)
        @assert length(x.f.params) == 1
        l = sample(env, x.l)

        function loop(l)
            ctor, args = l
            if Symbol(ctor) == :nil
                return ctor, args
            end
            @assert Symbol(ctor) == :cons
            hd, tl = args
            hd′ = sample(with_binding(env, x.f.params[1], hd), x.f.body)
            tl′ = loop(tl)
            (ctor, [hd′, tl′])
        end

        loop(l)
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
        function getlen(l)
            ctor, args = l
            if Symbol(ctor) == :nil
                return 0
            end
            @assert Symbol(ctor) == :cons
            hd, tl = args
            1 + getlen(tl)
        end

        function loop(l, len)
            ctor, (hd, tl) = l
            @assert Symbol(ctor) == :cons
            if rand(rs.rng) < 1/len
                return hd
            end
            loop(tl, len - 1)
        end

        l = sample(env, x.x)
        len = getlen(l)
        if len == 0
            sample(env, x.default)
        else
            loop(l, len)
        end
    end


    function sample(env::Env, x::L.Frequency)
        dependents = [sample(env, dependent) for dependent in x.dependents]
        # TODO: make this only do one execution path!

        # remaining_weight = 
        frequency_for_sample(rs, a, prim_map[x], dependents, [
            name => sample(env, body)
            for (name, body) in x.branches
        ])
    end

    function sample(env::Env, x::L.Backtrack)
        splice(v, i) = [x for (j, x) in enumerate(v) if j != i]

        function loop(weights_and_bodies, total_weight)
            if isempty(weights_and_bodies)
                return sample(env, x.none)
            end

            remaining_weight = total_weight
            for (i, (weight, body)) in enumerate(weights_and_bodies)
                if rand(rs.rng) < weight / remaining_weight
                    ctor, args = sample(env, body)
                    if Symbol(ctor) == :Some
                        # arg, = args
                        return ctor, args
                    else
                        @assert Symbol(ctor) == :None
                        loop(splice(weights_and_bodies, i), total_weight - weight)
                    end
                end
                remaining_weight -= weight
            end
        end

        dependents = [sample(env, dependent) for dependent in x.dependents]
        t = join([string(x) for x in dependents], "%")

        weights_and_bodies = []
        name = prim_map[x]
        total_weight = 0
        for (casename, body) in x.branches
            weight = compute(a, register_weight!(rs, "$(name)_$(casename)%%$(t)"))
            total_weight += weight
            push!(weights_and_bodies, (weight, body))
        end

        loop(weights_and_bodies, total_weight)
    end

    function sample(env::Env, x::L.GenNat)
        name = prim_map[x]
        dependents = [sample(env, dependent) for dependent in x.dependents]
        sum(
            begin
                if flip_for_sample(rs, a, "$(name)_num$(n)", dependents)
                    n
                else
                    0
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
                    n
                else
                    0
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
        0
    end

    function sample(env::Env, x::L.ArbitraryZ)
        0
    end

    # register var_vals
    # @infiltrate
    # pre_register(rs, prim_map)
    a = ADComputer(rs.var_vals)
    rs.coupled_ad_computer = a
    sampler() = sample(Env(), prog.res)
    sampler #, prim_map, function_results
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