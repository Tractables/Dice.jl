function module_of_func(f)
    @assert all(m.module == methods(f)[1].module for m in methods(f)) "$(f) $(methods(f))"
    methods(f)[1].module
end

function ctor_to_params(f)
    m = module_of_func(f)
    for (ctor, params) in variants(m.t)
        if f == ctor
            return params
        end
    end
    error("ctor_to_params failed $(f) $(m)")
end

ty_is_recursive(ty) = any(ty in params for (ctor, params) in variants(ty))

function collect_types(root_ty)
    to_visit = [root_ty]
    seen = Set([root_ty])
    tys = [root_ty]
    while !isempty(to_visit)
        ty = pop!(to_visit)
        for (ctor, params) in variants(ty)
            for param in params
                if param ∉ seen && hasmethod(variants, (Type{param},))
                    push!(seen, param)
                    push!(to_visit, param)
                    push!(tys, param)
                end
            end
        end
    end
    reverse!(tys) # top order

    type_ctor_parami_to_id = Dict()
    for ty in tys
        for (ctor, params) in variants(ty)
            for (parami, param) in enumerate(params)
                if param in tys
                    type_ctor_parami_to_id[(ty, ctor, parami)] = length(type_ctor_parami_to_id) + 1
                end
            end
        end
    end

    tys, type_ctor_parami_to_id
end

struct LangDerivedGenerator{T} <: GenerationParams{T}
    root_ty::Type
    ty_sizes::Vector{Pair{Type, Integer}}
    stack_size::Integer
    intwidth::Integer
    arbitrary_prims::Bool
end
LangDerivedGenerator{T}(; root_ty, ty_sizes, stack_size, intwidth, arbitrary_prims) where T =
    LangDerivedGenerator{T}(root_ty, ty_sizes, stack_size, intwidth, arbitrary_prims)
function to_subpath(p::LangDerivedGenerator{T}) where T
    [
        lowercase(string(T)),
        "langderived",
        "root_ty=$(p.root_ty)",
        "ty-sizes=$(join(["$(ty)-$(size)" for (ty, size) in p.ty_sizes],"-"))",
        "stack_size=$(p.stack_size)",
        "intwidth=$(p.intwidth)",
        "arbitrary_prims=$(p.arbitrary_prims)",
    ]
end
function generate(rs::RunState, p::LangDerivedGenerator{T}) where T
    prog = derive_lang_generator(p)
    res, prim_map, function_results = interp(rs, prog)
    constructors_overapproximation = []
    if T == STLC
        STLCGeneration(OptExpr.Some(res), [OptExpr.Some(e) for e in function_results["genExpr"]])
    elseif T == BST
        BSTGeneration(res, function_results["genTree"])
    elseif T == RBT
        RBTGeneration(res) #, function_results["genTree"])
    else
        error()
    end
end
function generation_params_emit_stats(rs::RunState, p::LangDerivedGenerator, s)
    prog = derive_lang_generator(p)

    path = joinpath(rs.out_dir, "$(s)_Generator.v")
    open(path, "w") do file
        println(file, to_coq(rs, p, prog))
    end
    println_flush(rs.io, "Saved Coq generator to $(path)")
    println_flush(rs.io)
end


struct LangSiblingDerivedGenerator{T} <: GenerationParams{T}
    root_ty::Type
    ty_sizes::Vector{Pair{Type, Integer}}
    stack_size::Integer
    intwidth::Integer
end
LangSiblingDerivedGenerator{T}(; root_ty, ty_sizes, stack_size, intwidth) where T =
    LangSiblingDerivedGenerator{T}(root_ty, ty_sizes, stack_size, intwidth)
function to_subpath(p::LangSiblingDerivedGenerator{T}) where T
    [
        lowercase(string(T)),
        "langsiblingderived",
        "root_ty=$(p.root_ty)",
        "ty-sizes=$(join(["$(ty)-$(size)" for (ty, size) in p.ty_sizes],"-"))",
        "stack_size=$(p.stack_size)",
        "intwidth=$(p.intwidth)",
    ]
end
function generate(rs::RunState, p::LangSiblingDerivedGenerator{T}) where T
    prog = derive_lang_sibling_generator(p)
    res, prim_map, function_results = interp(rs, prog)
    Generation(res, prog, Dict())
end
function generation_params_emit_stats(rs::RunState, p::LangSiblingDerivedGenerator, s)
    prog = derive_lang_sibling_generator(p)

    path = joinpath(rs.out_dir, "$(s)_Generator.v")
    open(path, "w") do file
        println(file, to_coq(rs, p, prog))
    end
    println_flush(rs.io, "Saved Coq generator to $(path)")
    println_flush(rs.io)
end

function derive_lang_generator(p::LangDerivedGenerator{T}) where T
    stack_vars = [Symbol("stack$(i)") for i in 1:p.stack_size]

    functions = []

    tys, type_ctor_parami_to_id = collect_types(p.root_ty)

    dependents() = vcat(
        [L.Var(:size)],
        [L.Var(x) for x in stack_vars]
    )

    function gen(ty, zero_case)
        freq_branches = []
        for (varianti, (ctor, params)) in enumerate(variants(ty))
            if zero_case && ty in params
                continue
            end
            freq_branch = L.ReturnGen(L.Construct(
                ctor, [
                    L.Var(Symbol("p$(i)"))
                    for i in 1:length(params)
                ]
            ))
            for (parami, param) in reverse(collect(enumerate(params)))
                freq_branch = L.BindGen(
                    if param in tys
                        L.Call("gen$(type_to_coq(param))", vcat(
                            [
                                if param == ty
                                    L.Var(:size1)
                                else
                                    L.Nat(Dict(p.ty_sizes)[param])
                                end
                            ],
                            [ L.Var(stack_vars[i]) for i in 2:p.stack_size ],
                            [L.Loc()],
                        ))
                    elseif param == Nat.t
                        if p.arbitrary_prims
                            L.ArbitraryNat()
                        else
                            L.GenNat(dependents(), p.intwidth)
                        end
                    elseif param == DistInt32
                        if p.arbitrary_prims
                            L.ArbitraryZ()
                        else
                            L.GenZ(dependents(), p.intwidth)
                        end
                    elseif param == AnyBool
                        if p.arbitrary_prims
                            L.ArbitraryBool()
                        else
                            L.GenBool(dependents())
                        end
                    else
                        error("bad param type $(param)")
                    end,
                    Symbol("p$(parami)"),
                    freq_branch
                )
            end
            push!(freq_branches,
                "$(ctor)" => freq_branch
            )
        end
        L.Frequency( dependents(), freq_branches)
    end

    for ty in tys
        recursive = any(ty in params for (ctor, params) in variants(ty))
        func = L.Function(
            "gen$(type_to_coq(ty))",
            vcat(
                [L.Param(:size, Nat.t)],
                [L.Param(stack_var, Nat.t) for stack_var in stack_vars],
            ),
            L.G{ty},
            if recursive
                L.Match(L.Var(:size), [
                    (:O, []) => gen(ty, true),
                    (:S, [:size1]) => gen(ty, false),
                ])
            else
                gen(ty, true)
            end
        )
        push!(functions, func)
    end

    L.Program(
        functions,
        L.Call(
            "gen$(type_to_coq(p.root_ty))",
            vcat(
                [L.Nat(Dict(p.ty_sizes)[p.root_ty])],
                [L.Nat(0) for _ in 1:p.stack_size]
            )
        )
    )
end

function ctor_enum_prefix(ty, leaf)
    leaf_s = if leaf "Leaf" else "" end
    "$(leaf_s)Ctor$(type_to_coq(ty))"
end

function ctor_enum(ty, leaf)
    pre = ctor_enum_prefix(ty, leaf)
    L.Enum(pre, [
        "$(pre)_$(nameof(ctor))"
        for (ctor, params) in variants2(ty, leaf)
    ])
end

variants2(ty, exclude_recursive) = if exclude_recursive
    [
        (ctor, params)
        for (ctor, params) in variants(ty)
        if !(ty in params)
    ]
else
    variants(ty)
end

function derive_lang_sibling_generator(p::LangSiblingDerivedGenerator{T}) where T
    stack_vars = [Symbol("stack$(i)") for i in 1:p.stack_size]

    functions = []

    tys, type_ctor_parami_to_id = collect_types(p.root_ty)

    dependents(leaf, zero_case) = collect(vcat(
        if !leaf && !zero_case()
            [L.Var(:size)]
        else
            []
        end,
        [L.Var(x) for x in stack_vars]
    ))

    function gen(ty, leaf, _zero_case)
        zero_case() = if leaf
            error("don't check zero_case() if leaf")
        else
            _zero_case
        end

        chosen_ctor_branches = []
        ce = ctor_enum(ty, leaf)
        for (chosen_ctor, chosen_ctor_params) in variants2(ty, leaf)
            sub_ctors_tys = [
                ctor_enum(param, !ty_is_recursive(param) || param == ty && zero_case())
                for param in chosen_ctor_params
                if param ∈ tys
            ]

            j = 0
            i_to_j = Dict()
            i_to_is_leaf = Dict()
            for (i, param) in enumerate(chosen_ctor_params)
                if param ∈ tys
                    j += 1
                    i_to_j[i] = j
                    i_to_is_leaf[i] = !ty_is_recursive(param) || param == ty && zero_case()
                end
            end

            temp = vec(collect(Iterators.product([
                [(sub_ctor_ty, ctor) for ctor in sub_ctor_ty.ctors]
                for sub_ctor_ty in sub_ctors_tys
            ]...)))

            res = L.ReturnGen(L.Construct(
                chosen_ctor, [
                    L.Var(Symbol("p$(i)"))
                    for i in 1:length(chosen_ctor_params)
                ]
            ))
            for (ccpi, chosen_ctor_param) in reverse(collect(enumerate(chosen_ctor_params)))
                res = L.BindGen(
                    if chosen_ctor_param in tys
                        chosen_ctor_param_is_leaf = !ty_is_recursive(chosen_ctor_param) || chosen_ctor_param == ty && !leaf && zero_case()
                        subres = L.Call(
                            if chosen_ctor_param_is_leaf
                                "genLeaf$(type_to_coq(chosen_ctor_param))"
                            else
                                "gen$(type_to_coq(chosen_ctor_param))"
                            end,
                            vcat(
                                if chosen_ctor_param_is_leaf
                                    []
                                elseif chosen_ctor_param == ty
                                    [ L.Var(:size1) ]
                                else
                                    [L.Nat(Dict(p.ty_sizes)[chosen_ctor_param] - 1) ]
                                end,
                                if haskey(i_to_j, ccpi)
                                    [L.Var(Symbol("ctor$(i_to_j[ccpi])"))]
                                else
                                    []
                                end,
                                [L.Var(stack_vars[i]) for i in 2:p.stack_size ],
                                [L.Loc()],
                            )
                        )
                    elseif chosen_ctor_param == Nat.t
                        L.GenNat(dependents(leaf, zero_case), p.intwidth)
                    elseif chosen_ctor_param == DistInt32
                        L.GenZ(dependents(leaf, zero_case), p.intwidth)
                    elseif chosen_ctor_param == AnyBool
                        L.GenBool(dependents(leaf, zero_case))
                    else
                        error("bad param type $(chosen_ctor_param)")
                    end,
                    Symbol("p$(ccpi)"),
                    res
                )
            end

            res = if isempty(sub_ctors_tys)
                res
            else
                L.BindGen(
                    L.Frequency(dependents(leaf, zero_case), [
                        "$(i)" => L.ReturnGen(L.Tuple(
                            sub_ctors_tys,
                            [L.ConstructEnum(enum, ctor) for (enum, ctor) in x],
                        ))
                        for (i, x) in enumerate(temp)
                    ]),
                    :param_variantis,
                    L.UnpackTuple(L.Var(:param_variantis),
                        [L.Param(Symbol("ctor$(i)"), sub_ctor_ty) for (i,sub_ctor_ty) in enumerate(sub_ctors_tys)],
                        res
                    )
                )
            end
            push!(chosen_ctor_branches, "$(ctor_enum_prefix(ty, leaf))_$(nameof(chosen_ctor))" => res)
        end
        L.MatchEnum(ctor_enum(ty, leaf), L.Var(:chosen_ctor), chosen_ctor_branches)
    end

    for ty in tys
        leaffunc = L.Function(
            "genLeaf$(type_to_coq(ty))",
            vcat(
                [L.Param(:chosen_ctor, ctor_enum(ty, true))],
                [L.Param(stack_var, Nat.t) for stack_var in stack_vars],
            ),
            L.G{ty},
            gen(ty, true, nothing)
        )
        push!(functions, leaffunc)

        if ty_is_recursive(ty)
            func = L.Function(
                "gen$(type_to_coq(ty))",
                vcat(
                    [L.Param(:size, Nat.t)],
                    [L.Param(:chosen_ctor, ctor_enum(ty, false))],
                    [L.Param(stack_var, Nat.t) for stack_var in stack_vars],
                ),
                L.G{ty},
                L.Match(L.Var(:size), [
                    (:O, []) => gen(ty, false, true),
                    (:S, [:size1]) => gen(ty, false, false),
                ])
            )
            push!(functions, func)
        end
    end

    root_ce = ctor_enum(p.root_ty, false)
    L.Program(
        functions,
        L.BindGen(
            L.Frequency([], [
                "$(i)" => L.ReturnGen(L.ConstructEnum(root_ce, ctor))
                for (i, ctor) in enumerate(root_ce.ctors)
            ]),
            :init_ctor,
            L.Call(
                "gen$(type_to_coq(p.root_ty))",
                vcat(
                    [L.Nat(Dict(p.ty_sizes)[p.root_ty] - 1)],
                    [L.Var(:init_ctor)],
                    [L.Nat(0) for _ in 1:p.stack_size]
                )
            )
        )
    )
end
