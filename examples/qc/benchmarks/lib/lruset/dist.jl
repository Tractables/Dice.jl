module LRUS
    using Dice
    import Dice: param_lists

    struct Statement <: InductiveType end
    function param_lists(::Type{LRUS.Statement})::Vector{Pair{String,Vector{Type}}}
        [
            "Insert" => [DistInt32],
            "Contains" => [DistInt32],
            "PopStale" => [],
        ]
    end
    Insert(v::DistInt32) = construct(Statement, "Insert", [v])
    Contains(v::DistInt32) = construct(Statement, "Contains", [v])
    PopStale() = construct(Statement, "PopStale", [])

    struct Program <: InductiveType end

    function param_lists(::Type{LRUS.Program})::Vector{Pair{String,Vector{Type}}}
        [
            "Nil" => [],
            "Cons" => [DistI{Statement}, DistI{Program}],
        ]
    end

    Nil() = construct(Program, "Nil",[])
    Cons(s::DistI{Statement}, p::DistI{Program}) =
        construct(Program, "Cons", [s, p])
    
    function vec_to_program(v)
        if isempty(v)
            Nil()
        else
            Cons(v[1], vec_to_program(v[2:end]))
        end
    end
end
    # import Dice: param_lists

    # function param_lists(::Type{LRUS.Statement})::Vector{Pair{String,Vector{Type}}}
    #     [
    #         "Insert" => [DistInt32],
    #         "Contains" => [DistInt32],
    #         "PopStale" => [],
    #     ]
    # end
    # function param_lists(::Type{LRUS.Program})::Vector{Pair{String,Vector{Type}}}
    #     [
    #         "Nil" => [],
    #         "Cons" => [DistI{LRUS.Statement}, DistI{LRUS.Program}],
    #     ]
    # end
