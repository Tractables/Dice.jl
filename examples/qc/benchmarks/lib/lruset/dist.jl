module LRUS
    using Dice
    @inductive Statement Insert(DistInt32) Contains(DistInt32) PopStale()
    @inductive Program Nil() Cons(Statement, Program)
    
    function vec_to_program(v)
        if isempty(v)
            Nil()
        else
            Cons(v[1], vec_to_program(v[2:end]))
        end
    end
end
