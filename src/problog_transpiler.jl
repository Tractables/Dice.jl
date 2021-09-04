# transpile to problog

toproblog(p::String, io = stdout) = 
    toproblog(Dice.parse(DiceProgram,p), io)

toproblog(p::DiceProgram, io = stdout) =
    toproblog(p.expr, io)

function toproblog(e::LetExpr, io)
    pred = topredicate(e.identifier)
    toproblog(e.e1, io, pred, "true.")
    toproblog(e.e2, io)
end

topredicate(e::Identifier) =
    lowercase(e.symbol)

function toproblog(e::Flip, io, id, body)
    println(io, "$(1-e.prob)::$id(0); $(e.prob)::$id(1) :- $body")
end

function toproblog(e::Categorical, io, id, body)
    heads = map(enumerate(e.probs)) do (i, p)
        "$p::$id($(i-1))"
    end
    head = join(heads, "; ")
    println(io, "$head :- $body")
end

function toproblog(e::Ite, io, id, body)
    test = toatom(e.cond_expr)
    toproblog(e.then_expr, io, id, "$test, $body")
    toproblog(e.else_expr, io, id, "\\+ $test, $body")
end

function toatom(test::EqualsOp)
    bid = test.e1::Identifier
    pred = topredicate(bid)
    bv = toterm(test.e2)
    "$pred($bv)"
end

toterm(x::DiceInt) = "$(x.v)"

function toatom(test::Identifier)
    pred = topredicate(test)
    "$pred(1)"
end

function toproblog(e::DiceTuple, io)
    toproblog(e.first, io)
    toproblog(e.second, io)
end

function toproblog(e::Identifier, io)
    pred = topredicate(e)
    println(io, "query($pred(_)).")
end
