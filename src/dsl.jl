using MacroTools: prewalk, postwalk
using IRTools
using IRTools: @dynamo, IR, recurse!, self, xcall, functional

export @dice_ite, @dice, dice, observe, constraint, assert_dice, @code_ir_dice, save_dot, pathcond

##################################
# Control flow macro
##################################

"Syntactic macro to make if-then-else supported by dice"
macro dice_ite(code)
    postwalk(esc(code)) do x
        if x isa Expr && (x.head == :if || x.head == :elseif)
            @assert length(x.args) == 3 "@dice_ite macro only supports purely functional if-then-else"
            ite_guard = gensym(:ite)
            return :(begin $ite_guard = $(x.args[1])
                    if ($(ite_guard) isa Dist{Bool})
                        ifelse($(ite_guard), $(x.args[2:3]...))
                    else
                        (if $(ite_guard)
                            $(x.args[2])
                        else
                            $(x.args[3])
                        end)
                    end
                end)
        end
        return x
    end
end

##################################
# Control flow + error + observation dynamo
##################################

"Interpret dice code with control flow, observations, and errors"
function dice(f) 
    dyna = DiceDyna()
    x = dyna(f)
    MetaDist(x, dyna.errors, dyna.observations, dyna.dots)
end

"Interpret dice code with control flow, observations, and errors"
macro dice(code)
    esc(quote
        dice() do
            $code
        end
    end)
end


struct DiceDyna
    path::Vector{AnyBool}
    errors::Vector{Tuple{AnyBool, ErrorException}}
    observations::Vector{AnyBool}
    dots::Vector{Tuple{Vector{AnyBool}, String}}
    DiceDyna() = new(AnyBool[], Tuple{AnyBool, String}[], AnyBool[], Tuple{Vector{AnyBool}, String}[])
end

"Assert that the current code must be run within an @dice evaluation"
assert_dice() = error("This code must be called from within an @dice evaluation.")

observe(_) = assert_dice()

save_dot(_xs, _filename) = assert_dice()

pathcond() = assert_dice()

global dynamoed = Vector()

@dynamo function (dyna::DiceDyna)(a...)
    ir, time, _ = @timed begin
        ir = IR(a...)
        (ir === nothing) && return
        ir = functional(ir)
        ir = prewalk(ir) do x
            if x isa Expr && x.head == :call
                return xcall(self, x.args...)
            end
            return x
        end
        ir
    end
    global dynamoed
    push!(dynamoed, (time, a[1]))
    return ir
end

reset_dynamoed() = begin
    global dynamoed
    empty!(dynamoed)
end

top_dynamoed() = sort(dynamoed; by = x -> x[1], rev = true)

(::DiceDyna)(::typeof(assert_dice)) = nothing

(::DiceDyna)(::typeof(IRTools.cond), guard, then, elze) = IRTools.cond(guard, then, elze)

function (dyna::DiceDyna)(::typeof(IRTools.cond), guard::Dist{Bool}, then, elze)
    push!(dyna.path, guard)
    t = then()
    pop!(dyna.path)
    push!(dyna.path, !guard)
    e = elze()
    pop!(dyna.path)
    ifelse(guard, t, e)
end

path_condition(dyna) = reduce(&, dyna.path; init=true)

# TODO catch Base exceptions in ifelse instead
(dyna::DiceDyna)(::typeof(error), msg) =
    push!(dyna.errors, (path_condition(dyna), ErrorException(msg)))

(dyna::DiceDyna)(::typeof(observe), x) =
    push!(dyna.observations, !path_condition(dyna) | x)

(dyna::DiceDyna)(::typeof(pathcond)) = path_condition(dyna)

(dyna::DiceDyna)(::typeof(save_dot), xs, filename) =
    push!(dyna.dots, (xs, filename))

(::DiceDyna)(::typeof(==), x::Dist, y) = 
    prob_equals(x,y)

(::DiceDyna)(::typeof(==), x, y::Dist) = 
    prob_equals(x,y)

(::DiceDyna)(::typeof(==), x::Dist, y::Dist) = 
    prob_equals(x,y)

# avoid transformation when it is known to trigger a bug
for f in :[getfield, typeof, Core.apply_type, typeassert, (===),
        Core.sizeof, Core.arrayset, tuple, isdefined, fieldtype, nfields,
        isa, Core.arraysize, repr, print, println, Base.vect, Broadcast.broadcasted,
        Broadcast.materialize, Core.Compiler.return_type, Base.union!, Base.getindex, Base.haskey,
        Base.pop!, Base.setdiff, unsafe_copyto!, Base.fma_emulated].args
    @eval (::DiceDyna)(::typeof($f), args...) = $f(args...)
end

# avoid transformation for performance (may cause probabilistic errors to become deterministic)
for f in :[xor, atleast_two, prob_equals, (&), (|), (!), isless, ifelse, 
    Base.collect_to!, Base.collect, Base.steprange_last, oneunit, 
    Base.pairwise_blocksize, eltype, firstindex, iterate, 
    continuous, uniform, flip].args
    @eval (::DiceDyna)(::typeof($f), args...) = $f(args...)
end

"Show pseudo-IR as run by dice's dynamo"
macro code_ir_dice(code)
    esc(quote
        ir = @code_ir $code
        functional(ir)
    end)
end