export to_dice_ir_string

using DAGs: DAGs, DAG, num_parents, Inner, Leaf, foldup_aggregate

struct IrMgr <: DiceManager end

abstract type IrNode <: DAG end
abstract type IrLeafNode <: IrNode end
abstract type IrInnerNode <: IrNode end

DAGs.NodeType(::Type{<:IrInnerNode}) = Inner()
DAGs.NodeType(::Type{<:IrLeafNode}) = Leaf()

# Leaf IR nodes
mutable struct IrFlip <: IrLeafNode
    # note: must be mutable to have reference equality
    prob::Float64
end

new_var(::IrMgr, prob) =
    IrFlip(prob)

struct IrConst <: IrLeafNode
    value
end

constant(::IrMgr, c::Bool) =
    IrConst(c)

struct IrId <: IrLeafNode
    id::Symbol
end

# Inner IR nodes
mutable struct IrNegate <: IrInnerNode
    x::IrNode
end
    
negate(::IrMgr, x) =
    IrNegate(x)

DAGs.children(n::IrNegate) = [n.x]

mutable struct IrConjoin <: IrInnerNode
    x::IrNode
    y::IrNode
end
    
conjoin(::IrMgr, x, y) =
    IrConjoin(x, y)
    
DAGs.children(n::IrConjoin) = [n.x, n.y]
mutable struct IrDisjoin <: IrInnerNode
    x::IrNode
    y::IrNode
end
    
disjoin(::IrMgr, x, y) =
    IrDisjoin(x, y)
    
DAGs.children(n::IrDisjoin) = [n.x, n.y]

mutable struct IrIte <: IrInnerNode
    cond::IrNode
    then::IrNode
    elze::IrNode
end

ite(::IrMgr, x, y, z) =
    IrIte(x, y, z)

DAGs.children(n::IrIte) = [n.cond, n.then, n.elze]
    
mutable struct IrLet <: IrInnerNode
    id::IrId
    x::IrNode
    y::IrNode
end

DAGs.children(n::IrLet) = [n.id, n.x, n.y]

rundice(::IrMgr, code::IrNode) =
    rundice(code) 

rundice(code::IrNode) =
    rundice(string(code)) 

infer(mgr::IrMgr, code::IrNode) =
    infer(code)

infer(code::IrNode) =
    infer_ocml(string(code))

###################################


function identify_reuse(root::IrNode)
    num_ids = 0
    identified = Dict{IrNode,IrId}()
    for (irnode, num_par) in num_parents(root)
        if !(irnode isa IrConst) && num_par > 1
            identified[irnode] = IrId(Symbol("x$(num_ids += 1)"))
        end
    end
    identified
end

function treeify(root::IrNode)
    ids = identify_reuse(root)
    lets = Vector{Tuple{IrId, IrNode}}()

    substitute(n_orig,n_sub) = begin
        if haskey(ids, n_orig)
            id = ids[n_orig]
            push!(lets, (id, n_sub))
            id
        else
            n_sub
        end
    end

    f_leaf(n::IrLeafNode) = substitute(n, n)
    f_inner(n::IrInnerNode, cs) = substitute(n, typeof(n)(cs...))
    root_sub = foldup_aggregate(root, f_leaf, f_inner, IrNode)

    foldr(lets; init=root_sub) do le, ir
        IrLet(le[1], le[2], ir)
    end    
end

Base.show(io::IO, ::IrMgr, ir::IrNode) =
    print(io, "(", ir, ")")

Base.show(io::IO, ir::IrFlip) =
    print(io, "flip ", ir.prob)

Base.show(io::IO, ir::IrId) =
    print(io, ir.id)

Base.show(io::IO, ir::IrConst) =
    print(io, ir.value)

Base.show(io::IO, ir::IrNegate) = 
    print(io, "!(", ir.x, ")")

Base.show(io::IO, ir::IrConjoin) = 
    print(io, "(", ir.x, ") && (", ir.y, ")")

Base.show(io::IO, ir::IrDisjoin) = 
    print(io, "(", ir.x, ") || (", ir.y, ")")

Base.show(io::IO, ir::IrIte) = begin
    print(io, "if ", ir.cond, 
             " then ", ir.then, 
             " else ", ir.elze) 
end

Base.show(io::IO, ir::IrLet) = begin
    print(io, "let ", ir.id, 
             " = ", ir.x, 
             " in ", ir.y) 
end
