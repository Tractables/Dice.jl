export to_dice_ir_string

struct IrMgr <: DiceManager end

abstract type IrNode end

struct IrFlip <: IrNode
    prob::Float64
end

new_var(::IrMgr, prob) =
    IrFlip(prob)
struct IrConst <: IrNode
    value
end

constant(::IrMgr, c::Bool) =
    IrConst(c)

struct IrNegate <: IrNode
    x::IrNode
end
    
negate(::IrMgr, x) =
    IrNegate(x)


struct IrConjoin <: IrNode
    x::IrNode
    y::IrNode
end
    
conjoin(::IrMgr, x, y) =
    IrConjoin(x, y)
    
struct IrDisjoin <: IrNode
    x::IrNode
    y::IrNode
end
    
disjoin(::IrMgr, x, y) =
    IrDisjoin(x, y)
    
struct IrIte <: IrNode
    cond::IrNode
    then::IrNode
    elze::IrNode
end
    
ite(::IrMgr, x, y, z) =
    IrIte(x, y, z)
    
rundice(::IrMgr, code::IrNode) =
    rundice(string(code)) 

infer(mgr::IrMgr, code::IrNode) =
    infer_ocml(string(code))

###################################

Base.show(io::IO, ::IrMgr, ir::IrNode) =
    print(io, "(", ir, ")")

Base.show(io::IO, ir::IrFlip) =
    print(io, "flip ", ir.prob)

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
