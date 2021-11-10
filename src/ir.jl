export to_dice_ir

struct IrMgr <: DiceManager end

ir_manager() = 
    IrMgr()

abstract type IrNode end

struct IrFlip <: IrNode
    prob::Float64
end

new_var(::IrMgr, prob) =
    IrFlip(prob)

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
    
###################################

to_dice_ir(pb::ProbBool) =
    to_dice_ir(pb.bit)

to_dice_ir(ir::IrFlip) = 
    "flip $(ir.prob)"

to_dice_ir(ir::IrNegate) = 
    "!($(to_dice_ir(ir.x)))"

to_dice_ir(ir::IrConjoin) = 
    "($(to_dice_ir(ir.x))) && ($(to_dice_ir(ir.y)))"

to_dice_ir(ir::IrDisjoin) = 
    "($(to_dice_ir(ir.x))) || ($(to_dice_ir(ir.y)))"