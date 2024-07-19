using Dice

@inductive Label L() M1() M2() H()
all_labels = [L(), M1(), M2(), H()]
bot = L()
@inductive BinOpT BAdd() BMult() BJoin() BFlowsTo() Beq()

RegId = DistInt32
@inductive Instr [
    # basic instructions
    Put(DistInt32, RegId),
    Mov(RegId, RegId),
    Load(RegId, RegId),
    Store(RegId, RegId),
    Write(RegId, RegId),
    BinOp(BinOpT, RegId, RegId, RegId),
    Nop(),
    Halt(),
    Jump(RegId),
    BNZ(DistInt32, RegId),
    BCall(RegId, RegId, RegId),
    BRet(),

    # public first-class labels 
    Lab(RegId, RegId),
    PcLab(RegId),
    PutLab(Label, RegId),

    # dynamic memory allocation
    Alloc(RegId, RegId, RegId),
    PGetOff(RegId, RegId),
    PSetOff(RegId, RegId, RegId),
    MSize(RegId, RegId),
    MLab(RegId, RegId),
]

@inductive OpCode [
  OpPut(),
  OpMov(),
  OpLoad(),
  OpStore(),
  OpWrite(),
  OpBinOp(),
  OpNop(),
  OpJump(),
  OpBNZ(),
  OpBCall(),
  OpBRet(),
  # missing for Halt
  OpLab(),
  OpPcLab(),
  OpPutLab(),
  OpAlloc(),
  OpPGetOff(),
  OpPSetOff(),
  OpMSize(),
  OpMLab(),
]

opCodes = [
  OpPut(),
  OpMov(),
  OpLoad(),
  OpStore(),
  OpWrite(),
  OpBinOp(),
  OpNop(),
  OpJump(),
  OpBNZ(),
  OpBCall(),
  OpBRet(),
  OpLab(),
  OpPcLab(),
  OpPutLab(),
  OpAlloc(),
  OpPGetOff(),
  OpPSetOff(),
  OpMSize(),
  OpMLab(),
]


Mframe = Block = Tuple{DistInt32, Label}
Imem = List{Instr}

@inductive Pointer Ptr_(Mframe, DistInt32)

@inductive Value Vint(DistInt32) Vptr(Pointer) Vlab(Label)
@inductive Atom Atm(Value, Label)

@inductive PtrAtom PAtm(DistInt32, Label)

Register = Atom
RegSet = List{Register}

@inductive StackFrame SF(PtrAtom, RegSet, RegId, Label)
@inductive Stack ST(List{StackFrame})

@inductive Memframe{A} Fr(Label, List{A})
# Definition mem A := Map.t (list (memframe A)).
# Definition memory := mem Atom.
# (* Specialize the Memory frame declaration *)
# Definition frame := memframe Atom.

@inductive SState St(Imem, Memory, Stack, RegSet, PtrAtom)

@inductive Variation{A} Var_(Label, A, A)

@inductive Map{K,V} 

# Variation{SState}

Info = Tuple{Mframe, DistInt32, List{Tuple{Mframe, DistInt32}}, DistInt32}

function gen_BinOpT(rs)
    frequency_for(rs, "BinOpT_weights", [
        BAdd(), BMult(), BJoin(), BFlowsTo(), Beq(),
    ])
end

function gen_label(rs)
    frequency_for(rs, "label_weights", all_labels)
end