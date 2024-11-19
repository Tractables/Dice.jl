(cd ~/Dice.jl && julia --project $TOOL -f "LangSiblingDerivedGenerator{STLC}(Main.Expr.t,Pair{Type,Integer}[Main.Expr.t=>5,Main.Typ.t=>2],2,3)" "Pair{SpecEntropy{STLC},Float64}[SpecEntropy{STLC}(2,200,wellTyped)=>0.3]" "2" "0.1")

(cd ~/Dice.jl && julia --project $TOOL -f "LangSiblingDerivedGenerator{BST}(Main.KVTree.t,Pair{Type,Integer}[Main.KVTree.t=>4],2,3)" "Pair{SpecEntropy{BST},Float64}[SpecEntropy{BST}(2,200,isBST)=>0.3]" "2000" "0.1")
(cd ~/Dice.jl && julia --project $TOOL -f "LangSiblingDerivedGenerator{RBT}(Main.ColorKVTree.t,Pair{Type,Integer}[Main.ColorKVTree.t=>4,Main.Color.t=>0],2,3)" "Pair{SpecEntropy{RBT},Float64}[SpecEntropy{RBT}(2,200,isRBT)=>0.3]" "2000" "0.1")
(cd ~/Dice.jl && julia --project $TOOL -f "LangSiblingDerivedGenerator{STLC}(Main.Expr.t,Pair{Type,Integer}[Main.Expr.t=>5,Main.Typ.t=>2],2,3)" "Pair{SpecEntropy{STLC},Float64}[SpecEntropy{STLC}(2,200,wellTyped)=>0.3]" "2000" "0.1")
(cd ~/Dice.jl && julia --project $TOOL -f "LangBespokeSTLCGenerator(5,2)" "[ApproxSTLCConstructorEntropy()=>0.03]" "2000" "0.1")
