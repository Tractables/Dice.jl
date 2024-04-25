#==
Coq < Coq < Coq < GenSizedColor = 
{|
  arbitrarySized :=
    fun s : nat =>
    (let
       fix arb_aux (size : nat) : G Color :=
         match size with
         | 0 => oneOf [returnGen R; returnGen B]
         | S _ => freq [ (1, returnGen R); (1, returnGen B)]
         end in
     arb_aux) s
|}
     : GenSized Color
==#

#==
Coq < Coq < Coq < GenSizedTree = 
{|
  arbitrarySized :=
    fun s : nat =>
    (let
       fix arb_aux (size : nat) : G Tree :=
         match size with
         | 0 => returnGen E
         | S size' =>
             freq [ (1, returnGen E);
             (1,
             bindGen arbitrary
               (fun p0 : Color =>
                bindGen (arb_aux size')
                  (fun p1 : Tree =>
                   bindGen arbitrary
                     (fun p2 : Z =>
                      bindGen arbitrary
                        (fun p3 : Z =>
                         bindGen (arb_aux size')
                           (fun p4 : Tree => returnGen (T p0 p1 p2 p3 p4)))))))]
         end in
     arb_aux) s
|}
     : GenSized Tree
==#
function tb_gen_rbt(rs, p, sz, parent_color)
    if sz == 0
        ColorKVTree.Leaf()
    else
        flip_leaf = if p.learn_leaf_weights
            leaf_group = if p.use_parent_color
                [sz, parent_color]
            else
                [sz]
            end
            flip_for(rs, "leaf", leaf_group)
        else
            flip(.5)
        end

        @dice_ite if flip_leaf
            ColorKVTree.Leaf()
        else
            red_group = []
            p.color_by_size && push!(red_group, sz)
            p.use_parent_color && push!(red_group, parent_color)
            color = @dice_ite if flip_for(rs, "red", red_group) Color.Red() else Color.Black() end
            k = uniform(DistInt32, 0, 100)
            v = DistInt32(0)
            l = tb_gen_rbt(rs, p, sz - 1, color)
            r = tb_gen_rbt(rs, p, sz - 1, color)
            ColorKVTree.Node(color, l, k, v, r)
        end
    end
end