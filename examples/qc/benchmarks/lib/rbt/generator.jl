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
function tb_gen_rbt(rs, p, sz, parent_red)
    if sz == 0
        ColorKVTree.Leaf()
    else
        flip_leaf = if p.learn_leaf_weights
            @dice_ite if parent_red | !p.use_parent_color
                flip(register_weight!(rs, "leaf_sz$(sz)_redparent"))
            else
                flip(register_weight!(rs, "leaf_sz$(sz)_blackparent"))
            end
        else
            flip(.5)
        end
        @dice_ite if flip_leaf
            ColorKVTree.Leaf()
        else
            flip_red = @dice_ite if parent_red | !p.use_parent_color
                flip(register_weight!(rs, if p.color_by_size "red_sz$(sz)_redparent" else "red_redparent" end))
            else
                flip(register_weight!(rs, if p.color_by_size "red_sz$(sz)_blackparent" else "red_blackparent" end))
            end
            color = if flip_red Color.Red() else Color.Black() end
            k = uniform(DistInt32, 0, 100)
            v = DistInt32(0)
            l = tb_gen_rbt(rs, p, sz - 1, flip_red)
            r = tb_gen_rbt(rs, p, sz - 1, flip_red)
            ColorKVTree.Node(color, l, k, v, r)
        end
    end
end