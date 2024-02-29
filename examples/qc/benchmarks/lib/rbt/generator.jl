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
function tb_gen_rbt(sz, color_by_sz)
    if sz == 0
        DistRBE()
    else
        @dice_ite if flip(register_weight!("leaf_sz$(sz)"))
            DistRBE()
        else
            color_group = if color_by_sz "red_sz$(sz)" else "red" end
            color = if flip(register_weight!(color_group)) DistRed() else DistBlack() end
            k = DistInt32(0)
            v = DistInt32(0)
            l = tb_gen_rbt(sz - 1, color_by_sz)
            r = tb_gen_rbt(sz - 1, color_by_sz)
            DistRBT(color, l, k, v, r)
        end
    end
end