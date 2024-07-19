function twopowers(n)
    [2^(i-1) for i in 1:n]
end

function tb_gen_rbt(rs, p, sz, parent_color, stack_tail)
    function get_dependent_dist(dependent)
        if     dependent == :size         sz
        elseif dependent == :parent_color parent_color
        elseif dependent == :stack_tail   stack_tail
        else error() end
    end
    function dependents_to_flip(name, dependents)
        if isnothing(dependents)
            flip(.5)
        else
            group = collect(Base.map(get_dependent_dist, dependents))
            flip_for(rs, name, group)
        end
    end

    if sz == 0
        ColorKVTree.Leaf()
    else
        flip_leaf = dependents_to_flip("leaf", p.leaf_dependents)
        @dice_ite if flip_leaf
            ColorKVTree.Leaf()
        else
            flip_red = dependents_to_flip("red", p.red_dependents)
            color = @dice_ite if flip_red Color.Red() else Color.Black() end
            k = sum(
                @dice_ite if dependents_to_flip("num$(n)", p.num_dependents)
                    DistInt32(n)
                else
                    DistInt32(0)
                end
                for n in twopowers(p.intwidth)
            )
            v = DistInt32(0)
            l = tb_gen_rbt(rs, p, sz - 1, color, update_stack_tail(p, stack_tail, 10))
            r = tb_gen_rbt(rs, p, sz - 1, color, update_stack_tail(p, stack_tail, 11))
            ColorKVTree.Node(color, l, k, v, r)
        end
    end
end