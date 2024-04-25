function twopowers(n)
    [2^(i-1) for i in 1:n]
end

function tb_gen_rbt(rs, p, sz, parent_color, last_callsite)
    function dependent_to_val(dependent)
        if dependent == :size
            sz
        elseif dependent == :parent_color
            parent_color
        elseif dependent == :last_callsite
            last_callsite
        else
            error()
        end
    end
    function dependents_to_flip(name, dependents)
        if isnothing(dependents)
            flip(.5)
        else
            group = collect(Base.map(dependent_to_val, dependents))
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
            l = tb_gen_rbt(rs, p, sz - 1, color, 20)
            r = tb_gen_rbt(rs, p, sz - 1, color, 30)
            ColorKVTree.Node(color, l, k, v, r)
        end
    end
end