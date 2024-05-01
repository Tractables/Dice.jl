safedec(x::DistUInt{T}) where T = @dice_ite if prob_equals(x, DistUInt{T}(0)) DistUInt{T}(0) else x - DistUInt{T}(1) end

function gen_tree(rs, s::Integer, lo::DistNat, hi::DistNat, approx_unif::Bool, track_return)
    track_return(
        @dice_ite if s == 0 || hi - lo < DistNat(2)
            KVTree.Leaf()
        else
            s′ = s - 1
            if flip(register_weight!(rs, "sz$(s)"))
                KVTree.Leaf()
            else
                k = if approx_unif
                    unif_approx(lo + DistNat(1), safedec(hi))
                else
                    unif(lo + DistNat(1), safedec(hi))
                end
                v = DistNat(0) # arbitrary
                l = gen_tree(rs, s′, lo, k, approx_unif, track_return)
                r = gen_tree(rs, s′, k, hi, approx_unif, track_return)
                KVTree.Node(l, k, v, r)
            end
        end
    )
end

function gen_tree_dummy_vals(rs, s::Integer, track_return)
    track_return(
        @dice_ite if s == 0
            KVTree.Leaf()
        else
            s′ = s - 1
            if flip(register_weight!(rs, "sz$(s)"))
                KVTree.Leaf()
            else
                k = DistNat(0)
                v = DistNat(0) # arbitrary
                l = gen_tree_dummy_vals(rs, s′, track_return)
                r = gen_tree_dummy_vals(rs, s′, track_return)
                KVTree.Node(l, k, v, r)
            end
        end
    )
end


function typebased_gen_tree(rs, p, size::Integer, last_callsite, track_return)
    function dependent_to_val(dependent)
        if     dependent == :size          size
        elseif dependent == :last_callsite last_callsite
        else error() end
    end
    function dependents_to_flip(name, dependents)
        if isnothing(dependents)
            flip(.5)
        else
            group = collect(Base.map(dependent_to_val, dependents))
            flip_for(rs, name, group)
        end
    end

    track_return(
        @dice_ite if size == 0
            KVTree.Leaf()
        else
            s′ = size - 1
            if dependents_to_flip("leaf", p.leaf_dependents)
                KVTree.Leaf()
            else
                l = typebased_gen_tree(rs, p, s′, 10, track_return)
                r = typebased_gen_tree(rs, p, s′, 11, track_return)
                k = sum(
                    @dice_ite if dependents_to_flip("num$(n)", p.num_dependents)
                        DistUInt32(n)
                    else
                        DistUInt32(0)
                    end
                    for n in twopowers(p.intwidth)
                )
                v = DistNat(0) # arbitrary
                KVTree.Node(l, k, v, r)
            end
        end
    )
end

function tree_size(e::KVTree.T)
    match(e, [
        :Leaf => () -> DistUInt32(0),
        :Node => (l, k, v, r) -> DistUInt32(1) + tree_size(l) + tree_size(r),
    ])
end
