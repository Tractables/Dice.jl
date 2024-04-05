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


function typebased_gen_tree(rs, s::Integer, track_return)
    track_return(
        @dice_ite if s == 0
            KVTree.Leaf()
        else
            s′ = s - 1
            if flip(register_weight!(rs, "sz$(s)"))
                KVTree.Leaf()
            else
                l = typebased_gen_tree(rs, s′, track_return)
                r = typebased_gen_tree(rs, s′, track_return)
                k = v = DistNat(0) # arbitrary
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
