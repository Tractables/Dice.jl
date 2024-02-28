safedec(x::DistUInt{T}) where T = @dice_ite if prob_equals(x, DistUInt{T}(0)) DistUInt{T}(0) else x - DistUInt{T}(1) end

function gen_tree(s::Integer, lo::DistNat, hi::DistNat, approx_unif::Bool, track_return)
    track_return(
        @dice_ite if s == 0 || hi - lo < DistNat(2)
            DistE()
        else
            s′ = s - 1
            if flip(register_weight!("sz$(s)"))
                DistE()
            else
                k = if approx_unif
                    unif_approx(lo + DistNat(1), safedec(hi))
                else
                    unif(lo + DistNat(1), safedec(hi))
                end
                v = DistNat(0) # arbitrary
                l = gen_tree(s′, lo, k, approx_unif, track_return)
                r = gen_tree(s′, k, hi, approx_unif, track_return)
                DistT(l, k, v, r)
            end
        end
    )
end

function gen_tree_dummy_vals(s::Integer, track_return)
    track_return(
        @dice_ite if s == 0
            DistE()
        else
            s′ = s - 1
            if flip(register_weight!("sz$(s)"))
                DistE()
            else
                k = DistNat(0)
                v = DistNat(0) # arbitrary
                l = gen_tree_dummy_vals(s′, track_return)
                r = gen_tree_dummy_vals(s′, track_return)
                DistT(l, k, v, r)
            end
        end
    )
end
