function bespoke_gen_lrusp(rs, sz)
    @dice_ite if sz == 0 || flip(register_weight!(rs, "nil$(sz)"))
        LRUS.Nil()
    else
        LRUS.Cons(
            frequency([
                register_weight!(rs, "insert$(sz)") =>
                    LRUS.Insert(uniform(DistInt32, 0, 3)),
                register_weight!(rs, "contains$(sz)") =>
                    LRUS.Contains(uniform(DistInt32, 0, 3)),
                register_weight!(rs, "popstale$(sz)") =>
                    LRUS.PopStale(),
            ]),
            bespoke_gen_lrusp(rs, sz - 1)
        )
    end
end