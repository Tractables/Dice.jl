using Dice

NUM_PEOPLE = 5
NUM_LIARS = 2
VOUCHES = Dict(
    1 => [2, 3],  # Person 1 says that Person 2 and Person 3 are truth-tellers
    2 => [1, 2],
    3 => [1],
    4 => [5],
    5 => [1, 4],
)

md = @dice begin
    liars = DistVector{DistUInt32}()

    # select unique liars
    for _ in 1:NUM_LIARS
        new_liar = uniform(DistUInt32, 1, NUM_PEOPLE + 1)
        observe(!prob_contains(liars, new_liar))
        liars = prob_append(liars, new_liar)
    end

    # check vouches
    for (person, vouchees) in VOUCHES
        person_liar = prob_contains(liars, DistUInt32(person))
        vouchees_honest = reduce(&, [!prob_contains(liars, DistUInt32(vouchee)) for vouchee in vouchees])
        observe(person_liar | vouchees_honest)
    end

    liars
end

pr(md)