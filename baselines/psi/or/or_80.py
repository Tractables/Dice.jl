def main() {
    prior := beta(1, 1);
    z1 := bernoulli(prior);

    z2 := bernoulli(0.5);
    z3 := bernoulli(0.5);
    z4 := bernoulli(0.5);
    z5 := bernoulli(0.5);
    z6 := bernoulli(0.5);
    z7 := bernoulli(0.5);
    z8 := bernoulli(0.5);
    z9 := bernoulli(0.5);
    z10 := bernoulli(0.5);
    z11 := bernoulli(0.5);
    z12 := bernoulli(0.5);
    z13 := bernoulli(0.5);
    z14 := bernoulli(0.5);
    z15 := bernoulli(0.5);
    z16 := bernoulli(0.5);
    z17 := bernoulli(0.5);
    z18 := bernoulli(0.5);
    z19 := bernoulli(0.5);
    z20 := bernoulli(0.5);
    z21 := bernoulli(0.5);
    z22 := bernoulli(0.5);
    z23 := bernoulli(0.5);
    z24 := bernoulli(0.5);
    z25 := bernoulli(0.5);
    z26 := bernoulli(0.5);
    z27 := bernoulli(0.5);
    z28 := bernoulli(0.5);
    z29 := bernoulli(0.5);
    z30 := bernoulli(0.5);
    z31 := bernoulli(0.5);
    z32 := bernoulli(0.5);
    z33 := bernoulli(0.5);
    z34 := bernoulli(0.5);
    z35 := bernoulli(0.5);
    z36 := bernoulli(0.5);
    z37 := bernoulli(0.5);
    z38 := bernoulli(0.5);
    z39 := bernoulli(0.5);
    z40 := bernoulli(0.5);
    z41 := bernoulli(0.5);
    z42 := bernoulli(0.5);
    z43 := bernoulli(0.5);
    z44 := bernoulli(0.5);
    z45 := bernoulli(0.5);
    z46 := bernoulli(0.5);
    z47 := bernoulli(0.5);
    z48 := bernoulli(0.5);
    z49 := bernoulli(0.5);
    z50 := bernoulli(0.5);
    z51 := bernoulli(0.5);
    z52 := bernoulli(0.5);
    z53 := bernoulli(0.5);
    z54 := bernoulli(0.5);
    z55 := bernoulli(0.5);
    z56 := bernoulli(0.5);
    z57 := bernoulli(0.5);
    z58 := bernoulli(0.5);
    z59 := bernoulli(0.5);
    z60 := bernoulli(0.5);
    z61 := bernoulli(0.5);
    z62 := bernoulli(0.5);
    z63 := bernoulli(0.5);
    z64 := bernoulli(0.5);
    z65 := bernoulli(0.5);
    z66 := bernoulli(0.5);
    z67 := bernoulli(0.5);
    z68 := bernoulli(0.5);
    z69 := bernoulli(0.5);
    z70 := bernoulli(0.5);
    z71 := bernoulli(0.5);
    z72 := bernoulli(0.5);
    z73 := bernoulli(0.5);
    z74 := bernoulli(0.5);
    z75 := bernoulli(0.5);
    z76 := bernoulli(0.5);
    z77 := bernoulli(0.5);
    z78 := bernoulli(0.5);
    z79 := bernoulli(0.5);
    z80 := bernoulli(0.5);
    y := 
z1 | 
z2 | 
z3 | 
z4 | 
z5 | 
z6 | 
z7 | 
z8 | 
z9 | 
z10 | 
z11 | 
z12 | 
z13 | 
z14 | 
z15 | 
z16 | 
z17 | 
z18 | 
z19 | 
z20 | 
z21 | 
z22 | 
z23 | 
z24 | 
z25 | 
z26 | 
z27 | 
z28 | 
z29 | 
z30 | 
z31 | 
z32 | 
z33 | 
z34 | 
z35 | 
z36 | 
z37 | 
z38 | 
z39 | 
z40 | 
z41 | 
z42 | 
z43 | 
z44 | 
z45 | 
z46 | 
z47 | 
z48 | 
z49 | 
z50 | 
z51 | 
z52 | 
z53 | 
z54 | 
z55 | 
z56 | 
z57 | 
z58 | 
z59 | 
z60 | 
z61 | 
z62 | 
z63 | 
z64 | 
z65 | 
z66 | 
z67 | 
z68 | 
z69 | 
z70 | 
z71 | 
z72 | 
z73 | 
z74 | 
z75 | 
z76 | 
z77 | 
z78 | 
z79 | 
z80;

            o1 := if y {gauss(1, 1)} else {gauss(-1, 1)};
    o2 := if y {gauss(1, 1)} else {gauss(-1, 1)};
    o3 := if y {gauss(1, 1)} else {gauss(-1, 1)};
    cobserve(o1,1.5);
    cobserve(o2,-1.5);
    //cobserve(o3, -1.5);

    return Expectation(prior);
}

