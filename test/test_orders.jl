using Pkg; Pkg.activate("Dice/test");
using Dice

function gen_code(nbcols = 5, nbrows = 5)
    code = ""
    for row = 1:nbrows
        for col = 1:nbcols
            if row == 1
                p = rand()
                code *= """
                        let x$(row)y$(col) = discrete($p, $(1-p)) in
                        """
            else
                p1 = rand()
                p2 = rand()
                code *= """
                        let x$(row)y$(col) = if x$(row-1)y$(col) == int(1,0) then 
                                discrete($p1, $(1-p1)) 
                            else 
                                discrete($p2, $(1-p2)) in
                        """
            end
        end
    end
    for col = 1:nbcols
        if col == 1
            p1 = rand()
            p2 = rand()
            code *= """
                    let z$col = if x$(nbrows)y$(col) == int(1,0) then 
                            discrete($p1, $(1-p1)) 
                        else 
                            discrete($p2, $(1-p2)) in
                    """
        else
            p1 = rand()
            p2 = rand()
            p3 = rand()
            p4 = rand()
            code *= """
                    let z$col = if x$(nbrows)y$(col) == int(1,0) then 
                            if z$(col-1) == int(1,0) then 
                                discrete($p1, $(1-p1)) 
                            else 
                                discrete($p2, $(1-p2)) in
                        else 
                            if z$(col-1) == int(1,0) then 
                                discrete($p3, $(1-p3)) 
                            else 
                                discrete($p4, $(1-p4)) in
                    """
        end
    end

    rtuple = ""
    for row = 1:nbrows
        for col = 1:nbcols
            if row ==1 && col ==1
                rtuple = "x1y1"
            else
                rtuple *= "(x$(row)y$(col),$rtuple)"
            end
        end
    end
    for col = 1:nbcols
        rtuple *= "(z$(col),$rtuple)"
    end

    code *= rtuple
    code
end

code = gen_code();
println(code)