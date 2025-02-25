import sys 

n = int(sys.argv[1])
data = [2, 0, 5, 6, 0, 6, 7, 1, 7, 8]



text = "def main(){\n"
text += f"ps := array({n}, 0:Z);\n"
text += f"data := {data[:n]};\n"
text += '''
    for i in [0..ps.length) {
        ps[i] = uniformInt(0, 9);
    }
    

    for i in [0..ps.length) {
        if (flip (1/2)) {
            observe(ps[i] == data[i]);
        }
    }

    double := true;
    sum:Z := 0;
    for i in [1..ps.length) {
        val := ps[i];
        if (double) {
            if (val > 4) {
                sum = sum + 2*val - 9;
            }
            else {
                sum = sum + 2*val;
            }
            double = false;
        }
        else {
            sum = sum + val;
            double = true;
        }
    }

    observe(10-(sum%10) == data[0]);
    
    return ps[0];
}'''


print(text)
