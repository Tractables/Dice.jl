using Pkg; Pkg.activate("Dice/test");
using HTTP
using Dice

bns = ["alarm", "andes", "asia", "barley", "cancer", "child", "diabetes", "earthquake", "hailfinder", "hepar2", "insurance", "link", "mildew", "munin", "munin1", "munin2", "munin3", "munin4", "pathfinder", "pigs", "sachs", "survey", "water", "win95pts", "BN_28", "BN_78", "BN_79", "alarm-alt", "alarm-safer", "cpcs54", "diagnose_a", "diagnose_a_multi", "diagnose_b", "diagnose_b_multi", "emdec6g", "fire_alarm", "moissac3", "spect", "tcc4e"]

dir = "problog_transpiled"
mkpath("$dir")

for bn in bns

    println("transpiling $bn")

    r = HTTP.request("GET", "https://raw.githubusercontent.com/ellieyhcheng/dice/master/benchmarks/bayesian-networks//$bn.dice"); nothing;
    bn_code = String(r.body); nothing;

    open("$dir/$bn.pl", "w") do io
        Dice.toproblog(bn_code, io)
    end

end
