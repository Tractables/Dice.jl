import sys

n = int(sys.argv[1])

print("""
var model = function() {\n""")
for i in range(n):
  print(f"    var prior{i}" + " = beta({a: 1, b: 1})\n")
  print(f"    var z{i}" + " = bernoulli({p: prior" + f"{i}" + "});")

print("     var y = z0 ")
for i in range(1,n):
  print(f" | z{i}")
print(";")
print("""
                                  if (y) {
                                              factor(Gaussian({mu: 80, sigma: 8}).score(79));
                                                } else{
                                                            factor(Gaussian({mu: 135, sigma: 8}).score(79));
                                                              }

                                                  if (y) {
                                                              factor(Gaussian({mu: 80, sigma: 8}).score(136));
                                                                } else{
                                                                            factor(Gaussian({mu: 135, sigma: 8}).score(136));
                                                                              }


                                                                            
                                                                                                  return prior0;
                                                                                                  }

var func1 = function() {
                return Infer({method: argv.m, particles: argv.s, samples: argv.s}, model);
                }

timeit( function() { return expectation(func1());})
      """)

