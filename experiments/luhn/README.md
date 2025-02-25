# Luhn model

This folder contains the code used for Figure 3 of the paper. Each subfolder contains runnable implementations of the Luhn model for IDs ranging from 2-10 digits.

Instructions for using the example code are given below. These assume you have already installed Dice.jl, WebPPL, and Psi according to the instructions in `../INSTALL.md`"



## Instructions
### Dice.jl
This folder contains 3 files:
- `luhn6_example.jl` is an example Luhn file with 6 ID digits; it can be run with `julia --project luhn6_example.jl`, and will output a time computed with the Julia BenchmarkTools utility.
- `luhn.jl` is a Luhn template program which can take a varying argument `n`, representing the number of digits in the ID. For example, calling `julia --project luhn.jl 6` will result in the same result as running `luhn6_example.jl`. `n` can range from 2-10. 
- `run.sh` is a shell script calling `luhn.jl` with all arguments from 2 to 10, and writing the time results to a file ` dicejl_luhn.txt`. 
### WebPPL
This folder contains 3 files:
- `luhn6_example.wppl` is an example Luhn file with 6 ID digits as above. To run it, use the command `webppl luhn6_example.wppl --require webppl-timeit`; this will return a time in milliseconds computed with `webppl-timeit`. 
- `luhn.wppl` is a template file as above, taking a named argument `n` representing the number of digits in the id. To replicate the program above, use the command `webppl luhn.wppl --require webppl-timeit -- --n 6`. As above, `n` can range from 2-10.
- `run.sh` is again a shell script calling `luhn.wppl` with arguments 2-10, and writing the results to a file `webppl_luhn.txt`.
### Psi
This folder contains 4 files:
- `luhn4_example.psi` is an example Luhn file with 4 ID digits. To run it, use the command `psi luhn4_example.psi`. As there is no built-in timing utility, we used the Bash `time` command to measure time for Psi. To call using the Psi DP algorithm, add the `--dp` flag (as in `psi --dp luhn4_example.psi`). 
- `gen_psi_luhn.py` is a Python script which takes a single parameter `n` and outputs a Psi Luhn program corresponding to `n` ID digits. For example, to generate a Psi program equivalent to `luhn4_example.psi`, call `python gen_psi_luhn.py 4 > output.psi`.
- `run.sh` and `run_dp.sh` are two shell scripts which iterate over ID lengths 2-10, first calling `gen_psi_luhn.py` then Psi to get a runtime in seconds for each length. They correspond to Psi and Psi (DP), and output to files `psi_luhn.txt` and `psi_dp_luhn.txt`, respectively. 

Note that for WebPPL and Psi, the provided scripts only run a single trial for each experiment. 




