# What value of X makes this uniform?
# frequency [(X, choose (1000, 2000)),
#            (1 - X, choose (5000, 8000))]

# The code is not very readable because we're doing it at the level of Dice
# using our relatively low-level primitives for differentiating.
# Imagine instead we added a "choose" operator to Lang, and wrote:
# prog = L.Frequency([], [
#     L.Choose(1000, 2000),
#     L.Choose(5000, 8000),
# ])
# g = interp(prog)
# maximize_entropy_with_REINFORCE(g) # this function is made-up, but its core parts
#                                      are in the implementation of spec entropy

using Dice

lo1, hi1, lo2, hi2 = 1000, 2000, 5000, 8000

X = sigmoid(Var("X_psp"))
g = @dice_ite if flip(X)
    uniform(DistUInt32, lo1, hi1)
else
    uniform(DistUInt32, lo2, hi2)
end

rand_int(lo, hi) = Integer(floor(rand() * (hi - lo) + lo))

function lang_sample(var_vals)
    p = sigmoid(var_vals[Var("X_psp")])
    if rand() < p
        rand_int(lo1, hi1)
    else
        rand_int(lo2, hi2)
    end
end

var_vals = Valuation([Var("X_psp") => 0.])
NUM_EPOCHS = 100
NUM_SAMPLES = 1000
for epoch in 1:NUM_EPOCHS
    a = ADComputer(var_vals)
    samples = [DistUInt32(lang_sample(var_vals)) for _ in 1:NUM_SAMPLES]

    println("EPOCH $(epoch)")
    println(count([Dice.frombits(sample,Dict()) for sample in samples]) do n
        n < hi1
    end)
    println("X = $(sigmoid(var_vals[Var("X_psp")]))")

    l = Dice.LogPrExpander(WMC(BDDCompiler([
        prob_equals(g,sample)
        for sample in samples
    ])))
    loss, actual_loss = sum(begin
        lpr_eq = Dice.expand_logprs(l, LogPr(prob_equals(g, sample)))
        [lpr_eq * compute(a, lpr_eq), lpr_eq]
        end
        for sample in samples
    )

    vals, derivs = differentiate(
        var_vals,
        Derivs(loss => 1)
    )
    for (adnode, d) in derivs
        if adnode isa Var
            var_vals[adnode] -= d * 0.0003
        end
    end
end

#==
EPOCH 1
510
X = 0.5
EPOCH 2
476
X = 0.48551772802249665
EPOCH 3
466
X = 0.4602939216756826
EPOCH 4
450
X = 0.44638670393246893
EPOCH 5
422
X = 0.4324212492344248
EPOCH 6
394
X = 0.4114004519490938
EPOCH 7
398
X = 0.38834986258314136
EPOCH 8
373
X = 0.3830293071898431
EPOCH 9
342
X = 0.3669815291939448
EPOCH 10
316
X = 0.3442160255912011
EPOCH 11
321
X = 0.32210094580094134
EPOCH 12
309
X = 0.3164689075355883
EPOCH 13
305
X = 0.3079633119376253
EPOCH 14
304
X = 0.30250445264404136
EPOCH 15
312
X = 0.29977076965537547
EPOCH 16
301
X = 0.3027769969317935
EPOCH 17
309
X = 0.2983385419321724
EPOCH 18
295
X = 0.30062737695395847
EPOCH 19
286
X = 0.2943869336766721
EPOCH 20
294
X = 0.28724914594475626
EPOCH 21
295
X = 0.28826717608102354
EPOCH 22
280
X = 0.2892095136124746
EPOCH 23
274
X = 0.28207450750230073
EPOCH 24
287
X = 0.27605917859232826
EPOCH 25
284
X = 0.2798632805307038
EPOCH 26
288
X = 0.2800501607988091
EPOCH 27
274
X = 0.2821263436559373
EPOCH 28
277
X = 0.276081505972824
EPOCH 29
257
X = 0.2749230573812961
EPOCH 30
275
X = 0.2646834610133474
EPOCH 31
288
X = 0.2688043591056264
EPOCH 32
293
X = 0.27708367593481026
EPOCH 33
283
X = 0.2833167758579155
EPOCH 34
280
X = 0.28105432365523175
EPOCH 35
287
X = 0.2785833726693394
EPOCH 36
297
X = 0.2809818118671273
EPOCH 37
274
X = 0.28705620619338584
EPOCH 38
267
X = 0.2781856573881626
EPOCH 39
278
X = 0.2709453993935347
EPOCH 40
286
X = 0.2731235574167136
EPOCH 41
283
X = 0.2780525762932744
EPOCH 42
262
X = 0.2787580765234978
EPOCH 43
260
X = 0.26876182976732876
EPOCH 44
252
X = 0.26340335378005003
EPOCH 45
266
X = 0.25717531095965523
EPOCH 46
259
X = 0.2609636239041802
EPOCH 47
273
X = 0.2593843360050436
EPOCH 48
263
X = 0.26537041965935776
EPOCH 49
266
X = 0.2633146516328447
EPOCH 50
271
X = 0.26381789621477725
EPOCH 51
264
X = 0.26646339181276424
EPOCH 52
263
X = 0.2642915414940629
EPOCH 53
276
X = 0.2628232470850334
EPOCH 54
278
X = 0.26843112609849146
EPOCH 55
281
X = 0.27198508078101985
EPOCH 56
260
X = 0.2750676033765828
EPOCH 57
273
X = 0.2661915194354423
EPOCH 58
266
X = 0.2685229104965594
EPOCH 59
266
X = 0.2661864441028282
EPOCH 60
262
X = 0.2651297752307472
EPOCH 61
280
X = 0.2627251654345005
EPOCH 62
232
X = 0.2703367776794666
EPOCH 63
235
X = 0.250867924675464
EPOCH 64
221
X = 0.24347501924147194
EPOCH 65
238
X = 0.23364824804491574
EPOCH 66
220
X = 0.23646782866349614
EPOCH 67
214
X = 0.22982054182400896
EPOCH 68
242
X = 0.22389867895598617
EPOCH 69
243
X = 0.2332420003406031
EPOCH 70
245
X = 0.23852815906861166
EPOCH 71
225
X = 0.2420976592220408
EPOCH 72
239
X = 0.23477849777652188
EPOCH 73
250
X = 0.23748906485114107
EPOCH 74
244
X = 0.2438760240643832
EPOCH 75
255
X = 0.24426918947147094
EPOCH 76
252
X = 0.2495605199931026
EPOCH 77
230
X = 0.25072394241587403
EPOCH 78
241
X = 0.2411241897601408
EPOCH 79
268
X = 0.2415490204628225
EPOCH 80
258
X = 0.2543208675081459
EPOCH 81
258
X = 0.2558102115137782
EPOCH 82
245
X = 0.2565118744707828
EPOCH 83
244
X = 0.2507279423793718
EPOCH 84
248
X = 0.2475561513253994
EPOCH 85
232
X = 0.2478983077613871
EPOCH 86
221
X = 0.2407065844122371
EPOCH 87
212
X = 0.2323223617954655
EPOCH 88
235
X = 0.22427059822105544
EPOCH 89
204
X = 0.2303071658262754
EPOCH 90
234
X = 0.21981492925736745
EPOCH 91
269
X = 0.22751276460956854
==#

