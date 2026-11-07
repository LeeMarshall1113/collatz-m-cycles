
## L9 setup_exists (Params.lean) -- parameter change recorded

No blueprint inequality was found false, but the plan's multiplier M = 24 L is NOT used. With
crude exp bounds (ln K <= b, ln 6 <= 2, ln 7 >= 3/2, ln 19 >= 5/2, ln(c b) <= b/5, 69/100 >= e^(-1/2))
the T1' exponent is 52000b^2 + 11600bh - (3/2)(24*400)bh, which is positive at h = 4b for M = 24L
(coefficient +15040 b^2). Chosen instead: L = 400b, M = 48L = 19200b, h0 = 4b (Siegel: 2*h0*M =
153600 b^2 <= 160000 b^2), J = least with 10*h0*2^J >= L^4, delta = exp(-K/2^80).
Domination used: 10^15*b^6*2^81 <= 2^b (b >= 333), all delta terms bounded by exp(8e13 b^6) delta.
Also fixed a pre-existing elaboration error in effMeasure100 (explicit `(p := p)`).
