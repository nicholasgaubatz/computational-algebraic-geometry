load "src/wlp.m2"

-- Config.
n = 13;

R = QQ[y_1..y_n];
squares = ideal((gens R) / (y -> y^2));
inI = squares + ideal(product(drop(gens R, 1)));
elapsedTime WLP(R/inI) -- n=13 takes 99 seconds.