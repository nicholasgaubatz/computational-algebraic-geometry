-- A function that takes in a set of linear forms and returns the Orlik-Terao algebra.
OTAlgebra = (L) -> (
    -- Define the base ring of the OT Algebra.
    R := ring(L#0);
    F := coefficientRing R;
    variables := vars(0..(#L-1)); -- Create a list of variables names that M2 can work with.
    S := F[variables];
    f := map(S, R);

    -- Determine the relations among the linear forms in L.
    I := ideal L;
    M := syz gens I;
    degs := (degrees M)#1;
    inds := positions(degs, i -> i=={1}); -- Determine columns where max degree is 1.
    deps := (entries transpose M)_inds;
    deps1 := deps / (dep -> apply(dep, i -> f(i)));
    rels := apply(deps1, dep -> sum(apply(dep, gens S, (a, y) -> a*y)));

    -- Compute and return the OT Algebra
    J := ideal rels;
    return S/J;
)

AOTAlgebra = (L) -> (
    A = OTAlgebra L;
    T = ambient A;
    I = ideal A;
    squares = ideal((gens T) / (i -> i^2));
    return T/(I + squares);
)

-------------------------------------

-- Load this file. Ensure that the terminal is open in the computational-algebraic-geometry/ directory.
-- load "misc/aot.m2"

R = QQ[x,y]
L = {x, y, x+y}
A = OTAlgebra L
describe A

B = AOTAlgebra L
describe B

load "misc/wlp.m2"

WLP(B)