-- 7.1.1. Write a Macaulay2 script which takes a set of points in \mathbb{P}^{2} and a
-- degree i, and computes the Hilbert function.
hilbertFunctionPoints = (X, i) -> (
    -- Get a list of evaluation maps from R to the underlying field k using the
    -- points in X
    maps = apply(X, L -> map(R, R, L));
    -- Get a list of the monomials of degree i in R
    basisI = (entries(basis(i, R)))#0;
    -- Create a small function to take in a function f and apply it to the above
    -- monomials
    evaluateBasis = (f) -> apply(basisI, m -> f(m));
    -- Create a matrix where each row is the result of evaluating the monomial list
    -- at the prescribed points
    matrixPhi = matrix apply(maps, f -> evaluateBasis(f));

    -- Return the rank of this matrix
    rank matrixPhi
)