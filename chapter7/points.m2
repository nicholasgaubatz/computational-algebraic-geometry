-- From section 7.1, compute the ideal of either a point represented as a column vector
-- or points represented as a matrix of column vectors
pointideal1 = (m) -> (
    v = transpose vars R;
    minors(2, (v|m))
)
-- Return the ideal of the point represented by a column matrix

pointsideal1 = (m) -> (
    t = rank source m;
    J = pointideal1(submatrix(m, , {0}));
    scan(t-1, i -> (J=intersect(J, pointideal1(submatrix(m, , {i+1})))));
    J
)
-- For a matrix with columns representing points, return the ideal of all the points