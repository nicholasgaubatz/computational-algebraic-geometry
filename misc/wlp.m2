-- A function to determine whether an Artinian algebra $R/I$ has the weak Lefschetz
-- property.
WLP = (A) -> (
    if dim(A)>0 then return "Error: algebra is not Artinian!";
    
    i = 0;
    ell = sum gens A;
    while basis(i,A) != 0 do (
        -- https://math.stackexchange.com/questions/4650612/induced-matrix-on-degrees-macaulay2
        -- https://macaulay2.com/doc/Macaulay2/share/doc/Macaulay2/Macaulay2Doc/html/_quotient_lp__Matrix_cm__Matrix_rp.html
        M = ell * basis(i,A) // basis(i+1,A);
        greatestRank = min(numrows M, numcols M);
        if rank M < greatestRank then return "A does not have WLP at A_" | toString i;
        i = i+1;
    );
    return "A has WLP";
)

-------------------------------------

R = ZZ/101[x,y]

-- An algebra that has WLP
I = ideal(x^2,y^3)
A = R/I
WLP(A)

-- A non-Artinian algebra
J = ideal(x*y,y^2)
A = R/J
WLP(A)

-- An algebra that fails WLP at A_2
R = ZZ/101[a..f]
I = ideal(a^2, b^2, c^2, d^2, e^2, f^2, a*b, c*d, e*f)
A = R/I
WLP(A)

-- Examine the matrix A_2 -> A_3
M = (sum gens A) * basis(2,A) // basis(3,A)
rank M