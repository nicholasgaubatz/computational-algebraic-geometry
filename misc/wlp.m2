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
    return "The AOT algebra has WLP";
)
