-- A function to determine whether an Artinian algebra $R/I$ has the weak Lefschetz
-- property.
WLP = (A) -> (
    if dim(A)>0 then return "Error: algebra is not Artinian!";
    
    i := 0;
    -- ell = sum gens A;
    R := ambient A;
    setRandomSeed(1);
    ell := (entries(random(R^{1}, R^1)))#0#0;
    while basis(i,A) != 0 do (
        -- https://math.stackexchange.com/questions/4650612/induced-matrix-on-degrees-macaulay2
        -- https://macaulay2.com/doc/Macaulay2/share/doc/Macaulay2/Macaulay2Doc/html/_quotient_lp__Matrix_cm__Matrix_rp.html
        M := ell * basis(i,A) // basis(i+1,A);
        greatestRank := min(numrows M, numcols M);
        if rank M < greatestRank then return "A does not have WLP at A_" | toString i;
        i = i+1;
    );
    return "The AOT algebra has WLP";
)

socleDegree = (I) ->(A:=(ring I)/I;
                                  m:=ideal vars A;
				  j:=0;
				  while m^j!=0 do j = j+1;
				  return j-1
				  )

-- From Hal.
WLPcheck = (I) ->(R := ring(I);
                 L := random(R^{1},R^1); --get random linear form
			     Acut := coker((gens I)|L); --quotient by random linear form
			     SD := socleDegree(I);
			     A := coker gens I;
			     INJorSURJ := apply(SD+1, i->({((hilbertFunction(i,A)+ hilbertFunction(i+1,Acut))==hilbertFunction(i+1,A)),
			                                 (hilbertFunction(i+1,Acut)==0)}));
			     IJ2 := apply(INJorSURJ, j->(if (j_0 or j_1) then 1 else 0));
			     if (product IJ2)==1 then true else false)