-- Appendix A: Macaulay2 code verifying WLP failure
-- for all initial ideals of the AOT algebra of K_4
-- with a dangling edge.


loadPackage("HyperplaneArrangements", Reload=>true);
loadPackage("Polyhedra", Reload=>true);

-- Define the graph, K_4 + dangling edge, as a list.

G = {{1, 2}, {1, 3}, {1, 4}, {2, 3}, {2, 4}, {3, 4}, {4, 5}};

-- Compute the AOT ideal using HyperplaneArrangements.

OTideal = orlikTerao graphic G; -- Orlik-Terao ideal
squares = ideal((gens ring OTideal) / (x -> x^2)); -- Squares of the variables
AOTideal = OTideal + squares -- Artinian Orlik-Terao ideal

-- Compute the state polytope and all initial ideals using Polyhedra.

-- For the first command, result is seq. of length 2: 
--   first elt is list of gens of all initial ideals,
--   second elt is state polytope.
initials = statePolytope AOTideal;
allInitialIdealGens = initials#0;
#allInitialIdealGens -- Number of distinct initial ideals; 54 here
allInitialIdeals = allInitialIdealGens / (M -> ideal M); -- Turn gen sets into ideals
allAmbientRings = allInitialIdeals / (I -> ring I); -- Get all ambient rings

-- Define a function that determines whether an Artinian algebra has WLP. Brute force.
-- Warning: uses a random linear form. 
-- If result is true, the algebra has WLP. 
-- If false, there is a very small probability that the algebra truly has WLP.

WLP = (A) -> (
    if dim(A)>0 then return "Error: algebra is not Artinian!"; -- Dimension check
    
    R := ambient A;
    setRandomSeed(1); -- Reproducibility; change this for different linear form
    ell := (entries(random(R^{1}, R^1)))#0#0; -- Get just the linear form
    i := 0;
    while basis(i,A) != 0 do (
        M := ell * basis(i,A) // basis(i+1,A); -- Constructs the matrix between bases
        greatestRank := min(numrows M, numcols M); -- Maximum possible rank
        if rank M < greatestRank then return false;
        i = i+1; -- Move on if full rank
    );
    return true;
)

-- Determine whether each initial ideal has WLP.

-- Apply the above function.
wlpValues = apply(allInitialIdeals, allAmbientRings, (I, S) -> (WLP(S/I)));

-- Display the number of initial ideals that have WLP.
number(wlpValues, b -> b) -- 0 here