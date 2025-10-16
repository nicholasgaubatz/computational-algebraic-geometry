OTALgebra = method();
AOTAlgebra = method();

-- A function that takes in a set of linear forms and returns the Orlik-Terao algebra.
OTAlgebra = {MonomialOrder => GRevLex} >> opts -> (L) -> (
    -- Define the base ring of the OT Algebra.
    R := ring(L#0);
    F := coefficientRing R;
    variables := vars(0..(#L-1)); -- Create a list of variables names that M2 can work with.
    S := F[variables, MonomialOrder=>opts.MonomialOrder];
    f := map(S, R);

    -- Determine the relations among the linear forms in L.
    I := ideal L;
    M := syz gens I;
    degs := (degrees M)#1;
    inds := positions(degs, i -> i=={1}); -- Determine columns where max degree is 1.
    deps := (entries transpose M)_inds;
    deps1 := deps / (dep -> apply(dep, i -> f(i)));
    appropriateGens := apply(deps1, lst -> (gens S)_(toList(select(0..(#(gens S)-1), i -> lst#i != 0))));
    rels := apply(deps1, appropriateGens, (dep, lst) -> sum(apply(dep, gens S, (a, y) -> a*product(select(lst, e -> e != y)))));

    -- Compute and return the OT Algebra.
    if (#rels == 0) then return S else (
        J := ideal rels;
        return S/J;
    )
)

AOTAlgebra = {MonomialOrder => GRevLex} >> opts -> (L) -> (
    A = OTAlgebra(L, MonomialOrder=>opts.MonomialOrder);
    T = ambient A;
    I = ideal A;
    squares = ideal((gens T) / (i -> i^2));
    return T/(I + squares);
)

-- Take in an Artinian algebra and return a list of its nonzero Hilbert series entries.
hilbertSeriesAsList = (A) -> (
    hilbSer := hilbertSeries(A, Reduce=>true);
    if value(denominator hilbSer != Product(1)) == true then return "Error" else (
        pol := numerator hilbSer;
        coefs := (entries(flatten((coefficients(pol))#1)))#0;
        return coefs / (a -> (map(ZZ, ring coefs#0))(a));
    );
)

-------------------------------------

-- Load this file. Ensure that the terminal is open in the computational-algebraic-geometry/ directory.
-- load "misc/aot.m2"

load "misc/wlp.m2"

R = QQ[x,y]
L = {x, y, x+y}
A = OTAlgebra(L, MonomialOrder=>Lex)
describe A

B = AOTAlgebra(L, MonomialOrder=>Lex)
describe B

WLP(B)

-- Bowtie graph doesn't have WLP.
R = QQ[a,b,c,d,e]
L = {a-b,a-c,a-d,a-e,b-c,d-e}
C = AOTAlgebra(L, MonomialOrder=>Lex)
describe C
WLP(C)
Cprime = C / (sum gens C)
reduceHilbert hilbertSeries C
reduceHilbert hilbertSeries Cprime

--------------------------------------

-- Test all sorts of graphic arrangements. We'll only consider connected graphs of a
-- certain number of vertices at a time.

loadPackage("Graphs", Reload=>true)
loadPackage("NautyGraphs", Reload=>true)
loadPackage("HyperplaneArrangements", Reload=>true)

-- Configs: set the number of vertices to examine and ground field of the polynomial ring.
n = 5;
groundField = QQ;

-- Compute the polynomial ring.
R = groundField[toList vars(0..(n-1))];
varsList = gens R;
-- Use NautyGraphs to generate all isomorphism classes of graphs of the given number of vertices.
elapsedTime allGraphs = generateGraphs(n, OnlyConnected=>true) / (str -> stringToGraph str);
#allGraphs
-- Get all the edges of these graphs.
elapsedTime allGraphsEdges = allGraphs / (e -> edges e);
-- Convert each set to a list.
elapsedTime allGraphsEdges = allGraphsEdges / (L -> (L / (e -> toList e)));
-- These edges are zero-indexed, but we need them one-indexed.
elapsedTime allGraphsEdges = allGraphsEdges / (L -> (L / (e -> {e#0+1, e#1+1})));
-- For each graph, construct the graphic arrangement.
-- We're very finicky here, because it appears everything depends on the ordering of the variables in the defining linear forms of the hyperplanes.
elapsedTime allGraphicArrangements = allGraphsEdges / (L -> (L / (e -> (varsList#(min(e)-1) - varsList#(max(e)-1)))));
-- Construct the AOTs.
-- elapsedTime allAOTAlgebras = allGraphicArrangements / (A -> AOTAlgebra(A, MonomialOrder=>Lex));
-- Takes 4 seconds for n=6, 141 seconds for n=7
elapsedTime allOTAlgebraIdeals = allGraphicArrangements / (A -> orlikTerao(arrangement A, groundField[y_1..y_(#A)], NaiveAlgorithm=>true)); -- NaiveAlgorithm is actually faster here???
elapsedTime allOTAlgebras = apply(allOTAlgebraIdeals, allGraphicArrangements, (A, L) -> (if ring(A)===ZZ then (ideal(0_(groundField[y_1..y_(#L)]))) else (A)));
elapsedTime allAOTAlgebras = allOTAlgebras / (I -> ((ring I) / ideal(gens gb (I + ideal((gens ring I) / (x -> x^2))))));
elapsedTime allAOTAlgebrasAsStrings = allAOTAlgebras / (A -> toString A);
-- Determine whether these arrangements have WLP.
-- elapsedTime allWLP = allAOTAlgebras / (A -> WLP(A) == "The AOT algebra has WLP") -- Takes too long for n=5.
--  Get all graphs whose arrangements fail WLP.
-- allGraphs_(positions(allWLP, i -> i == false))
-- Get all graphs whose arrangements satisfy WLP.
-- allGraphs_(positions(allWLP, i -> i == true))

-- Just as another sanity check, let's check WLP using the Hilbert series.
-- This may also be quicker than the above.
-- First, compute the Hilbert series of each AOTAlgebra.
elapsedTime allHilbSeries = allAOTAlgebras / (A -> hilbertSeriesAsList(A));
-- Modify each original Hilbert series by padding the front with a zero and removing the last element.
allHilbSeriesShifted = allHilbSeries / (L -> ({0} | (drop(L, -1))));
-- Compute differences between original Hilbert series entries.
allDiffs = apply(allHilbSeries, allHilbSeriesShifted, (L, K) -> (apply(L, K, (m, n) -> max(0, m-n))));
-- Compute the Hilbert series of each AOTAlgebra quotiented by the sum of its variables.
-- Takes not much time for n=6, but about an hour and a half for n=7.
elapsedTime allHilbSeriesL = allAOTAlgebras / (A -> hilbertSeriesAsList((ambient A)/ideal(gens gb (ideal A + ideal(sum gens ambient A)))));
-- Zero-pad the end of the just-computed Hilbert series to match the first length.
allHilbSeriesLPadded = apply(allHilbSeries, allHilbSeriesL, (L, K) -> join(K, apply(#L-#K, i -> 0)));
-- Test equality of the two computations to determine WLP.
allWLPv2 = apply(allDiffs, allHilbSeriesLPadded, (L, K) -> L == K)
-- Get all graphs whose arrangements fail WLP in this manner.
allGraphs_(positions(allWLPv2, i -> i == false))

------------------------------------------------

-- Save the above so we don't have to recompute everything.

directory = "artifacts/n=" | n | "/"
directory | "allGraphicArrangements.m2" << allGraphicArrangements << endl << close;
directory | "allAOTAlgebrasAsStrings.m2" << allAOTAlgebrasAsStrings << endl << close;
directory | "allHilbSeries.m2" << allHilbSeries << endl << close;
directory | "allHilbSeriesL.m2" << allHilbSeriesL << endl << close;

------------------------------------------------

-- Load everything saved above and get all the graphs that don't satisfy WLP.

-- Load the files.
directory = "artifacts/n=" | n | "/"
allGraphicArrangements1 = value get (directory | "allGraphicArrangements.m2");
allAOTAlgebrasAsStrings1 = value get (directory | "allAOTAlgebrasAsStrings.m2");
allHilbSeries1 = value get (directory | "allHilbSeries.m2");
allHilbSeriesL1 = value get (directory | "allHilbSeriesL.m2");

-- Compare the Hilbert series.

-- Use NautyGraphs to generate all isomorphism classes of graphs of the given number of vertices.
elapsedTime allGraphs1 = generateGraphs(n, OnlyConnected=>true) / (str -> stringToGraph str);
-- Modify each original Hilbert series by padding the front with a zero and removing the last element.
allHilbSeriesShifted1 = allHilbSeries1 / (L -> ({0} | (drop(L, -1))));
-- Compute differences between original Hilbert series entries.
allDiffs1 = apply(allHilbSeries1, allHilbSeriesShifted1, (L, K) -> (apply(L, K, (m, n) -> max(0, m-n))));
-- Zero-pad the end of the just-computed Hilbert series to match the first length.
allHilbSeriesLPadded1 = apply(allHilbSeries1, allHilbSeriesL1, (L, K) -> join(K, apply(#L-#K, i -> 0)));
-- Test equality of the two computations to determine WLP.
allWLPv21 = apply(allDiffs1, allHilbSeriesLPadded1, (L, K) -> L == K)
-- Get all graphs whose arrangements fail WLP in this manner.
allGraphs1_(positions(allWLPv21, i -> i == false))
#positions(allWLPv21, i -> i == false)
#allGraphs1