-- Load this file. Ensure that the terminal is open in the computational-algebraic-geometry/ directory.
-- load "misc/aot.m2"

load "wlp.m2"

--------------------------------------

-- Test all sorts of graphic arrangements. We'll only consider connected graphs of a
-- certain number of vertices at a time.

-- Configs: set the number of vertices to examine and ground field of the polynomial ring.
n = 7;
groundField = QQ;

-- Compute the polynomial ring.
R = groundField[toList vars(0..(n-1))];
varsList = gens R;
-- Use NautyGraphs to generate all isomorphism classes of graphs of the given number of vertices.
elapsedTime allGraphs = generateGraphs(n, OnlyConnected=>true) / (str -> stringToGraph str);
-- elapsedTime allGraphs = (generateGraphs(n) / (str -> stringToGraph str))_{1..(#allGraphs)};
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
-- Takes 137 seconds for n=7.
elapsedTime allOTAlgebraIdeals = allGraphicArrangements / (A -> orlikTerao(arrangement A, groundField[y_1..y_(#A)], NaiveAlgorithm=>true)); -- NaiveAlgorithm is actually faster here???
elapsedTime allOTAlgebras = apply(allOTAlgebraIdeals, allGraphicArrangements, (A, L) -> (if ring(A)===ZZ then (ideal(0_(groundField[y_1..y_(#L)]))) else (A)));
elapsedTime allAOTAlgebras = allOTAlgebras / (I -> ((ring I) / ideal(gens gb (I + ideal((gens ring I) / (x -> x^2))))));
elapsedTime allAOTAlgebrasAsStrings = allAOTAlgebras / (A -> toString A);
-- Determine whether these arrangements have WLP.
-- elapsedTime allWLP = allAOTAlgebras / (A -> WLP(A) == "The AOT algebra has WLP") -- Takes too long for n=5.
-- Hal's function. For n=7, first 700 algebras take 92 seconds.
-- elapsedTime allWLP = allAOTAlgebras / (A -> WLPcheck(ideal A))
elapsedTime allWLP = allAOTAlgebras / (A -> WLP(A) == "The AOT algebra has WLP")
--  Get all graphs whose arrangements fail WLP.
allGraphs_(positions(allWLP, i -> i == false))
#(allGraphs_(positions(allWLP, i -> i == false)))
-- Get all graphs whose arrangements satisfy WLP.
allGraphs_(positions(allWLP, i -> i == true))

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
setRandomSeed(0);
allAOTAlgebrasL = allAOTAlgebras / (A -> (ambient A)/ideal(gens gb (ideal A + ideal(random((ambient A)^{1}, (ambient A)^1)))));
elapsedTime allHilbSeriesL = allAOTAlgebrasL / (A -> hilbertSeriesAsList A);
-- Zero-pad the end of the just-computed Hilbert series to match the first length.
allHilbSeriesLPadded = apply(allHilbSeries, allHilbSeriesL, (L, K) -> join(K, apply(#L-#K, i -> 0)));
-- Test equality of the two computations to determine WLP.
allWLPv2 = apply(allDiffs, allHilbSeriesLPadded, (L, K) -> L == K)
-- Get all graphs whose arrangements fail WLP in this manner.
allGraphs_(positions(allWLPv2, i -> i == false))

------------------------------------------------

-- Save the above so we don't have to recompute everything.

directory = "../artifacts/n=" | n | "/"
directory | "allGraphicArrangements.m2" << allGraphicArrangements << endl << close;
directory | "allAOTAlgebrasAsStrings.m2" << allAOTAlgebrasAsStrings << endl << close;
directory | "allHilbSeries.m2" << allHilbSeries << endl << close;
directory | "allHilbSeriesL.m2" << allHilbSeriesL << endl << close;
directory | "allBadGraphs.m2" << (allGraphs_(positions(allWLP, i -> i == false)) / (G -> toString G)) << endl << close;

------------------------------------------------

-- Load everything saved above and get all the graphs that don't satisfy WLP.

-- Load the files.
directory = "../artifacts/n=" | n | "/"
allGraphicArrangements1 = value get (directory | "allGraphicArrangements.m2");
allAOTAlgebrasAsStrings2 = value get (directory | "allAOTAlgebrasAsStrings.m2");
allHilbSeries1 = value get (directory | "allHilbSeries.m2");
allHilbSeriesL1 = value get (directory | "allHilbSeriesL.m2");
allBadGraphs = value get (directory | "allBadGraphs.m2");

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

k = 18;
L = allGraphicArrangements#k;
WLPcheck ideal(allAOTAlgebras#k)
WLP(allAOTAlgebras#k)
graphicArrToGraph L

------------------------------------------------

-- in(I) WLP => I WLP. Are there any graphs where I WLP but in(I) not, or vice versa?

-- n = 6;
-- groundField = QQ;
-- R = groundField[toList vars(0..(n-1))];

-- -- Load the files.
-- directory = "artifacts/n=" | n | "/"
-- allGraphicArrangements1 = value get (directory | "allGraphicArrangements.m2");
-- allAOTAlgebrasAsStrings1 = value get (directory | "allAOTAlgebrasAsStrings.m2");
-- allHilbSeries1 = value get (directory | "allHilbSeries.m2");
-- allHilbSeriesL1 = value get (directory | "allHilbSeriesL.m2");
-- allBadGraphs = value get (directory | "allBadGraphs.m2");

-- allWLP = allAOTAlgebrasAsStrings1 / (A -> WLP A == "The AOT algebra has WLP")
-- allWLPHal = allAOTAlgebrasAsStrings1 / (A -> WLPcheck ideal A)

-- allAOTAlgebrasInitial = allAOTAlgebrasAsStrings1 / (A -> (ambient A)/(ideal leadTerm ideal A));
-- allWLPInitial = allAOTAlgebrasInitial / (A -> WLP A == "The AOT algebra has WLP")
-- allWLPInitialHal = allAOTAlgebrasAsStrings1 / (A -> WLPcheck ideal A)

-- comparison = apply(allWLP, allWLPInitial, (L, K) -> L == K)
-- thoseThatBreak = positions(comparison, i -> i == false) -- {12, 13, 15, 16, 18, 19, 20} for n=5.

-- IhasWLPbutInIdoesnt = positions(apply(allWLPHal, allWLPInitialHal, (a, b) -> (a==true and b==false)), i -> i == true) -- {12, 13, 15, 16, 18, 19, 20} for n=5.
-- InIhasWLPbutIdoesnt = positions(apply(allWLPHal, allWLPInitialHal, (a, b) -> (a==false and b==true)), i -> i == true) -- {} for n=5. Should be empty if everything's working!

-- -- allAOTAlgebras#6
-- -- allGraphs#6
-- -- WLP(allAOTAlgebras#6)
-- -- WLP((ambient(allAOTAlgebras#6)) / (ideal leadTerm ideal(allAOTAlgebras#6)))

-- -- Hal's code results in something bad! n=6, graph index 83. Let's verify.
-- -- Actually, it's ok now.

-- -- My code:
-- H = allGraphicArrangements1#83
-- H
-- A = AOTAlgebra(H)
-- describe A
-- WLP(A)

-- A1 = leadTermQuotient(A)
-- describe A1
-- WLP(A1)

-- -- Hal's:
-- WLPcheck(ideal A)
-- WLPcheck(ideal A1)