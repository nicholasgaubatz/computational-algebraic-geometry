-- TODO: convert this into a function that returns a list of hash tables.
n = 6;

elapsedTime allGraphs = connGraphs(n);
elapsedTime allArrs = allGraphs / (G -> graphToArr G);
-- For some reason, NaiveAlgorithm is faster!
elapsedTime allAOTs = allArrs / (L -> AOTAlgebra(L, NaiveAlgorithm=>true));
elapsedTime allWLPcheck = allAOTs / (A -> WLPcheck ideal A);
elapsedTime allWLP = allAOTs / (A -> WLP A);
elapsedTime allWLPbool = allWLP / (s -> s == "The AOT algebra has WLP");
if allWLPcheck == allWLPbool then print "Success!" else print "Failure."
