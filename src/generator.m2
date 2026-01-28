load(srcDirectory | "aot.m2")
load(srcDirectory | "graphic.m2")
load(srcDirectory | "misc.m2")
load(srcDirectory | "wlp.m2")

loadPackage("JSON", Reload=>true)

-- Given a graph G, compute the corresponding graphic arrangement L, compute the
-- Artinian Orlik-Terao algebra, determine whether it has WLP using our two different
-- functions, compute the AOT's Hilbert series, and return a hash table. 
graphToWLPHash = (G1) -> (
    L1 := graphToArr G1;
    -- For some reason, NaiveAlgorithm is faster!
    A1 := AOTAlgebra(L1, NaiveAlgorithm=>true);
    A2in := leadTermQuotient(A1);
    W1 := WLPcheck ideal A1;
    W2 := WLP A1;
    W3in := WLPcheck ideal A2in;
    W4in := WLP A2in;
    W2bool := W2 == "The AOT algebra has WLP";
    W4inbool := W4in == "The AOT algebra has WLP";
    if not W1 == W2bool then (error "Got differing results from two WLP functions!");
    if not W3in == W4inbool then (error "Got differing results from two WLP functions for initial ideal!");
    H1 := hilbertSeries(A1, Reduce=>true);
    H2 := hilbertSeries(A2in, Reduce=>true);
    if value (H1 == H2) == false then (error "Got differing Hilbert functions for R/I and R/in(I)!");
    if value (denominator H1 == 1) == true then (H1 = numerator H1) else (error "Hilbert series has denominator not equal to 1!");
    S := QQ[x];
    use S;
    return hashTable {graph => edges G1,
                      hyperplanes => L1,
                      AOTideal => ideal A1,
                      WLPfull => toExternalString W2,
                      AOTinIdeal => ideal A2in,
                      WLPin => toExternalString W4in,
                      hSeries => H1,
                      numVariables => #(gens ambient A1)};
)

-- Given a graphToWLPHash returned hash table, return some commands the user can copy and paste into M2.
WLPHashToCommands = (hashTable1) -> (
    return (
        "R = " | toString(QQ[y_1 .. y_(hashTable1#numVariables)]) | "\n" |
        "AOTideal = " | toExternalString(hashTable1#AOTideal) | "\n" |
        "AOTinIdeal = " | toExternalString(hashTable1#AOTinIdeal) | "\n" |
        "G = graph " | toString(hashTable1#graph)
    )
)

-- Given a graphToWLPHash returned hash table, convert it to something M2 can read in once saved to a file.
WLPHashToFileFormat = (hashTable1) -> (
    return hashTable {
        graph => edges(hashTable1#graph),
        hyperplanes => hashTable1#hyperplanes,
        AOTideal => toExternalString(ideal(hashTable1#AOTideal)),
        WLPfull => hashTable1#WLPfull,
        AOTinIdeal => toExternalString(ideal(hashTable1#AOTinIdeal)),
        WLPin => hashTable1#WLPin,
        hSeries => hashTable1#hSeries,
        numVariables => hashTable1#numVariables,
    }
)

-- Given a graph G, a file path f, and an integer i, call graphToWLPHash(G) and store the result at f.
saveGraphHash = (G1, path1, i1) -> (
    if fileExists path1 then (error("File " | path1 | " already exists!")) else (
        ht := graphToWLPHash G1;
        htCommands := WLPHashToCommands ht;
        -- ht := pairs WLPHashToFileFormat graphToWLPHash G1;
        path1 << ht << endl << endl << endl << htCommands << endl << close;
    );
)

-- Given a positive integer n and an existing directory, generate all isomorphism classes of graphs on n vertices,
-- construct the above hash table for each, create a subdirectory titled "n", and save each hash table in a
-- file titled "i", where the graph is the ith graph in the list. Make sure existing directory string has no slash at end.
generateTablesForN = (n1, parentDir1) -> (
    newDirectory1 = parentDir1 | "/n=" | n1 | "/";
    makeDirectory(newDirectory1);
    
    elapsedTime allGraphs1 := connGraphs(n1);
    numGraphs1 := #allGraphs1;
    print("Graphs generated.");

    elapsedTime for i1 from 0 to (numGraphs1-1) do (
        filename1 := newDirectory1 | (frontPadInt(i1, 4)) | ".m2";
        try (saveGraphHash(allGraphs1#i1, filename1, i1)) else (print("Saving graph " | i1 | " failed, skipping."));
        if i1 % (numGraphs1 // 10) == 0 then (print(toString(i1 // (numGraphs1 // 10) * 10) | "% done!"));
    );

    print("Done!")
)

-- Tests.
asdf = connGraphs(4);
grape = asdf#7;
cherry = graphToWLPHash grape;
kiwi = WLPHashToCommands cherry;
-- orange = WLPHashToFileFormat cherry;
-- toJSON cherry 

-- TODO: figure out how to store results. hash table isn't loadable, json doesn't work with ideals.

-- Generate hash tables.
-- n = 3;
-- generateTablesForN(n, "artifacts")

-- TODO: create a function that saves the above hash table to a file, then another function to wrap around and iterate over all graphs on n vertices.
-- Make sure it goes to a user-specified directory.

-- elapsedTime allArrs = allGraphs / (G -> graphToArr G);
-- -- For some reason, NaiveAlgorithm is faster!
-- elapsedTime allAOTs = allArrs / (L -> AOTAlgebra(L, NaiveAlgorithm=>true));
-- elapsedTime allWLPcheck = allAOTs / (A -> WLPcheck ideal A);
-- elapsedTime allWLP = allAOTs / (A -> WLP A);
-- elapsedTime allWLPbool = allWLP / (s -> s == "The AOT algebra has WLP");
-- if allWLPcheck == allWLPbool then print "Success!" else print "Failure."
