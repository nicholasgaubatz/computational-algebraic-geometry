loadPackage("Graphs", Reload=>true)
loadPackage("NautyGraphs", Reload=>true)
loadPackage("HyperplaneArrangements", Reload=>true)

-- Given a list of hyperplanes, construct the Artinian Orlik-Terao algebra.
AOTAlgebra = (L) -> (
    I = orlikTerao(arrangement L);
    T = ring I;
    squares = ideal((gens T) / (i -> i^2));
    return T/(I + squares);
)

-- Given a quotient ring, construct the new quotient ring using the ideal's initial ideal.
leadTermQuotient = (A) -> (
    R = ambient A;
    I = ideal A;
    return R/(ideal leadTerm I);
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

-- Use https://csacademy.com/app/graph_editor/ to visualize output.
graphicArrToGraph = (L) -> (
    apply(L, h -> (
        h1 := toString((flatten entries gens ideal h)#0);
        print(h1#0 | " " | h1#2);)
    );
)
