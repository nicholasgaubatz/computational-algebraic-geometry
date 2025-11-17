connGraphs = method()
-- Generate all graphs on n vertices.
connGraphs(ZZ) := List => (n1) -> (
    return drop(generateGraphs(n1), 1) / (str -> stringToGraph str);
)

-- Generate a sublist of all graphs on n vertices.
connGraphs(ZZ, List) := List => (n1, subList1) -> (
    return drop(generateGraphs(n1), 1)_subList1 / (str -> stringToGraph str);
)

-- Given a string representation of a graph, return its graphic arrangement.
-- This is necessary because generateGraphs gives its vertices zero-indexed,
-- while graphic requires one-indexed vertices.
graphToArr = (G1) -> (
    -- Get all the edges of these graphs.
    E1 := edges G1;
    -- Convert each set to a list.
    E1 = E1 / (e -> toList e);
    -- Define a polynomial ring with non-indexed variables.
    R1 := QQ[vars(0..(#vertexSet(G1)-1))];
    varsList1 := gens R1;
    -- Convert vertices into variables.
    L1 := E1 / (e -> (varsList1#(min(e)) - varsList1#(max(e))));
    -- Return the graphic arrangement.
    return L1;
)