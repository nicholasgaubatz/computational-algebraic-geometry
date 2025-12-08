loadPackage("Polyhedra", Reload=>true);
load "scripts/load_src.m2";

initials = statePolytope AOTideal;
L = initials#0;
#L -- Number of distinct initial ideals
allIdeals = L / (M -> ideal M);
allRings = allIdeals / (I -> ring I);
wlpValues = apply(allIdeals, allRings, (I, S) -> (WLP(S/I)));
bools = wlpValues / (s -> s == "The AOT algebra has WLP")
number(wlpValues, (s -> s == "The AOT algebra has WLP"))