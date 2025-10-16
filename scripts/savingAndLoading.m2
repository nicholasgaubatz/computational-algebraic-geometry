-- saveBigList(bigList, filename) : write an .m2 file that reconstructs bigList
saveBigList = (bigList, filename) -> (
    s := "";                             -- accumulator string
    for i from 0 to (#bigList - 1) list (
        Li := bigList_i;
        if #Li == 0 then (
            s = s | ("L" | toString i | " = {};\n");
        ) else (
            R := ring Li_0;             -- ring for this inner list
            s = s | ("R" | toString i | " = " | toString R | ";\n");
            for j from 0 to (#Li - 1) list (
                p := Li_j;
                nm := "p" | toString i | "_" | toString j;
                s = s | (nm | " = " | toString p | ";\n");
            );
            -- collect the p names into L_i
            entries1 := apply(0..(#Li - 1), j -> "p" | toString i | "_" | toString j);
            s = s | ("L" | toString i | " = {" | concat(entries1, ", ") | "};\n");
        )
    );
    -- biglist variable
    bigEntries := apply(0..(#bigList - 1), i -> "L" | toString i);
    s = s | ("biglist = {" | concat(bigEntries, ", ") | "};\n");
    writeFile(filename, s);
);

-- Example usage:
R1 = QQ[a,b,c]; R2 = ZZ/101[x,y];
L1 = {a-b, b-c, a+b*c};
L2 = {x^2 + y, x - 3*y};
big = {L1, L2};
saveBigList(big, "myBigList.m2");
