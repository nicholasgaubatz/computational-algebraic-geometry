-- Format an integer n with leading zeros so that the integer has length at least w.
frontPadInt = (n, w1) -> (
    s1 := toString n;
    while #s1 < w1 do (
        s1 = "0" | s1;
    );
    s1
)




-- A homebrewed progress bar from ChatGPT.
-- TODO: implement this
-- progressBar = (i, n) -> (
--     width1 := 40;
--     done1 := floor(width1 * i / n);
--     bar1 := repeat("=", done1) | repeat(".", width1 - done1);
--     stdout << "\r[" << bar << "] " << toString i << "/" << toString n << flush;
-- );



-- n = #graphsList;
-- for i from 0 to n-1 do (
--     progressBar(i, n);
--     ... -- work
-- );
-- stdout << endl;