-- Ensure that the terminal is open in the computational-algebraic-geometry/ directory.
load "misc/wlp.m2"

-- An algebra that has WLP
R = ZZ/101[x,y]
I = ideal(x^2,y^3)
A = R/I
WLP(A)

-- A non-Artinian algebra
R = ZZ/101[x,y]
J = ideal(x*y,y^2)
A = R/J
WLP(A)

-- An algebra that fails WLP at A_2 (octahedron)
R = ZZ/101[a..f]
I = ideal(a^2, b^2, c^2, d^2, e^2, f^2, a*b, c*d, e*f)
A = R/I
WLP(A)

-- Examine the matrix A_2 -> A_3
M = (sum gens A) * basis(2,A) // basis(3,A)
rank M

-- An Artinian Orlik-Terao algebra (example 1.3) from the 2-formality paper from 2015)
R = ZZ/101[x,y,z,w]
I = ideal(y*z*w + x*z*w + x*y*w - x*y*z) + ideal(x^2,y^2,z^2,w^2)
A = R/I
WLP(A)

-- Square ideals
squareWLP = (k) -> (
    R = ZZ/101[x_0..x_k];
    I = ideal((gens R) / (x -> x^2));
    A = R/I;
    WLP(A)
)
-- (0..20) / (i -> squareWLP i)