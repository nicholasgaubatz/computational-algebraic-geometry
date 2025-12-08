-- Config: number of edges in graph.
numEdges = 6;

-- Define the ambient ring and ideal of squares of variables.
R = QQ[y_1..y_numEdges];
J = ideal(gens R / (y -> y^2));

-- Config: squarefree ideal.
-- I = J + ideal(y_1*y_2 - y_1*y_3 + y_2*y_3, y_4*y_5 - y_4*y_6 + y_5*y_6); -- Bowtie
I = AOTideal

-- Define coefficients of generic linear form.
S = frac QQ[a_1..a_numEdges];
T = R**S;
Y = submatrix(vars T, 0..(numEdges-1));
A = submatrix(vars T, numEdges..(2*numEdges-1));
L = Y * transpose A;
phi = map(T, R, Y); -- Lift?
TotIdeal = phi(I);

-- Config: map to examine.
i = 2;

-- Compute the matrix.
Bi = super basis(i, coker gens TotIdeal);
Bi1 = super basis(i+1, coker gens TotIdeal);
N = L * ambient Bi;
M = contract(ambient Bi1, transpose N)
rank M

-- W = matrix {toList(numEdges:(0_S))}
-- W1 = (W | vars S)
-- W2 = map(S, T, W1)
-- M1 = W2(M)
-- rank M1

-- Examine the kernel and cokernel.
kernel1 = kernel transpose M
cokernel1 = kernel M

-- Determine a true element of the cokernel.
cokernel2 = generators cokernel1
cokernel3 = map(target cokernel2, source cokernel2, cokernel2);
cokernel4 = submatrix(cokernel3, , {0})
eltOfCoker = (entries(Bi1 * cokernel4))#0#0

-- Determine whether it factors!
factor eltOfCoker