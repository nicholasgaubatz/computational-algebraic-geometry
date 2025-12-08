-- Required variables before running these lines: R and AOTideal.

-- Config: pull in AOT ideal.
I = AOTideal

-- Get the number of variables.
numEdges = #(gens ring AOTideal);

-- Define coefficients of generic linear form.
S = frac QQ[a_1..a_numEdges];
T = R**S;
Y = submatrix(vars T, 0..(numEdges-1));
A = submatrix(vars T, numEdges..(2*numEdges-1));
phi = map(T, R, Y); -- Lift?
TotIdeal = phi(I);

-- Config: map to examine.
i = 2;

-- Compute the matrix.
Bi = super basis(i, coker gens TotIdeal);
Bi1 = super basis(i+1, coker gens TotIdeal);
ell = sum apply((entries A)#0, (entries Y)#0, (i,j) -> i*j)
M = ell * Bi // Bi1
rank M

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