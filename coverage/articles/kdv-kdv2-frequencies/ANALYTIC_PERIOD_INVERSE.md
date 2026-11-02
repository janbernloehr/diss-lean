# Actual infinite period operator and analytic inverse

The actual infinite period matrix is now realized as a bounded operator
on complex ℓ², analytic in the Banach operator norm near the free
potential. Its free value is the identity. On a constructed smaller
neighborhood it has an analytic two-sided inverse of norm at most two.
The selected critical and entire numerator data are retained on that
identical neighborhood. **Convergent entire normalized differentials,
canonical products and all article main theorems remain open.**

Potentials remain `C([0,1],ℂ)` in the sup Banach norm. The contours are
the actual squared images of the positive circles `C(k*pi,pi/4)`, with
the exact Jacobian `2*z` and source normalization `1/(2*pi)`.

## One constructed all-mode spectral family

`ClassicalAllContourPeriods.lean` proves existence of
`ClassicalAllContourPeriodData N V A`. This packages one open complex V
containing zero, one positive amplitude bound A, and the identical N for:

- all selected critical branches, their free values, analyticity,
  actual critical equation, simplicity and half-radius frequency control;
- all entire numerator basis elements, joint analyticity, exact free
  numerators and the actual filled factor identity;
- actual source-root coverage and shifted-primitive bounds on every
  positive contour, including the low modes;
- every scalar period entry, analytic on V and equal to the full
  Kronecker delta at zero.

The construction reuses the established all-contour primitive estimates
and critical localization. It derives the numerators from the selected
critical family, rather than combining unrelated existential choices.
The proved `mono` lemma preserves the whole package on smaller open
neighborhoods containing zero.

The definition `classicalHillUniformHighPeriod` is used for every positive
contour index here. Its earlier use on a tail imposed no restriction on
the definition itself. This all-frequency-circle family removes changes
of contour in the finite head from the matrix estimates. Compatibility
with globally prescribed rough spectral cycles remains a separate task.

## Full matrix majorant, including the diagonal

`ClassicalAllContourPeriodBounds.lean` proves from that same constructed
data, for every q in V and all positive n,k,

```text
|P_nn(q)| <= (80/pi)*A,
|P_nk(q)| <= (5/pi)*A/|k-n|²,  n!=k.
```

The diagonal proof uses `|z²-mu_n| >= (pi²/8)*n`; the off-diagonal proof
uses the verified quadratic energy separation. All low modes are included.
No denominator or primitive estimate is supplied by an external caller
to the actual existence theorem.

`ReciprocalSquareKernel.lean` constructs a complex ℓ¹ kernel b whose norm
at d is one for d=0 and `1/|d|²` otherwise. Hölder multiplication of the
proved ℓ² punctured reciprocal lattice gives `norm b<=5`.

## Constructed bounded matrix action and operator analyticity

`ConvolutionDominatedMatrix.lean` proves the reusable matrix realization
theorem. If `|a_mn|<=|b_(m-n)|` for an ℓ¹ majorant b, it constructs an
operator on every Banach coefficient space ℓᵖ, including infinity, with
the exact entries and norm at most `norm b`. The proof sums shifted
bounded diagonal operators absolutely in operator norm. Bounded action
of the infinite matrix is a conclusion.

`ConvolutionMatrixAnalytic.lean` constructs a bounded linear map from
the ℓ-infinity space of encoded matrix symbols to bounded operators on
ℓ². A fixed integer-pair equivalence encodes the two matrix indices.
Division by a nonvanishing convolution majorant makes the actual symbol
uniformly bounded. The existing bounded-coordinate analyticity theorem
then gives Banach analyticity of that symbol. Applying the constructed
bounded linear assembly map gives **operator-norm analyticity**, rather
than inferring it from scalar entries alone.

`ClassicalPeriodOperator.lean` applies this construction to the actual
matrix. Positive inputs are numerator coefficients; positive outputs are
contour periods. The complementary nonpositive coordinates have an
auxiliary identity block and mixed blocks are zero. This is an operator
device, not a physical signed-coordinate identification. The resulting T
has the exact actual positive entries, a common norm bound and `T(0)=Id`.

## Actual analytic inverse

`ClassicalPeriodInverse.lean` uses operator-norm continuity at zero to
construct a neighborhood on which `norm(T-Id)<1`. The Neumann criterion
proves invertibility there. Analytic Banach-algebra inversion supplies R,
both identities `T.comp R=Id` and `R.comp T=Id`, and `R(0)=Id`.
Continuity permits a further common neighborhood with `norm R<=2`.
Both T and R are analytic there. The theorem retains the actual matrix
entries and the full `ClassicalAllContourPeriodData` package with the
same N and neighborhood. No inverse or invertibility hypothesis is assumed.

## Validation and remaining obligations

The focused strict checker and full transitive axiom auditor select the
same 70 modules, including all seven new proof modules and six newly
selected existing dependencies. Pinned Lean 4.33.1/mathlib v4.33.1,
`autoImplicit=false`, `warningAsError=true`, default heartbeats and the
three-standard-axiom restriction are unchanged. Final audit counts and
all checked source hashes are in `VALIDATION.md` and `source.json`.

The next step is to construct the entire normalized functions from the
inverse columns. This requires a joint ℓ²-valued entire numerator basis,
convergence of its coefficient pairings, interchange with every contour
integral, and positive-subspace compatibility. Operator inversion alone
does not establish the literal source normalized entire family or its
canonical zero/product representation.

Global and rough spectral compatibility, sharp moment sums, physical
Hamiltonian-frequency identities, action descent, weighted asymptotics,
compact derivatives and actual Birkhoff/PDE flow identification also
remain essential. No main theorem is marked verified by this milestone.
