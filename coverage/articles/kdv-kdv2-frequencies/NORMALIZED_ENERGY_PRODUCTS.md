# Actual selected energy products and entire normalized quotients

This step concerns source (52)–(53), PDF page 21. **No article main
statement is closed.** The potential space is the complex Banach space
C([0,1], C) with the sup norm, used for period-one Hill potentials,
locally near zero.
For each omitted positive n the source subneighborhood may depend on n.

## Constructed products

Write xi_k = sqrt(mu_k), where mu_k is the selected critical energy
(source lambda-dot_k, not a Dirichlet eigenvalue), and let x be the actual
analytic Hilbert displacement branch constructed previously. Its auxiliary
nonpositive and omitted-n coordinates vanish. Set sigma_k = (xi_k+x_k)^2.
The signed frequencies eta_0=0 and eta_±k=±(xi_k+x_k) have genuine l2
free-lattice displacement and are injective. At ±n the critical frequency
is a placeholder, to be removed rather than claimed as a Psi_n root.

The literal positive energy cutoffs

    G_M(lambda) = - product_(1<=m<=M) (sigma_m-lambda)/(m*pi)^2

converge locally uniformly on the **whole** energy plane to an entire G.
The exact frequency identity is E_eta(z) = 2*z*G(z^2). The construction
fills the zero frequency by a divided difference and descends the even
quotient through squaring; it does not select an analytic square root at
energy zero. G has exactly the sigma_m as zeros, all simple, and G(0)!=0.

The omitted cutoffs

    B^sigma_(n,M)(lambda) = 2/(n*pi)
      * product_(1<=m<=M, m!=n) (sigma_m-lambda)/(m*pi)^2

converge locally uniformly on the whole energy plane to an entire B^sigma_n.
The prefactor is literally 2/(n*pi), with no unspecified multiplier in
this **candidate** product. The filled identity is

    (lambda-sigma_n)*B^sigma_n(lambda) = 2*n*pi*G(lambda).

Its zeros are precisely sigma_k for k!=n and are simple. In particular,
the filled value at sigma_n is nonzero; no point is excluded from the
convergence statements. At zero displacement this product is the already
verified actual critical basis B_n.

## Factorization of the actual normalized function

Every zero of B^sigma_n is an actual simple zero of the previously
constructed normalized entire Psi_n, defined using the actual inverse R.
Define Q_n = filledSimpleQuotient(Psi_n,B^sigma_n), using the derivative
ratio at denominator zeros. The following are proved:

- Q_n is entire on the energy plane.
- Psi_n(lambda) = Q_n(lambda)*B^sigma_n(lambda) at every energy.
- Q_n(sigma_k) != 0 for every k!=n.
- Q_n is exactly one at the free potential, on the whole energy plane,
  including the free zeros where the quotient uses derivative ratios.

`exists_classicalHill_local_normalized_product_factorizations` constructs
N,V,R first, retains every literal normalization period on V, and then
constructs for each n one analytic sequence branch on an open U_n containing
zero. On U_n all the product convergence, exact simple product zero-set,
entire quotient, global energy factor identity and nonzero selected-root
quotient properties hold simultaneously. The stronger intermediate
`exists_actual_normalized_product_quotient_family` also retains the exact
free energies and energy analyticity and actual Psi_n simplicity.

This is an actual entire factorization, **not yet** the equality Psi_n =
B^sigma_n at nonzero potentials. An entire quotient can have additional
zeros elsewhere. Neither completeness of the Psi_n zero set nor the exact
source-normalized Psi_n product is inferred from the selected roots.

## Lean declarations

| File / declaration | Verified result |
| --- | --- |
| `NLS/ComplexAnalysis/OddSquareDescent.lean` | Filled division of any odd entire function by twice its argument, entire descent through squaring, and the exact factor identity including zero. |
| `NLS/ZakharovShabat/PairedEnergyProduct.lean` | Exact pairing of literal signed cutoffs, oddness of the signed limit, entire energy product and locally uniform positive energy cutoff convergence. |
| `NLS/ZakharovShabat/PairedEnergyZeros.lean` | Nonzero value at zero, exact positive energy zero set, injective squared positive labels and simple energy zeros. |
| `NLS/ZakharovShabat/OmittedPairedEnergyProduct.lean` | Exact literal 2/(n*pi) omitted products, filled factor identity, locally uniform whole-plane convergence, exact omitted zero set and simplicity. |
| `NLS/KdV/ClassicalCandidateEnergyProducts.lean` | Instantiation with the actual selected Hill root sequence; literal sigma_m energy cutoffs and zero-displacement identification with the actual filled critical basis. |
| `NLS/ComplexAnalysis/FilledSimpleQuotient.lean` | Reused removable quotient, with added exact multiplication identity and nonzero quotient at common simple zeros. |
| `NLS/KdV/ClassicalNormalizedProductQuotient.lean` | Entire quotient for the literal normalized Psi_n, factorization, nonzero selected-root values, exact free value one and constructed local families retaining every period. |

The generic paired-product theorems require arbitrary complex l^p displaced
roots (finite p>=1, p>1 for simplicity), pairing and injectivity. They do
not require a real-type potential or real spectral gaps. In particular,
no ZS RealType hypothesis is applied to the Hill pair (-1,-q).

## Remaining source obligations

Prove that Q_n is constant, determine its exact value at nonzero
potentials, and thereby identify the normalized product and complete zero
set. A possible leading scalar from the actual l1 critical residues is
(1/n)*sum_m m*(R e_n)_m; its required normalization must be proved rather
than assumed. One common source neighborhood for all omitted n, real gap
placement and sharp root estimates (54), rough/global source compatibility,
sharp moments, physical Hamiltonian-frequency identities and all main
frequency/flow theorems remain open. All main inventory rows stay open.

Strict full validation and audit counts are recorded in `VALIDATION.md`
and `source.json`; no new axioms, placeholders, heartbeat increases or
linter exceptions are used.
