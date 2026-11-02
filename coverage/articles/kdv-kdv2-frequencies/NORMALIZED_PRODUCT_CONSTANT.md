# Constant normalized quotient and complete actual zero set

This step advances the normalized functions used in source (52)–(53),
PDF page 21. **Every article main theorem remains open.** The source
neighborhood is in C([0,1], C) with the sup norm, near zero. For each
omitted positive mode n the smaller neighborhood U_n can depend on n.

## Actual result

Let a_m = (R(q)e_n)_m, with R the constructed inverse of the actual
period operator. Its compatible twice-weighted inverse Q gives an actual
Hilbert vector v = n^2 Q(q)e_n with v_m = m^2 a_m at every positive m.
The positive residues c_m = m*a_m form a genuine analytic l1 sequence.
The leading scalar is defined, rather than postulated, by

    L_n(q) = (1/n) * sum_(m>=1) m*(R(q)e_n)_m.

This scalar is analytic on the common base neighborhood V, equals one
at the free potential, and is nonzero on the constructed U_n.

Let sigma_k^n be the previously constructed analytic actual normalized
zeros, with the critical placeholder sigma_n^n = mu_n at the omitted
mode, and let B_n^sigma be the literal omitted energy product with
prefactor 2/(n*pi). Then on U_n, for every complex energy lambda,

    Psi_n(lambda,q) = L_n(q) * B_n^sigma(lambda,q).

The filled entire quotient is exactly L_n(q), independently of energy.
The cutoffs L_n(q)*B_(n,M)^sigma converge locally uniformly on the whole
energy plane to the actual Psi_n. Its zeros are **precisely** the
sigma_k^n with k!=n, and every zero is simple. The original literal
normalization periods remain delta_nk on V. The analytic zero branch,
free energies, energy analyticity and auxiliary zero coordinates are
retained on each U_n.

`exists_classicalHill_local_complete_normalized_products` constructs
N,V,R,Q before choosing n and its U_n and branch. Its
`ClassicalNormalizedProductData` records the nonzero scalar, constant
quotient, exact product identity, locally uniform actual Psi_n products,
complete zero set and simplicity of every actual zero. The scalar's
analyticity and exact free value are also part of the existence theorem.

This does **not** assert L_n(q)=1 at nonzero q. Consequently source (52)
with its exact Psi_n prefactor, as stated on the full source W, remains
open even though local completeness and a nonzero scalar product identity
are now proved. The literal candidate product prefactor and the actual
Psi_n prefactor must not be conflated.

## Exterior argument

For fixed q,n and a fixed complex sigma, the actual two-weight vector
constructs an odd l2 frequency direction with positive coordinates

    h_m = -c_m*(mu_m-sigma)/(2*xi_m),  xi_m = sqrt(mu_m).

Indeed h_m = d_m*v_m, where

    d_m = -(mu_m-sigma)/(2*m*xi_m)
    |d_m| <= (4*pi^2+|sigma|)/pi.

The proof uses the actual critical quadratic upper bound and positive
frequency lower bound, rather than an assumed weighted coefficient class.
Reflection gives the negative coordinates and the zero coordinate is zero.
The literal, absolutely convergent signed resolvent pairs to

    sum_(j in Z) h_j/(xi_j-z)
      = sum_(m>=1) c_m*(mu_m-sigma)/(z^2-mu_m).

The existing arbitrary-complex l2 root-resolvent exterior estimate makes
this uniformly small at large frequency parameters separated from the
free lattice. Thus

    (z^2-sigma)*sum_m c_m/(z^2-mu_m) -> sum_m c_m.

The exact quotient/resolvent identity combines this with the ratio of
the actual signed critical product to the signed selected-zero product.
Both products have the same free sine normalization, so their ratio tends
to one. The entire energy quotient therefore tends to L_n on the separated
exterior. Its square pullback minus L_n is an entire frequency function;
uniform decay on expanding half-integer circles forces it to vanish.

At one retained selected root the actual Psi_n derivative and the
candidate product derivative are nonzero, so their derivative ratio
L_n cannot vanish. The entire factorization then excludes any additional
Psi_n zeros. No real-type or real-gap hypothesis is used for Hill(-1,-q).

## Lean map

| File | Checked result |
| --- | --- |
| `NLS/SequenceSpaces/PositiveOddMultiplier.lean` | A bounded positive symbol and an actual l^p vector construct an actual odd l^p extension. |
| `NLS/ZakharovShabat/PairedEnergyResolventExterior.lean` | Exact pairing of absolutely convergent frequency resolvents, energy avoidance and uniform smallness of the energy remainder. |
| `NLS/KdV/ClassicalNormalizedResolventExterior.lean` | Actual analytic leading scalar and free value; critical symbol bounds; constructed actual Hilbert direction; actual energy resolvent asymptotic. |
| `NLS/ZakharovShabat/SingleSpectralProductRatioExterior.lean` | Added reusable separated-path limit one for the ratio of two arbitrary complex l^p products. |
| `NLS/KdV/ClassicalNormalizedProductAsymptotics.lean` | Exact ordinary quotient identity on the zero-free exterior and its actual residue-sum limit. |
| `NLS/KdV/ClassicalNormalizedProductConstant.lean` | Constant quotient, nonzero analytic scalar product, complete actual simple zero set, whole-plane locally uniform actual Psi_n cutoffs and constructed local families with every period. |

The reused `SourcePsiRootResolventExterior`, `EntireCircleDecay` and
`CentralCircleThresholds` are selected for direct strict recompilation.
The complete transitive audit includes their imported NLS dependencies.

## Remaining obligations

Prove L_n(q)=1 at nonzero potentials, establish one common neighborhood
for every omitted n, real gap placement and sharp root estimates (54),
and extend to the source's rough/global domains. Sharp moments and the
physical Hamiltonian-frequency/Birkhoff flow identities remain open,
as do all main theorem rows. Analyticity in q and L_n(0)=1 alone do not
prove the required normalization. The current constant-quotient theorem
must not be reported as the exact source-normalized (52).

Subsequent necessary moment progress is recorded in
`NORMALIZED_ODD_MOMENTS.md`: the literal actual normalized moments now
have all-mode analyticity, exact zeroth periods and every odd cancellation
on one common near-zero complex continuous-potential neighborhood.
This uses the original inverse R and does not assume the open exact
canonical leading-scalar identity at nonzero potentials.
