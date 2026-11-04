# Actual rough normalized numerators and corrections are spectral invariants

This step supplies a necessary ingredient of the action-descent argument
following source Theorem 3.4 (73) and Remark 3.5, PDF pages 31–32. It proves
invariance under equality of the intrinsic Hill discriminant. It does not
identify action fibers with isospectral sets or identify the correction with
the Hamiltonian frequency (69).

## Entire actual numerators at every real rough base

`HillHminusOneMiuraSpectralInvariance.lean` proves that equality of the actual
rough Hill discriminants, at two inputs of one fixed real-type Miura chart,
gives equality of their shifted NLS discriminants. The established equivalence
with periodic spectral data includes algebraic multiplicities. Canonical real
psi-root uniqueness then identifies the actual normalized root vectors.
Consequently the entire actual Miura energy numerators agree at every energy
and every signed index. The canonical energy-root products agree as literal
functions as well, with their normalization signs retained.

`exists_hillHminus_real_spectral_miura_family` constructs such an actual jointly
complex-analytic normalized family around every physically real rough base.
Its real spectral-invariance statement covers the whole real slice of its fixed
chart domain, including closed gaps. This is not a comparison between charts
with different energy translations or a global action-coordinate construction.

The canonical dissertation modules `SourceIsospectralSet.lean` and
`SourcePsiGapRootIsospectral.lean` are reused unchanged and explicitly compiled
and selected for audit. The former was already a transitive dependency of
older selected modules; its explicit selection is placed before those consumers.

## Root signs and logarithmic phases on original contours

`HillHminusOneIsospectralSheets.lean` proves one imaginary strip of half-width
`pi/2` for every shifted continued primitive on all original positive frequency
circles. The high tail uses the existing uniform strip theorem. Compact source
tubes for the finite head use the strict free bound `pi/4`, enlarged to
`3*pi/8`. A finite intersection gives one common rough neighborhood before
any contour index.

On a single ball around zero, equal real-input discriminants give equal
continued roots on every original contour. The proof compares both roots with
the actual canonical root of one real-preserving chart along real radial source
paths. Equal traces and roots give equal exponentials of the primitives; the
common strip fixes their integer logarithm ambiguity. Thus the primitives
agree as well. Equality of squares alone is never used to infer a sign or phase.
The ball precedes both inputs, every contour index and every point on its circle.

## One analytic series family with spectral invariance

`HillHminusOneSpectralMiuraFrequencySeries.lean` constructs a single actual
real-preserving chart, positive real energy translation, normalized NLS data and
complex rough-input ball. On that same ball, before all indices and orders:

- Actual numerators are jointly analytic, and all literal moments are analytic.
- Zeroth periods are exact and all odd moments vanish.
- Every second-moment series converges absolutely and locally uniformly.
- Every actual second-moment correction is analytic.
- For two physically real inputs with equal intrinsic discriminants, every
  actual moment of every order and every correction agree.

The family is chosen from actual original-period data so its real-preserving
property remains explicit. Genuine Hilbert representation and inverse-column
uniqueness identify this same family with the constructed weighted family on
the real slice; the physical real-form identity extends the equality to the
whole complex ball. The already proved weighted summation result transfers to
that same family. Its real spectral invariance then follows by literal integrand
congruence using the numerator, root and primitive equalities. No unrelated
existential witnesses are combined, and no convergence claim is made from a
totalized sum identity alone.

All main theorem rows remain open. Still needed are the actual physical
Hamiltonian-frequency/Poisson identities, action realization and descent,
global source domains, canonical leading normalization, sharp weighted
remainders and compact derivatives, KdV2 constructions and Birkhoff/PDE transfer.

Validation reuses 431 unchanged previously checked Lean sources, strictly
compiles two unchanged canonical modules and three new modules, and runs a
fresh combined transitive axiom audit of all 436 selected modules. This is
incremental validation, not a repeated full build. Ordered checker/audit
selections respect transitive dependencies; compilation evidence is the prior
checks plus these five incremental checks. Source hashes, private fresh outputs,
seven unchanged provenance records and unchanged clean canonical main are
verified before publication.
