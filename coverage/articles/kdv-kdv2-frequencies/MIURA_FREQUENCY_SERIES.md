# Actual Miura normalized moments and analytic correction series

`HillHminusOneMiuraFrequencySeries.lean` defines the literal original-circle
moments using the actual Miura energy numerator, the independently constructed
rough Hill frequency primitive and its continued root, including the square
Jacobian `2*z`. The definition contains no auxiliary inverse-column family.
The second-moment correction candidate is exactly
`-12 * ∑' k : ℕ+, k * hillHminusMiuraMoment C s n k 2 q`.

The three comparison lemmas identify every moment order, signed-lattice
second-moment term and the full correction with the constructed weighted
normalized family, whenever its entire numerator agrees with the actual Miura
numerator. These are equalities of the literal integrals and sums, obtained
from integrand congruence; they do not assume prescribed moment values or a
Hamiltonian-frequency identity.

`exists_hillHminus_analytic_miura_frequency_series` constructs an actual chart,
a positive radius, actual normalized NLS data and a common complex rough-input
ball around zero before every numerator index, contour index and moment order.
It retains chart-domain inclusion, source membership and joint complex
analyticity of all actual energy numerators. On that same ball it proves:

- Analyticity of every literal actual moment.
- Exact zeroth periods with factor `2*pi` and all positive indices.
- Vanishing of every odd moment, with no finite-head or collapsed-gap exclusion.
- Absolute convergence of each positive second-moment series.
- Analyticity of each actual second-moment correction candidate.
- Locally uniform convergence of the ordinary positive partial sums, represented
  by the signed interval `Finset.Icc 1 L` with zero nonpositive terms.

The construction starts with the proved weighted moment/series family and
uses full complex-source numerator identification for that very family. A
single ball is selected inside its series domain and the identification ball.
Moment identities transfer analyticity, exact periods, odd cancellation and
summability; congruence transfers the locally uniform partial-sum limit.
No additional convergence assumption or unrelated existential family is used.

This supplies the actual-numerator local spectral series corresponding to
source Theorem 3.4, formula (73), PDF page 31, and the local moment properties
from Lemma 3.1, PDF pages 23–26. It is not the full source theorem: the physical
Hamiltonian-frequency identity (69), action descent and the global neighborhood
of all real rough inputs remain open. No identification of the separately
mapped NLS primitive with the Hill primitive is asserted here. Canonical
leading normalization, sharp weighted remainders and compact derivatives,
KdV2 frequency construction and Birkhoff/PDE identification also remain open.
Every main inventory row remains open.

Validation reuses the strict checks of 430 unchanged selected sources,
strictly compiles this one new module and runs a fresh combined transitive
axiom audit of all 431 selected modules. This is incremental validation, not
a repeated full build. Checker/audit selections, all source hashes, private
fresh outputs, seven provenance records and unchanged canonical main are
verified before publication.
