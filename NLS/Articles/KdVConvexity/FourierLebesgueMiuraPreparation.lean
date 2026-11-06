import NLS.Articles.KdVConvexity.MainTheorem11
import NLS.KdV.HillHminusFourierLebesgueMiuraCharts

/-! # Actual Fourier-Lebesgue Miura preparation for Theorem 1.2

`HillHminusMiuraChart.fourierLebesgue_iff` gives the exact one-derivative
regularity shift for every actual chart, every s>=-1/2 and every finite
p>=2, including the endpoint and infinite support.

`exists_hillHminus_real_Miura_all_fourierLebesgue_chart` chooses ONE chart
before all stronger norms. Its fixed lift has complex analytic native
restrictions, preserving the real form, zero-free shift and original
physical Hill labels. Its Sobolev clause covers p=2 and its other clause
covers every finite real p>2.

Theorem 1.2 additionally requires the exact Fourier-Lebesgue criterion
for the SAME physical Birkhoff map, analytic inverse, restricted derivative
inverses and surjectivity. Those assertions are not proved by this module.
-/
