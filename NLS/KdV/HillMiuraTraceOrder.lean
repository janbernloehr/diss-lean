import NLS.KdV.HminusOneMiuraTrace
import NLS.KdV.HillHminusOneSourcePrimitive
import NLS.ZakharovShabat.FiniteDiscriminant

noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

/-- The actual entire Miura energy trace has its exact frequency pullback. -/
theorem hillMiuraL2Discriminant_sq (u : Coeff 2) (z : ℂ) :
    hillMiuraL2Discriminant u (z^2)=hillMiuraFrequencyTrace u z := by
  rcases eq_or_eq_neg_of_sq_eq_sq (Complex.sqrt (z^2)) z (complex_sqrt_sq (z^2)) with h | h
  · rw [hillMiuraL2Discriminant,h]
  · rw [hillMiuraL2Discriminant,h,hillMiuraFrequencyTrace_even]

/-- Literal shifted Miura transport compares the unchanged scalar trace
with the actual fixed Dirac trace, not only their zero sets. -/
theorem hillHminusDiscriminant_shifted_miura_square (q : PeriodOneHminusOne)
    (u : Coeff 2) (c z : ℂ)
    (himage : periodOneMiura u=q+periodOneL2Inclusion (lp.single 2 0 c)) :
    hillHminusDiscriminant q (z^2-c)=
      canonicalDiscriminant (by norm_num) (periodOnePotential (hillMiuraDiagonal u)) z := by
  rw [hillHminusDiscriminant_eq_miura_of_shifted_image q u c (z^2-c) himage,
    sub_add_cancel,hillMiuraL2Discriminant_sq]
  rfl

/-- Every nonzero frequency preserves the FULL analytic scalar Hill order
and the original Dirac algebraic multiplicity under literal energy translation.
No singular-operator multiplicity hypothesis or source reality is required. -/
theorem analyticOrderNatAt_hillHminusRadicand_shifted_miura
    (q : PeriodOneHminusOne) (u : Coeff 2) (c z : ℂ) (hz : z≠0)
    (himage : periodOneMiura u=q+periodOneL2Inclusion (lp.single 2 0 c)) :
    analyticOrderNatAt (hillHminusRadicand q) (z^2-c)=
      periodicAlgebraicMultiplicity (by norm_num) (periodOnePotential (hillMiuraDiagonal u)) z := by
  have hg : AnalyticAt ℂ (fun w : ℂ => w^2-c) z := (analyticAt_id.pow 2).sub analyticAt_const
  have hd : HasDerivAt (fun w : ℂ => w^2-c) (2*z) z := by
    simpa using! ((hasDerivAt_id z).pow 2).sub_const c
  have hdn : deriv (fun w : ℂ => w^2-c) z≠0 := by
    rw [hd.deriv]
    exact mul_ne_zero (by norm_num) hz
  have ho := congrArg ENat.toNat (analyticOrderAt_comp_of_deriv_ne_zero
    (f := hillHminusRadicand q) hg hdn)
  change analyticOrderNatAt (fun w : ℂ => hillHminusRadicand q (w^2-c)) z=
    analyticOrderNatAt (hillHminusRadicand q) (z^2-c) at ho
  rw [←ho]
  have he : (fun w : ℂ => hillHminusRadicand q (w^2-c))=
      (fun w : ℂ => (canonicalDiscriminant (by norm_num)
        (periodOnePotential (hillMiuraDiagonal u)) w)^2-4) := by
    funext w
    rw [hillHminusRadicand,hillHminusDiscriminant_shifted_miura_square q u c w himage]
  rw [he]
  have hm := congrArg ENat.toNat (analyticOrderAt_canonicalDiscriminant_sq_sub_four
    (by norm_num) (by norm_num) (periodOnePotential (hillMiuraDiagonal u)) (periodOnePotential_mem _) z)
  simpa only [analyticOrderNatAt,ENat.toNat_natCast] using hm

end NLS.KdV
