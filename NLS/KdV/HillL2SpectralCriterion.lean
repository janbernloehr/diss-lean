import NLS.KdV.HillFirstOrderReduction
import NLS.KdV.HillAnalytic
import NLS.KdV.HillPeriodOnePotential
import NLS.ZakharovShabat.L2Discriminant

/-! # The actual L2 monodromy trace detects Hill eigenvalues

The explicit constant-upper operator comparison identifies the actual
periodic H2 Hill eigen-equation with the already proved physical L2
monodromy criterion. The trace here still uses the frequency `z`, with
Hill energy `z^2`. Descent to an entire energy discriminant, and equality
of the relevant algebraic multiplicities, are not asserted here.
-/

noncomputable section
open Set
open NLS.ZakharovShabat
namespace NLS.KdV

theorem hillFirstOrderPotential_mem_even (q : Coeff 2) (hq : q ∈ Coeff.paritySubspace 0) :
    hillFirstOrderPotential q ∈ pairParitySubspace 0 := by
  refine ⟨?_, (Coeff.paritySubspace 0).neg_mem hq⟩
  change (lp.single 2 0 (-1) : Coeff 2) ∈ Coeff.paritySubspace 0
  apply (Coeff.mem_paritySubspace 0 _).mpr
  intro k hk
  have hk0 : k ≠ 0 := by intro h; simp only [h, Int.zero_emod] at hk; exact hk rfl
  simp [lp.single_apply, hk0]

/-- The trace of the actual L2 unit-interval monodromy for `(-1,-q)`. -/
def hillL2FrequencyDiscriminant (q : Coeff 2) (z : ℂ) : ℂ :=
  l2Discriminant (physicalRestrictionL2 (hillFirstOrderPotential q)) z

/-- The physical trace is jointly analytic in the L2 potential and frequency. -/
theorem analyticOnNhd_hillL2FrequencyDiscriminant_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × Coeff 2 => hillL2FrequencyDiscriminant p.2 p.1) univ := by
  intro p _
  have hphi : AnalyticAt ℂ (fun r : ℂ × Coeff 2 => hillFirstOrderPotential r.2) p :=
    analyticAt_const.prod analyticAt_snd.neg
  have hu := (physicalRestrictionL2CLM.analyticAt (hillFirstOrderPotential p.2)).comp
    (f := fun r : ℂ × Coeff 2 => hillFirstOrderPotential r.2) hphi
  exact (analyticOnNhd_l2Discriminant_joint
    (p.1,physicalRestrictionL2 (hillFirstOrderPotential p.2)) (mem_univ _)).comp
      (f := fun r : ℂ × Coeff 2 => (r.1,physicalRestrictionL2 (hillFirstOrderPotential r.2)))
      (analyticAt_fst.prod hu)

/-- Exact characteristic equivalence on the actual H2 Hill domain for
every even-supported complex L2 potential, without a continuity assumption. -/
theorem hill_eigenvector_iff_l2FrequencyDiscriminant
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0) (z : ℂ) :
    (∃ f : HillSobolevDomain, f ≠ 0 ∧
      hillOperator (SpectralWeight.one.toCoeff q) f = z^2 • hillDomainToL2 f) ↔
      hillL2FrequencyDiscriminant (SpectralWeight.one.toCoeff q) z ^ 2 = 4 := by
  exact (hill_eigenvector_iff_firstOrder_spectrum q z).trans
    (l2Discriminant_sq_eq_four_iff _ (hillFirstOrderPotential_mem_even _ hq) z).symm

/-- The high-strip determinant and the actual rough physical monodromy
have exactly the same spectral zero condition at the squared energy. -/
theorem hillReduced_zero_iff_l2FrequencyDiscriminant
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z^2 ∈ reducedHillStrip n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    hillReducedDeterminant SpectralWeight.one n (q,z^2) = 0 ↔
      hillL2FrequencyDiscriminant (SpectralWeight.one.toCoeff q) z ^ 2 = 4 := by
  have he := hillReducedDeterminant_eq SpectralWeight.one n hn (q,z^2) hz hcut
  exact (show hillReducedDeterminant SpectralWeight.one n (q,z^2) = 0 ↔
      (hillReducedOperator SpectralWeight.one q n hn (z^2) hz hcut).toLinearMap.det = 0 by rw [he]).trans
    ((hillReduced_det_eq_zero_iff_domainEigenvector q n hn (z^2) hz hcut).trans
      (hill_eigenvector_iff_l2FrequencyDiscriminant q hq z))

/-- The rough monodromy spectral condition depends only on the Hill energy,
even before analytic descent of the trace itself has been constructed. -/
theorem hillL2FrequencyDiscriminant_spectral_condition_of_sq_eq
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0) (z w : ℂ) (he : z^2 = w^2) :
    hillL2FrequencyDiscriminant (SpectralWeight.one.toCoeff q) z ^ 2 = 4 ↔
      hillL2FrequencyDiscriminant (SpectralWeight.one.toCoeff q) w ^ 2 = 4 := by
  rw [← hill_eigenvector_iff_l2FrequencyDiscriminant q hq z,
    ← hill_eigenvector_iff_l2FrequencyDiscriminant q hq w, he]

/-- The characteristic equivalence applied to the checked, norm-preserving
embedding of the source's original period-one L2 coefficients. -/
theorem hillPeriodOne_eigenvector_iff_l2FrequencyDiscriminant
    (q : WeightedCoeff SpectralWeight.one.doubleIndex.toWeight 2) (z : ℂ) :
    (∃ f : HillSobolevDomain, f ≠ 0 ∧
      hillOperator (SpectralWeight.one.toCoeff (hillPeriodOnePotential SpectralWeight.one q)) f =
        z^2 • hillDomainToL2 f) ↔
      hillL2FrequencyDiscriminant
        (SpectralWeight.one.toCoeff (hillPeriodOnePotential SpectralWeight.one q)) z ^ 2 = 4 := by
  apply hill_eigenvector_iff_l2FrequencyDiscriminant
  rw [toCoeff_hillPeriodOnePotential]
  exact Coeff.periodDouble_mem _

end NLS.KdV
