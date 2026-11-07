import NLS.KdV.PhysicalDiagonalFrequencySymbol
import NLS.KdV.PhysicalOffDiagonalLocalAnalytic
import NLS.KdV.HillPhysicalMeanZeroRoughDensity
import NLS.KdV.HillHminusPhysicalArnoldActions
import NLS.Articles.KdVConvexity.GlobalSpectralActions

/-! The original physical diagonal factorization extends to every real
mean-zero rough potential in the germ, with the actual global intrinsic
Arnold map. The density uses the original raw Fourier coefficients. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
namespace NLS.KdV.PhysicalMiuraFrequencyChart

theorem exists_local_diagonal_symbol_rough_Arnold
    (B : PhysicalMiuraFrequencyChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      B.psi.family.originalDomain B.psi.family.domain B.psi.family.roots)
    (Ω : Set PeriodOneHminusOne) (hΩ : {q | IsRealPeriodOneHminusOne q}⊆Ω)
    (I : PeriodOneHminusOne → BaseActionSpace) (hI : AnalyticOnNhd ℂ I Ω)
    (hΩopen : IsOpen Ω)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n)=hillHminusRealGapContourMoment q hr n 0)
    (q0 : PeriodOneHminusOne) (hq0 : q0∈B.domain) (hr0 : IsRealPeriodOneHminusOne q0) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q0∈U ∧ U⊆B.domain∩Ω ∧
      ∃ M : ℝ, 0≤M ∧ ∃ S : PeriodOneHminusOne → Coeff 2,
        AnalyticOnNhd ℂ S U ∧ (∀ q∈U, ‖S q‖≤M) ∧
        (∀ q∈U, ∀ j : ℤ, j≤0 → S q j=0) ∧
        ∀ q∈U, IsRealPeriodOneHminusOne q → q.val 0=0 → ∀ n : ℕ+,
          B.correction n q+6*(I q).val (actionIndexEquiv.symm n)=
            B.offDiagonalCorrection n q+6*(I q).val (actionIndexEquiv.symm n)*S q (n : ℤ) := by
  obtain ⟨T,hT,hqT,hTB,M,hM,S,hSa,hSb,hSz,hphys⟩ := B.exists_local_diagonal_frequency_symbol H q0 hq0 hr0
  obtain ⟨V,hV,hqV,_hVB,hVa⟩ := B.exists_local_analytic_offDiagonal q0 hq0 hr0
  let U := (T∩V)∩Ω
  have hU : IsOpen U := (hT.inter hV).inter hΩopen
  have hi (n : ℕ+) : AnalyticOnNhd ℂ (fun q => (I q).val (actionIndexEquiv.symm n)) Ω := fun q hq =>
    ((WeightedCoeff.evalCLM baseActionWeight 1 (actionIndexEquiv.symm n)).analyticAt _).comp (hI q hq)
  refine ⟨U,hU,⟨⟨hqT,hqV⟩,hΩ hr0⟩,fun q hq => ⟨hTB hq.1.1,hq.2⟩,M,hM,S,
    hSa.mono (fun q hq => hq.1.1),fun q hq => hSb q hq.1.1,
    fun q hq j hj => hSz q hq.1.1 j hj,?_⟩
  intro q hq hr hmean n
  have hiU : AnalyticOnNhd ℂ (fun q => (I q).val (actionIndexEquiv.symm n)) U :=
    (hi n).mono (fun q hq => hq.2)
  have hsU : AnalyticOnNhd ℂ (fun q => S q (n : ℤ)) U := fun q hq =>
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)).analyticAt _).comp (hSa q hq.1.1)
  have hf : ContinuousOn (fun q => B.correction n q+6*(I q).val (actionIndexEquiv.symm n)) U :=
    (((B.analytic_correction n).mono (fun q hq => hTB hq.1.1)).add
      (analyticOnNhd_const.mul hiU)).continuousOn
  have hg : ContinuousOn (fun q => B.offDiagonalCorrection n q+
      6*(I q).val (actionIndexEquiv.symm n)*S q (n : ℤ)) U :=
    (((hVa n).mono (fun q hq => hq.1.2)).add ((analyticOnNhd_const.mul hiU).mul hsU)).continuousOn
  apply eq_on_real_meanZero_of_original_physical hU _ _ hf hg ?_ q hq hr hmean
  intro p _hpmean hp
  have hIp := (hrec (hillOriginalHminusSource p.val)
    (hillOriginalHminusSource_real p.val p.property.2) n).trans
      (hillHminusRealGapContourMoment_original_source p n 0)
  simpa only [hIp] using hphys p hp.1.1 n

end NLS.KdV.PhysicalMiuraFrequencyChart
