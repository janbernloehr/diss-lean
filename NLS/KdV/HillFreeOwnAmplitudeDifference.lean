import NLS.KdV.HillFreeScaledDirichletSheetDifferential
import NLS.KdV.HillOriginalOwnFactorConjugation
import NLS.KdV.HillHminusOriginalAllGapConjugateGerms
import NLS.ComplexAnalysis.ProductZeroDifferential

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ComplexConjugate
namespace NLS.KdV

/-- Literal conjugation of the original own amplitude reverses just its
scaled signed sheet. All closed and open gaps are included. -/
theorem hillOwnCartesianAmplitude_conj_eq_sub_sheet (q : RealPeriodOneHillPotential) (n : ℕ+) :
    conj (hillOwnCartesianAmplitude q.val q.property.1 q.property.2 n n.pos) =
      hillOwnCartesianAmplitude q.val q.property.1 q.property.2 n n.pos -
        2*hillActionGapPrefactor q.val q.property.1 q.property.2 n *
          (hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
            (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos)/
            hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 n
              (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos)) := by
  rw [hillOwnCartesianAmplitude_conj,hillOwnCartesianAmplitude,hillOwnGapFactor]
  ring

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- Construct the ACTUAL original own amplitude and its conjugate through
every free collapsed gap, with the full antisymmetric H-minus-one differential. -/
theorem exists_hillFree_ownAmplitude_pair_difference (n : ℕ+) :
    ∃ A C : PeriodOneHminusOne → ℂ,
      AnalyticAt ℂ A 0 ∧ AnalyticAt ℂ C 0 ∧ A 0 = 0 ∧ C 0 = 0 ∧
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
        A (hillOriginalHminusSource p.val) = hillOwnCartesianAmplitude p.val p.property.1 p.property.2 n n.pos ∧
        C (hillOriginalHminusSource p.val) = conj (hillOwnCartesianAmplitude p.val p.property.1 p.property.2 n n.pos)) ∧
      ∀ h : PeriodOneHminusOne,
        (fderiv ℂ A 0) h-(fderiv ℂ C 0) h =
          hillActionGapPrefactor 0 h0q h0r n*(h.val n-h.val (-(n : ℤ))) := by
  let Q : RealPeriodOneHillPotential := ⟨0,h0q,h0r⟩
  obtain ⟨A,hA,hAM⟩ := exists_hillOriginal_ownCartesianAmplitude_hminus_physical_germ Q n
  have hAA : AnalyticAt ℂ A 0 := by simpa only [Q,map_zero] using hA
  have hgap : hillRealGapHalfLength 0 h0q h0r n = 0 := by
    obtain ⟨hl,hu⟩ := hillFreeGapEndpoints h0q h0r n n.pos
    rw [hillRealGapHalfLength,hl,hu,sub_self,zero_div]
  have hA0 : A 0 = 0 := by
    have hh := hAM.self_of_nhds
    simpa only [Q,map_zero,hillOwnCartesianAmplitude_closed 0 h0q h0r n n.pos hgap] using hh
  obtain ⟨T,hT,hT0,hTM,hTD⟩ := exists_hillFree_scaledDirichletSheet_hminus_fourier_germ h0q h0r n
  let P := hillHminusIntrinsicActionGapPrefactor 0 h0q h0r n
  have hP : AnalyticAt ℂ P 0 := by
    simpa only [map_zero] using analyticAt_hillHminusIntrinsicActionGapPrefactor 0 h0q h0r n n.pos
  have hPM := hillHminusIntrinsicActionGapPrefactor_eventually_eq_physical 0 h0q h0r n n.pos
  have hP0 : P 0 = hillActionGapPrefactor 0 h0q h0r n := by
    simpa only [P,map_zero] using hPM.self_of_nhds
  let D : PeriodOneHminusOne → ℂ := fun p => T p*(2*P p)
  let C : PeriodOneHminusOne → ℂ := fun p => A p-D p
  have hD : AnalyticAt ℂ D 0 := hT.mul (analyticAt_const.mul hP)
  have hC : AnalyticAt ℂ C 0 := hAA.sub hD
  have hC0 : C 0 = 0 := by simp only [C,D,hA0,hT0,zero_mul,sub_zero]
  refine ⟨A,C,hAA,hC,hA0,hC0,?_,?_⟩
  · filter_upwards [hAM,hTM,hPM] with p hpA hpT hpP
    refine ⟨hpA,?_⟩
    dsimp only [C,D,P]
    rw [hpA,hpT,hpP,hillOwnCartesianAmplitude_conj_eq_sub_sheet]
    ring
  · intro h
    have hCD : fderiv ℂ C 0 = fderiv ℂ A 0-fderiv ℂ D 0 :=
      (hAA.differentiableAt.hasFDerivAt.sub hD.differentiableAt.hasFDerivAt).fderiv
    have hDD : fderiv ℂ D 0 = (2*P 0) • fderiv ℂ T 0 :=
      fderiv_mul_of_left_zero T (fun p => 2*P p) 0 hT (analyticAt_const.mul hP) hT0
    rw [hCD,sub_apply,hDD,smul_apply,smul_eq_mul,hTD,hP0]
    ring

end NLS.KdV
