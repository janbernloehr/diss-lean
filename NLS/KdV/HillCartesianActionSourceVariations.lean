import NLS.KdV.HillHamiltonianSourceContinuity
import NLS.KdV.HillRegularTerminalDensity
import NLS.KdV.HillRegularCartesianSourceVariations

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



private theorem eq_at_of_dense_germ_eq {A : Type} [TopologicalSpace A]
    (F G : A → ℂ) (q : A) (S : Set A) (hS : Dense S)
    (hF : ContinuousAt F q) (hG : ContinuousAt G q)
    (he : ∀ᶠ p in 𝓝 q, p∈S → F p=G p) : F q=G q := by
  have hf : ∃ᶠ p in 𝓝 q, p∈S := mem_closure_iff_frequently.mp (hS q)
  have hpair : ∃ᶠ p in 𝓝 q, (F p,G p)∈{t : ℂ × ℂ | t.1=t.2} := by
    exact (hf.and_eventually he).mono (fun _ hp => hp.2 hp.1)
  exact (isClosed_eq continuous_fst continuous_snd).mem_of_frequently_of_tendsto hpair
    (hF.prodMk_nhds hG)

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- The exact action-source rotation of every actual analytic Cartesian germ at every
real rough Hill source, including zero terminal sheets and collapsed gaps. -/
theorem hillSpectralCartesianGerm_actionSource_fderiv
    (n : ℕ) (hn : 1≤n)
    (Z : Coeff 2 → ℂ) (hZ : AnalyticAt ℂ Z (SpectralWeight.one.toCoeff q))
    (hZreal : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      Z (SpectralWeight.one.toCoeff p.val)=hillSpectralCartesian p.val p.property.1 p.property.2 n hn) :
    ∀ k : ℕ, ∀ hk : 1≤k,
      (fderiv ℂ Z (SpectralWeight.one.toCoeff q))
        (SpectralWeight.one.toCoeff (hillPhysicalMomentHamiltonianSource q hq hr k hk 0))=
          -I*(if k=n then 1 else 0 : ℂ)*hillSpectralCartesian q hq hr n hn := by
  let qR : RealPeriodOneHillPotential := ⟨q,hq,hr⟩
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  obtain ⟨W,hWsub,hW,hqW⟩ := _root_.mem_nhds_iff.mp hZreal
  have hA : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 qR, AnalyticAt ℂ Z (P p) :=
    hP.continuousAt.tendsto.eventually hZ.eventually_analyticAt
  intro k hk
  let H : RealPeriodOneHillPotential → Coeff 2 := fun p =>
    SpectralWeight.one.toCoeff (hillPhysicalMomentHamiltonianSource p.val p.property.1 p.property.2 k hk 0)
  have hH : Continuous H := SpectralWeight.one.toCoeff.continuous.comp
    (continuous_hillPhysicalMomentHamiltonianSource k hk 0)
  let F : RealPeriodOneHillPotential → ℂ := fun p => (fderiv ℂ Z (P p)) (H p)
  let G : RealPeriodOneHillPotential → ℂ := fun p =>
    -I*(if k=n then 1 else 0 : ℂ)*hillSpectralCartesian p.val p.property.1 p.property.2 n hn
  have hF : ContinuousAt F qR :=
    (hZ.fderiv.continuousAt.comp (f := P) hP.continuousAt).clm_apply hH.continuousAt
  have hG : Continuous G := continuous_const.mul (continuous_hillSpectralCartesian h0q h0r n hn)
  have he : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 qR, p∈hillRegularTerminalLocus → F p=G p := by
    filter_upwards [hA,hW.mem_nhds hqW] with p hpA hpW
    intro hpReg
    have hmatch : ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 p,
        Z (SpectralWeight.one.toCoeff r.val)=hillSpectralCartesian r.val r.property.1 r.property.2 n hn :=
      Filter.Eventually.mono (hW.mem_nhds hpW) (fun _ hrW => hWsub hrW)
    exact hillSpectralCartesianGerm_regular_actionSource_fderiv p.val p.property.1 p.property.2
      h0q h0r n hn hpReg Z hpA hmatch k hk
  exact eq_at_of_dense_germ_eq F G qR hillRegularTerminalLocus dense_hillRegularTerminalLocus hF hG.continuousAt he

/-- At every real source the actual analytic physical Cartesian coordinate carries
all exact action-source rotations simultaneously, without any terminal regularity assumption. -/
theorem exists_hillSpectralCartesian_actionSource_variations (n : ℕ) (hn : 1≤n) :
    ∃ Z : Coeff 2 → ℂ, AnalyticAt ℂ Z (SpectralWeight.one.toCoeff q) ∧
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        Z (SpectralWeight.one.toCoeff p.val)=hillSpectralCartesian p.val p.property.1 p.property.2 n hn) ∧
      ∀ k : ℕ, ∀ hk : 1≤k,
        (fderiv ℂ Z (SpectralWeight.one.toCoeff q))
          (SpectralWeight.one.toCoeff (hillPhysicalMomentHamiltonianSource q hq hr k hk 0))=
            -I*(if k=n then 1 else 0 : ℂ)*hillSpectralCartesian q hq hr n hn := by
  obtain ⟨Z,hZ,hZreal⟩ := exists_hillSpectralCartesian_analytic_extension h0q h0r q hq hr n hn
  exact ⟨Z,hZ,hZreal,hillSpectralCartesianGerm_actionSource_fderiv q hq hr h0q h0r n hn Z hZ hZreal⟩

end NLS.KdV
