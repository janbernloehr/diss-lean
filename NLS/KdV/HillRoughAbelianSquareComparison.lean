import NLS.KdV.HillPhysicalSheetRegularGermIdentity
import NLS.KdV.HillHminusPhysicalDirichletLabels
import NLS.KdV.HillHminusOriginalSourceAdapter
import NLS.SequenceSpaces.PeriodOneHminusAnalyticContinuation

/-! # Physical Abelian squares determine complex rough coordinate norms

A genuine nontrivial physical sheet detector removes the sheet restriction
at the free source. Native L2 analytic continuation and rough density then
identify one constant sign throughout the whole common complex rough ball.
The resulting norm identity works at every complex source and index.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

private theorem zero_parity : SpectralWeight.one.toCoeff
    (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0 := by simp
private theorem zero_real : IsRealHillPotential (SpectralWeight.one.toCoeff
    (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by intro n;simp

/-- Actual physical square agreement, even initially only off the sheet,
forces exact scalar norm agreement on the WHOLE COMPLEX rough ball. -/
theorem norm_eq_on_rough_ball_of_physical_abelian_sq
    (η : ℝ) (hη : 0<η) (n : ℕ+) (f g : PeriodOneHminusOne → ℂ)
    (hf : AnalyticOnNhd ℂ f (ball (0 : PeriodOneHminusOne) η))
    (hg : AnalyticOnNhd ℂ g (ball (0 : PeriodOneHminusOne) η))
    (he : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η →
      hillDirichletSheetRoot (SpectralWeight.one.toCoeff p.val)
        (hillDirichletEnergy p.val p.property.1 p.property.2 n n.pos)≠0 →
      (f (hillPhysicalHminusEmbedding p).val)^2=(g (hillPhysicalHminusEmbedding p).val)^2) :
    ∀ q∈ball (0 : PeriodOneHminusOne) η, ‖f q‖=‖g q‖ := by
  let F := fun a : Coeff 2 => f (periodOneL2Inclusion a)
  let G := fun a : Coeff 2 => g (periodOneL2Inclusion a)
  have hf0 : AnalyticAt ℂ f (periodOneL2Inclusion 0) := by
    simpa only [map_zero] using hf 0 (mem_ball_self hη)
  have hg0 : AnalyticAt ℂ g (periodOneL2Inclusion 0) := by
    simpa only [map_zero] using hg 0 (mem_ball_self hη)
  have hFa : AnalyticAt ℂ F 0 := hf0.comp (periodOneL2Inclusion.analyticAt 0)
  have hGa : AnalyticAt ℂ G 0 := hg0.comp (periodOneL2Inclusion.analyticAt 0)
  have ht : Tendsto (fun p : RealPeriodOneHillPotential => hillOriginalHminusSource p.val)
      (𝓝 (⟨0,zero_parity,zero_real⟩ : RealPeriodOneHillPotential)) (𝓝 (0 : PeriodOneHminusOne)) := by
    simpa only [Function.comp_def,map_zero] using
      (hillOriginalHminusSource.continuous.comp continuous_subtype_val).tendsto
        (⟨0,zero_parity,zero_real⟩ : RealPeriodOneHillPotential)
  have hphysical : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,zero_parity,zero_real⟩,
      hillDirichletSheetRoot (SpectralWeight.one.toCoeff p.val)
        (hillDirichletEnergy p.val p.property.1 p.property.2 n n.pos)≠0 →
      (F (Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val)))^2=
        (G (Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val)))^2 := by
    filter_upwards [ht.eventually (ball_mem_nhds (0 : PeriodOneHminusOne) hη)] with p hp
    intro hw
    exact he p hp hw
  rcases eventuallyEq_or_neg_native_of_physical_sheet_regular_sq zero_parity zero_real n F G hFa hGa hphysical with h | h
  · have H := eqOn_periodOneHminus_ball_of_L2_germ η hη f g hf hg h
    exact fun q hq => congrArg norm (H hq)
  · have H := eqOn_periodOneHminus_ball_of_L2_germ η hη f (fun q => -g q) hf
      (fun q hq => (hg q hq).neg) h
    intro q hq
    simpa only [norm_neg] using congrArg norm (H hq)

end NLS.KdV
