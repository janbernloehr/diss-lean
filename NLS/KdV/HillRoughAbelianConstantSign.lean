import NLS.KdV.HillPhysicalSheetRegularGermIdentity
import NLS.KdV.HillHminusPhysicalDirichletLabels
import NLS.KdV.HillHminusOriginalSourceAdapter
import NLS.SequenceSpaces.PeriodOneHminusAnalyticContinuation

/-! # Physical Abelian squares fix one constant coordinate sign

The physical sheet detector and genuine complex rough continuation
retain the exact alternative throughout the WHOLE common complex ball.
The sign is selected before the source, with no mode-dependent radius.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

private theorem zero_parity : SpectralWeight.one.toCoeff
    (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0 := by simp
private theorem zero_real : IsRealHillPotential (SpectralWeight.one.toCoeff
    (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by intro n;simp

/-- Actual physical square agreement off the original sheet fixes ONE
constant sign on the WHOLE complex rough ball, before all source points. -/
theorem eqOn_or_neg_rough_ball_of_physical_abelian_sq
    (η : ℝ) (hη : 0<η) (n : ℕ+) (f g : PeriodOneHminusOne → ℂ)
    (hf : AnalyticOnNhd ℂ f (ball (0 : PeriodOneHminusOne) η))
    (hg : AnalyticOnNhd ℂ g (ball (0 : PeriodOneHminusOne) η))
    (he : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η →
      hillDirichletSheetRoot (SpectralWeight.one.toCoeff p.val)
        (hillDirichletEnergy p.val p.property.1 p.property.2 n n.pos)≠0 →
      (f (hillPhysicalHminusEmbedding p).val)^2=(g (hillPhysicalHminusEmbedding p).val)^2) :
    EqOn f g (ball (0 : PeriodOneHminusOne) η) ∨
      EqOn f (fun q => -g q) (ball (0 : PeriodOneHminusOne) η) := by
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
  · exact Or.inl (eqOn_periodOneHminus_ball_of_L2_germ η hη f g hf hg h)
  · exact Or.inr (eqOn_periodOneHminus_ball_of_L2_germ η hη f (fun q => -g q) hf
      (fun q hq => (hg q hq).neg) h)

end NLS.KdV
