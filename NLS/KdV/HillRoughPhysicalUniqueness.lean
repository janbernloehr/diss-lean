import NLS.KdV.HillPhysicalRealGermIdentity
import NLS.KdV.HillHminusPhysicalDirichletLabels
import NLS.KdV.HillHminusOriginalSourceAdapter
import NLS.SequenceSpaces.PeriodOneHminusAnalyticContinuation
import NLS.SequenceSpaces.WeightedFiniteCoefficients

/-! # Original physical recovery uniquely fixes the complex rough map

Equality at physical real L2 sources fixes a native analytic germ. Dense
complex linear continuation then identifies the WHOLE common complex
rough ball, before any coefficient or stronger Sobolev order is chosen.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

private theorem zero_parity : SpectralWeight.one.toCoeff
    (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0 := by simp
private theorem zero_real : IsRealHillPotential (SpectralWeight.one.toCoeff
    (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by intro n;simp

/-- Original physical real values determine scalar analytic functions
on the WHOLE common complex rough ball, without a physical L2 norm bound. -/
theorem eqOn_rough_ball_of_physical_scalar_eq
    (η : ℝ) (hη : 0<η) (f g : PeriodOneHminusOne → ℂ)
    (hf : AnalyticOnNhd ℂ f (ball (0 : PeriodOneHminusOne) η))
    (hg : AnalyticOnNhd ℂ g (ball (0 : PeriodOneHminusOne) η))
    (he : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η →
        f (hillPhysicalHminusEmbedding p).val=g (hillPhysicalHminusEmbedding p).val) :
    EqOn f g (ball (0 : PeriodOneHminusOne) η) := by
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
      F (Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val))=
        G (Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val)) := by
    filter_upwards [ht.eventually (ball_mem_nhds (0 : PeriodOneHminusOne) hη)] with p hp
    exact he p hp
  exact eqOn_periodOneHminus_ball_of_L2_germ η hη f g hf hg
    (eventuallyEq_native_of_physical_real_germ zero_parity zero_real F G hFa hGa hphysical)

/-- The entire actual weighted sequence map is uniquely fixed by its
original physical real recovery, including every signed coordinate. -/
theorem eqOn_weighted_rough_ball_of_physical_eq
    (w : Weight) (η : ℝ) (hη : 0<η)
    (F G : PeriodOneHminusOne → WeightedCoeff w 2)
    (hF : AnalyticOnNhd ℂ F (ball (0 : PeriodOneHminusOne) η))
    (hG : AnalyticOnNhd ℂ G (ball (0 : PeriodOneHminusOne) η))
    (he : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η →
        F (hillPhysicalHminusEmbedding p).val=G (hillPhysicalHminusEmbedding p).val) :
    EqOn F G (ball (0 : PeriodOneHminusOne) η) := by
  have hcoord (j : ℤ) : EqOn (fun q => (F q).val j) (fun q => (G q).val j)
      (ball (0 : PeriodOneHminusOne) η) := by
    apply eqOn_rough_ball_of_physical_scalar_eq η hη
      (fun q => (F q).val j) (fun q => (G q).val j)
      (fun q hq => ((WeightedCoeff.evalCLM w 2 j).analyticAt _).comp (hF q hq))
      (fun q hq => ((WeightedCoeff.evalCLM w 2 j).analyticAt _).comp (hG q hq))
    intro p hp
    exact congrArg (fun a : WeightedCoeff w 2 => a.val j) (he p hp)
  intro q hq
  apply Subtype.ext
  funext j
  exact hcoord j hq

end NLS.KdV
