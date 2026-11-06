import NLS.Articles.KdVKdV2Frequencies.RoughUniformActionAmplitudes
import NLS.Articles.KdVKdV2Frequencies.NativeRoughTerminalPacket
import NLS.KdV.HillHminusRegularPhaseGerms

/-! # Actual physical Abelian coordinates have complex rough scalar germs

The phase includes its own-index regular term. The output remains scalar;
a common radius before all output indices is not asserted here.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

private theorem zero_parity : SpectralWeight.one.toCoeff
    (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0 := by simp
private theorem zero_real : IsRealHillPotential (SpectralWeight.one.toCoeff
    (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by intro j; simp

theorem exists_hillDirichletAbelianCoordinate_rough_scalar_germ (n : ℕ+) :
    ∃ F : PeriodOneHminusOne → ℂ, AnalyticAt ℂ F 0 ∧ F 0=0 ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,zero_parity,zero_real⟩,
        F (hillPhysicalHminusEmbedding p).val=
          hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos := by
  obtain ⟨r,_CA,A,hr,_hCA,hA⟩ := exists_hillHminus_all_physical_action_amplitudes
  obtain ⟨s,_CZ,Z,hs,_hCZ,hZa,hZ0,_hZb,hZp⟩ := exists_hillHminus_native_normalized_terminal_packet
  obtain ⟨P,hPa,hPp⟩ := exists_hillHminus_full_regular_correction_physical_germ zero_parity zero_real n
  let F : PeriodOneHminusOne → ℂ := fun q =>
    A n q*((n : ℂ)*Z q (n : ℤ))*exp (I*P q)
  have hcoord := ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)).analyticAt (Z 0)).comp
    (hZa 0 (mem_ball_self hs))
  have hFa : AnalyticAt ℂ F 0 :=
    (((hA n).1 0 (mem_ball_self hr)).mul (analyticAt_const.mul hcoord)).mul
      (analyticAt_const.mul hPa).cexp'
  have hF0 : F 0=0 := by simp only [F,hZ0,lp.coeFn_zero,Pi.zero_apply,mul_zero,zero_mul]
  refine ⟨F,hFa,hF0,?_⟩
  have ht : Tendsto (fun p : RealPeriodOneHillPotential => hillOriginalHminusSource p.val)
      (𝓝 (⟨0,zero_parity,zero_real⟩ : RealPeriodOneHillPotential)) (𝓝 (0 : PeriodOneHminusOne)) := by
    simpa only [Function.comp_def,map_zero] using
      (hillOriginalHminusSource.continuous.comp continuous_subtype_val).tendsto
        (⟨0,zero_parity,zero_real⟩ : RealPeriodOneHillPotential)
  filter_upwards [hPp,ht.eventually (ball_mem_nhds (0 : PeriodOneHminusOne) hr),
    ht.eventually (ball_mem_nhds (0 : PeriodOneHminusOne) hs)] with p hpP hpA hpZ
  have heZ := hZp p hpZ n
  have hnn : (n : ℂ)≠0 := by exact_mod_cast n.ne_zero
  have hterminal : (n : ℂ)*Z (hillPhysicalHminusEmbedding p).val (n : ℤ)=
      hillDirichletAbelianTerminalFactor p.val p.property.1 p.property.2 n n.pos := by
    rw [heZ,mul_div_cancel₀ _ hnn]
  change A n _*((n : ℂ)*Z _ (n : ℤ))*exp (I*P _)=_
  have hpP' : P (hillPhysicalHminusEmbedding p).val=
      hillSummedRegularAbelianCorrection p.val p.property.1 p.property.2 n n.pos := hpP
  rw [(hA n).2.2.2 p hpA,hterminal,hpP']
  exact (hillDirichletAbelianCoordinate_eq_factor p.val p.property.1 p.property.2 n n.pos).symm

end NLS.Articles.KdVKdV2Frequencies
