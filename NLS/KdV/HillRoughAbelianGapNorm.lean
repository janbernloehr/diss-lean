import NLS.KdV.HillPhysicalMeanZeroRoughDensity
import NLS.KdV.HillAbelianCoordinateFactor

/-! # Exact rough Abelian coordinate, gap-square and amplitude identity

The actual physical identity extends by real mean-zero rough density.
A nonzero amplitude then detects precisely the zero gap-square symbol.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

theorem physical_action_gap_amplitude_norm_relation
    (p : RealPeriodOneHillPotential) (n : ℕ+) (z m g : ℂ)
    (hz : z=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos)
    (hm : m=(Real.sqrt (1+(n : ℝ)) : ℂ)*
      hillAbelianAmplitudePrefactor p.val p.property.1 p.property.2 n)
    (hg : g=(((hillRealLabels p.val p.property.1 p.property.2 (2*(n : ℕ)) : ℂ)-
      (hillRealLabels p.val p.property.1 p.property.2 (2*(n : ℕ)-1) : ℂ))/(n : ℂ))^2) :
    4*(1+(n : ℝ))*‖z‖^2=(n : ℝ)^2*‖g‖*‖m‖^2 := by
  have h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0 := by simp
  have h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by intro j; simp
  have hzsq : ‖z‖^2=hillRealGapIntegral p.val p.property.1 p.property.2 n 0 := by
    rw [hz]
    exact norm_sq_hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 h0q h0r n n.pos
  have hi : 0≤hillRealGapIntegral p.val p.property.1 p.property.2 n 0 := by
    simpa only [mul_zero] using hillRealGapIntegral_nonneg_even p.val p.property.1 p.property.2 n n.pos 0
  have hsi := congrArg (fun v : ℂ => ‖v‖^2)
    (sqrt_hillAction_eq_halfLength_mul_abelianPrefactor p.val p.property.1 p.property.2 n n.pos)
  simp only [norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt hi,
    norm_mul,mul_pow,sq_abs] at hsi
  have hmn : ‖m‖^2=(1+(n : ℝ))*‖hillAbelianAmplitudePrefactor p.val p.property.1 p.property.2 n‖^2 := by
    rw [hm,norm_mul,mul_pow,norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (by positivity)]
  have hgn : (n : ℝ)^2*‖g‖=4*(hillRealGapHalfLength p.val p.property.1 p.property.2 n)^2 := by
    have hn : (n : ℝ)≠0 := by exact_mod_cast n.ne_zero
    rw [hg,norm_pow,norm_div,←ofReal_sub,norm_real,Real.norm_eq_abs]
    have hnorm : ‖(n : ℂ)‖=(n : ℝ) := by
      simpa only [norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity : (0 : ℝ)≤n)] using
        congrArg norm (show (n : ℂ)=((n : ℝ) : ℂ) by norm_cast)
    rw [hnorm,div_pow]
    dsimp only [hillRealGapHalfLength]
    field_simp
    nlinarith [sq_abs (hillRealLabels p.val p.property.1 p.property.2 (2*(n : ℕ))-
      hillRealLabels p.val p.property.1 p.property.2 (2*(n : ℕ)-1))]
  rw [hzsq,hmn,← mul_assoc,hgn]
  nlinarith [hsi]

theorem rough_abelian_gap_norm_relation_on_real_meanZero
    {U : Set PeriodOneHminusOne} (hU : IsOpen U)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (M : PeriodOneHminusOne → Coeff ⊤) (E : PeriodOneHminusOne → Coeff 1)
    (hZ : ContinuousOn Z U) (hM : ContinuousOn M U) (hE : ContinuousOn E U)
    (hZp : ∀ p : RealPeriodOneHillPotential, hillOriginalHminusSource p.val∈U → ∀ n : ℕ+,
      (Z (hillOriginalHminusSource p.val)).val (n : ℤ)=
        hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos)
    (hMp : ∀ p : RealPeriodOneHillPotential, hillOriginalHminusSource p.val∈U → ∀ n : ℕ+,
      M (hillOriginalHminusSource p.val) (n : ℤ)=(Real.sqrt (1+(n : ℝ)) : ℂ)*
        hillAbelianAmplitudePrefactor p.val p.property.1 p.property.2 n)
    (hEp : ∀ p : RealPeriodOneHillPotential, hillOriginalHminusSource p.val∈U → ∀ n : ℕ+,
      E (hillOriginalHminusSource p.val) (n : ℤ)=
        (((hillRealLabels p.val p.property.1 p.property.2 (2*(n : ℕ)) : ℂ)-
          (hillRealLabels p.val p.property.1 p.property.2 (2*(n : ℕ)-1) : ℂ))/(n : ℂ))^2)
    (q : PeriodOneHminusOne) (hq : q∈U) (hr : IsRealPeriodOneHminusOne q) (hm : q.val 0=0)
    (n : ℕ+) :
    4*(1+(n : ℝ))*‖(Z q).val (n : ℤ)‖^2=(n : ℝ)^2*‖E q (n : ℤ)‖*‖M q (n : ℤ)‖^2 := by
  have hzc : ContinuousOn (fun a => (Z a).val (n : ℤ)) U :=
    (WeightedCoeff.evalCLM (Weight.sobolev (-1/2)) 2 (n : ℤ)).continuous.comp_continuousOn hZ
  have hmc : ContinuousOn (fun a => M a (n : ℤ)) U :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) ⊤ (n : ℤ)).continuous.comp_continuousOn hM
  have hec : ContinuousOn (fun a => E a (n : ℤ)) U :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 1 (n : ℤ)).continuous.comp_continuousOn hE
  apply eq_on_real_meanZero_of_original_physical hU _ _
    (continuousOn_const.mul (hzc.norm.pow 2))
    ((continuousOn_const.mul hec.norm).mul (hmc.norm.pow 2)) _ q hq hr hm
  intro p _ hp
  exact physical_action_gap_amplitude_norm_relation p n _ _ _
    (hZp p hp n) (hMp p hp n) (hEp p hp n)

theorem rough_abelian_zero_iff_gap_symbol_zero
    (n : ℕ+) (z m g : ℂ) (hm : m≠0)
    (he : 4*(1+(n : ℝ))*‖z‖^2=(n : ℝ)^2*‖g‖*‖m‖^2) : z=0 ↔ g=0 := by
  have hn : (n : ℝ)≠0 := by exact_mod_cast n.ne_zero
  have hms : ‖m‖^2≠0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hm)
  constructor
  · intro hz
    rw [hz,norm_zero,zero_pow (by decide : (2 : ℕ)≠0),mul_zero] at he
    exact norm_eq_zero.mp ((mul_eq_zero.mp
      ((mul_eq_zero.mp he.symm).resolve_right hms)).resolve_left (pow_ne_zero 2 hn))
  · intro hg
    rw [hg,norm_zero,mul_zero,zero_mul] at he
    have hc : 4*(1+(n : ℝ))≠0 := by positivity
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp he).resolve_left hc))

end NLS.KdV
