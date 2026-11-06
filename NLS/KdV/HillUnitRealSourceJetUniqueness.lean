import NLS.KdV.HillRealSourceJetUniqueness
import NLS.KdV.HillAbelianCoordinateContinuity

/-! # Unit-period physical real germs determine the full complex L2 derivative -/
noncomputable section
open Set Complex Filter Topology
open scoped ComplexConjugate
open NLS.ComplexAnalysis
namespace NLS.KdV

private theorem unit_jet_eq_real_direction (F G : Coeff 2 → ℂ)
    (hF : DifferentiableAt ℂ F 0) (hG : DifferentiableAt ℂ G 0)
    (he : ∀ᶠ p : RealHillWeightedPotential SpectralWeight.one in 𝓝
      (⟨0,by intro j;simp⟩ : RealHillWeightedPotential SpectralWeight.one),
      F (SpectralWeight.one.doubleIndex.toCoeff p.val)=G (SpectralWeight.one.doubleIndex.toCoeff p.val))
    (v : Coeff 2) (hv : IsRealHillPotential v) : (fderiv ℂ F 0) v = (fderiv ℂ G 0) v := by
  let lift := (WeightedCoeff.weightIsometry SpectralWeight.one.doubleIndex.toWeight 2).symm
  have hcoeff (c : Coeff 2) : SpectralWeight.one.doubleIndex.toCoeff (lift c) = c := by
    ext k
    rw [SpectralWeight.toCoeff_apply]
    change c k/(1 : ℂ)=c k
    exact div_one _
  have hprop (t : ℝ) : IsRealHillPotential (SpectralWeight.one.doubleIndex.toCoeff ((t : ℂ) • lift v)) := by
    rw [map_smul,hcoeff]
    intro k
    simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,map_mul,conj_ofReal,hv k]
  let line : ℝ → RealHillWeightedPotential SpectralWeight.one := fun t => ⟨(t : ℂ) • lift v,hprop t⟩
  have hc : Continuous line := Continuous.subtype_mk (Complex.continuous_ofReal.smul continuous_const) _
  have h0 : line 0 = (⟨0,by intro j;simp⟩ : RealHillWeightedPotential SpectralWeight.one) := by
    apply Subtype.ext
    simp only [line,ofReal_zero,zero_smul]
  have ht : Tendsto line (𝓝 0) (𝓝 (⟨0,by intro j;simp⟩ : RealHillWeightedPotential SpectralWeight.one)) := by
    rw [← h0]
    exact hc.tendsto 0
  apply fderiv_apply_eq_of_real_line_eventuallyEq F G 0 v hF hG
  filter_upwards [ht.eventually he] with t ht0
  simpa only [line,map_smul,hcoeff,zero_add] using ht0

private def unitRealDirection (v : Coeff 2) : Coeff 2 := (1/2 : ℂ) • (v+star (Coeff.reflection v))
private def unitImagDirection (v : Coeff 2) : Coeff 2 := (-I/2 : ℂ) • (v-star (Coeff.reflection v))

private theorem unitRealDirection_real (v : Coeff 2) : IsRealHillPotential (unitRealDirection v) := by
  intro k
  change (1/2 : ℂ)*(v (-k)+conj (v (-(-k))))=conj ((1/2 : ℂ)*(v k+conj (v (-k))))
  have htwo : conj (2 : ℂ)=(2 : ℂ) := map_ofNat _ _
  simp [htwo,add_comm]
private theorem unitImagDirection_real (v : Coeff 2) : IsRealHillPotential (unitImagDirection v) := by
  intro k
  change (-I/2 : ℂ)*(v (-k)-conj (v (-(-k))))=conj ((-I/2 : ℂ)*(v k-conj (v (-k))))
  have htwo : conj (2 : ℂ)=(2 : ℂ) := map_ofNat _ _
  simp [htwo]
  ring
private theorem unitDirection_decomp (v : Coeff 2) : v = unitRealDirection v+I • unitImagDirection v := by
  unfold unitRealDirection unitImagDirection
  rw [smul_smul]
  have he : (I : ℂ)*(-I/2)=1/2 := by rw [mul_div,mul_neg,I_mul_I,neg_neg]
  rw [he,← smul_add]
  have hsum : v+star (Coeff.reflection v)+(v-star (Coeff.reflection v))=(2 : ℂ) • v := by module
  rw [hsum,smul_smul]
  norm_num

theorem fderiv_eq_of_eventuallyEq_unit_realPotentials (F G : Coeff 2 → ℂ)
    (hF : DifferentiableAt ℂ F 0) (hG : DifferentiableAt ℂ G 0)
    (he : ∀ᶠ p : RealHillWeightedPotential SpectralWeight.one in 𝓝
      (⟨0,by intro j;simp⟩ : RealHillWeightedPotential SpectralWeight.one),
      F (SpectralWeight.one.doubleIndex.toCoeff p.val)=G (SpectralWeight.one.doubleIndex.toCoeff p.val)) :
    fderiv ℂ F 0 = fderiv ℂ G 0 := by
  ext v
  have hr := unit_jet_eq_real_direction F G hF hG he (unitRealDirection v) (unitRealDirection_real v)
  have hi := unit_jet_eq_real_direction F G hF hG he (unitImagDirection v) (unitImagDirection_real v)
  calc
    _ = (fderiv ℂ F 0) (unitRealDirection v+I • unitImagDirection v) := congrArg _ (unitDirection_decomp v)
    _ = (fderiv ℂ G 0) (unitRealDirection v+I • unitImagDirection v) := by rw [map_add,map_smul,hr,hi,map_add,map_smul]
    _ = _ := congrArg _ (unitDirection_decomp v).symm

end NLS.KdV
