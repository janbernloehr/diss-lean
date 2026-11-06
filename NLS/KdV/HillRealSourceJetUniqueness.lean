import NLS.KdV.HillL2GardnerDirections
import NLS.ComplexAnalysis.RealLineDerivativeUniqueness

/-! # Physical real potentials determine period-one source derivatives

Agreement on a neighborhood in the actual real L2 potential space determines
complex Frechet derivatives on every even Fourier direction. Real affine
curves give the real directions; conjugate Fourier reflection supplies their
complexification. In particular this applies to the actual Gardner directions.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ComplexConjugate
open NLS.ComplexAnalysis
namespace NLS.KdV

private theorem jet_eq_real_direction
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (F G : Coeff 2 → ℂ) (hF : DifferentiableAt ℂ F (SpectralWeight.one.toCoeff q))
    (hG : DifferentiableAt ℂ G (SpectralWeight.one.toCoeff q))
    (he : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      F (SpectralWeight.one.toCoeff p.val)=G (SpectralWeight.one.toCoeff p.val))
    (v : Coeff 2) (hv : v∈Coeff.paritySubspace 0) (hvr : IsRealHillPotential v) :
    (fderiv ℂ F (SpectralWeight.one.toCoeff q)) v=(fderiv ℂ G (SpectralWeight.one.toCoeff q)) v := by
  let lift := (WeightedCoeff.weightIsometry SpectralWeight.one.toWeight 2).symm
  have hcoeff (c : Coeff 2) : SpectralWeight.one.toCoeff (lift c)=c := by
    ext k
    rw [SpectralWeight.toCoeff_apply]
    change c k/(1 : ℂ)=c k
    exact div_one _
  have hlineprop (t : ℝ) :
      SpectralWeight.one.toCoeff (q+(t : ℂ) • lift v)∈Coeff.paritySubspace 0 ∧
        IsRealHillPotential (SpectralWeight.one.toCoeff (q+(t : ℂ) • lift v)) := by
    rw [map_add,map_smul,hcoeff]
    constructor
    · exact (Coeff.paritySubspace 0).add_mem hq ((Coeff.paritySubspace 0).smul_mem _ hv)
    · intro k
      simp only [lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,map_add,map_mul,conj_ofReal,hr k,hvr k]
  let line : ℝ → RealPeriodOneHillPotential := fun t => ⟨q+(t : ℂ) • lift v,hlineprop t⟩
  have hcont : Continuous line := by
    apply Continuous.subtype_mk
    exact continuous_const.add (Complex.continuous_ofReal.smul continuous_const)
  have hline0 : line 0=(⟨q,hq,hr⟩ : RealPeriodOneHillPotential) := by
    apply Subtype.ext
    simp [line]
  have ht : Tendsto line (𝓝 0) (𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)) := by
    rw [← hline0]
    exact hcont.tendsto 0
  apply fderiv_apply_eq_of_real_line_eventuallyEq F G _ v hF hG
  filter_upwards [ht.eventually he] with t ht0
  simpa only [line,map_add,map_smul,hcoeff] using ht0

private def realDirection (v : Coeff 2) : Coeff 2 := (1/2 : ℂ) • (v+star (Coeff.reflection v))
private def imagDirection (v : Coeff 2) : Coeff 2 := (-I/2 : ℂ) • (v-star (Coeff.reflection v))

private theorem realDirection_isReal (v : Coeff 2) : IsRealHillPotential (realDirection v) := by
  intro k
  change (1/2 : ℂ)*(v (-k)+conj (v (-(-k))))=conj ((1/2 : ℂ)*(v k+conj (v (-k))))
  have htwo : conj (2 : ℂ)=(2 : ℂ) := map_ofNat _ _
  simp [htwo,add_comm]

private theorem imagDirection_isReal (v : Coeff 2) : IsRealHillPotential (imagDirection v) := by
  intro k
  change (-I/2 : ℂ)*(v (-k)-conj (v (-(-k))))=conj ((-I/2 : ℂ)*(v k-conj (v (-k))))
  have htwo : conj (2 : ℂ)=(2 : ℂ) := map_ofNat _ _
  simp [htwo]
  ring

private theorem reflection_star_mem_parity (v : Coeff 2) (hv : v∈Coeff.paritySubspace 0) :
    star (Coeff.reflection v)∈Coeff.paritySubspace 0 := by
  rw [Coeff.mem_paritySubspace]
  intro k hk
  have hzero := (Coeff.mem_paritySubspace 0 v).mp hv (-k) (by omega)
  simp [hzero]

private theorem realDirection_add_I_imagDirection (v : Coeff 2) :
    v=realDirection v+I • imagDirection v := by
  unfold realDirection imagDirection
  rw [smul_smul]
  have he : (I : ℂ)*(-I/2)=1/2 := by rw [mul_div,mul_neg,I_mul_I,neg_neg]
  rw [he,← smul_add]
  have hsum : v+star (Coeff.reflection v)+(v-star (Coeff.reflection v))=(2 : ℂ) • v := by module
  rw [hsum,smul_smul]
  norm_num

/-- Nearby agreement on genuine physical real potentials determines the
complex source derivative in every period-one Fourier direction. -/
theorem fderiv_eq_on_parity_of_eventuallyEq_realPotentials
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (F G : Coeff 2 → ℂ) (hF : DifferentiableAt ℂ F (SpectralWeight.one.toCoeff q))
    (hG : DifferentiableAt ℂ G (SpectralWeight.one.toCoeff q))
    (he : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      F (SpectralWeight.one.toCoeff p.val)=G (SpectralWeight.one.toCoeff p.val))
    (v : Coeff 2) (hv : v∈Coeff.paritySubspace 0) :
    (fderiv ℂ F (SpectralWeight.one.toCoeff q)) v=(fderiv ℂ G (SpectralWeight.one.toCoeff q)) v := by
  have hreal := jet_eq_real_direction q hq hr F G hF hG he (realDirection v)
    ((Coeff.paritySubspace 0).smul_mem _ ((Coeff.paritySubspace 0).add_mem hv (reflection_star_mem_parity v hv)))
    (realDirection_isReal v)
  have himag := jet_eq_real_direction q hq hr F G hF hG he (imagDirection v)
    ((Coeff.paritySubspace 0).smul_mem _ ((Coeff.paritySubspace 0).sub_mem hv (reflection_star_mem_parity v hv)))
    (imagDirection_isReal v)
  calc
    _ = (fderiv ℂ F (SpectralWeight.one.toCoeff q)) (realDirection v+I • imagDirection v) :=
      congrArg _ (realDirection_add_I_imagDirection v)
    _ = (fderiv ℂ G (SpectralWeight.one.toCoeff q)) (realDirection v+I • imagDirection v) := by
      rw [map_add,map_smul,hreal,himag,map_add,map_smul]
    _ = _ := congrArg _ (realDirection_add_I_imagDirection v).symm

end NLS.KdV
