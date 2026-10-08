import NLS.ZakharovShabat.SourceFullAbelianHamiltonianInversion
import NLS.ComplexAnalysis.PolynomialInversionCircleCoefficients

/-! # All-order exterior contours of the physical Hamiltonian hierarchy -/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- Every higher exterior action contour is its physical Hamiltonian divided
by the exact power of two. One radius threshold works for all orders. -/
theorem exists_sourceFiniteGap_higherAction_exterior
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R → ∀ k : ℕ,
      -(Real.pi : ℂ)⁻¹ * (∮ z in C(0,R), z^k*sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val)) =
        sourceFiniteGapNLSHamiltonian hp hp1 φ hf (k+1)/2^k := by
  obtain ⟨S₀,hS₀,A,hA₀,_,hcoeff,hval₀⟩ :=
    exists_sourceFullAbelian_finiteGap_hamiltonian_inversion C φ hφ hf
  obtain ⟨r,hr,hA⟩ := hA₀.exists_ball_analyticOnNhd
  let S := max S₀ r⁻¹+1
  have hS : 0 < S := by dsimp [S]; linarith [le_max_left S₀ r⁻¹]
  have hrS : r⁻¹ < S := by dsimp [S]; linarith [le_max_right S₀ r⁻¹]
  have hval (z : ℂ) (hz : S < ‖z‖) :
      sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val) = -I*z+A z⁻¹ := by
    have hS₀z : S₀ < ‖z‖ := by dsimp [S] at hz; linarith [le_max_left S₀ r⁻¹]
    simpa only [Int.cast_zero,mul_zero,add_zero] using hval₀ 0 z hS₀z
  refine ⟨S+1,by linarith,?_⟩
  intro R hR k
  have hSR : S < R := by linarith
  have hRpos : 0 < R := hS.trans hSR
  have hRr : R⁻¹ < r := (inv_lt_comm₀ hRpos hr).mpr (hrS.trans hSR)
  have hz0 (z : ℂ) (hz : z ∈ sphere (0 : ℂ) R) : z ≠ 0 := by
    have hn : ‖z‖ = R := by simpa only [mem_sphere,dist_zero_right] using hz
    exact norm_pos_iff.mp (hn.symm ▸ hRpos)
  have hgi : CircleIntegrable (fun z : ℂ => z^k*A z⁻¹) 0 R := by
    apply ContinuousOn.circleIntegrable hRpos.le
    intro z hz
    have hn : ‖z‖ = R := by simpa only [mem_sphere,dist_zero_right] using hz
    have hw : z⁻¹ ∈ ball (0 : ℂ) r := by simpa only [mem_ball,dist_zero_right,norm_inv,hn] using hRr
    exact ((continuousAt_id.pow k).mul ((hA z⁻¹ hw).continuousAt.comp
      (continuousAt_inv₀ (hz0 z hz)))).continuousWithinAt
  have hpoly : Differentiable ℂ (fun z : ℂ => z^k*(-I*z)) := by intro z; fun_prop
  have hzero : (∮ z in C(0,R), z^k*(-I*z)) = 0 :=
    (DiffContOnCl.mk_ball hpoly.differentiableOn
      hpoly.continuous.continuousOn).circleIntegral_eq_zero hRpos.le
  have he : (∮ z in C(0,R), z^k*sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val)) =
      (2*Real.pi*I : ℂ)*(iteratedDeriv (k+1) A 0/(k+1).factorial) := by
    calc
      _ = ∮ z in C(0,R), z^k*(-I*z)+z^k*A z⁻¹ := by
        apply circleIntegral.integral_congr hRpos.le
        intro z hz
        have hn : ‖z‖ = R := by simpa only [mem_sphere,dist_zero_right] using hz
        dsimp only
        rw [hval z (hn.symm ▸ hSR),mul_add]
      _ = _ := by
        rw [circleIntegral.integral_add (hpoly.continuous.continuousOn.circleIntegrable hRpos.le) hgi,
          hzero,zero_add,circleIntegral_pow_mul_comp_inv_eq A r R hr hRpos hRr hA k]
  rw [he,hcoeff]
  have hfac : ((k+1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k+1)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [mul_div_cancel_left₀ _ hfac,pow_succ]
  field_simp
  ring_nf
  simp only [I_sq]
  ring

end NLS.ZakharovShabat
