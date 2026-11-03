import NLS.KdV.HillAbelianCosineDifferential
import NLS.ComplexAnalysis.ParametricConvexPrimitive
import NLS.ComplexAnalysis.PrimitiveRadialContinuation

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillAbelianCosinePrimitive (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (θ : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (θ-(Real.pi : ℂ))*hillAbelianCosineDifferential q hq hr n hn k
    ((Real.pi : ℂ)+(t : ℂ)*(θ-(Real.pi : ℂ)))

theorem hillAbelianCosinePrimitive_pi (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    hillAbelianCosinePrimitive q hq hr n hn k (Real.pi : ℂ) = 0 := by
  simp only [hillAbelianCosinePrimitive,sub_self,mul_zero,add_zero,zero_mul,intervalIntegral.integral_zero]

theorem hillAbelianCosinePrimitive_im_eq_zero (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) :
    (hillAbelianCosinePrimitive q hq hr n hn k (θ : ℂ)).im = 0 := by
  let f : ℝ → ℝ := fun t => (θ-Real.pi)*
    (hillAbelianCosineDifferential q hq hr n hn k ((Real.pi+t*(θ-Real.pi) : ℝ) : ℂ)).re
  have he : (fun t : ℝ => ((θ : ℂ)-(Real.pi : ℂ))*hillAbelianCosineDifferential q hq hr n hn k
      ((Real.pi : ℂ)+(t : ℂ)*((θ : ℂ)-(Real.pi : ℂ)))) = fun t => (f t : ℂ) := by
    funext t
    have harg : (Real.pi : ℂ)+(t : ℂ)*((θ : ℂ)-(Real.pi : ℂ)) = ((Real.pi+t*(θ-Real.pi) : ℝ) : ℂ) := by
      push_cast
      rfl
    have hD : hillAbelianCosineDifferential q hq hr n hn k ((Real.pi+t*(θ-Real.pi) : ℝ) : ℂ) =
        ((hillAbelianCosineDifferential q hq hr n hn k ((Real.pi+t*(θ-Real.pi) : ℝ) : ℂ)).re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa only [ofReal_im] using hillAbelianCosineDifferential_im_eq_zero q hq hr n hn k hk (Real.pi+t*(θ-Real.pi))
    rw [harg,hD]
    simp only [f,ofReal_mul,ofReal_sub]
  rw [hillAbelianCosinePrimitive,he,intervalIntegral.integral_ofReal]
  exact ofReal_im _

theorem exists_hillAbelianCosinePrimitive_analytic_chart (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) :
    ∃ Ω : Set ℂ, IsOpen Ω ∧ Convex ℝ Ω ∧ segment ℝ (0 : ℂ) (Real.pi : ℂ) ⊆ Ω ∧
      AnalyticOnNhd ℂ (hillAbelianCosinePrimitive q hq hr n hn k) Ω ∧
      ∀ θ ∈ Ω, HasDerivAt (hillAbelianCosinePrimitive q hq hr n hn k)
        (hillAbelianCosineDifferential q hq hr n hn k θ) θ := by
  let J := cosineGapPoint (hillRealGapCenter q hq hr k : ℂ) (hillRealGapHalfLength q hq hr k : ℂ)
  let U := J ⁻¹' hillGapFilledDomain q hq hr k
  have hJc : Continuous J := by unfold J cosineGapPoint;fun_prop
  have hU : IsOpen U := (isOpen_hillGapFilledDomain q hq hr k).preimage hJc
  have hseg : segment ℝ (0 : ℂ) (Real.pi : ℂ) ⊆ U := by
    intro θ hθ
    have hθim := im_eq_zero_of_mem_real_segment 0 Real.pi θ hθ
    have hθeq : θ = (θ.re : ℂ) := by apply Complex.ext <;> simp [hθim]
    change J θ ∈ hillGapFilledDomain q hq hr k
    rw [hθeq]
    exact hillCosineGapPoint_mem_filledDomain q hq hr k hk θ.re
  obtain ⟨Ω,hΩ,hconv,hKΩ,hΩU⟩ := exists_convex_open_neighborhood_of_segment (0 : ℂ) Real.pi U hU hseg
  let D := hillAbelianCosineDifferential q hq hr n hn k
  have hD : AnalyticOnNhd ℂ D Ω := by
    intro θ hθ
    have hE : J θ ∈ hillGapFilledDomain q hq hr k := hΩU hθ
    have hJ : AnalyticAt ℂ J θ := by
      unfold J cosineGapPoint
      exact analyticAt_const.add (analyticAt_const.mul Complex.analyticAt_cos)
    have hN := (analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q hq hr n hn (J θ) (mem_univ _)).comp (f := J) hJ
    have hR := (analyticOnNhd_hillDeflatedEnergyCanonicalRoot q hq hr k (J θ) hE).comp (f := J) hJ
    exact analyticAt_const.mul (hN.div hR (hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr k hk (J θ) hE))
  let F : ℂ × ℂ → ℂ := fun t => D t.1
  have hF : AnalyticOnNhd ℂ F (Ω ×ˢ univ) := fun t ht => (hD t.1 ht.1).comp
    (f := fun t : ℂ × ℂ => t.1) analyticAt_fst
  have hπ : (Real.pi : ℂ) ∈ Ω := hKΩ (right_mem_segment ℝ _ _)
  have hprim := analyticOnNhd_parametricConvexPrimitive F Ω univ Real.pi hΩ hconv isOpen_univ hπ hF
  refine ⟨Ω,hΩ,hconv,hKΩ,?_,?_⟩
  · intro θ hθ
    exact (hprim (θ,0) ⟨hθ,mem_univ _⟩).comp (f := fun θ : ℂ => (θ,(0 : ℂ))) (analyticAt_id.prod analyticAt_const)
  · intro θ hθ
    exact hasDerivAt_parametricConvexPrimitive F Ω univ Real.pi hΩ hconv hπ hF 0 (mem_univ _) θ hθ

end NLS.KdV
