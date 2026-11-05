import NLS.KdV.HillStateGrowthBounds
import NLS.KdV.HillIndexedDiscriminantSources
import NLS.KdV.HillCurveRealizationCLM

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



private theorem norm_doubled_triple_le (a b c : ℂ) (K : ℝ) (hK : 0≤K)
    (ha : ‖a‖≤K) (hb : ‖b‖≤K) (hc : ‖c‖≤K) :
    ‖(2*a)*(b*c)‖≤2*K^3 := by
  rw [norm_mul,norm_mul (2 : ℂ) a,norm_mul b c,Complex.norm_ofNat]
  calc
    _ ≤ (2*K)*(K*K) := by gcongr
    _ = _ := by ring

/-- The actual spatial discriminant cotangent has a cubic bound in the
uniform norms of the original fundamental scalar states. -/
theorem norm_hillDiscriminantGradientSpatialCurve_le_of_state_bounds
    (q : Coeff 2) (z : ℂ) (K : ℝ) (hK : 0≤K)
    (hC : ‖hillL2FrequencyStateCurve q z (1,0)‖≤K)
    (hS : ‖hillL2FrequencyStateCurve q z (0,1)‖≤K) :
    ‖hillDiscriminantGradientSpatialCurve q z‖≤8*K^3 := by
  let C := hillL2FrequencyStateCurve q z (1,0)
  let S := hillL2FrequencyStateCurve q z (0,1)
  have hc (t : Icc (0 : ℝ) 1) : ‖(C t).1‖≤K := (norm_fst_le (C t)).trans ((C.norm_coe_le_norm t).trans hC)
  have hd (t : Icc (0 : ℝ) 1) : ‖(C t).2‖≤K := (norm_snd_le (C t)).trans ((C.norm_coe_le_norm t).trans hC)
  have hs (t : Icc (0 : ℝ) 1) : ‖(S t).1‖≤K := (norm_fst_le (S t)).trans ((S.norm_coe_le_norm t).trans hS)
  have ht (t : Icc (0 : ℝ) 1) : ‖(S t).2‖≤K := (norm_snd_le (S t)).trans ((S.norm_coe_le_norm t).trans hS)
  let t1 : Icc (0 : ℝ) 1 := ⟨1,by norm_num⟩
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  change ‖(2*(S t1).1)*((C t).1*(C t).2)+
    ((S t1).2-(C t1).1)*((C t).2*(S t).1+(C t).1*(S t).2)-
    (2*(C t1).2)*((S t).1*(S t).2)‖≤8*K^3
  have hfirst := norm_doubled_triple_le (S t1).1 (C t).1 (C t).2 K hK (hs t1) (hc t) (hd t)
  have hlast := norm_doubled_triple_le (C t1).2 (S t).1 (S t).2 K hK (hd t1) (hs t) (ht t)
  have hmiddle : ‖((S t1).2-(C t1).1)*((C t).2*(S t).1+(C t).1*(S t).2)‖≤4*K^3 := by
    have ha : ‖(S t1).2-(C t1).1‖≤2*K :=
      (norm_sub_le _ _).trans ((add_le_add (ht t1) (hc t1)).trans_eq (by ring))
    have hb : ‖(C t).2*(S t).1+(C t).1*(S t).2‖≤2*K^2 := by
      apply (norm_add_le _ _).trans
      rw [norm_mul,norm_mul]
      calc
        _ ≤ K*K+K*K := by
          gcongr
          · exact hd t
          · exact hs t
          · exact hc t
          · exact ht t
        _ = _ := by ring
    rw [norm_mul]
    exact (mul_le_mul ha hb (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hh := (norm_sub_le ((2*(S t1).1)*((C t).1*(C t).2)+
      ((S t1).2-(C t1).1)*((C t).2*(S t).1+(C t).1*(S t).2))
      ((2*(C t1).2)*((S t).1*(S t).2))).trans (add_le_add (norm_add_le _ _) le_rfl)
  nlinarith

/-- A uniform bound for the actual energy Hamiltonian source on every
bounded complex source and frequency ball, including frequency zero. -/
theorem exists_hillEnergyHamiltonianSource_uniform_frequency_bound
    (B R : ℝ) (_hB : 0≤B) (hR : 0≤R) :
    ∃ A : ℝ, 0<A ∧ ∀ p : Coeff 2, ‖p‖≤B → ∀ z : ℂ, ‖z‖≤R →
      ‖hillEnergyHamiltonianSource p (z^2)‖≤A := by
  let K : ℝ := (1+R)^2*Real.exp (R+2*(1+B))
  have hK : 0<K := by dsimp only [K];positivity
  refine ⟨1+‖hillCurveRealizationCLM‖*(8*K^3),by positivity,?_⟩
  intro p hp z hz
  have hstate (v : ℂ × ℂ) (hv : ‖v‖=1) : ‖hillL2FrequencyStateCurve p z v‖≤K := by
    apply (norm_hillL2FrequencyStateCurve_le p z v).trans
    rw [hv,mul_one]
    dsimp only [K]
    gcongr
  have hg := norm_hillDiscriminantGradientSpatialCurve_le_of_state_bounds p z K hK.le
    (hstate (1,0) (by norm_num [Prod.norm_def])) (hstate (0,1) (by norm_num [Prod.norm_def]))
  have henergy : hillEnergyDiscriminantGradientSpatialCurve p (z^2)=hillDiscriminantGradientSpatialCurve p z := by
    dsimp only [hillEnergyDiscriminantGradientSpatialCurve,hillDiscriminantGradientSpatialCurve]
    rw [hillL2FrequencyStateCurve_eq_of_sq_eq p (Complex.sqrt (z^2)) z (1,0) (complex_sqrt_sq (z^2)),
      hillL2FrequencyStateCurve_eq_of_sq_eq p (Complex.sqrt (z^2)) z (0,1) (complex_sqrt_sq (z^2))]
  have he : hillEnergyHamiltonianSource p (z^2)=hillCurveRealizationCLM (-(hillDiscriminantGradientSpatialCurve p z)) := by
    rw [hillEnergyHamiltonianSource,←hillCurveRealizationCLM_closed,henergy]
  rw [he]
  apply ((hillCurveRealizationCLM.le_opNorm _).trans ?_).trans (le_add_of_nonneg_left (by norm_num))
  rw [norm_neg]
  exact mul_le_mul_of_nonneg_left hg (norm_nonneg _)

/-- The same actual energy-source bound on bounded energy balls, with no
chosen square-root branch or excluded energy. -/
theorem exists_hillEnergyHamiltonianSource_uniform_energy_bound
    (B D : ℝ) (hB : 0≤B) (hD : 0≤D) :
    ∃ A : ℝ, 0<A ∧ ∀ p : Coeff 2, ‖p‖≤B → ∀ E : ℂ, ‖E‖≤D →
      ‖hillEnergyHamiltonianSource p E‖≤A := by
  obtain ⟨A,hA,hbound⟩ := exists_hillEnergyHamiltonianSource_uniform_frequency_bound B (D+1) hB (by linarith)
  refine ⟨A,hA,?_⟩
  intro p hp E hE
  have hs : ‖Complex.sqrt E‖^2=‖E‖ := by rw [←norm_pow,complex_sqrt_sq]
  have hr : ‖Complex.sqrt E‖≤D+1 := by nlinarith [sq_nonneg (‖Complex.sqrt E‖-1)]
  simpa only [complex_sqrt_sq] using hbound p hp (Complex.sqrt E) hr

end NLS.KdV
