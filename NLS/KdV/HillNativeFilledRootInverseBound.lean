import NLS.KdV.HillAllRadiusRootProduct
import NLS.KdV.HillNativeEnergyDensityTransfer

/-! # Uniform inverse bounds for every filled root on one complex source ball

Actual root separation and the genuine quadratic/root product control
the inverse on the boundary. Maximum modulus fills the energy discs.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillFilledFreeGapRoot_all_inverse_bound :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ k : ℕ+, ∀ u ∈ ball (0 : Coeff 2) η,
      AnalyticOnNhd ℂ (fun E => (hillFilledFreeGapRoot h0q h0r (k : ℕ) (E,Coeff.periodDouble u))⁻¹)
        (closedBall (freeHillEnergy k) (k : ℝ)) ∧
      ∀ E ∈ closedBall (freeHillEnergy k) (k : ℝ),
        ‖(hillFilledFreeGapRoot h0q h0r (k : ℕ) (E,Coeff.periodDouble u))⁻¹‖ ≤ C*(k : ℝ) := by
  have hr : 0 < 1/(4*Real.pi) := by positivity
  have hrpi : 1/(4*Real.pi) ≤ Real.pi/4 := by
    apply (div_le_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
    nlinarith [Real.pi_gt_three]
  obtain ⟨δ,b,hδ,hb,_,hroot⟩ := exists_hillHminus_uniform_annular_root_bound _ hr hrpi
  obtain ⟨ε,hε,hprod⟩ := exists_hillRadiusEnergyCircle_all_root_product_matching h0q h0r
  obtain ⟨εQ,hεQ,_,hQ⟩ := exists_hillRadiusEnergyCircle_all_quadratic_data h0q h0r
  obtain ⟨εU,hεU,_,hU⟩ := exists_hillFilledFreeGapRoot_all_radius_data h0q h0r
  let ρ := min ε (min εQ εU)
  have hρ : 0 < ρ := lt_min hε (lt_min hεQ hεU)
  obtain ⟨θ,hθ,hsource0⟩ := exists_common_ball_linear_preimage periodOneL2Inclusion δ (ρ/2)
    hδ (by positivity) univ isOpen_univ (mem_univ _)
  let η := min θ ρ
  have hη : 0 < η := lt_min hθ hρ
  have hηρ : η ≤ ρ := min_le_right _ _
  have hsource (u : Coeff 2) (hu : u ∈ ball 0 η) :=
    hsource0 u (ball_subset_ball (min_le_left θ ρ) hu)
  have hsourceQ (u : Coeff 2) (hu : u ∈ ball 0 η) : Coeff.periodDouble u ∈ ball (0 : Coeff 2) εQ := by
    rw [mem_ball_zero_iff,Coeff.norm_periodDouble]
    exact (hsource u hu).2.2.trans_lt (by dsimp only [ρ]; have h := min_le_right ε (min εQ εU); have hh := min_le_left εQ εU; linarith)
  have hsourceU (u : Coeff 2) (hu : u ∈ ball 0 η) : Coeff.periodDouble u ∈ ball (0 : Coeff 2) εU := by
    rw [mem_ball_zero_iff,Coeff.norm_periodDouble]
    exact (hsource u hu).2.2.trans_lt (by dsimp only [ρ]; have h := min_le_right ε (min εQ εU); have hh := min_le_right εQ εU; linarith)
  have hboundary (u : Coeff 2) (hu : u ∈ ball 0 η) (k : ℕ+)
      (E : ℂ) (hE : E ∈ sphere (freeHillEnergy k) (k : ℝ)) :
      (E,periodOneL2Inclusion u) ∈ hillHminusContinuationDomain ∧
        b ≤ ‖hillHminusContinuedRoot (E,periodOneL2Inclusion u)‖ := by
    obtain ⟨hz,hfar⟩ := hillFreeEnergyCircle_frequency_bounds k E hE
    have hzq := closedBall_subset_closedBall (by linarith [Real.pi_pos] : Real.pi/8 ≤ Real.pi/4) hz
    have h := hroot _ (hsource u hu).1 k (sqrt E) hzq hfar
    simpa only [sq_sqrt] using h
  have hmatch := hprod η hη (hηρ.trans (min_le_left _ _)) (fun u hu k E hE => (hboundary u hu k E hE).1)
  refine ⟨η,2/b,hη,by positivity,?_⟩
  intro k u hu
  let U : ℂ → ℂ := fun E => hillFilledFreeGapRoot h0q h0r (k : ℕ) (E,Coeff.periodDouble u)
  have ha : AnalyticOnNhd ℂ (fun E => (U E)⁻¹) (closedBall (freeHillEnergy k) (k : ℝ)) := by
    intro E hE
    exact (((hU k).1 (E,Coeff.periodDouble u) ⟨hE,hsourceU u hu⟩).comp
      (f := fun E : ℂ => (E,Coeff.periodDouble u)) (analyticAt_id.prod analyticAt_const)).inv
      ((hU k).2 _ (hsourceU u hu) E hE).1
  refine ⟨ha,?_⟩
  have hbound (E : ℂ) (hE : E ∈ sphere (freeHillEnergy k) (k : ℝ)) : ‖(U E)⁻¹‖ ≤ (2/b)*(k : ℝ) := by
    let Q := hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,Coeff.periodDouble u)
    let S := hillHminusContinuedRoot (E,periodOneL2Inclusion u)
    have hd : (k : ℝ)/2 ≤ ‖E-freeHillEnergy k‖ := by rw [mem_sphere_iff_norm.mp hE]; linarith [show (0 : ℝ) < k by positivity]
    have hqn : Q ≠ 0 := ((hQ k).2.1 _ (hsourceQ u hu) E hd).2.1
    have hqb : ‖Q‖ ≤ 2*(k : ℝ) := by
      simpa only [mem_sphere_iff_norm.mp hE] using ((hQ k).2.1 _ (hsourceQ u hu) E hd).2.2.2
    have hpr : Q*U E = S := hmatch k u hu E hE
    have hi : (U E)⁻¹ = Q/S := by rw [← hpr,div_mul_eq_div_div,div_self hqn,one_div]
    rw [hi,norm_div]
    exact (div_le_div₀ (by positivity) hqb hb (hboundary u hu k E hE).2).trans_eq (by ring)
  intro E hE
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball (x := freeHillEnergy k) (r := (k : ℝ)))
    (DiffContOnCl.mk_ball (ha.differentiableOn.mono ball_subset_closedBall) ha.continuousOn)
  · intro w hw
    rw [frontier_ball _ (by positivity : (k : ℝ) ≠ 0)] at hw
    exact hbound w hw
  · rw [closure_ball _ (by positivity : (k : ℝ) ≠ 0)]
    exact hE

end NLS.KdV
