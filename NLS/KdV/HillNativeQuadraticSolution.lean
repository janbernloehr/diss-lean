import NLS.KdV.HillRadiusQuadraticData
import NLS.ComplexAnalysis.NativeBoundedQuadraticSolution

/-! # Native quadratic solutions on the actual high Hill gaps

The actual symmetric gap polynomial and literal quadratic root are used.
One cutoff precedes all bounded complex sources and all native numerators.
The filled solution has a full Hilbert norm bound of order `M/k`.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillRadius_native_quadratic_solutions
    (η B : ℝ)
    (hsource : ∀ u ∈ ball (0 : Coeff 2) η, Coeff.periodDouble u ∈ ball (0 : Coeff 2) B) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ k : ℕ+, N ≤ (k : ℕ) →
      ∀ g : ℂ × Coeff 2 → Coeff 2, ∀ M : ℝ, 0 ≤ M →
      AnalyticOnNhd ℂ g (closedBall (freeHillEnergy k) (k : ℝ) ×ˢ ball (0 : Coeff 2) η) →
      (∀ u ∈ ball (0 : Coeff 2) η, ∀ E ∈ closedBall (freeHillEnergy k) (k : ℝ), ‖g (E,u)‖ ≤ M) →
      (∀ u ∈ ball (0 : Coeff 2) η,
        (∮ E in C(freeHillEnergy k,(k : ℝ)),
          (hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,Coeff.periodDouble u))⁻¹ • g (E,u)) = 0) →
      ∃ H : ℂ × Coeff 2 → Coeff 2,
        AnalyticOnNhd ℂ H (ball (freeHillEnergy k) (3*(k : ℝ)/4) ×ˢ ball (0 : Coeff 2) η) ∧
        (∀ u ∈ ball (0 : Coeff 2) η, ∀ E ∈ ball (freeHillEnergy k) (3*(k : ℝ)/4),
          hillLocalGapPolynomial 0 h0q h0r (k : ℕ) (Coeff.periodDouble u) E • deriv (fun z => H (z,u)) E +
            (E-hillLocalGapMidpoint 0 h0q h0r (k : ℕ) (Coeff.periodDouble u)) • H (E,u) = g (E,u)) ∧
        ∀ u ∈ ball (0 : Coeff 2) η, ∀ E ∈ closedBall (freeHillEnergy k) ((k : ℝ)/4),
          ‖H (E,u)‖ ≤ 18*Real.pi*M/(k : ℝ) := by
  obtain ⟨N,hN,hQdata⟩ := exists_hillRadiusEnergyCircle_quadratic_data h0q h0r B
  refine ⟨N,hN,?_⟩
  intro k hk g M hM hg hbound hperiod
  have hkpos : (0 : ℝ) < k := by positivity
  let c := freeHillEnergy k
  let V := ball (0 : Coeff 2) η
  let K := closedBall c (k : ℝ) \ ball c ((k : ℝ)/2)
  let Q : ℂ × Coeff 2 → ℂ := fun t => hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (t.1,Coeff.periodDouble t.2)
  let τ := fun u => hillLocalGapMidpoint 0 h0q h0r (k : ℕ) (Coeff.periodDouble u)
  let s := fun u => hillLocalGapSquare 0 h0q h0r (k : ℕ) (Coeff.periodDouble u)/4
  have hdist (E : ℂ) (hE : E ∈ K) : (k : ℝ)/2 ≤ ‖E-c‖ := by
    simpa only [mem_ball_iff_norm, not_lt] using hE.2
  have hQa : AnalyticOnNhd ℂ Q (K ×ˢ V) := by
    intro t ht
    exact ((hQdata k hk).1 (t.1,Coeff.periodDouble t.2)
      ⟨hdist t.1 ht.1,hsource t.2 ht.2⟩).comp
        (f := fun t : ℂ × Coeff 2 => (t.1,Coeff.periodDouble t.2))
        (analyticAt_fst.prod ((Coeff.periodDouble.toContinuousLinearMap.analyticAt t.2).comp analyticAt_snd))
  have hd (u : Coeff 2) (hu : u ∈ V) (E : ℂ) (hE : E ∈ K) :=
    (hQdata k hk).2.1 _ (hsource u hu) E (hdist E hE)
  have hD : AnalyticOnNhd ℂ (fun t => (Q t)⁻¹ • g t) (K ×ˢ V) := by
    intro t ht
    exact ((hQa t ht).inv (hd t.2 ht.2 t.1 ht.1).2.1).smul (hg t ⟨ht.1.1,ht.2⟩)
  have hpinner (u : Coeff 2) (hu : u ∈ V) :
      (∮ E in C(c,(k : ℝ)/2), (Q (E,u))⁻¹ • g (E,u)) = 0 := by
    have hslice : AnalyticOnNhd ℂ (fun E => (Q (E,u))⁻¹ • g (E,u)) K := by
      intro E hE
      exact (hD (E,u) ⟨hE,hu⟩).comp (f := fun E : ℂ => (E,u))
        (analyticAt_id.prod analyticAt_const)
    have he := Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      (show 0 < (k : ℝ)/2 by positivity) (show (k : ℝ)/2 ≤ k by linarith)
      (s := ∅) countable_empty hslice.continuousOn (by
        intro E hE
        exact (hslice E ⟨ball_subset_closedBall hE.1.1,
          fun h => hE.1.2 (ball_subset_closedBall h)⟩).differentiableAt)
    rw [← he]
    exact hperiod u hu
  have hcircle (E : ℂ) (hE : E ∈ sphere c (3*(k : ℝ)/4)) : E ∈ K := by
    have hh := mem_sphere.mp hE
    exact ⟨mem_closedBall.mpr (by linarith),fun h => by
      have ht := mem_ball.mp h
      linarith⟩
  have hQlower (u : Coeff 2) (hu : u ∈ V) (E : ℂ) (hE : E ∈ sphere c (3*(k : ℝ)/4)) :
      (k : ℝ)/4 ≤ ‖Q (E,u)‖ := by
    have hh := (hd u hu E (hcircle E hE)).2.2.1
    rw [mem_sphere_iff_norm.mp hE] at hh
    change (k : ℝ)/4 ≤ ‖hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,Coeff.periodDouble u)‖
    linarith
  have hDbound (u : Coeff 2) (hu : u ∈ V) (E : ℂ) (hE : E ∈ sphere c (3*(k : ℝ)/4)) :
      ‖(Q (E,u))⁻¹ • g (E,u)‖ ≤ 4*M/(k : ℝ) := by
    rw [norm_smul,norm_inv,← div_eq_inv_mul]
    have hh := div_le_div₀ hM (hbound u hu E (hcircle E hE).1)
      (show 0 < (k : ℝ)/4 by positivity) (hQlower u hu E hE)
    exact hh.trans_eq (by field_simp)
  obtain ⟨H,hHa,hHeq,hHb⟩ := exists_bounded_native_quadratic_solution_of_zero_period
    g Q τ s c ((k : ℝ)/2) (3*(k : ℝ)/4) (k : ℝ) ((k : ℝ)/4) ((k : ℝ)/4) (4*M/(k : ℝ))
    (by linarith) (by positivity) (by positivity) (by positivity) (by linarith) (by linarith)
    V isOpen_ball hg hQa (fun u hu E hE => (hd u hu E hE).2.1)
    (fun u hu E hE => (hd u hu E hE).1) hpinner hQlower hDbound
  refine ⟨H,hHa,hHeq,?_⟩
  intro u hu E hE
  have hh := hHb u hu E hE
  convert hh using 1
  field_simp
  ring

end NLS.KdV
