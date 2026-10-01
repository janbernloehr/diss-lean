import NLS.ZakharovShabat.PowerTailBallBudget
import NLS.ZakharovShabat.WeightedResonantCenterRemainderAnalytic
import NLS.ComplexAnalysis.BanachHolomorphicC1

/-!
# Small derivatives of the actual closing remainder on a fixed ball

The quantitative remainder budget gives a bound proportional to the
square of a chosen source radius. Schwarz estimates then make its full
Fréchet derivative arbitrarily small on a fixed smaller ball, for every
larger cutoff. The derivative is also Lipschitz there, with an explicit
constant independent of the chosen radius.

These estimates concern the actual sequence remainder with its original
component-sum norm. They do not assume a small derivative or an inverse,
and do not yet solve the simultaneous closing equations.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The fixed-ball quadratic remainder constant at a source norm bound. -/
def resonantCenterRemainderBallConstant (p : ℝ≥0∞) (M : ℝ) : ℝ :=
  ((offDiagonalSummationConstant p+1)*M^p.toReal*(1+5^(2*p.toReal)))^(1/p.toReal)

omit [Fact (1 ≤ p)] in
/-- The explicit quadratic constant is positive at a positive source
norm bound. -/
theorem resonantCenterRemainderBallConstant_pos (M : ℝ) (hM : 0 < M) :
    0 < resonantCenterRemainderBallConstant p M := by
  have hC := offDiagonalSummationConstant_nonneg p
  dsimp [resonantCenterRemainderBallConstant]
  positivity

/-- Raising the quadratic constant to the source exponent recovers
the exact power budget. -/
theorem resonantCenterRemainderBallConstant_rpow (hp : p ≠ ⊤) (M : ℝ) (hM : 0 < M) :
    (resonantCenterRemainderBallConstant p M)^p.toReal =
      (offDiagonalSummationConstant p+1)*M^p.toReal*(1+5^(2*p.toReal)) := by
  have hP : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
  have hC := offDiagonalSummationConstant_nonneg p
  dsimp [resonantCenterRemainderBallConstant]
  rw [← Real.rpow_mul (by positivity),one_div_mul_cancel hP.ne',Real.rpow_one]

/-- At every source, one positive fixed radius gives arbitrarily small
actual remainder derivatives and a Lipschitz derivative bound, uniformly
for every larger cutoff. The fourfold ball retains the exact coefficients
and the quadratic norm estimate used to prove these conclusions. -/
theorem exists_fixedBall_weightedResonantCenterRemainder_derivative
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (η : ℝ) (hη : 0 < η) :
    let K := resonantCenterRemainderBallConstant p (‖φ‖+1);
    ∃ r : ℝ, 0 < r ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      AnalyticOnNhd ℂ (fun ψ => weightedResonantCenterRemainder hp w ψ N) (ball φ (4*r)) ∧
      (∀ ψ ∈ ball φ (4*r),
        (∀ positive : Bool, Memℓp (weightedResonantCenterRemainderCoordinate hp w ψ N positive) p) ∧
        ‖weightedResonantCenterRemainder hp w ψ N‖ ≤ K*r^2) ∧
      (∀ ψ ∈ ball φ (3*r),
        ‖fderiv ℂ (fun χ => weightedResonantCenterRemainder hp w χ N) ψ‖ < η) ∧
      (∀ x ∈ ball φ (3*r), ∀ y ∈ ball φ (3*r),
        ‖weightedResonantCenterRemainder hp w y N-weightedResonantCenterRemainder hp w x N‖ ≤ η*‖y-x‖) ∧
      ∀ x ∈ ball φ r, ∀ y ∈ ball φ r,
        ‖fderiv ℂ (fun χ => weightedResonantCenterRemainder hp w χ N) y-
          fderiv ℂ (fun χ => weightedResonantCenterRemainder hp w χ N) x‖ ≤ 4*K*‖y-x‖ := by
  let M := ‖φ‖+1
  let K := resonantCenterRemainderBallConstant p M
  have hM : 0 < M := by dsimp [M]; positivity
  have hK : 0 < K := resonantCenterRemainderBallConstant_pos M hM
  have hP : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
  have hP1 : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  obtain ⟨N₁,hN₁,U₁,ho₁,_,hφ₁,_,h₁⟩ :=
    exists_uniform_analytic_weightedResonantCenterRemainder hp hp1 w φ 1 (by norm_num)
  obtain ⟨N₂,_,U₂,ho₂,_,hφ₂,_,h₂⟩ :=
    exists_uniform_weightedResonantCenterRemainder_bound hp hp1 w φ
  obtain ⟨ρ,hρ,hρsub⟩ := Metric.mem_nhds_iff.mp
    ((ho₁.inter ho₂).mem_nhds (show φ ∈ U₁ ∩ U₂ from ⟨hφ₁,hφ₂⟩))
  let r := min (ρ/8) (min (1/8) (η/(8*K)))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrρ : 4*r ≤ ρ := by have h := min_le_left (ρ/8) (min (1/8) (η/(8*K))); change r ≤ ρ/8 at h; linarith
  have hr1 : 4*r ≤ 1 := by
    have h := (min_le_right (ρ/8) (min (1/8) (η/(8*K)))).trans (min_le_left (1/8) (η/(8*K)))
    change r ≤ 1/8 at h
    linarith
  have hrη : 2*K*r < η := by
    have h := (min_le_right (ρ/8) (min (1/8) (η/(8*K)))).trans (min_le_right (1/8) (η/(8*K)))
    change r ≤ η/(8*K) at h
    have he := (le_div_iff₀ (by positivity : 0 < 8*K)).mp h
    nlinarith
  have hsub : ball φ (4*r) ⊆ U₁ ∩ U₂ := fun ψ hψ => hρsub (ball_subset_ball hrρ hψ)
  obtain ⟨N₃,_,h₃⟩ := exists_fixedBall_powerTail_budget hp w φ M r (2*p.toReal)
    (min 1 (p.toReal-1)) hr (by positivity) (by positivity)
  refine ⟨r,hr,max N₁ (max N₂ N₃),hN₁.trans (le_max_left _ _),?_⟩
  intro N hN
  have hA : AnalyticOnNhd ℂ (fun ψ => weightedResonantCenterRemainder hp w ψ N) (ball φ (4*r)) :=
    fun ψ hψ => (h₁ N (by omega)).1 ψ (hsub hψ).1
  have hdata (ψ : WeightedCoeffPair w.toWeight p) (hψ : ψ ∈ ball φ (4*r)) :
      (∀ positive : Bool, Memℓp (weightedResonantCenterRemainderCoordinate hp w ψ N positive) p) ∧
      ‖weightedResonantCenterRemainder hp w ψ N‖ ≤ K*r^2 := by
    have hb := h₂ ψ (hsub hψ).2 N (by omega)
    have hψM : ‖ψ‖ ≤ M := by
      have hdist : ‖ψ-φ‖ < 4*r := by simpa only [mem_ball,dist_eq_norm] using hψ
      have hnorm := norm_le_norm_sub_add ψ φ
      dsimp [M]
      linarith
    have hC := offDiagonalSummationConstant_nonneg p
    have hpower : ‖weightedResonantCenterRemainder hp w ψ N‖^p.toReal ≤ (K*r^2)^p.toReal := by
      apply hb.2.trans
      calc
        _ ≤ (offDiagonalSummationConstant p+1)*M^p.toReal*
            (M^(2*p.toReal)/(N : ℝ)^(min 1 (p.toReal-1))+
              ‖weightedPairFourierTail w.toWeight (N/2) ψ‖^(2*p.toReal)) := by gcongr; linarith
        _ ≤ (offDiagonalSummationConstant p+1)*M^p.toReal*((1+5^(2*p.toReal))*r^(2*p.toReal)) :=
          mul_le_mul_of_nonneg_left (h₃ N (by omega) ψ hψ) (by positivity)
        _ = (K*r^2)^p.toReal := by
          have hrpow : (r^2)^p.toReal = r^(2*p.toReal) := by
            rw [← Real.rpow_natCast,← Real.rpow_mul hr.le]
            norm_num
          rw [Real.mul_rpow hK.le (sq_nonneg r),resonantCenterRemainderBallConstant_rpow hp M hM,hrpow]
          ring
    exact ⟨hb.1,(Real.rpow_le_rpow_iff (norm_nonneg _) (by positivity) hP).mp hpower⟩
  have hinner : ball φ (3*r) ⊆ ball φ (4*r) := ball_subset_ball (by linarith)
  have hAt (ψ : WeightedCoeffPair w.toWeight p) (hψ : ψ ∈ ball φ (3*r)) :
      DifferentiableAt ℂ (fun χ => weightedResonantCenterRemainder hp w χ N) ψ :=
    (hA ψ (hinner hψ)).differentiableAt
  have hder (ψ : WeightedCoeffPair w.toWeight p) (hψ : ψ ∈ ball φ (3*r)) :
      ‖fderiv ℂ (fun χ => weightedResonantCenterRemainder hp w χ N) ψ‖ < η := by
    have houter : 3*r+r = 4*r := by ring
    have hb := NLS.ComplexAnalysis.norm_fderiv_le_of_ball_bound
      (fun χ => weightedResonantCenterRemainder hp w χ N) φ ψ (3*r) r (K*r^2) hr
      (by simpa only [houter] using hA.differentiableOn)
      (fun χ hχ => (hdata χ (by simpa only [houter] using hχ)).2) hψ
    apply hb.trans_lt
    have he : 2*(K*r^2)/r = 2*K*r := by field_simp
    simpa only [he] using hrη
  refine ⟨hA,hdata,hder,?_,?_⟩
  · intro x hx y hy
    exact (convex_ball φ (3*r)).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ)
      (f := fun χ => weightedResonantCenterRemainder hp w χ N) hAt
      (fun ψ hψ => (hder ψ hψ).le) hx hy
  · intro x hx y hy
    have hb := NLS.ComplexAnalysis.norm_fderiv_sub_le_of_holomorphic_ball_bound
      (fun χ => weightedResonantCenterRemainder hp w χ N) φ r (K*r^2) hr
      hA.differentiableOn (fun ψ hψ => (hdata ψ hψ).2) hx hy
    have he : 4*(K*r^2)/r^2 = 4*K := by field_simp
    simpa only [he] using hb

end NLS.ZakharovShabat
