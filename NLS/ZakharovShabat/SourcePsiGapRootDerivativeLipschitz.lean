import NLS.ZakharovShabat.SourcePsiGapRootMap
import NLS.ComplexAnalysis.BanachHolomorphicC1

/-!
# Local derivative bound for the canonical gap roots

The complex local branch of the canonical gap-root map is holomorphic.
The Banach-space Cauchy estimate makes its Fréchet derivative locally
Lipschitz in operator norm. This gives quantitative regularity around
every real-type source, including on nearby real-type points where the
branch equals the canonical root map.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat

/-- Around each real-type source, the canonical roots have a complex
local branch whose derivative is Lipschitz in operator norm. -/
theorem exists_local_lipschitz_fderiv_sourcePsiGapRoot
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : realTypeSourceLocus p) :
    ∃ s : CoeffPair p → DeletedCoeff p n,
      s φ.val = sourcePsiGapRoot hp hp1 n φ ∧
      ∃ R K : ℝ, 0 < R ∧ 0 ≤ K ∧
        DifferentiableOn ℂ s (ball φ.val R) ∧
        (∀ χ ∈ ball φ.val R,
          ∀ hχ : IsRealType (CoeffPair.toMax p χ),
            s χ = sourcePsiGapRoot hp hp1 n ⟨χ,hχ⟩) ∧
        ∀ χ ∈ ball φ.val R, ∀ ψ ∈ ball φ.val R,
          ‖fderiv ℂ s χ - fderiv ℂ s ψ‖ ≤ K * ‖χ - ψ‖ := by
  obtain ⟨s,hs,hsφ,hbranch⟩ :=
    exists_C1_local_extension_sourcePsiGapRoot hp hp1 n φ
  obtain ⟨δ,hδ,hδball⟩ := Metric.mem_nhds_iff.mp hbranch
  obtain ⟨U,hUopen,hφU,hC1raw⟩ := hs.contDiffOn' le_rfl (by simp)
  have hC1 : ContDiffOn ℂ 1 s U := by
    simpa only [insert_eq_of_mem (mem_univ φ.val),univ_inter] using hC1raw
  obtain ⟨R₀,hR₀,hUball⟩ := Metric.isOpen_iff.mp hUopen φ.val hφU
  obtain ⟨R₁,hR₁,hFball⟩ := Metric.mem_nhds_iff.mp
    (hs.continuousAt (ball_mem_nhds (s φ.val) (by norm_num : (0 : ℝ) < 1)))
  let R : ℝ := min (min R₀ R₁) δ / 4
  have hR : 0 < R := by dsimp [R]; positivity
  have hR4 : 4 * R = min (min R₀ R₁) δ := by dsimp [R]; ring
  have hballU : ball φ.val (4 * R) ⊆ U := by
    apply (ball_subset_ball ?_).trans hUball
    rw [hR4]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hballF : ball φ.val (4 * R) ⊆ ball φ.val R₁ := by
    apply ball_subset_ball
    rw [hR4]
    exact (min_le_left _ _).trans (min_le_right _ _)
  let M : ℝ := ‖s φ.val‖ + 1
  have hbound : ∀ z ∈ ball φ.val (4 * R), ‖s z‖ ≤ M := by
    intro z hz
    have hzF : ‖s z - s φ.val‖ < 1 := by
      simpa only [Set.mem_preimage, mem_ball, dist_eq_norm] using
        hFball (hballF hz)
    have h := norm_le_norm_sub_add (s z) (s φ.val)
    change ‖s z‖ ≤ ‖s φ.val‖ + 1
    linarith only [h, hzF]
  let K : ℝ := 4 * M / R ^ 2
  have hK : 0 ≤ K := by dsimp [K, M]; positivity
  have hballSmall : ball φ.val R ⊆ U := by
    apply (ball_subset_ball ?_).trans hballU
    nlinarith [hR]
  refine ⟨s,hsφ,R,K,hR,hK,
    hC1.differentiableOn_one.mono hballSmall,?_,?_⟩
  · intro χ hχ hreal
    have hχδ : χ ∈ ball φ.val δ := by
      apply (ball_subset_ball ?_) hχ
      have hle : R ≤ δ / 4 := by
        dsimp [R]
        exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      linarith
    exact hδball hχδ hreal
  · intro χ hχ ψ hψ
    simpa only [K] using
      NLS.ComplexAnalysis.norm_fderiv_sub_le_of_holomorphic_ball_bound
        s φ.val R M hR (hC1.differentiableOn_one.mono hballU)
        hbound hψ hχ

/-- The canonical gap roots admit a local complex first-order
approximation with a quadratic remainder. At real-type endpoints,
the value of the branch is the canonical gap-root vector. -/
theorem exists_local_quadratic_remainder_sourcePsiGapRoot
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : realTypeSourceLocus p) :
    ∃ s : CoeffPair p → DeletedCoeff p n,
      s φ.val = sourcePsiGapRoot hp hp1 n φ ∧
      DifferentiableAt ℂ s φ.val ∧
      ∃ R K : ℝ, 0 < R ∧ 0 ≤ K ∧
        (∀ χ ∈ ball φ.val R,
          ∀ hχ : IsRealType (CoeffPair.toMax p χ),
            s χ = sourcePsiGapRoot hp hp1 n ⟨χ,hχ⟩) ∧
        ∀ χ ∈ ball φ.val R,
          ‖s χ - s φ.val - (fderiv ℂ s φ.val) (χ - φ.val)‖ ≤
            K * ‖χ - φ.val‖ ^ 2 := by
  obtain ⟨s,hsφ,R,K,hR,hK,hdiff,hreal,hLip⟩ :=
    exists_local_lipschitz_fderiv_sourcePsiGapRoot hp hp1 n φ
  have hsDiff : DifferentiableAt ℂ s φ.val :=
    (hdiff φ.val (mem_ball_self hR)).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self hR))
  refine ⟨s,hsφ,hsDiff,R,K,hR,hK,hreal,?_⟩
  intro χ hχ
  let ρ : ℝ := ‖χ - φ.val‖
  have hρR : ρ < R := by
    simpa only [ρ, mem_ball, dist_eq_norm] using hχ
  have hclosed : closedBall φ.val ρ ⊆ ball φ.val R :=
    closedBall_subset_ball hρR
  have hφclosed : φ.val ∈ closedBall φ.val ρ := by
    exact mem_closedBall_self (norm_nonneg _)
  have hχclosed : χ ∈ closedBall φ.val ρ := by
    simp only [mem_closedBall, dist_eq_norm]
    exact le_rfl
  have hdiffAt (z : CoeffPair p) (hz : z ∈ closedBall φ.val ρ) :
      DifferentiableAt ℂ s z :=
    (hdiff z (hclosed hz)).differentiableAt
      (isOpen_ball.mem_nhds (hclosed hz))
  have hbound (z : CoeffPair p) (hz : z ∈ closedBall φ.val ρ) :
      ‖fderiv ℂ s z - fderiv ℂ s φ.val‖ ≤ K * ρ := by
    have hzρ : ‖z - φ.val‖ ≤ ρ := by
      simpa only [mem_closedBall, dist_eq_norm] using hz
    exact (hLip z (hclosed hz) φ.val (mem_ball_self hR)).trans
      (mul_le_mul_of_nonneg_left hzρ hK)
  have hmv := (convex_closedBall φ.val ρ).norm_image_sub_le_of_norm_fderiv_le'
    hdiffAt hbound hφclosed hχclosed
  simpa only [ρ, pow_two, mul_assoc] using hmv

/-- The same quadratic remainder directly estimates the canonical
root vector on the real-type source locus. Its linear term is the
complex derivative of a local branch. -/
theorem exists_local_quadratic_remainder_sourcePsiGapRoot_real
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : realTypeSourceLocus p) :
    ∃ L : CoeffPair p →L[ℂ] DeletedCoeff p n,
      ∃ R K : ℝ, 0 < R ∧ 0 ≤ K ∧
        ∀ χ ∈ ball φ.val R,
          ∀ hχ : IsRealType (CoeffPair.toMax p χ),
            ‖sourcePsiGapRoot hp hp1 n ⟨χ,hχ⟩ -
                sourcePsiGapRoot hp hp1 n φ - L (χ - φ.val)‖ ≤
              K * ‖χ - φ.val‖ ^ 2 := by
  obtain ⟨s,hsφ,_,R,K,hR,hK,hreal,hbound⟩ :=
    exists_local_quadratic_remainder_sourcePsiGapRoot hp hp1 n φ
  refine ⟨fderiv ℂ s φ.val,R,K,hR,hK,?_⟩
  intro χ hχ hχreal
  simpa only [hreal χ hχ hχreal,hsφ] using hbound χ hχ

end NLS.ZakharovShabat
