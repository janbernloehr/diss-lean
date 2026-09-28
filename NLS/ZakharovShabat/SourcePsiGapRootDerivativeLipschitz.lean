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
  refine ⟨s,hsφ,R,K,hR,hK,?_,?_⟩
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

end NLS.ZakharovShabat
