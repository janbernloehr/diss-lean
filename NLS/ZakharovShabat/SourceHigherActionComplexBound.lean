import NLS.ZakharovShabat.SourceHigherActionComplexCosine
import NLS.ZakharovShabat.SourceFullAbelianAllGapBound

/-! # Complex higher-action bounds from gap width and spectral size -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An upper bound for the modulus of every point on the selected segment. -/
def sourceGapSpectralRadius (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) : ℝ :=
  ‖sourceStandardRootMidpoint hp hp1 ψ n‖ + ‖sourceStandardRootHalfGap hp hp1 ψ n‖

theorem norm_sourceGapCosinePoint_le (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) (θ : ℝ) :
    ‖sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ:ℂ)‖ ≤
      sourceGapSpectralRadius hp hp1 ψ n := by
  have hc : ‖(Real.cos θ:ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one θ
  exact (norm_add_le _ _).trans (add_le_add le_rfl
    ((norm_mul _ _).le.trans ((mul_le_mul_of_nonneg_left hc (norm_nonneg _)).trans_eq (mul_one _))))

/-- Integrating the boundary bound gives one gap factor and one spectral power. -/
theorem SourceFullAbelianUniformCauchyFamily.norm_higherActionBoundaryIntegral_le
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (ψ : CoeffPair p) (n : ℤ) (k : ℕ)
    (B : ℝ) (hb : ∀ θ ∈ Icc (0:ℝ) Real.pi, ‖C.gapBoundary n ψ θ true‖ ≤ B) :
    ‖(2/Real.pi:ℂ)*∫ θ in (0:ℝ)..Real.pi,
      (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ:ℂ))^k *
      ((sourceStandardRootHalfGap hp hp1 ψ n*(Real.sin θ:ℂ))*C.gapBoundary n ψ θ true)‖ ≤
        sourceGapSpectralRadius hp hp1 ψ n ^ k *
        ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖ * B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hb 0 ⟨le_rfl,Real.pi_pos.le⟩)
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := Real.pi)
    (f := fun θ => (sourceStandardRootMidpoint hp hp1 ψ n+
      sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ:ℂ))^k *
      ((sourceStandardRootHalfGap hp hp1 ψ n*(Real.sin θ:ℂ))*C.gapBoundary n ψ θ true))
    (C := sourceGapSpectralRadius hp hp1 ψ n ^ k * (‖sourceStandardRootHalfGap hp hp1 ψ n‖*B)) (by
      intro θ hθ
      rw [uIoc_of_le Real.pi_pos.le] at hθ
      have hs : ‖(Real.sin θ:ℂ)‖ ≤ 1 := by
        simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_sin_le_one θ
      simp only [norm_mul,norm_pow]
      apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (norm_sourceGapCosinePoint_le hp hp1 ψ n θ) k)
      · exact (mul_le_mul (mul_le_mul_of_nonneg_left hs (norm_nonneg _))
          (hb θ ⟨hθ.1.le,hθ.2⟩) (norm_nonneg _) (by positivity)).trans_eq (by rw [mul_one])
      · positivity
      · exact pow_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) k)
  simp only [sub_zero,abs_of_pos Real.pi_pos] at hint
  have hn : ‖(2/Real.pi:ℂ)‖ = 2/Real.pi := by
    simp only [norm_div,norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [norm_mul,hn]
  calc
    _ ≤ (2/Real.pi) * ((sourceGapSpectralRadius hp hp1 ψ n ^ k *
        (‖sourceStandardRootHalfGap hp hp1 ψ n‖*B))*Real.pi) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by
      simp only [sourceStandardRootHalfGap,norm_div,norm_ofNat]
      field_simp

namespace SourceHigherActionAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} (A : SourceHigherActionAtlas hp hp1)

/-- One neighborhood and one constant control all complex higher actions
by the squared gap and the appropriate spectral power. -/
theorem exists_local_all_actions_gap_bound (φ : realTypeSourceSubmodule p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧ U ⊆ A.domain ∧ ∃ B : ℝ, 0 < B ∧
      ∀ ψ ∈ U, ∀ (n : ℤ) (k : ℕ), ‖A.action n k ψ‖ ≤
        B * sourceGapSpectralRadius hp hp1 ψ n ^ k *
        ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2 := by
  obtain ⟨W,_,_,hlocal⟩ := exists_sourceFullAbelian_all_gap_bound hp hp1
  obtain ⟨C,V,hV,hφV,hVC,B,hB,hb⟩ := hlocal φ
  obtain ⟨r,hr,hsub,hformula⟩ := A.exists_ball_all_actions_eq_boundaryIntegral C φ (hVC hφV)
  refine ⟨V ∩ ball φ.val r,hV.inter isOpen_ball,⟨hφV,mem_ball_self hr⟩,
    fun ψ hψ => (hsub hψ.2).1,B,hB,?_⟩
  intro ψ hψ n k
  rw [hformula ψ hψ.2 n k]
  have h := C.norm_higherActionBoundaryIntegral_le ψ n k _ (fun θ hθ => hb ψ hψ.1 n θ hθ true)
  rw [← sourcePeriodicGapDisplacement_apply hp hp1 ψ n] at h
  exact h.trans_eq (by ring)

end SourceHigherActionAtlas
end NLS.ZakharovShabat
