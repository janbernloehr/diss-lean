import NLS.ZakharovShabat.SourceDiagonalReciprocalGapBound
import NLS.ZakharovShabat.SourceFullAbelianAllGapBound

/-! # The uniform inverse-frequency bound for the physical action level

The actual Laurent level zero has one reciprocal frequency and two
powers of the gap. One complex neighborhood and one constant work for
every noncentral signed index, including collapsed complex gaps.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem norm_inverseWeighted_boundaryIntegral_le
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (ψ : CoeffPair p) (n : ℤ)
    (B D : ℝ) (hD : 0 ≤ D)
    (hb : ∀ θ ∈ Icc (0 : ℝ) Real.pi, ‖C.gapBoundary n ψ θ true‖ ≤
      B*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖)
    (hw : ∀ θ ∈ Icc (0 : ℝ) Real.pi,
      ‖(sourceStandardRootMidpoint hp hp1 ψ n+
        sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ : ℂ))⁻¹‖ ≤ D) :
    ‖(2/Real.pi : ℂ)*∫ θ in (0 : ℝ)..Real.pi,
      (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ : ℂ))⁻¹ *
        ((sourceStandardRootHalfGap hp hp1 ψ n*(Real.sin θ : ℂ))*C.gapBoundary n ψ θ true)‖ ≤
      D*B*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2 := by
  let G := ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := Real.pi)
    (f := fun θ => (sourceStandardRootMidpoint hp hp1 ψ n+
      sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ : ℂ))⁻¹ *
        ((sourceStandardRootHalfGap hp hp1 ψ n*(Real.sin θ : ℂ))*C.gapBoundary n ψ θ true))
    (C := D*(‖sourceStandardRootHalfGap hp hp1 ψ n‖*(B*G))) (by
      intro θ hθ
      rw [uIoc_of_le Real.pi_pos.le] at hθ
      have hs : ‖(Real.sin θ : ℂ)‖ ≤ 1 := by
        simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_sin_le_one θ
      have hhalf : ‖sourceStandardRootHalfGap hp hp1 ψ n*(Real.sin θ : ℂ)‖ ≤
          ‖sourceStandardRootHalfGap hp hp1 ψ n‖ := by
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_left hs (norm_nonneg _)).trans_eq (mul_one _)
      rw [norm_mul,norm_mul]
      exact mul_le_mul (hw θ ⟨hθ.1.le,hθ.2⟩)
        (mul_le_mul hhalf (hb θ ⟨hθ.1.le,hθ.2⟩) (norm_nonneg _) (norm_nonneg _))
        (by positivity) hD)
  have hhalf : ‖sourceStandardRootHalfGap hp hp1 ψ n‖ = G/2 := by
    simp only [G,sourceStandardRootHalfGap,sourcePeriodicGapDisplacement_apply,norm_div,norm_ofNat]
  have hn : ‖(2/Real.pi : ℂ)‖ = 2/Real.pi := by
    simp only [norm_div,norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [norm_mul,hn]
  calc
    _ ≤ (2/Real.pi)*(D*(‖sourceStandardRootHalfGap hp hp1 ψ n‖*(B*G))*Real.pi) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [sub_zero,abs_of_pos Real.pi_pos] using hint
    _ = _ := by rw [hhalf]; field_simp; ring

end SourceFullAbelianUniformCauchyFamily
namespace SourceDiagonalLaurentAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p}

theorem exists_local_zeroLevel_inverse_frequency_bound
    (A : SourceDiagonalLaurentAtlas hp hp1) (φ : realDiagonalSourceLocus p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧ U ⊆ A.domain ∧
      ∃ K : ℝ, 0 < K ∧ ∀ ψ ∈ U, ∀ n : ℤ, n ≠ 0 →
        ‖A.action n 0 ψ‖ ≤ K/(1+|(n : ℝ)|)*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2 := by
  obtain ⟨W,_,_,hlocal⟩ := exists_sourceFullAbelian_all_gap_bound hp hp1
  obtain ⟨C,V,hV,hφV,hVC,B,hB,hb⟩ := hlocal ⟨φ.val,φ.property.1⟩
  obtain ⟨D,hD,hd⟩ := C.exists_diagonal_gapPoint_inverse_bound φ (hVC hφV)
  obtain ⟨r,hr,hsub,hformula⟩ := A.exists_ball_all_laurent_actions_eq_boundaryIntegral C φ (hVC hφV)
  refine ⟨V ∩ ball φ.val r,hV.inter isOpen_ball,⟨hφV,mem_ball_self hr⟩,
    fun ψ hψ => (hsub hψ.2).1,D*B,mul_pos hD hB,?_⟩
  intro ψ hψ n hn
  rw [hformula ψ hψ.2 n hn 0]
  simp only [zero_sub,zpow_neg_one]
  have he := C.norm_inverseWeighted_boundaryIntegral_le ψ n B (D/(1+|(n : ℝ)|))
    (by positivity) (by
      intro θ hθ
      simpa only [sourcePeriodicGapDisplacement_apply] using hb ψ hψ.1 n θ hθ true)
    (fun θ _ => hd ψ (hVC hψ.1) n hn θ)
  exact he.trans_eq (by ring)

end SourceDiagonalLaurentAtlas
end NLS.ZakharovShabat
