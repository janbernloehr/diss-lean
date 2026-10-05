import NLS.ZakharovShabat.SourcePrimitivePowerComplexCosine
import NLS.ZakharovShabat.SourceFullAbelianAllGapBound
import NLS.ZakharovShabat.SourcePrimitivePowerPositive

/-! # Uniform complex gap bounds for primitive-power moments

One connected open neighborhood of the full real source locus supports
the bound in Lemma 21.1(iii), locally uniformly at every complex source
and uniformly over all signed indices and all natural orders.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Integrating a bounded boundary power supplies one gap-width factor. -/
theorem SourceFullAbelianUniformCauchyFamily.norm_powerBoundaryIntegral_le
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (ψ : CoeffPair p) (n : ℤ) (m : ℕ)
    (B : ℝ) (hb : ∀ θ ∈ Icc (0:ℝ) Real.pi, ‖C.gapBoundary n ψ θ true‖ ≤ B) :
    ‖(2/Real.pi:ℂ)*∫ θ in (0:ℝ)..Real.pi,
      (sourceStandardRootHalfGap hp hp1 ψ n*(Real.sin θ:ℂ))*(C.gapBoundary n ψ θ true)^(2*m+1)‖ ≤
        ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖*B^(2*m+1) := by
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := Real.pi)
    (f := fun θ => (sourceStandardRootHalfGap hp hp1 ψ n*(Real.sin θ:ℂ))*(C.gapBoundary n ψ θ true)^(2*m+1))
    (C := ‖sourceStandardRootHalfGap hp hp1 ψ n‖*B^(2*m+1)) (by
      intro θ hθ
      rw [uIoc_of_le Real.pi_pos.le] at hθ
      have hs : ‖(Real.sin θ:ℂ)‖ ≤ 1 := by
        simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_sin_le_one θ
      simp only [norm_mul,norm_pow]
      exact (mul_le_mul (mul_le_mul_of_nonneg_left hs (norm_nonneg _))
        (pow_le_pow_left₀ (norm_nonneg _) (hb θ ⟨hθ.1.le,hθ.2⟩) _)
        (pow_nonneg (norm_nonneg _) _) (mul_nonneg (norm_nonneg _) zero_le_one)).trans_eq (by rw [mul_one]))
  simp only [sub_zero,abs_of_pos Real.pi_pos] at hint
  have hn : ‖(2/Real.pi:ℂ)‖ = 2/Real.pi := by
    simp only [norm_div,norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  have hhalf : ‖sourceStandardRootHalfGap hp hp1 ψ n‖ =
      ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖/2 := by
    simp only [sourceStandardRootHalfGap,norm_div,norm_ofNat]
  rw [norm_mul,hn]
  calc
    _ ≤ (2/Real.pi) * ((‖sourceStandardRootHalfGap hp hp1 ψ n‖*B^(2*m+1))*Real.pi) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by rw [hhalf]; field_simp

namespace SourcePrimitivePowerAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (A : SourcePrimitivePowerAtlas hp hp1 W)

/-- Every real source has a complex neighborhood controlling all moments
and all gaps with one positive constant. -/
theorem exists_local_all_moments_power_bound (φ : realTypeSourceSubmodule p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧ U ⊆ A.domain ∧ ∃ B : ℝ, 0 < B ∧
      ∀ ψ ∈ U, ∀ (n : ℤ) (m : ℕ), ‖A.moment n m ψ‖ ≤ B^m *
        ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖^(m+1) := by
  obtain ⟨V,_,_,hlocal⟩ := exists_sourceFullAbelian_all_gap_bound hp hp1
  obtain ⟨C,U,hU,hφU,hUC,B,hB,hb⟩ := hlocal φ
  obtain ⟨r,hr,hsub,hformula⟩ := A.exists_ball_all_odd_moments_eq_boundaryIntegral C φ (hUC hφU)
  refine ⟨U ∩ ball φ.val r,hU.inter isOpen_ball,⟨hφU,mem_ball_self hr⟩,
    fun ψ hψ => (hsub hψ.2).1,B,hB,?_⟩
  intro ψ hψ n m
  obtain ⟨k,hk | hk⟩ := Nat.even_or_odd' m
  · rw [hk,A.moment_even ψ (hsub hψ.2).1 n k,norm_zero]
    positivity
  · rw [hk,hformula ψ hψ.2 n k]
    calc
      _ ≤ ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖ *
          (B*‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖)^(2*k+1) :=
        C.norm_powerBoundaryIntegral_le ψ n k _
          (fun θ hθ => hb ψ hψ.1 n θ hθ true)
      _ = _ := by rw [mul_pow,pow_succ]; ring

/-- Lemma 21.1(iii) on one connected almost-real domain. The radius and
constant are chosen before both the gap index and the moment order. -/
theorem exists_almostReal_all_moments_power_bound :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧ U ⊆ A.domain ∧
      ∀ φ ∈ U, ∃ r : ℝ, 0 < r ∧ ball φ r ⊆ U ∧ ∃ B : ℝ, 0 < B ∧
        ∀ ψ ∈ ball φ r, ∀ (n : ℤ) (m : ℕ), ‖A.moment n m ψ‖ ≤ B^m *
          ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖^(m+1) := by
  choose V hV hφV hsub B hB hb using A.exists_local_all_moments_power_bound
  let S : Set (CoeffPair p) := ⋃ φ : realTypeSourceSubmodule p, V φ
  have hS : IsOpen S := isOpen_iUnion hV
  have hrealS : realTypeSourceLocus p ⊆ S := fun ψ hψ => mem_iUnion.mpr ⟨⟨ψ,hψ⟩,hφV ⟨ψ,hψ⟩⟩
  let U := connectedComponentIn S (0 : CoeffPair p)
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  have hrealU : realTypeSourceLocus p ⊆ U :=
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hrealS
  have hUS : U ⊆ S := connectedComponentIn_subset S 0
  have hU : IsOpen U := hS.connectedComponentIn
  refine ⟨U,hU,isConnected_connectedComponentIn_iff.mpr (hrealS hzero),hrealU,?_,?_⟩
  · intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hUS hψ)
    exact hsub φ hφ
  · intro χ hχ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hUS hχ)
    obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp ((hU.inter (hV φ)).mem_nhds ⟨hχ,hφ⟩)
    exact ⟨r,hr,fun ψ hψ => (hrsub hψ).1,B φ,hB φ,
      fun ψ hψ n m => hb φ ψ (hrsub hψ).2 n m⟩

end SourcePrimitivePowerAtlas
end NLS.ZakharovShabat
