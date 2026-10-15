import NLS.ZakharovShabat.SourceAngularOriginalAnnulus
import NLS.ZakharovShabat.SourceAngularBetaRegularFactorBound
import NLS.ZakharovShabat.SourcePsiOriginalChiMajorant
import NLS.ZakharovShabat.SourcePsiUniformRetainedRootBounds

/-!
# Uniform deleted-index estimates on the original angular charts

The original all-disk lp majorant bounds every chi factor with one
constant. Applying that bound on a selected annulus gives the literal
reciprocal-index beta estimate for all deleted indices, near any complex
source in W. No reality assumption or new root family is needed.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Every original chi factor is uniformly bounded on all original disks. -/
theorem angular_original_chi_bound (H : SourceLemma12_12Data hp hp1 W₀ W s)
    {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : CoeffPair p) (hφ : φ ∈ W) (hφV : φ ∈ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∩ V ∧
      ∃ M : ℝ, 0 < M ∧ ∀ ψ ∈ U, ∀ n m : ℤ, m ≠ n → ∀ z ∈ D m,
        ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m (s n ψ) ψ z‖ ≤ M := by
  obtain ⟨U,hU,hφU,hUV,C,hC,hbound⟩ :=
    H.previous.original_allDisk_chi_errorBound hD hV φ hφ hφV
  refine ⟨U,hU,hφU,hUV,C+1,by positivity,?_⟩
  intro ψ hψ n m hmn z hz
  obtain ⟨E,hE,he⟩ := hbound ψ hψ n
  have herr := (he m hmn z hz).trans
    ((lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' E m).trans hE)
  calc
    _ ≤ ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m (s n ψ) ψ z-Complex.I‖+‖Complex.I‖ :=
      by simpa only [sub_add_cancel] using
        norm_add_le (sourcePsiMidpointFilledRegularFactor hp hp1 n m (s n ψ) ψ z-Complex.I) Complex.I
    _ ≤ C+1 := by rw [norm_I]; exact add_le_add herr le_rfl

/-- A single local constant controls all deleted indices for a fixed selected gap. -/
theorem beta_original_uniform_selected_bound (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) (m : ℤ) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ U, ∀ n : ℤ, m ≠ n →
        ‖sourceAngularBeta hp hp1 n m s ψ‖ ≤ C *
          (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ +
            ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m-
              sourceStandardRootMidpoint hp hp1 ψ m‖) / |((n-m : ℤ) : ℝ)| := by
  obtain ⟨V,c,T,r,R,z₀,hφV,D,C₀,hD⟩ := H.angular_original_annulus_chart φ hφ m
  let ρ := (r+R)/2
  have hrρ : r < ρ := by dsimp only [ρ]; linarith [D.inner_lt_outer]
  have hρR : ρ < R := by dsimp only [ρ]; linarith [D.inner_lt_outer]
  have hρ : 0 < ρ := D.inner_pos.trans hrρ
  obtain ⟨Uχ,hUχ,hφχ,hUχV,M,hM,hχ⟩ := H.angular_original_chi_bound hD D.source_open φ hφ hφV
  obtain ⟨Ur,hUr,hφr,_,A,hA,hroots⟩ :=
    H.angular_extension.exists_local_uniform_retainedRoot_displacement_bound φ hφ
  let B := A+‖(Real.pi:ℂ)*m-c m‖
  let C := ρ^2*(B+ρ)*M/(ρ-r)^3
  have hB : 0 < B := by dsimp only [B]; positivity
  have hC : 0 < C := by have hd := sub_pos.mpr hrρ; dsimp only [C]; positivity
  refine ⟨Uχ ∩ Ur,hUχ.inter hUr,⟨hφχ,hφr⟩,(fun ψ hψ => (hUχV hψ.1).1),C,hC,?_⟩
  intro ψ hψ n hmn
  have hroot : ‖displacedRoots (s n ψ : Coeff p) m-c m‖ ≤ B := by
    rw [show displacedRoots (s n ψ : Coeff p) m-c m =
      (displacedRoots (s n ψ : Coeff p) m-(Real.pi:ℂ)*m)+((Real.pi:ℂ)*m-c m) by ring]
    exact (norm_add_le _ _).trans (add_le_add (hroots ψ hψ.2 n m hmn) le_rfl)
  have h := D.norm_beta_le_of_midpointFilledRegularFactor_bound ψ (hUχV hψ.1).2 n hmn ρ M hrρ hρR hM.le
    (fun z hz => hχ ψ hψ.1 n m hmn z (mem_ball.mpr
      ((mem_sphere.mp hz).trans_lt (hρR.trans D.outer_lt_assigned))))
  have hcoeff : ρ^2*(‖displacedRoots (s n ψ : Coeff p) m-c m‖+ρ)*M/(ρ-r)^3 ≤ C := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add hroot (le_refl ρ)) (sq_nonneg _)) hM.le
  exact h.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff (by positivity)) (abs_nonneg _))

end SourceLemma12_12Data
end NLS.ZakharovShabat
