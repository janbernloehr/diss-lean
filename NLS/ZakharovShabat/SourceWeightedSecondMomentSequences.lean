import NLS.ZakharovShabat.SourceAbelianMomentLemma20_3
import NLS.SequenceSpaces.WeightedCubicRows
import NLS.SequenceSpaces.LocallyBoundedRealization

/-! # Analytic ell1 realizations of the actual index-weighted second moments -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

def SourceAbelianMomentAtlas.weightedSecondMomentTerms
    (A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W s)
    (n : ℤ) (ψ : CoeffPair 2) : Coeff 1 :=
  Coeff.ofFunctionOrZero 1 (fun k : ℤ => (k : ℂ)*A.moment n k 2 ψ)

/-- A single connected complex neighborhood contains all real Hilbert
sources and supports every signed weighted row as a genuine analytic ell1
map. Its literal coefficients and one local bound before all row indices
are retained; neither an analytic choice of individual gaps nor a uniform
tail limit on one fixed infinite-dimensional ball is required. -/
theorem SourceAbelianMomentAtlas.exists_analytic_weightedSecondMomentTerms
    (A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W s)
    (hs : SourcePsiSquaredGapComplexExtension (by norm_num) (by norm_num) V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus 2 ⊆ V) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus 2 ⊆ U ∧
      U ⊆ A.domain ∩ V ∧
      (∀ n : ℤ, AnalyticOnNhd ℂ (A.weightedSecondMomentTerms n) U) ∧
      (∀ ψ ∈ U, ∀ n k : ℤ, A.weightedSecondMomentTerms n ψ k=(k : ℂ)*A.moment n k 2 ψ) ∧
      ∀ φ ∈ U, ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ∀ n : ℤ,
          ‖A.weightedSecondMomentTerms n ψ‖ ≤ (1+‖(n : ℂ)‖)*C := by
  obtain ⟨U,hU,hUc,hreal,hUV,hlocal⟩ := A.exists_lemma20_3_refined hs hV hrealV
  have hrows (φ : CoeffPair 2) (hφ : φ ∈ U) :
      ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∀ ψ ∈ T, ∀ n : ℤ, ∃ b : Coeff 1,
          (∀ k, b k=(k : ℂ)*A.moment n k 2 ψ) ∧ ‖b‖ ≤ (1+‖(n : ℂ)‖)*C := by
    obtain ⟨ρ,hρ,hball,hcoeff⟩ := hlocal φ hφ
    obtain ⟨M,hM,hdata⟩ := hcoeff 2 (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨_,_,G,hG,hφG,R,hR,hgap⟩ :=
      exists_uniform_small_sourcePeriodicGapDisplacement (p := 2) (by norm_num) (by norm_num) φ
        (by norm_num : (0 : ℝ)<1)
    let T := ball φ ρ ∩ G
    let D := (Real.pi+M)/4
    let C := (D+R*M)*R^2
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hC : 0 ≤ C := by dsimp [C]; positivity
    refine ⟨T,isOpen_ball.inter hG,⟨mem_ball_self hρ,hφG⟩,fun ψ hψ => hball hψ.1,C,hC,?_⟩
    intro ψ hψ n
    obtain ⟨d,_hdval,hdnorm,hdfactor,hoff⟩ := hdata ψ hψ.1
    obtain ⟨a,_haval,_han,hanorm,hafactor⟩ := hoff n
    have hdiag : ‖A.moment n n 2 ψ‖ ≤ D*‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ n‖^2 := by
      rw [hdfactor n,norm_mul,norm_div,norm_pow]
      have hdn := (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) d n).trans hdnorm
      have hb : ‖(Real.pi : ℂ)+d n‖ ≤ Real.pi+M := by
        apply (norm_add_le _ _).trans
        simpa only [Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le] using add_le_add le_rfl hdn
      norm_num only [Complex.norm_ofNat]
      calc
        _ ≤ ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ n‖^2/4*(Real.pi+M) := by gcongr
        _ = _ := by dsimp [D]; ring
    obtain ⟨b,hb,hbnorm⟩ := Coeff.exists_int_weighted_cubic_row n
      (sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ) a
      (fun k => A.moment n k 2 ψ) R M D hR hM.le hD (hgap ψ hψ.2).1 hanorm hdiag hafactor
    refine ⟨b,hb,hbnorm.trans ?_⟩
    dsimp only [C]
    nlinarith [mul_nonneg hD (sq_nonneg R)]
  have hconstruct (n : ℤ) := Coeff.analytic_realization_of_local_bounds
    (fun ψ : CoeffPair 2 => fun k : ℤ => (k : ℂ)*A.moment n k 2 ψ) hU
    (fun k ψ hψ => analyticAt_const.mul (A.analytic_moment n k 2 ψ (hUV hψ).1)) (by
      intro φ hφ
      obtain ⟨T,hT,hφT,hTU,C,_hC,hb⟩ := hrows φ hφ
      exact ⟨T,hT,hφT,hTU,(1+‖(n : ℂ)‖)*C,fun ψ hψ => hb ψ hψ n⟩)
  refine ⟨U,hU,hUc,hreal,hUV,fun n => (hconstruct n).2,
    fun ψ hψ n k => (hconstruct n).1 ψ hψ k,?_⟩
  intro φ hφ
  obtain ⟨T,hT,hφT,hTU,C,hC,hb⟩ := hrows φ hφ
  refine ⟨T,hT,hφT,hTU,C,hC,?_⟩
  intro ψ hψ n
  obtain ⟨b,hb,hbnorm⟩ := hb ψ hψ n
  change ‖Coeff.ofFunctionOrZero 1 (fun k : ℤ => (k : ℂ)*A.moment n k 2 ψ)‖ ≤ _
  rwa [Coeff.ofFunctionOrZero_eq_of_coordinates _ b hb]

end NLS.ZakharovShabat
