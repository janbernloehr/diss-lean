import NLS.ZakharovShabat.SourceFiniteGapFourthOpenFrequency

/-! # Open-action Lemma 5.2 with all spectral data constructed

The actual H₄ action derivative is identified with the weighted second
moments of any normalized atlas; the angular and primitive domains may differ.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W V₀ C V X : Set (CoeffPair 2)}
  {s u : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Lemma 5.2 at an open selected action, for any actual normalized moment atlas. -/
theorem finiteGapFourthOpenFrequency_renormalized_eq_moments
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) X u)
    (hs : SourcePsiNormalizedComplexExtension (by simp) (by norm_num) V u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0) :
    D.finiteGapFourthOpenFrequency φ hf n hn-
      6*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 2-
      (12*Real.pi:ℂ)*n*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1-
      (2*(n:ℂ)*Real.pi)^3 = -12*(∑' k : ℤ, (k:ℂ)*A.moment n k 2 φ.val) := by
  classical
  obtain ⟨Y,Z,_,F⟩ := exists_sourceFullAbelianDifferentialData (p := 2) (by simp) (by norm_num)
  obtain ⟨V₁,B₁,V₂,hV₁,_,hrealV₁,_,_,_,v,E⟩ :=
    exists_sourceAngularTheta_theorem13_1_iv (p := 2) (by simp) (by norm_num)
  obtain ⟨Wa,_,_,hlocal⟩ := E.psi.toSourcePsiNormalizedComplexExtension.exists_moment_localCharts hV₁ hrealV₁
  choose L hL using hlocal
  let Aa : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa v := ⟨L⟩
  obtain ⟨T,_,hformula⟩ := A.exists_finiteGap_cubic_contour_formula hs φ hf
  obtain ⟨R,hR,hTR,hcircle,hseg⟩ := exists_sourceCanonicalRoot_circle_enclosing_finite_gaps
    (by simp) (by norm_num) φ.val hf.toFinset T
  obtain ⟨Fφ⟩ := F.charts φ.val (F.real_subset φ.property)
  obtain ⟨Aφ⟩ := (A.localChart φ).charts φ.val (mem_ball_self (A.localChart φ).radius_pos)
  have hbranch : (v n φ.val : Coeff 2) = (u n φ.val : Coeff 2) := by
    rw [E.psi.real_agreement n φ,hs.real_agreement n φ]
  rw [D.finiteGapFourthOpenFrequency_eq_fourthContour_bracket E F Aa φ hf n hn R hR hcircle hseg,
    E.theta_fourthContour_eq_cubic F le_rfl n φ (F.real_subset φ.property) hn 0 R hR.le hcircle,
    hbranch,sourceAbelianMomentCircle_independent_neighborhood (by simp) (by norm_num) Y X n 0 3
      (u n φ.val) φ.val Fφ Aφ 0 R hR.le hcircle]
  linear_combination hformula R hTR hcircle n hn

/-- The physical derivative is independent of the chosen Birkhoff realization. -/
theorem finiteGapFourthOpenFrequency_independent_coordinates
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (D' : SourceBirkhoffMapComplexData (by simp) (by norm_num) V₀ C V u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0) :
    D.finiteGapFourthOpenFrequency φ hf n hn = D'.finiteGapFourthOpenFrequency φ hf n hn := by
  classical
  obtain ⟨Y,Z,_,_,_,_,v,hs,hlocal⟩ := exists_sourceAbelianMoment_localCharts (p := 2) (by simp) (by norm_num)
  choose L hL using hlocal
  let A : SourceAbelianMomentAtlas (by simp) (by norm_num) Y v := ⟨L⟩
  have hD := D.finiteGapFourthOpenFrequency_renormalized_eq_moments A hs φ hf n hn
  have hD' := D'.finiteGapFourthOpenFrequency_renormalized_eq_moments A hs φ hf n hn
  linear_combination hD-hD'

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
