import NLS.Articles.KdVKdV2Frequencies.LocalWeakSpectralActionFamily
import NLS.Articles.KdVKdV2Frequencies.LocalWeakKdVActionFrequency
import NLS.KdV.HillRoughScalarReality

/-! A common complex weak-action neighborhood for EVERY actual KdV frequency
correction. This proves the order of the neighborhood/index quantifiers;
sharp sequence-valued target bounds are a separate obligation. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV NLS.ZakharovShabat
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- ONE full complex weak-action ball is chosen BEFORE EVERY frequency
index, and all TRUE KdV corrections have analytic scalar factors on that SAME
ball. Every original real mean-zero native H1 source with
its ORIGINAL normalized weak actions in that ball is recovered. No phase,
finite-support, open-gap or independently assumed frequency factor is used.
The action normalization is exactly weight(-1) times the original actions. -/
theorem exists_common_kdv_weak_action_frequency (D : GlobalRoughAbelianForwardData) :
    ∃ ρ : ℝ, ∃ g : ℕ+ → Coeff 1 → ℂ, 0<ρ ∧ (∀ n : ℕ+, AnalyticOnNhd ℂ (g n) (ball (0 : Coeff 1) ρ)) ∧
      (∀ a∈ball (0 : Coeff 1) ρ, a∈Coeff.nonnegativeLocus 1 → ∀ n : ℕ+, (g n a).im=0) ∧
      ∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)),
        D.nativeWeakActionSequence 1 q∈ball (0 : Coeff 1) ρ →
        ∀ n : ℕ+, g n (D.nativeWeakActionSequence 1 q)=
          (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3 := by
  obtain ⟨δ,F,hδ,hF,hinv,hnative⟩ := D.exists_native_kdv_isospectral_rough_extension_near_zero
  obtain ⟨Z,T,g,hZ,h0Z,hT,h0T,_,hg,hsource, hrec⟩ := D.exists_local_weak_spectral_action_family δ hδ
    F hF (fun n q hq p hp hqr hpr ht => hinv q hq p hp hqr hpr ht n)
  obtain ⟨R,hR,hballZ⟩ := Metric.isOpen_iff.mp hZ 0 h0Z
  obtain ⟨ε,hε,hballT⟩ := Metric.isOpen_iff.mp hT 0 h0T
  let ρ := min ε (R^2/2)
  have hρ : 0<ρ := lt_min hε (by positivity)
  have hsub : ball (0 : Coeff 1) ρ⊆T := (ball_subset_ball (min_le_left _ _)).trans hballT
  have hFreal (n : ℕ+) (q : PeriodOneHminusOne) (hqr : IsRealPeriodOneHminusOne q)
      (hqm : q.val 0=0) (hq : q∈ball (0 : PeriodOneHminusOne) δ) : (F n q).im=0 := by
    apply hillRoughScalar_real_of_native_real δ (F n) (hF n).continuousOn ?_ q hqr hqm hq
    intro u hu
    have hc : (2*(n : ℂ)*Real.pi)^3=(((2*(n : ℝ)*Real.pi)^3 : ℝ) : ℂ) := by push_cast; rfl
    rw [hnative u hu n,hc]
    simp only [sub_im,ofReal_im,sub_self]
  refine ⟨ρ,g,hρ,(fun n => (hg n).mono hsub),?_,?_⟩
  · intro a ha hapos n
    obtain ⟨z,hzr,hQ,_⟩ := Coeff.exists_real_quadraticActions_lift (p := 2) (q := 1) (by simp) a hapos
    have hbound := Coeff.norm_sq_le_two_norm_quadraticActions (p := 2) (q := 1) (by simp) z hzr
    rw [hQ] at hbound
    have hsmall : ‖a‖<ρ := mem_ball_zero_iff.mp ha
    have hznorm : ‖z‖<R := (sq_lt_sq₀ (norm_nonneg z) hR.le).mp (by
      have hle : ρ≤R^2/2 := min_le_right _ _
      nlinarith)
    have hz : z∈Z := hballZ (mem_ball_zero_iff.mpr hznorm)
    have he := hrec n z hz hzr
    rw [hQ] at he
    rw [he]
    exact hFreal n _ (D.realWeakInverseSource_real _) (D.realWeakInverseSource_zero_mode _) (hsource z hz hzr)
  · intro q hq n
    let a := D.nativeWeakSignedTarget 1 q
    let z := Coeff.signedToCartesian a.val
    have hzreal : z∈Coeff.realPairLocus 2 := Coeff.signedToCartesian_real a
    have hQ : quadraticActionsExponent (q := 1) z=D.nativeWeakActionSequence 1 q := rfl
    have hbound := Coeff.norm_sq_le_two_norm_quadraticActions (p := 2) (q := 1) (by simp) z hzreal
    rw [hQ] at hbound
    have hsmall : ‖D.nativeWeakActionSequence 1 q‖<ρ := mem_ball_zero_iff.mp hq
    have hznorm : ‖z‖<R := (sq_lt_sq₀ (norm_nonneg z) hR.le).mp (by
      have hle : ρ≤R^2/2 := min_le_right _ _
      nlinarith)
    have hz : z∈Z := hballZ (mem_ball_zero_iff.mpr hznorm)
    have hsrc := hsource z hz hzreal
    have he := hrec n z hz hzreal
    have htarget : (⟨Coeff.cartesianToSigned z,Coeff.cartesianToSigned_real z hzreal⟩ : physicalRealDeletedSubmodule)=a :=
      Subtype.ext (Coeff.cartesianToSigned_signedToCartesian a.val)
    rw [htarget,D.nativeWeakSignedTarget_inverse] at hsrc he
    rw [hQ] at he
    exact he.trans (hnative q hsrc n)


end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
