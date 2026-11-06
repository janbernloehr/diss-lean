import NLS.Articles.KdVKdV2Frequencies.LocalWeakSpectralActionDescent
import NLS.Articles.KdVKdV2Frequencies.NativeWeakActionCoordinates
import NLS.Articles.KdVKdV2Frequencies.NativeInfiniteGapKdVFrequency
import NLS.KdV.HillOriginalSpectralSecondMomentSeries
import NLS.SequenceSpaces.RealActionNormLowerBound

/-! Genuine analytic weak-action factors of the ACTUAL KdV frequencies near
zero. Every native source whose normalized weak actions are in the action
ball is recovered, with arbitrary phases, infinite support and closed gaps. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV NLS.ZakharovShabat
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- The SAME analytic rough correction is spectrally invariant on its
entire real rough ball and equals the TRUE native physical frequency. -/
theorem exists_native_kdv_isospectral_rough_extension_near_zero (D : GlobalRoughAbelianForwardData) :
    ∃ δ : ℝ, ∃ F : ℕ+ → PeriodOneHminusOne → ℂ, 0<δ ∧
      (∀ n : ℕ+, AnalyticOnNhd ℂ (F n) (ball (0 : PeriodOneHminusOne) δ)) ∧
      (∀ q∈ball (0 : PeriodOneHminusOne) δ, ∀ p∈ball (0 : PeriodOneHminusOne) δ,
        IsRealPeriodOneHminusOne q → IsRealPeriodOneHminusOne p →
        hillHminusDiscriminant p=hillHminusDiscriminant q → ∀ n : ℕ+, F n p=F n q) ∧
      ∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)),
        nativeHillSource 1 q.val∈ball (0 : PeriodOneHminusOne) δ → ∀ n : ℕ+,
        F n (nativeHillSource 1 q.val)=
          (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3 := by
  obtain ⟨δ₀,F,hδ₀,hF,hinv,hphys⟩ := exists_hillOriginal_isospectral_analytic_second_moment_series
  obtain ⟨δ₁,F₁,hδ₁,_,hnative⟩ := D.exists_native_kdv_original_moment_frequency_near_zero
  let δ := min δ₀ δ₁
  have hsub₀ : ball (0 : PeriodOneHminusOne) δ⊆ball 0 δ₀ := ball_subset_ball (min_le_left _ _)
  have hsub₁ : ball (0 : PeriodOneHminusOne) δ⊆ball 0 δ₁ := ball_subset_ball (min_le_right _ _)
  refine ⟨δ,F,lt_min hδ₀ hδ₁,(fun n => (hF n).mono hsub₀),?_,?_⟩
  · intro q hq p hp
    exact hinv q (hsub₀ hq) p (hsub₀ hp)
  · intro q hq n
    let p := nativeHillPhysicalSource 1 q.val q.property.1
    have hp : hillOriginalHminusSource p.val=nativeHillSource 1 q.val := by
      rw [hillOriginalHminusSource_eq_physical]
      exact (nativeHillSource_eq_physical 1 q.val q.property.1).symm
    have he := (hphys p (by rw [hp];exact hsub₀ hq) n).2
    rw [hp] at he
    exact he.trans (hnative q (hsub₁ hq) n).2.2.symm

/-- Each TRUE KdV correction has a complex analytic factor on a full weak
action ball about zero. Every original real mean-zero native H1 source with
its ORIGINAL normalized weak actions in that ball is recovered. No phase,
finite-support, open-gap or independently assumed frequency factor is used.
The action normalization is exactly weight(-1) times the original actions. -/
theorem exists_local_kdv_weak_action_frequency (D : GlobalRoughAbelianForwardData) (n : ℕ+) :
    ∃ ρ : ℝ, ∃ g : Coeff 1 → ℂ, 0<ρ ∧ AnalyticOnNhd ℂ g (ball (0 : Coeff 1) ρ) ∧
      ∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)),
        D.nativeWeakActionSequence 1 q∈ball (0 : Coeff 1) ρ →
        g (D.nativeWeakActionSequence 1 q)=
          (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3 := by
  obtain ⟨δ,F,hδ,hF,hinv,hnative⟩ := D.exists_native_kdv_isospectral_rough_extension_near_zero
  obtain ⟨Z,T,g,hZ,h0Z,hT,h0T,_,hg,hrec⟩ := D.exists_local_weak_spectral_action_factor δ hδ
    (F n) (hF n) (fun q hq p hp hqr hpr ht => hinv q hq p hp hqr hpr ht n)
  obtain ⟨R,hR,hballZ⟩ := Metric.isOpen_iff.mp hZ 0 h0Z
  obtain ⟨ε,hε,hballT⟩ := Metric.isOpen_iff.mp hT 0 h0T
  let ρ := min ε (R^2/2)
  have hρ : 0<ρ := lt_min hε (by positivity)
  have hsub : ball (0 : Coeff 1) ρ⊆T := (ball_subset_ball (min_le_left _ _)).trans hballT
  refine ⟨ρ,g,hρ,hg.mono hsub,?_⟩
  intro q hq
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
  obtain ⟨hsource,he⟩ := hrec z hz hzreal
  have htarget : (⟨Coeff.cartesianToSigned z,Coeff.cartesianToSigned_real z hzreal⟩ : physicalRealDeletedSubmodule)=a :=
    Subtype.ext (Coeff.cartesianToSigned_signedToCartesian a.val)
  rw [htarget,D.nativeWeakSignedTarget_inverse] at hsource he
  rw [hQ] at he
  exact he.trans (hnative q hsource n)

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
