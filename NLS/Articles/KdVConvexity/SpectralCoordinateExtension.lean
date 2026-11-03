import NLS.Articles.KdVConvexity.IsospectralCanonicalMoments
import NLS.Articles.KdVConvexity.CoordinateActionExtension

/-! # From actual spectral periods to the global positive-ell2 extension

This reduction uses the proved actual potential-space family. Its only
remaining input is a spectral coordinate realization: an analytic map on
a neighborhood of all real normalized Hilbert pairs, taking real pairs
to real potentials, with the real Arnold-action identity and discriminant
invariance along real action fibers. No such realization is constructed
or assumed to exist here. In particular this is not Theorem 1.1.

Real-form uniqueness continues the real Arnold identity to each complex
ball, simultaneously for every index. Thus no complex action identity,
extra period estimate, or common action neighborhood is an input.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.Articles.KdVConvexity
open NLS.KdV

/-- The precise remaining coordinate inputs for the extension step.
This structure asserts neither existence nor symplecticity. -/
structure SpectralCoordinateRealization where
  domain : Set (Coeff 2 × Coeff 2)
  isOpen_domain : IsOpen domain
  real_subset : Coeff.realPairLocus 2 ⊆ domain
  potential : (Coeff 2 × Coeff 2) → PeriodOneHminusOne
  analytic_potential : AnalyticOnNhd ℂ potential domain
  real_potential : ∀ z, z ∈ Coeff.realPairLocus 2 → IsRealPeriodOneHminusOne (potential z)
  arnold_action : ∀ z (hz : z ∈ Coeff.realPairLocus 2) (n : ℕ+),
    hillHminusRealGapContourMoment (potential z) (real_potential z hz) n 0 =
      (normalizedCoordinateActions z).val (actionIndexEquiv.symm n)
  discriminant_invariant : ∀ z v, z ∈ Coeff.realPairLocus 2 → v ∈ Coeff.realPairLocus 2 →
    normalizedCoordinateActions v = normalizedCoordinateActions z →
      hillHminusDiscriminant (potential v) = hillHminusDiscriminant (potential z)

theorem analyticAt_normalizedCoordinateAction (k : ℤ) (z : Coeff 2 × Coeff 2) :
    AnalyticAt ℂ (fun v => (normalizedCoordinateActions v).val k) z := by
  have hx : AnalyticAt ℂ (fun v : Coeff 2 × Coeff 2 => v.1 k) z :=
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k).analyticAt z.1).comp analyticAt_fst
  have hy : AnalyticAt ℂ (fun v : Coeff 2 × Coeff 2 => v.2 k) z :=
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k).analyticAt z.2).comp analyticAt_snd
  simp only [normalizedCoordinateActions,WeightedCoeff.actionsFromNormalizedCoordinates_apply]
  exact ((hx.pow 2).add (hy.pow 2)).div_const

/-- The actual cubic periods descend to one base-action neighborhood and
sum analytically on one neighborhood of the entire positive ell2 cone,
conditional only on the stated spectral coordinate realization. -/
theorem global_contour_extension_of_spectral_coordinate_realization
    (S : SpectralCoordinateRealization) :
    ∃ U : Set BaseActionSpace, ∃ R : ℕ+ → BaseActionSpace → ℂ,
      IsOpen U ∧ WeightedCoeff.nonnegativeLocus baseActionWeight 1 ⊆ U ∧
      (∀ n, AnalyticOnNhd ℂ (R n) U) ∧
      (∀ n z (hz : z ∈ Coeff.realPairLocus 2),
        R n (normalizedCoordinateActions z) =
          hillHminusRealGapCubicContourMoment (S.potential z) (S.real_potential z hz) n) ∧
      (∀ b ∈ WeightedCoeff.nonnegativeLocus baseActionWeight 1, ∀ n,
        (R n b).im = 0 ∧ (R n b).re ≤ 0 ∧
          (R n b = 0 ↔ b.val (actionIndexEquiv.symm n) = 0)) ∧
      IsOpen (baseActionInclusion ⁻¹' U) ∧ positiveQuadrant ⊆ baseActionInclusion ⁻¹' U ∧
      AnalyticOnNhd ℂ (contourHamiltonian R) (baseActionInclusion ⁻¹' U) ∧
      (∀ a ∈ baseActionInclusion ⁻¹' U,
        Summable (fun n => ‖weightedContourTerm R n (baseActionInclusion a)‖)) ∧
      contourHamiltonian R 0 = 0 ∧
      ∀ a ∈ positiveQuadrant, (contourHamiltonian R a).im = 0 ∧ (contourHamiltonian R a).re ≤ 0 := by
  obtain ⟨Ω,hΩ,hrealΩ,A,P,hA,hP,hvalues,hinvariant,htail⟩ :=
    exists_global_isospectral_canonical_moment_family
  let W := S.domain ∩ S.potential ⁻¹' Ω
  have hW : IsOpen W :=
    S.analytic_potential.continuousOn.isOpen_inter_preimage S.isOpen_domain hΩ
  have hrealW : Coeff.realPairLocus 2 ⊆ W := fun z hz =>
    ⟨S.real_subset hz,hrealΩ (S.real_potential z hz)⟩
  let M : ℕ+ → (Coeff 2 × Coeff 2) → ℂ := fun n z => P n (S.potential z)
  have hM (n : ℕ+) : AnalyticOnNhd ℂ (M n) W := fun z hz =>
    (hP n _ hz.2).comp (S.analytic_potential z hz.1)
  have hMA (n : ℕ+) : AnalyticOnNhd ℂ (fun z => A n 0 (S.potential z)) W := fun z hz =>
    (hA n 0 _ hz.2).comp (S.analytic_potential z hz.1)
  have hbound : ∀ z ∈ Coeff.realPairLocus 2,
      ∃ T : Set (Coeff 2 × Coeff 2), IsOpen T ∧ z ∈ T ∧ T ⊆ W ∧
        ∃ s : Finset ℕ+, ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ T, ∀ n ∉ s,
          ‖((8*(n : ℝ)*Real.pi : ℝ) : ℂ)*M n v‖ ≤
            C*‖(normalizedCoordinateActions v).val (actionIndexEquiv.symm n)‖^2 := by
    intro z hzr
    obtain ⟨C,N,V,hC,hN,hV,hzV,hVΩ,hb⟩ := htail (S.potential z) (S.real_potential z hzr)
    have hopen : IsOpen (S.domain ∩ S.potential ⁻¹' V) :=
      S.analytic_potential.continuousOn.isOpen_inter_preimage S.isOpen_domain hV
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds ⟨S.real_subset hzr,hzV⟩)
    have hBW : ball z r ⊆ W := fun v hv => ⟨(hball hv).1,hVΩ (hball hv).2⟩
    have ha (n : ℕ+) : EqOn (fun v => A n 0 (S.potential v))
        (fun v => (normalizedCoordinateActions v).val (actionIndexEquiv.symm n)) (ball z r) := by
      apply Coeff.eqOn_of_realPair_agreement _ _ _ isOpen_ball (convex_ball z r) z
        (mem_ball_self hr) hzr ((hMA n).mono hBW).differentiableOn
        (fun v _ => (analyticAt_normalizedCoordinateAction _ v).differentiableAt.differentiableWithinAt)
      intro v _ hvr
      exact ((hvalues (S.potential v) (S.real_potential v hvr) n).1 0).trans (S.arnold_action v hvr n)
    let s : Finset ℕ+ := (Finset.range N).image (fun k : ℕ => (⟨k+1,by omega⟩ : ℕ+))
    refine ⟨ball z r,isOpen_ball,mem_ball_self hr,hBW,s,C,hC.le,?_⟩
    intro v hv n hn
    have hnN : N ≤ (n : ℕ) := by
      by_contra h
      have hpos := n.property
      apply hn
      exact Finset.mem_image.mpr ⟨(n : ℕ)-1,Finset.mem_range.mpr (by omega),by
        apply Subtype.ext
        exact Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)⟩
    have hbnd := (hb n hnN (S.potential v) (hball hv).2).2.2
    have he := ha n hv
    dsimp only at he
    rw [he] at hbnd
    simpa only [M,Nat.cast_ofNat] using hbnd
  obtain ⟨U,R,hU,hcone,hR,hrec,hopen,hpos,hH,hsum⟩ :=
    global_contour_extension_from_coordinate_moments M W hW hrealW hM (by
      intro n z _ v _ hzr hvr he
      exact (hinvariant (S.potential v) (S.potential z) (S.real_potential v hvr)
        (S.real_potential z hzr) (S.discriminant_invariant z v hzr hvr he)).2 n) hbound
  have hrecover (n : ℕ+) (z : Coeff 2 × Coeff 2) (hz : z ∈ Coeff.realPairLocus 2) :
      R n (normalizedCoordinateActions z) =
        hillHminusRealGapCubicContourMoment (S.potential z) (S.real_potential z hz) n :=
    (hrec n z hz).trans (hvalues (S.potential z) (S.real_potential z hz) n).2.1
  have hsign (b : BaseActionSpace) (hb : b ∈ WeightedCoeff.nonnegativeLocus baseActionWeight 1) (n : ℕ+) :
      (R n b).im = 0 ∧ (R n b).re ≤ 0 ∧ (R n b = 0 ↔ b.val (actionIndexEquiv.symm n) = 0) := by
    obtain ⟨z,hzr,hq,_⟩ := Coeff.exists_real_quadraticActions_lift (p := 2) (by norm_num)
      (WeightedCoeff.weightIsometry baseActionWeight 1 b)
      ((WeightedCoeff.mem_nonnegativeLocus_iff baseActionWeight 1 b).mp hb)
    have hi : normalizedCoordinateActions z = b := by
      apply (WeightedCoeff.weightIsometry baseActionWeight 1).injective
      simpa only [normalizedCoordinateActions,WeightedCoeff.weight_actionsFromNormalizedCoordinates] using hq
    obtain ⟨ha,hp,_,hneg,him,hzero⟩ := hvalues (S.potential z) (S.real_potential z hzr) n
    have he : R n b = P n (S.potential z) := by rw [← hi]; exact hrec n z hzr
    have heA : A n 0 (S.potential z) = b.val (actionIndexEquiv.symm n) := by
      rw [ha 0,S.arnold_action z hzr n,hi]
    rw [he]
    exact ⟨him,hneg,by rwa [heA] at hzero⟩
  refine ⟨U,R,hU,hcone,hR,hrecover,hsign,hopen,hpos,hH,hsum,?_,?_⟩
  · have hz (n : ℕ+) : R n 0 = 0 :=
      ((hsign 0 (WeightedCoeff.zero_mem_nonnegativeLocus baseActionWeight 1) n).2.2).mpr rfl
    simp only [contourHamiltonian,map_zero,weightedContourTerm,hz,mul_zero,tsum_zero]
  intro a ha
  have hs := (hsum a (hpos ha)).of_norm
  have hb := baseActionInclusion_mem_nonnegative a ha
  constructor
  · rw [contourHamiltonian,Complex.im_tsum hs]
    have hz (n : ℕ+) : (weightedContourTerm R n (baseActionInclusion a)).im = 0 := by
      simp only [weightedContourTerm,mul_im,ofReal_re,ofReal_im,zero_mul,add_zero,(hsign _ hb n).1,mul_zero]
    simp only [hz,tsum_zero]
  · rw [contourHamiltonian,Complex.re_tsum hs]
    apply tsum_nonpos
    intro n
    simp only [weightedContourTerm,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hsign _ hb n).2.1

end NLS.Articles.KdVConvexity
