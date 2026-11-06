import NLS.Articles.KdVConvexity.LocalSpectralPairCharts
import NLS.Articles.KdVConvexity.SpectralCoordinateExtension

/-! # Actual local cubic moment families with uniform quadratic action bounds -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.Articles.KdVConvexity
open NLS.KdV NLS.Articles.KdVKdV2Frequencies

/-- Each actual real mean-zero rough source yields one common local pair
chart for all cubic moments. The exact quadratic complex tail bound holds
on that SAME chart, with the neighborhood chosen before the gap index. -/
theorem exists_local_cubic_pair_chart
    (D : GlobalRoughAbelianForwardData)
    (ΩI : Set PeriodOneHminusOne) (hΩI : {q | IsRealPeriodOneHminusOne q} ⊆ ΩI)
    (I : PeriodOneHminusOne → BaseActionSpace) (hI : AnalyticOnNhd ℂ I ΩI)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n) = hillHminusRealGapContourMoment q hr n 0)
    (q0 : PeriodOneHminusOne) (hr0 : IsRealPeriodOneHminusOne q0) (hm0 : q0.val 0 = 0) :
    ∃ z0 : Coeff 2 × Coeff 2, z0 ∈ Coeff.realPairLocus 2 ∧
      normalizedCoordinateActions z0 = I q0 ∧
      ∃ U : Set (Coeff 2 × Coeff 2), ∃ Q : (Coeff 2 × Coeff 2) → PeriodOneHminusOne,
      ∃ M : ℕ+ → (Coeff 2 × Coeff 2) → ℂ,
        IsOpen U ∧ z0 ∈ U ∧ AnalyticOnNhd ℂ Q U ∧ Q z0 = q0 ∧
        (∀ n, AnalyticOnNhd ℂ (M n) U) ∧
        (∀ z ∈ U, z ∈ Coeff.realPairLocus 2 → ∃ hr : IsRealPeriodOneHminusOne (Q z),
          (Q z).val 0 = 0 ∧ I (Q z) = normalizedCoordinateActions z ∧
            ∀ n, M n z = hillHminusRealGapCubicContourMoment (Q z) hr n) ∧
        ∃ s : Finset ℕ+, ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ U, ∀ n ∉ s,
          ‖((8*(n : ℝ)*Real.pi : ℝ) : ℂ)*M n z‖ ≤
            C*‖(normalizedCoordinateActions z).val (actionIndexEquiv.symm n)‖^2 := by
  obtain ⟨Ω,hΩ,_hreal,A,P,hA,hP,hvalues,_hinv,htail⟩ :=
    exists_global_isospectral_canonical_moment_family
  obtain ⟨z0,hzr,hza,U,hU,hzU,Q,hQ,hQ0,hd⟩ :=
    exists_local_spectral_pair_chart D ΩI hΩI I hI hrec q0 hr0 hm0
  obtain ⟨C,N,V,hC,_hN,hV,hqV,hVΩ,hb⟩ := htail q0 hr0
  have hopen : IsOpen (U ∩ Q ⁻¹' V) := hQ.continuousOn.isOpen_inter_preimage hU hV
  have hbase : z0 ∈ U ∩ Q ⁻¹' V := ⟨hzU,by change Q z0 ∈ V; rwa [hQ0]⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hbase)
  let W := ball z0 r
  let M : ℕ+ → (Coeff 2 × Coeff 2) → ℂ := fun n z => P n (Q z)
  have hMQ (n : ℕ+) : AnalyticOnNhd ℂ (M n) W := fun z hz =>
    (hP n _ (hVΩ (hball hz).2)).comp (hQ z (hball hz).1)
  have hAQ (n : ℕ+) : AnalyticOnNhd ℂ (fun z => A n 0 (Q z)) W := fun z hz =>
    (hA n 0 _ (hVΩ (hball hz).2)).comp (hQ z (hball hz).1)
  have hact (n : ℕ+) : EqOn (fun z => A n 0 (Q z))
      (fun z => (normalizedCoordinateActions z).val (actionIndexEquiv.symm n)) W := by
    apply Coeff.eqOn_of_realPair_agreement _ _ W isOpen_ball (convex_ball z0 r) z0
      (mem_ball_self hr) hzr (hAQ n).differentiableOn
      (fun z _ => (analyticAt_normalizedCoordinateAction _ z).differentiableAt.differentiableWithinAt)
    intro z hz hzz
    obtain ⟨hqz,hi⟩ := (hd z (hball hz).1).2 hzz
    rw [(hvalues (Q z) hqz n).1 0,←hrec (Q z) hqz n,hi]
  let s : Finset ℕ+ := (Finset.range N).image (fun k => (⟨k+1,by omega⟩ : ℕ+))
  refine ⟨z0,hzr,hza,W,Q,M,isOpen_ball,mem_ball_self hr,hQ.mono (fun z hz => (hball hz).1),
    hQ0,hMQ,?_,s,C,hC.le,?_⟩
  · intro z hz hzz
    obtain ⟨hqz,hi⟩ := (hd z (hball hz).1).2 hzz
    exact ⟨hqz,(hd z (hball hz).1).1,hi,fun n => (hvalues (Q z) hqz n).2.1⟩
  · intro z hz n hn
    have hnN : N ≤ (n : ℕ) := by
      by_contra h
      apply hn
      exact Finset.mem_image.mpr ⟨(n : ℕ)-1,Finset.mem_range.mpr (by have := n.pos; omega),
        Subtype.ext (Nat.sub_add_cancel n.pos)⟩
    have h := (hb n hnN (Q z) (hball hz).2).2.2
    have he := hact n hz
    dsimp only at he
    rw [he] at h
    simpa only [M] using h

end NLS.Articles.KdVConvexity
