import NLS.KdV.HillCubicKernelFilledDomain
import NLS.KdV.ClassicalHillWholeGapQuotients

/-! # Actual shifted primitive differentials through every real Hill gap -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillL2ShiftedPrimitive (k : ℕ) (E : ℂ) : ℂ :=
  hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E+I*(k:ℂ)*Real.pi

def hillL2ShiftedDifferential (k : ℕ) (P : ℂ → ℂ) (E : ℂ) : ℂ :=
  hillL2ShiftedPrimitive q k E*P E/hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E

def hillL2FilledShiftedDifferential (k : ℕ) (P : ℂ → ℂ) : ℂ → ℂ :=
  denseLimitExtension (hillL2ShiftedDifferential q k P) {E : ℂ | E.im≠0}

theorem hillL2RealCutRoot_eq_shifted_sinh (k : ℕ) (E : ℂ) :
    hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E=
      2*((-1:ℂ)^k)*sinh (hillL2ShiftedPrimitive q k E) := by
  have hs : ((-1:ℂ)^k)^2=1 := by rw [pow_two,← mul_pow];simp
  rw [hillL2RealCutRoot,hillL2ShiftedPrimitive,sinh_add_hill_index]
  linear_combination -2*sinh (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E)*hs

theorem exists_hillL2ShiftedDifferential_gap_chart
    (k : ℕ) (hk : 1≤k) (P : ℂ → ℂ) (hP : AnalyticOnNhd ℂ P univ) (x : ℝ)
    (hx : x∈Icc (hillRealLabels q hq hr (2*k-1)) (hillRealLabels q hq hr (2*k))) :
    ∃ B : Set ℂ, ∃ G : ℂ → ℂ, IsOpen B ∧ (x:ℂ)∈B ∧
      AnalyticOnNhd ℂ G B ∧ EqOn G (hillL2ShiftedDifferential q k P) (B∩{E : ℂ | E.im≠0}) := by
  let K := hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) k
  let D : ℂ → ℂ := fun E => deriv squaredCosh (K E)
  let σ : ℂ := (-1)^k
  let G : ℂ → ℂ := fun E => (σ/(4*D E))*P E
  have hσ : σ^2=1 := by dsimp only [σ];rw [pow_two,← mul_pow];simp
  have hK : AnalyticAt ℂ K (x:ℂ) := analyticAt_hillL2RealGapPrimitiveSquare_on_gap q hq hr k hk x hx
  have hD0 : D (x:ℂ)≠0 := by
    dsimp only [D,K]
    rw [hillL2RealGapPrimitiveSquare_on_gap q hq hr k hk x hx]
    change deriv coshSquareCoordinate _≠0
    exact deriv_coshSquareCoordinate_sq_ne_zero _ (hillRealGapProfile_nonneg q hq hr k hk x hx)
  have hD : AnalyticAt ℂ D (x:ℂ) :=
    ((analyticOnNhd_squaredCosh (K (x:ℂ)) (mem_univ _)).deriv).comp hK
  have hG : AnalyticAt ℂ G (x:ℂ) :=
    (analyticAt_const.div (analyticAt_const.mul hD) (mul_ne_zero (by norm_num) hD0)).mul (hP _ (mem_univ _))
  obtain ⟨B,hB,hBo,hxB⟩ := _root_.eventually_nhds_iff.mp
    (hG.eventually_analyticAt.and (hD.continuousAt.eventually_ne hD0))
  refine ⟨B,G,hBo,hxB,fun E hE => (hB E hE).1,?_⟩
  intro E hE
  have hR := hillL2RealCutRoot_ne_zero q hq hr E (Or.inl hE.2)
  have he := primitive_root_ratio_eq σ (hillL2ShiftedPrimitive q k E) (K E)
    (hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E) hσ rfl
    (hillL2RealCutRoot_eq_shifted_sinh q k E) hR (hB E hE.1).2
  change σ/(4*D E)=hillL2ShiftedPrimitive q k E/hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E at he
  dsimp only [G,hillL2ShiftedDifferential]
  rw [he]
  ring

theorem analyticOnNhd_hillL2ShiftedDifferential_realCut
    (k : ℕ) (P : ℂ → ℂ) (hP : AnalyticOnNhd ℂ P univ) :
    AnalyticOnNhd ℂ (hillL2ShiftedDifferential q k P) (hillL2RealCutDomain q hq hr) := by
  intro E hE
  have hF := analyticOnNhd_hillL2RealCutPrimitive q hq hr E hE
  have hS : AnalyticAt ℂ (hillL2ShiftedPrimitive q k) E := hF.add analyticAt_const
  have hR : AnalyticAt ℂ (hillL2RealCutRoot (SpectralWeight.one.toCoeff q)) E :=
    analyticAt_const.mul (Complex.analyticAt_sinh.comp hF)
  exact (hS.mul (hP E (mem_univ _))).div hR (hillL2RealCutRoot_ne_zero q hq hr E hE)

theorem hillL2FilledShiftedDifferential_eq_on_realCut
    (k : ℕ) (P : ℂ → ℂ) (hP : AnalyticOnNhd ℂ P univ) :
    EqOn (hillL2FilledShiftedDifferential q k P) (hillL2ShiftedDifferential q k P)
      (hillL2RealCutDomain q hq hr) :=
  denseLimitExtension_eqOn_local _ _ _ _ dense_complex_nonreal
    (isOpen_hillL2RealCutDomain q hq hr)
    (analyticOnNhd_hillL2ShiftedDifferential_realCut q hq hr k P hP).continuousOn (fun _ _ => rfl)

theorem analyticOnNhd_hillL2FilledShiftedDifferential
    (k : ℕ) (hk : 1≤k) (P : ℂ → ℂ) (hP : AnalyticOnNhd ℂ P univ) :
    AnalyticOnNhd ℂ (hillL2FilledShiftedDifferential q k P)
      (ball (hillRealGapCenter q hq hr k : ℂ)
        (hillRealGapHalfLength q hq hr k+2*hillRealGapCollar q hq hr k)) := by
  obtain ⟨_hd,_hη,_hl,_hu,hsub⟩ := hillRealGapContour_geometry q hq hr k hk
  apply denseLimitExtension_analyticOnNhd _ _ _ dense_complex_nonreal
  intro E hE
  by_cases hseg : E∈segment ℝ (hillRealLabels q hq hr (2*k-1):ℂ) (hillRealLabels q hq hr (2*k):ℂ)
  · have hx := re_mem_Icc_of_mem_real_segment _ _ (monotone_hillRealLabels q hq hr (by omega : 2*k-1≤2*k)) E hseg
    have hi := im_eq_zero_of_mem_real_segment _ _ E hseg
    have hEC : E=(E.re : ℂ) := by apply Complex.ext <;> simp [hi]
    simpa only [← hEC] using exists_hillL2ShiftedDifferential_gap_chart q hq hr k hk P hP E.re hx
  · exact ⟨hillL2RealCutDomain q hq hr,hillL2ShiftedDifferential q k P,
      isOpen_hillL2RealCutDomain q hq hr,hsub ⟨hE,hseg⟩,
      analyticOnNhd_hillL2ShiftedDifferential_realCut q hq hr k P hP,fun _ _ => rfl⟩
/-- The filled differential has the literal article integrand on each
intrinsic contour, with the verified canonical product root. -/
theorem hillL2FilledShiftedDifferential_eq_on_gapContour
    (k : ℕ) (hk : 1≤k) (P : ℂ → ℂ) (hP : AnalyticOnNhd ℂ P univ) (E : ℂ)
    (hE : E∈sphere (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)) :
    hillL2FilledShiftedDifferential q k P E=hillL2ShiftedPrimitive q k E*
      (P E/hillEnergyCanonicalRootProduct q hq hr E) := by
  have hc := hillRealGapContour_sphere_subset q hq hr k hk hE
  rw [hillL2FilledShiftedDifferential_eq_on_realCut q hq hr k P hP hc,
    hillEnergyCanonicalRootProduct_eq_realCutRoot q hq hr hc]
  dsimp only [hillL2ShiftedDifferential]
  ring

/-- At a collapsed gap the actual shifted primitive itself is analytic
on the entire intrinsic outer disc. -/
theorem analyticOnNhd_hillL2ShiftedPrimitive_collapsed
    (k : ℕ) (hk : 1≤k)
    (hc : hillRealLabels q hq hr (2*k-1)=hillRealLabels q hq hr (2*k)) :
    AnalyticOnNhd ℂ (hillL2ShiftedPrimitive q k)
      (ball (hillRealGapCenter q hq hr k : ℂ)
        (hillRealGapHalfLength q hq hr k+2*hillRealGapCollar q hq hr k)) := by
  obtain ⟨_hd,_hη,_hl,_hu,hsub⟩ := hillRealGapContour_geometry q hq hr k hk
  intro E hE
  by_cases he : E=(hillRealLabels q hq hr (2*k-1):ℂ)
  · rw [he]
    exact (analyticAt_hillL2RealCutPrimitive_collapsed q hq hr k hk hc).add analyticAt_const
  · have hnot : E∉segment ℝ (hillRealLabels q hq hr (2*k-1):ℂ) (hillRealLabels q hq hr (2*k):ℂ) := by
      simpa only [← hc,segment_same,mem_singleton_iff] using he
    exact (analyticOnNhd_hillL2RealCutPrimitive q hq hr E (hsub ⟨hE,hnot⟩)).add analyticAt_const

end NLS.KdV
