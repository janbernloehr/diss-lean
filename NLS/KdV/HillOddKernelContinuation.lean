import NLS.KdV.HillCubicKernelFilledDomain

/-! # Actual odd-power Hill kernels through the ground cut and closed gaps -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillL2OddKernel (m : ℕ) (P : ℂ → ℂ) (E : ℂ) : ℂ :=
  hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E^(2*m+1)*P E/
    hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E

theorem exists_hillL2OddKernel_ground_chart
    (m : ℕ) (P : ℂ → ℂ) (hP : AnalyticOnNhd ℂ P univ) (x : ℝ)
    (hx : x≤hillLowestEnergy q hq hr) :
    ∃ B : Set ℂ, ∃ G : ℂ → ℂ, IsOpen B ∧ (x:ℂ)∈B ∧
      AnalyticOnNhd ℂ G B ∧ EqOn G (hillL2OddKernel q m P) (B∩{E : ℂ | E.im≠0}) := by
  let F := hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q)
  let K : ℂ → ℂ := fun E => F E^2
  let D : ℂ → ℂ := fun E => deriv squaredCosh (K E)
  let G : ℂ → ℂ := fun E => (K E)^m*(1/(4*D E))*P E
  have hK : AnalyticAt ℂ K (x:ℂ) := by
    have he : hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) 0=K := by
      funext E
      simp only [hillL2RealGapPrimitiveSquare,Nat.cast_zero,mul_zero,zero_mul,add_zero]
      rfl
    rw [← he]
    exact analyticAt_hillL2GroundSquare q hq hr x hx
  have hFreal : (F (x:ℂ)).im=0 := by
    simpa only [F,hillL2RealCutPrimitive,ofReal_im,if_true,ofReal_re] using
      (hillL2UpperBoundaryPrimitive_ground_sheet q hq hr x hx).1
  have hFnonneg : 0≤(F (x:ℂ)).re := by
    simpa only [F,hillL2RealCutPrimitive,ofReal_im,if_true,ofReal_re] using
      (hillL2UpperBoundaryPrimitive_ground_sheet q hq hr x hx).2
  have hKval : K (x:ℂ)=(((F (x:ℂ)).re : ℂ))^2 := by
    have he : F (x:ℂ)=((F (x:ℂ)).re : ℂ) := by apply Complex.ext <;> simp [hFreal]
    exact congrArg (fun z : ℂ => z^2) he
  have hD0 : D (x:ℂ)≠0 := by
    dsimp only [D]
    rw [hKval]
    change deriv coshSquareCoordinate _≠0
    exact deriv_coshSquareCoordinate_sq_ne_zero _ hFnonneg
  have hD : AnalyticAt ℂ D (x:ℂ) :=
    ((analyticOnNhd_squaredCosh (K (x:ℂ)) (mem_univ _)).deriv).comp hK
  have hG : AnalyticAt ℂ G (x:ℂ) :=
    ((hK.pow m).mul (analyticAt_const.div (analyticAt_const.mul hD) (mul_ne_zero (by norm_num) hD0))).mul (hP _ (mem_univ _))
  obtain ⟨B,hB,hBo,hxB⟩ := _root_.eventually_nhds_iff.mp
    (hG.eventually_analyticAt.and (hD.continuousAt.eventually_ne hD0))
  refine ⟨B,G,hBo,hxB,fun E hE => (hB E hE).1,?_⟩
  intro E hE
  have hR : hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E≠0 :=
    hillL2RealCutRoot_ne_zero q hq hr E (Or.inl hE.2)
  have he := primitive_root_ratio_eq 1 (F E) (K E)
    (hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E) (by norm_num) rfl
    (by simp only [hillL2RealCutRoot,F,mul_one]) hR (hB E hE.1).2
  change 1/(4*D E)=F E/hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E at he
  dsimp only [G,hillL2OddKernel]
  rw [he]
  dsimp only [K,F]
  rw [pow_add,pow_mul,pow_one]
  ring

theorem exists_hillL2OddKernel_collapsed_chart
    (m n k : ℕ) (hn : 1≤n) (hk : 1≤k) (hkn : k≠n)
    (hc : hillRealLabels q hq hr (2*k-1)=hillRealLabels q hq hr (2*k)) :
    ∃ B : Set ℂ, ∃ G : ℂ → ℂ, IsOpen B ∧ (hillRealLabels q hq hr (2*k-1):ℂ)∈B ∧
      AnalyticOnNhd ℂ G B ∧ EqOn G
        (hillL2OddKernel q m (hillAbelianSelectedGlobalPsi q hq hr n hn)) (B∩{E : ℂ | E.im≠0}) := by
  let a : ℂ := hillRealLabels q hq hr (2*k-1)
  let F := hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q)
  let U := hillDeflatedEnergyCanonicalRoot q hq hr k
  let P := hillAbelianSelectedGlobalPsi q hq hr n hn
  let g : ℂ → ℂ := fun E => P E/U E
  let H : ℂ → ℂ := fun E => -dslope g a E
  let G : ℂ → ℂ := fun E => F E^(2*m+1)*H E
  have ha : a∈hillGapFilledDomain q hq hr k :=
    hillGapSegment_subset_filledDomain q hq hr k hk (left_mem_segment ℝ _ _)
  have hg : AnalyticAt ℂ g a :=
    (analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q hq hr n hn a (mem_univ _)).div
      (analyticOnNhd_hillDeflatedEnergyCanonicalRoot q hq hr k a ha)
      (hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr k hk a ha)
  have hg0 : g a=0 := by
    dsimp only [g,P,a]
    rw [hillAbelianSelectedGlobalPsi_collapsed_label_eq_zero q hq hr n k hn hk hkn hc,zero_div]
  have hG : AnalyticAt ℂ G a :=
    ((analyticAt_hillL2RealCutPrimitive_collapsed q hq hr k hk hc).pow (2*m+1)).mul
      (analyticAt_dslope_same hg).neg
  obtain ⟨R,hR,hGa⟩ := hG.exists_ball_analyticOnNhd
  refine ⟨ball a R,G,isOpen_ball,mem_ball_self hR,hGa,?_⟩
  intro E hE
  have hEa : E≠a := by intro he;exact hE.2 (by rw [he];exact ofReal_im _)
  have hUE : U E≠0 := hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr k hk E (Or.inl hE.2)
  have hroot : hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E=(a-E)*U E := by
    rw [← hillEnergyCanonicalRootProduct_eq_realCutRoot q hq hr (Or.inl hE.2),
      hillEnergyCanonicalRootProduct_eq_endpoint_mul_deflated q hq hr k hk E,← hc]
    have he : endpointRoot a a E=a-E := by
      simp only [endpointRoot,sub_self,zero_pow (by norm_num : 2≠0),
        normalizedStandardRoot_zeroGap,show (a+a)/2=a by ring]
    change endpointRoot a a E*U E=(a-E)*U E
    rw [he]
  have hH : H E=P E/hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E := by
    dsimp only [H]
    rw [dslope_of_ne g hEa,slope_def_field,hg0,sub_zero,hroot]
    dsimp only [g]
    field_simp
    ring
  dsimp only [G,hillL2OddKernel]
  rw [hH]
  dsimp only [F,P]
  ring

/-- A single continuation chosen by the actual nonreal spectral data. -/
def hillL2FilledOddKernel (m : ℕ) (P : ℂ → ℂ) : ℂ → ℂ :=
  denseLimitExtension (hillL2OddKernel q m P) {E : ℂ | E.im≠0}

theorem analyticOnNhd_hillL2OddKernel_realCut
    (m : ℕ) (P : ℂ → ℂ) (hP : AnalyticOnNhd ℂ P univ) :
    AnalyticOnNhd ℂ (hillL2OddKernel q m P) (hillL2RealCutDomain q hq hr) := by
  intro E hE
  have hF := analyticOnNhd_hillL2RealCutPrimitive q hq hr E hE
  have hR : AnalyticAt ℂ (hillL2RealCutRoot (SpectralWeight.one.toCoeff q)) E :=
    analyticAt_const.mul (Complex.analyticAt_sinh.comp hF)
  exact ((hF.pow (2*m+1)).mul (hP E (mem_univ _))).div hR
    (hillL2RealCutRoot_ne_zero q hq hr E hE)

theorem hillL2FilledOddKernel_eq_on_realCut
    (m : ℕ) (P : ℂ → ℂ) (hP : AnalyticOnNhd ℂ P univ) :
    EqOn (hillL2FilledOddKernel q m P) (hillL2OddKernel q m P) (hillL2RealCutDomain q hq hr) := by
  exact denseLimitExtension_eqOn_local _ _ _ _ dense_complex_nonreal
    (isOpen_hillL2RealCutDomain q hq hr)
    (analyticOnNhd_hillL2OddKernel_realCut q hq hr m P hP).continuousOn (fun _ _ => rfl)

theorem analyticOnNhd_hillL2FilledOddKernel
    (m n : ℕ) (hn : 1≤n) :
    AnalyticOnNhd ℂ (hillL2FilledOddKernel q m (hillAbelianSelectedGlobalPsi q hq hr n hn))
      (hillCubicFilledDomain q hq hr n) := by
  let P := hillAbelianSelectedGlobalPsi q hq hr n hn
  have hP : AnalyticOnNhd ℂ P univ := analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q hq hr n hn
  apply denseLimitExtension_analyticOnNhd _ _ _ dense_complex_nonreal
  intro E hE
  have hnot := hE.2
  rcases hE.1 with hcut | hground | ⟨k,hk,hclosed,hre⟩
  · exact ⟨hillL2RealCutDomain q hq hr,hillL2OddKernel q m P,
      isOpen_hillL2RealCutDomain q hq hr,hcut,
      analyticOnNhd_hillL2OddKernel_realCut q hq hr m P hP,fun _ _ => rfl⟩
  · by_cases hi : E.im≠0
    · exact ⟨hillL2RealCutDomain q hq hr,hillL2OddKernel q m P,
        isOpen_hillL2RealCutDomain q hq hr,Or.inl hi,
        analyticOnNhd_hillL2OddKernel_realCut q hq hr m P hP,fun _ _ => rfl⟩
    have hEC : E=(E.re : ℂ) := by apply Complex.ext <;> simp [not_ne_iff.mp hi]
    simpa only [← hEC] using exists_hillL2OddKernel_ground_chart q hq hr m P hP E.re hground
  · by_cases hi : E.im≠0
    · exact ⟨hillL2RealCutDomain q hq hr,hillL2OddKernel q m P,
        isOpen_hillL2RealCutDomain q hq hr,Or.inl hi,
        analyticOnNhd_hillL2OddKernel_realCut q hq hr m P hP,fun _ _ => rfl⟩
    have hEC : E=(hillRealLabels q hq hr (2*k-1) : ℂ) := by
      apply Complex.ext <;> simp [hre,not_ne_iff.mp hi]
    have hkn : k≠n := by
      intro he
      subst k
      exact hnot (hEC ▸ left_mem_segment ℝ _ _)
    simpa only [← hEC] using exists_hillL2OddKernel_collapsed_chart q hq hr m n k hn hk hkn hclosed

include hq hr in
/-- Filling the real cuts changes no centered circle integral. -/
theorem circleIntegral_hillL2FilledOddKernel_eq
    (m : ℕ) (P : ℂ → ℂ) (hP : AnalyticOnNhd ℂ P univ) (r : ℝ) (hrp : 0<r) :
    (∮ E in C(0,r), hillL2FilledOddKernel q m P E)=
      ∮ E in C(0,r), hillL2OddKernel q m P E := by
  apply circleIntegral.circleIntegral_congr_codiscreteWithin ?_ hrp.ne'
  rw [abs_of_pos hrp]
  exact eventuallyEq_circle_of_eq_nonreal _ _ r hrp (fun E hE =>
    hillL2FilledOddKernel_eq_on_realCut q hq hr m P hP (Or.inl hE))

include hq hr in
/-- The actual and filled odd-power kernels have the same circle integrability. -/
theorem circleIntegrable_hillL2FilledOddKernel_iff
    (m : ℕ) (P : ℂ → ℂ) (hP : AnalyticOnNhd ℂ P univ) (r : ℝ) (hrp : 0<r) :
    CircleIntegrable (hillL2FilledOddKernel q m P) 0 r ↔ CircleIntegrable (hillL2OddKernel q m P) 0 r := by
  apply circleIntegrable_congr_codiscreteWithin
  rw [abs_of_pos hrp]
  exact eventuallyEq_circle_of_eq_nonreal _ _ r hrp (fun E hE =>
    hillL2FilledOddKernel_eq_on_realCut q hq hr m P hP (Or.inl hE))

end NLS.KdV
