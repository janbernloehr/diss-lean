import NLS.KdV.HillL2GroundSquare
import NLS.KdV.FrequencyPrimitiveContinuation
import NLS.KdV.HillGlobalDifferentialReality
import NLS.KdV.HillDeflatedCanonicalRoot
import NLS.KdV.HillEnergyRootIdentification
import NLS.ComplexAnalysis.SimplePoleQuotient

/-! # Actual cubic Hill kernel through the ground cut and collapsed gaps -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillL2CubicKernel (P : ℂ → ℂ) (E : ℂ) : ℂ :=
  hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E^3*P E/
    hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E

theorem exists_hillL2CubicKernel_ground_chart
    (P : ℂ → ℂ) (hP : AnalyticOnNhd ℂ P univ) (x : ℝ)
    (hx : x≤hillLowestEnergy q hq hr) :
    ∃ B : Set ℂ, ∃ G : ℂ → ℂ, IsOpen B ∧ (x:ℂ)∈B ∧
      AnalyticOnNhd ℂ G B ∧ EqOn G (hillL2CubicKernel q P) (B∩{E : ℂ | E.im≠0}) := by
  let F := hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q)
  let K : ℂ → ℂ := fun E => F E^2
  let D : ℂ → ℂ := fun E => deriv squaredCosh (K E)
  let G : ℂ → ℂ := fun E => K E*(1/(4*D E))*P E
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
    (hK.mul (analyticAt_const.div (analyticAt_const.mul hD) (mul_ne_zero (by norm_num) hD0))).mul (hP _ (mem_univ _))
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
  dsimp only [G,hillL2CubicKernel]
  rw [he]
  dsimp only [K,F]
  ring

theorem hillAbelianSelectedGlobalPsi_collapsed_label_eq_zero
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (hkn : k≠n)
    (hc : hillRealLabels q hq hr (2*k-1)=hillRealLabels q hq hr (2*k)) :
    hillAbelianSelectedGlobalPsi q hq hr n hn (hillRealLabels q hq hr (2*k-1))=0 := by
  have hb := (hillAbelianSelectedGlobalRoots q hq hr n hn).property (k-1)
  change _∈Icc _ _ at hb
  have he : k-1+1=k := by omega
  rw [he] at hb
  have hroot : (hillAbelianSelectedGlobalRoots q hq hr n hn).val (k-1)=hillRealLabels q hq hr (2*k-1) := by
    linarith [hb.1,hb.2]
  apply (hillAbelianSelectedGlobalPsi_zero_iff q hq hr n hn _).2
  exact ⟨k-1,by simpa only [he] using hkn,congrArg (fun a : ℝ => (a:ℂ)) hroot⟩

theorem exists_hillL2CubicKernel_collapsed_chart
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (hkn : k≠n)
    (hc : hillRealLabels q hq hr (2*k-1)=hillRealLabels q hq hr (2*k)) :
    ∃ B : Set ℂ, ∃ G : ℂ → ℂ, IsOpen B ∧ (hillRealLabels q hq hr (2*k-1):ℂ)∈B ∧
      AnalyticOnNhd ℂ G B ∧ EqOn G
        (hillL2CubicKernel q (hillAbelianSelectedGlobalPsi q hq hr n hn)) (B∩{E : ℂ | E.im≠0}) := by
  let a : ℂ := hillRealLabels q hq hr (2*k-1)
  let F := hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q)
  let U := hillDeflatedEnergyCanonicalRoot q hq hr k
  let P := hillAbelianSelectedGlobalPsi q hq hr n hn
  let g : ℂ → ℂ := fun E => P E/U E
  let H : ℂ → ℂ := fun E => -dslope g a E
  let G : ℂ → ℂ := fun E => F E^3*H E
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
    ((analyticAt_hillL2RealCutPrimitive_collapsed q hq hr k hk hc).pow 3).mul
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
  dsimp only [G,hillL2CubicKernel]
  rw [hH]
  dsimp only [F,P]
  ring

end NLS.KdV
