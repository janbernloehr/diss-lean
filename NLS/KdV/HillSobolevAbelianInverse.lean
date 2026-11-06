import NLS.KdV.HillSobolevAbelianDerivative
import NLS.KdV.HillHminusAbelianDerivative
import NLS.ComplexAnalysis.AnalyticOpenInverse
import NLS.ComplexAnalysis.LocalRightInverseMatching

/-! # Actual stronger Abelian inverse germs at zero

Native complex analyticity and the exact Fourier derivative give a
strong inverse by the Banach analytic inverse theorem. Weak local
injectivity identifies it with the GIVEN rough inverse. No inference
from pointwise real Sobolev membership is used.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

/-- For every native order, a genuine analytic forward restriction and
its exact Fourier jet give a strong analytic germ of the SAME rough inverse.
The target chart is the isometric mean-zero chart of h^(s+1/2). -/
theorem exists_sobolev_abelian_inverse_of_actual_restriction
    (η : ℝ) (hη : 0<η)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (hZa : AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η)) (hZ0 : Z 0=0)
    (hFourier : ∀ h : PeriodOneHminusOne, h.val 0=0 → ∀ j : ℤ,
      ((fderiv ℂ Z 0) h).val j=(Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹*h.val j)
    (W : Set (DeletedCoeff 2 0)) (hW : IsOpen W) (h0W : (0 : DeletedCoeff 2 0)∈W)
    (R : DeletedCoeff 2 0 → PeriodOneHminusOne) (hRc : ContinuousOn R W) (hR0 : R 0=0)
    (hRdata : ∀ b∈W, (R b).val 0=0 ∧
      Z (R b)=WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b)
    (s : ℝ) (hs : -1≤s)
    (V : Set (WeightedCoeff (Weight.sobolev s) 2)) (hV : IsOpen V)
    (h0V : (0 : WeightedCoeff (Weight.sobolev s) 2)∈V)
    (g : WeightedCoeff (Weight.sobolev s) 2 → WeightedCoeff (Weight.sobolev (s+1/2)) 2)
    (hga : AnalyticOnNhd ℂ g V)
    (hcomm : ∀ p∈V, WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤s+1/2) (g p)=
      Z (WeightedCoeff.sobolevInclusion hs p)) :
    ∃ T : Set (DeletedCoeff 2 0), IsOpen T ∧ 0∈T ∧
      ∃ G : DeletedCoeff 2 0 → WeightedCoeff (Weight.sobolev s) 2,
        AnalyticOnNhd ℂ G T ∧ G 0=0 ∧ ∀ b∈T,
          WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ)≤s+1/2) b∈W ∧
          WeightedCoeff.sobolevInclusion hs (G b)=
            R (WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ)≤s+1/2) b) ∧
          G b∈V ∧ (G b).val 0=0 ∧
          g (G b)=WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (s+1/2)) b := by
  let L0 := WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))
  let P0 := WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1))
  let Q0 := WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))
  let F0 := WeightedCoeff.meanZeroWeightedMap (Weight.sobolev (-1/2))
    (fun u => Z ((WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2).symm u))
  have hF0a : AnalyticOnNhd ℂ F0 (ball (0 : DeletedCoeff 2 0) η) := by
    intro a ha
    have hm : L0 a∈ball (0 : PeriodOneHminusOne) η := by
      simpa only [L0,mem_ball_zero_iff,WeightedCoeff.meanZeroWeightedLift_norm] using ha
    exact (Q0.analyticAt _).comp ((hZa _ hm).comp (L0.analyticAt a))
  have hunit0 := isUnit_fderiv_meanZeroHminusAbelianMap Z
    (hZa 0 (mem_ball_self hη)).differentiableAt hFourier
  obtain ⟨U0,_B0,hU0,_hB0,h0U0,_h0B0,_hsub0,_him0,hbij0,_G0,_ha0,_hGa0,_hl0,_hr0⟩ :=
    NLS.ComplexAnalysis.exists_analytic_inverse_open_sets isOpen_ball hF0a (mem_ball_self hη) hunit0
  let R0 := fun b => P0 (R b)
  have hR0zero : R0 0=0 := by simp only [R0,hR0,map_zero]
  have hR0solve (b : DeletedCoeff 2 0) (hb : b∈W) : F0 (R0 b)=b := by
    change Q0 (Z (L0 (P0 (R b))))=b
    rw [WeightedCoeff.meanZeroWeightedLift_projection _ _ (hRdata b hb).1,(hRdata b hb).2]
    exact WeightedCoeff.meanZeroWeightedProjection_lift _ b
  let L := WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev s)
  let Q := WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (s+1/2))
  let F := WeightedCoeff.meanZeroWeightedMap (Weight.sobolev (s+1/2))
    (fun u => g ((WeightedCoeff.weightIsometry (Weight.sobolev s) 2).symm u))
  let A := L ⁻¹' V
  have hA : IsOpen A := hV.preimage L.continuous
  have h0A : (0 : DeletedCoeff 2 0)∈A := by simpa only [A,mem_preimage,map_zero] using h0V
  have hFa : AnalyticOnNhd ℂ F A := by
    intro a ha
    exact (Q.analyticAt _).comp ((hga (L a) ha).comp (L.analyticAt a))
  have hg0 : g 0=0 := by
    apply WeightedCoeff.sobolevInclusion_injective (by linarith : (-1/2 : ℝ)≤s+1/2)
    simpa only [map_zero,hZ0] using hcomm 0 h0V
  have hF0 : F 0=0 := by change Q (g (L 0))=0;rw [map_zero,hg0,map_zero]
  have hraw := sobolev_abelian_fourier_derivative_of_restriction s hs Z
    (hZa 0 (mem_ball_self hη)).differentiableAt hFourier g (hga 0 h0V).differentiableAt
    (Filter.eventuallyEq_of_mem (hV.mem_nhds h0V) hcomm)
  have hd : fderiv ℂ F 0=hillAbelianWeightedFourierEquiv.toContinuousLinearMap :=
    fderiv_meanZeroSobolevAbelianMap_eq s g (hga 0 h0V).differentiableAt hraw
  have hunit : IsUnit (fderiv ℂ F 0) := by
    rw [hd]
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr hillAbelianWeightedFourierEquiv.bijective
  obtain ⟨US,WS,_hUS,hWS,h0US,h0WS,hsubS,_himS,_hbijS,GS,_hFaS,hGSa,hleftS,hrightS⟩ :=
    NLS.ComplexAnalysis.exists_analytic_inverse_open_sets hA hFa h0A hunit
  have h0WS' : (0 : DeletedCoeff 2 0)∈WS := by simpa only [hF0] using h0WS
  have hGS0 : GS 0=0 := by simpa only [hF0] using hleftS 0 h0US
  let iE := WeightedCoeff.meanZeroSobolevInclusion hs
  let iF := WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ)≤s+1/2)
  have hnormalized (a : DeletedCoeff 2 0) (ha : a∈A) : F0 (iE a)=iF (F a) := by
    change Q0 (Z (L0 (iE a)))=iF (Q (g (L a)))
    rw [WeightedCoeff.meanZeroSobolevInclusion_lift,←hcomm (L a) ha]
    exact (WeightedCoeff.meanZeroSobolevInclusion_projection _ _).symm
  have hnewsolve (b : DeletedCoeff 2 0) (hb : b∈WS) : F0 (iE (GS b))=iF b := by
    rw [hnormalized _ (hsubS (hrightS b hb).1),(hrightS b hb).2]
  obtain ⟨T,hT,h0T,hTsub,_hGSaT,hmatch⟩ := NLS.ComplexAnalysis.exists_local_rightInverse_matching
    iE iF F0 U0 hU0 h0U0 hbij0.injOn W hW h0W R0
    (P0.continuous.comp_continuousOn hRc) hR0zero hR0solve
    WS hWS h0WS' GS hGSa hGS0 hnewsolve
  let G := fun b => L (GS b)
  have hGinc (b : DeletedCoeff 2 0) (hb : b∈T) :
      WeightedCoeff.sobolevInclusion hs (G b)=R (iF b) := by
    have H := congrArg L0 (hmatch b hb).2
    rw [WeightedCoeff.meanZeroSobolevInclusion_lift] at H
    exact H.trans (WeightedCoeff.meanZeroWeightedLift_projection _ _ (hRdata _ (hmatch b hb).1).1)
  refine ⟨T,hT,h0T,G,?_,?_,?_⟩
  · intro b hb
    exact (L.analyticAt _).comp (hGSa b (hTsub hb))
  · change L (GS 0)=0
    rw [hGS0,map_zero]
  · intro b hb
    have hGb : G b∈V := hsubS (hrightS b (hTsub hb)).1
    refine ⟨(hmatch b hb).1,hGinc b hb,hGb,WeightedCoeff.meanZeroWeightedLift_zero _ _,?_⟩
    apply WeightedCoeff.sobolevInclusion_injective (by linarith : (-1/2 : ℝ)≤s+1/2)
    rw [hcomm (G b) hGb,hGinc b hb,(hRdata _ (hmatch b hb).1).2]
    exact WeightedCoeff.meanZeroSobolevInclusion_lift (by linarith : (-1/2 : ℝ)≤s+1/2) b

end NLS.KdV
