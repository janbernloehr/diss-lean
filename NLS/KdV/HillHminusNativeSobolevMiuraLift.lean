import NLS.KdV.HillHminusStrongMiuraCharts

/-! # Explicit native Sobolev realizations of the SAME actual Hill Miura lift

The literal rough coefficients define a stronger native function on each
Sobolev domain. At EVERY eligible point it agrees EXACTLY on an open neighborhood
with a native map complex analytic in the stronger norms.
The chosen rough chart, energy shift and original Hill labels are retained.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

/-- Native source regularity gives literal native lift membership for ANY
actual chart. This membership statement does not itself assert analyticity. -/
theorem HillHminusMiuraChart.lift_mem_sobolev_of_native
    (C : HillHminusMiuraChart) (t : ℝ) (ht : 0≤t)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hq : periodOneSobolevImageInclusion t ht q∈C.domain) :
    Memℓp (fun n => (Weight.sobolev t n : ℂ)*C.lift (periodOneSobolevImageInclusion t ht q) n) 2 := by
  have hf : Memℓp (fun n => (Weight.sobolev (t-1) n : ℂ)*
      (periodOneSobolevImageInclusion t ht q).val n) 2 := by
    simpa only [periodOneSobolevImageInclusion_apply] using
      (show Memℓp (fun n => (Weight.sobolev (t-1) n : ℂ)*q.val n) 2 from q.property)
  have H := periodOneMiura_lift_mem_sobolev_of_image _ (C.lift _) C.energyShift (C.image _ hq)
    (t-1) (by linarith) hf
  simpa only [sub_add_cancel] using H

/-- The actual rough lift, using its SAME raw coefficients as a native
H^t function on native H^(t-1) inputs. Zero extends it outside the chart. -/
def hillHminusNativeSobolevMiuraLift (C : HillHminusMiuraChart) (t : ℝ) (ht : 0≤t)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2) : WeightedCoeff (Weight.sobolev t) 2 := by
  classical
  exact if hq : periodOneSobolevImageInclusion t ht q∈C.domain then
    ⟨C.lift (periodOneSobolevImageInclusion t ht q),C.lift_mem_sobolev_of_native t ht q hq⟩ else 0

@[simp] theorem hillHminusNativeSobolevMiuraLift_apply_of_mem
    (C : HillHminusMiuraChart) (t : ℝ) (ht : 0≤t)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hq : periodOneSobolevImageInclusion t ht q∈C.domain) (n : ℤ) :
    (hillHminusNativeSobolevMiuraLift C t ht q).val n=C.lift (periodOneSobolevImageInclusion t ht q) n := by
  classical
  simp [hillHminusNativeSobolevMiuraLift, hq]

theorem hillHminusNativeSobolevMiuraLift_toL2_of_mem
    (C : HillHminusMiuraChart) (t : ℝ) (ht : 0≤t)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hq : periodOneSobolevImageInclusion t ht q∈C.domain) :
    WeightedCoeff.sobolevToL2 ht (hillHminusNativeSobolevMiuraLift C t ht q)=
      C.lift (periodOneSobolevImageInclusion t ht q) := by
  ext n
  rw [WeightedCoeff.sobolevToL2_apply,hillHminusNativeSobolevMiuraLift_apply_of_mem C t ht q hq n]

private theorem nativeLift_eq_of_toL2_eq
    (C : HillHminusMiuraChart) (t : ℝ) (ht : 0≤t)
    (p : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hp : periodOneSobolevImageInclusion t ht p∈C.domain)
    (a : WeightedCoeff (Weight.sobolev t) 2)
    (ha : WeightedCoeff.sobolevToL2 ht a=C.lift (periodOneSobolevImageInclusion t ht p)) :
    a=hillHminusNativeSobolevMiuraLift C t ht p := by
  apply Subtype.ext
  funext n
  have H := congrArg (fun v : Coeff 2 => v n) ha
  rw [WeightedCoeff.sobolevToL2_apply] at H
  exact H.trans (hillHminusNativeSobolevMiuraLift_apply_of_mem C t ht p hp n).symm

/-- At EVERY real rough base, ONE actual complex Hill Miura chart has
EXACT native analytic germs at EVERY eligible stronger Sobolev source,
before all orders and sources. All original Hill labels, real form and
the outside-spectrum energy shift are retained. -/
theorem exists_hillHminus_real_native_all_sobolev_analytic_Miura_germs
    (q0 : PeriodOneHminusOne) (hr0 : IsRealPeriodOneHminusOne q0) :
    ∃ C : HillHminusMiuraChart, ∃ c : ℝ,
      0<c ∧ C.energyShift=(c : ℂ)^2 ∧ q0∈C.domain ∧
      (∀ q∈C.domain, IsRealPeriodOneHminusOne q → periodOneL2Conjugation (C.lift q)=C.lift q) ∧
      (∀ q∈C.domain, hillHminusRadicand q (-C.energyShift)≠0) ∧
      (∀ q∈C.domain, ∀ hr : IsRealPeriodOneHminusOne q, ∀ n : ℕ, 0<n →
        hillHminusRealLabels q hr (2*n-1)=(hillMiuraDiracLeft (C.lift q) n).re^2-c^2 ∧
        hillHminusRealLabels q hr (2*n)=(hillMiuraDiracRight (C.lift q) n).re^2-c^2) ∧
      (∀ t : ℝ, ∀ ht : 0≤t, ∀ q : WeightedCoeff (Weight.sobolev (t-1)) 2,
        periodOneSobolevImageInclusion t ht q∈C.domain →
        WeightedCoeff.sobolevToL2 ht (hillHminusNativeSobolevMiuraLift C t ht q)=
          C.lift (periodOneSobolevImageInclusion t ht q)) ∧
      ∀ t : ℝ, ∀ ht : 0≤t, ∀ q : WeightedCoeff (Weight.sobolev (t-1)) 2,
        periodOneSobolevImageInclusion t ht q∈C.domain →
        ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
          ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev t) 2,
            AnalyticOnNhd ℂ g V ∧ ∀ p∈V,
              periodOneSobolevImageInclusion t ht p∈C.domain ∧
              g p=hillHminusNativeSobolevMiuraLift C t ht p := by
  obtain ⟨C,c,hc,hshift,hq0,hreal,houtside,hlabels,hstrong⟩ :=
    exists_hillHminus_real_Miura_all_strong_sobolev_chart q0 hr0
  refine ⟨C,c,hc,hshift,hq0,hreal,houtside,hlabels,?_,?_⟩
  · exact fun t ht q hq => hillHminusNativeSobolevMiuraLift_toL2_of_mem C t ht q hq
  · intro t ht q hq
    obtain ⟨V,hV,hqV,g,hga,hdata⟩ := hstrong t ht q hq
    exact ⟨V,hV,hqV,g,hga,fun p hp =>
      ⟨(hdata p hp).1,nativeLift_eq_of_toL2_eq C t ht p (hdata p hp).1 (g p) (hdata p hp).2⟩⟩

end NLS.KdV
