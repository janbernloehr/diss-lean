import NLS.MKdV.MiuraNativeActionVelocityContinuity

/-! # Local analytic extensions of actual physical action Lie derivatives

An independently defined real functional with a local complex analytic
extension has a locally analytic derivative along the actual complete
physical action flow. This uses the checked velocity, not a prescribed
coordinate vector field.
-/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.MKdV

def miuraNativeActionLieDerivative (s : ℕ) (j : ℕ)
    (F : MiuraRealSobolevSource s → ℂ) (a : MiuraRealSobolevSource s) : ℂ :=
  deriv (fun t => F (miuraNativeRealActionFlow s a j t)) 0

theorem miuraNativeActionLieDerivative_conj (s j : ℕ)
    (F : MiuraRealSobolevSource s → ℂ) (a : MiuraRealSobolevSource s) :
    miuraNativeActionLieDerivative s j (fun b => conj (F b)) a =
      conj (miuraNativeActionLieDerivative s j F a) := by
  exact deriv.star

theorem hasDerivAt_miuraNativeAction_functional_of_analytic_extension
    (s : ℕ) (hs : 1 ≤ s) (j : ℕ) (hj : 1 ≤ j)
    (F : MiuraRealSobolevSource s → ℂ) (a : MiuraRealSobolevSource s)
    (P : ScalarSobolev s → ℂ) (hP : AnalyticAt ℂ P a.val)
    (hmatch : ∀ᶠ b : MiuraRealSobolevSource s in 𝓝 a,P b.val = F b) :
    HasDerivAt (fun t => F (miuraNativeRealActionFlow s a j t))
      (fderiv ℂ P a.val (miuraNativeActionVelocity s a j)) 0 := by
  have hflow : Continuous (miuraNativeRealActionFlow s a j) :=
    (continuous_miuraActionFlow s a.val (fun k => a.property k) j).subtype_mk _
  have h0 : miuraNativeRealActionFlow s a j 0 = a :=
    Subtype.ext (miuraActionFlow_zero s a.val (fun k => a.property k) j)
  have he : (fun t => F (miuraNativeRealActionFlow s a j t)) =ᶠ[𝓝 (0:ℝ)]
      (fun t => P (miuraActionFlow s a.val (fun k => a.property k) j t)) := by
    have ht := hflow.tendsto 0
    rw [h0] at ht
    filter_upwards [ht.eventually hmatch] with t hm
    exact hm.symm
  have hPflow : HasFDerivAt P ((fderiv ℂ P a.val).restrictScalars ℝ)
      (miuraActionFlow s a.val (fun k => a.property k) j 0) := by
    rw [miuraActionFlow_zero]
    exact hP.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hd := hPflow.comp_hasDerivAt 0
    (hasDerivAt_miuraActionFlow_native_zero s hs a j hj)
  exact hd.congr_of_eventuallyEq he

theorem exists_miuraNativeActionLieDerivative_analytic_extension
    (s : ℕ) (hs : 1 ≤ s) (j : ℕ) (hj : 1 ≤ j)
    (F : MiuraRealSobolevSource s → ℂ) (a : MiuraRealSobolevSource s)
    (P : ScalarSobolev s → ℂ) (hP : AnalyticAt ℂ P a.val)
    (hmatch : ∀ᶠ b : MiuraRealSobolevSource s in 𝓝 a,P b.val = F b) :
    ∃ L : ScalarSobolev s → ℂ,AnalyticAt ℂ L a.val ∧
      ∀ᶠ b : MiuraRealSobolevSource s in 𝓝 a,L b.val = miuraNativeActionLieDerivative s j F b := by
  obtain ⟨V,hV,hVm⟩ := exists_miuraNativeActionVelocity_analytic_extension s hs j hj a
  let L (b : ScalarSobolev s) := fderiv ℂ P b (V b)
  have hL : AnalyticAt ℂ L a.val :=
    ((ContinuousLinearMap.apply (E := ScalarSobolev s) ℂ ℂ).analyticAt_bilinear _).comp₂ hV hP.fderiv
  obtain ⟨U,hU,hUopen,haU⟩ := mem_nhds_iff.mp hmatch
  have hnear : ∀ᶠ b : MiuraRealSobolevSource s in 𝓝 a,AnalyticAt ℂ P b.val :=
    continuous_subtype_val.continuousAt.tendsto.eventually hP.eventually_analyticAt
  refine ⟨L,hL,?_⟩
  filter_upwards [hVm,hnear,hUopen.mem_nhds haU] with b hv hp hb
  have hm : ∀ᶠ c : MiuraRealSobolevSource s in 𝓝 b,P c.val = F c :=
    Filter.mem_of_superset (hUopen.mem_nhds hb) hU
  have hd := hasDerivAt_miuraNativeAction_functional_of_analytic_extension s hs j hj F b P hp hm
  dsimp only [L,miuraNativeActionLieDerivative]
  rw [hv,hd.deriv]

theorem continuousAt_miuraNativeActionLieDerivative_of_analytic_extension
    (s : ℕ) (hs : 1 ≤ s) (j : ℕ) (hj : 1 ≤ j)
    (F : MiuraRealSobolevSource s → ℂ) (a : MiuraRealSobolevSource s)
    (P : ScalarSobolev s → ℂ) (hP : AnalyticAt ℂ P a.val)
    (hmatch : ∀ᶠ b : MiuraRealSobolevSource s in 𝓝 a,P b.val = F b) :
    ContinuousAt (miuraNativeActionLieDerivative s j F) a := by
  obtain ⟨L,hL,he⟩ := exists_miuraNativeActionLieDerivative_analytic_extension s hs j hj F a P hP hmatch
  exact (hL.continuousAt.comp continuous_subtype_val.continuousAt).congr_of_eventuallyEq
    (Filter.EventuallyEq.symm he)

end NLS.MKdV
