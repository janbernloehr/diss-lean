import NLS.ComplexAnalysis.ParametricIntervalIntegralAnalytic
import NLS.ComplexAnalysis.LogarithmicPathIntegral

/-! # Logarithm continuation along a convex parameter domain

Integrating the logarithmic source derivative along straight source
segments gives a jointly analytic increment. Exponentiating the
increment transports the multiplier exactly from the fixed source to
the new source. The spectral domain need not be bounded or convex.
-/
noncomputable section
open Set Filter Topology Complex MeasureTheory
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

def sourceSegmentMap (b : A) (q : ℂ × (ℂ × A)) : ℂ × A :=
  (q.2.1,b+q.1 • (q.2.2-b))

def sourceLogIntegrand (M : ℂ × A → ℂ) (b : A) (q : ℂ × (ℂ × A)) : ℂ :=
  (fderiv ℂ M (sourceSegmentMap b q)) (0,q.2.2-b) / M (sourceSegmentMap b q)

/-- The logarithmic increment along a straight source segment. -/
def parametricSourceLogIncrement (M : ℂ × A → ℂ) (b : A) (t : ℂ × A) : ℂ :=
  ∫ s in (0:ℝ)..1, sourceLogIntegrand M b ((s : ℂ),t)

theorem analyticAt_sourceSegmentMap (b : A) (q : ℂ × (ℂ × A)) :
    AnalyticAt ℂ (sourceSegmentMap b) q := by
  have hz : AnalyticAt ℂ (fun q : ℂ × (ℂ × A) => q.2.1) q :=
    analyticAt_fst.comp (f := fun q : ℂ × (ℂ × A) => q.2) analyticAt_snd
  have ha : AnalyticAt ℂ (fun q : ℂ × (ℂ × A) => q.2.2) q :=
    analyticAt_snd.comp (f := fun q : ℂ × (ℂ × A) => q.2) analyticAt_snd
  exact hz.prod (analyticAt_const.add (analyticAt_fst.smul (ha.sub analyticAt_const)))

theorem analyticOnNhd_sourceLogIntegrand (M : ℂ × A → ℂ) (b : A) (D : Set (ℂ × A))
    (hM : AnalyticOnNhd ℂ M D) (hne : ∀ t ∈ D, M t ≠ 0) :
    AnalyticOnNhd ℂ (sourceLogIntegrand M b) (sourceSegmentMap b ⁻¹' D) := by
  intro q hq
  have hT := analyticAt_sourceSegmentMap b q
  have hd := (hM.fderiv _ hq).comp (f := sourceSegmentMap b) hT
  have ha : AnalyticAt ℂ (fun q : ℂ × (ℂ × A) => q.2.2) q :=
    analyticAt_snd.comp (f := fun q : ℂ × (ℂ × A) => q.2) analyticAt_snd
  have hv : AnalyticAt ℂ (fun q : ℂ × (ℂ × A) => ((0 : ℂ),q.2.2-b)) q :=
    analyticAt_const.prod (ha.sub analyticAt_const)
  have happ := ((ContinuousLinearMap.id ℂ ((ℂ × A) →L[ℂ] ℂ)).analyticAt_bilinear
    (fderiv ℂ M (sourceSegmentMap b q),(0,q.2.2-b))).comp
      (f := fun q : ℂ × (ℂ × A) => (fderiv ℂ M (sourceSegmentMap b q),(0,q.2.2-b))) (hd.prod hv)
  exact happ.div ((hM _ hq).comp (f := sourceSegmentMap b) hT) (hne _ hq)

theorem sourceSegmentMap_mem (U : Set ℂ) (V : Set A) (b : A)
    (hV : Convex ℝ V) (hb : b ∈ V) (t : ℂ × A) (ht : t ∈ U ×ˢ V)
    (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : sourceSegmentMap b ((s : ℂ),t) ∈ U ×ˢ V := by
  refine ⟨ht.1,?_⟩
  have h := hV.lineMap_mem hb ht.2 hs
  simpa only [sourceSegmentMap,AffineMap.lineMap_apply_module',Complex.coe_smul,add_comm] using h

/-- A single source domain works over the whole spectral set, with no
spectral compactness or boundedness assumption. -/
theorem analyticOnNhd_parametricSourceLogIncrement
    (M : ℂ × A → ℂ) (U : Set ℂ) (V : Set A) (b : A)
    (hU : IsOpen U) (hV : IsOpen V) (hcV : Convex ℝ V) (hb : b ∈ V)
    (hM : AnalyticOnNhd ℂ M (U ×ˢ V)) (hne : ∀ t ∈ U ×ˢ V, M t ≠ 0) :
    AnalyticOnNhd ℂ (parametricSourceLogIncrement M b) (U ×ˢ V) := by
  have hT : Continuous (sourceSegmentMap b) := continuous_iff_continuousAt.mpr (fun x => (analyticAt_sourceSegmentMap b x).continuousAt)
  apply analyticOnNhd_intervalIntegral_of_jointAnalytic (sourceLogIntegrand M b)
    ((hU.prod hV).preimage hT) (analyticOnNhd_sourceLogIntegrand M b _ hM hne) 0 1 (hU.prod hV)
  intro t ht s hs
  exact sourceSegmentMap_mem U V b hcV hb t ht s (by simpa only [uIcc_of_le zero_le_one] using hs)

@[simp] theorem parametricSourceLogIncrement_base (M : ℂ × A → ℂ) (b : A) (z : ℂ) :
    parametricSourceLogIncrement M b (z,b) = 0 := by
  have hz : ((0 : ℂ),(0 : A)) = (0 : ℂ × A) := rfl
  simp [parametricSourceLogIncrement,sourceLogIntegrand,hz]

/-- The increment transports the multiplier exactly, without a
principal-logarithm assumption or an undetermined period. -/
theorem exp_parametricSourceLogIncrement_mul_of_segment
    (M : ℂ × A → ℂ) (D : Set (ℂ × A)) (b : A)
    (hM : AnalyticOnNhd ℂ M D) (hne : ∀ t ∈ D, M t ≠ 0)
    (t : ℂ × A) (hsegment : ∀ s ∈ Icc (0:ℝ) 1, sourceSegmentMap b ((s : ℂ),t) ∈ D) :
    exp (parametricSourceLogIncrement M b t)*M (t.1,b) = M t := by
  let q : ℝ → ℂ := fun s => sourceLogIntegrand M b ((s : ℂ),t)
  let g : ℝ → ℂ := fun s => M (sourceSegmentMap b ((s : ℂ),t))
  have hmem := hsegment
  have hmap : Continuous (fun s : ℝ => ((s : ℂ),t)) := continuous_ofReal.prodMk continuous_const
  have hqc : ContinuousOn q (Icc (0:ℝ) 1) :=
    (analyticOnNhd_sourceLogIntegrand M b _ hM hne).continuousOn.comp hmap.continuousOn hmem
  have hgc : ContinuousOn g (Icc (0:ℝ) 1) :=
    hM.continuousOn.comp
      ((show Continuous (sourceSegmentMap b) from continuous_iff_continuousAt.mpr (fun x => (analyticAt_sourceSegmentMap b x).continuousAt)).comp hmap).continuousOn hmem
  have hgd (s : ℝ) (hs : s ∈ Ioo (0:ℝ) 1) : HasDerivAt g (q s*g s) s := by
    have hpath : HasDerivAt (fun w : ℂ => (t.1,b+w • (t.2-b))) (0,t.2-b) (s : ℂ) := by
      simpa using (hasDerivAt_const (s : ℂ) t.1).prodMk
        (((hasDerivAt_id (s : ℂ)).smul_const (t.2-b)).const_add b)
    have h := ((hM _ (hmem s (Ioo_subset_Icc_self hs))).differentiableAt.hasFDerivAt.comp_hasDerivAt (s : ℂ) hpath).comp_ofReal
    convert! h using 1
    change ((fderiv ℂ M (sourceSegmentMap b ((s : ℂ),t))) (0,t.2-b) / M (sourceSegmentMap b ((s : ℂ),t))) * M (sourceSegmentMap b ((s : ℂ),t)) = _
    exact div_mul_cancel₀ _ (hne _ (hmem s (Ioo_subset_Icc_self hs)))
  have he := eq_exp_integral_mul_of_hasDerivAt q g
    (hqc.intervalIntegrable_of_Icc zero_le_one) (hqc.mono Ioo_subset_Icc_self) hgc hgd
  simpa [g,sourceSegmentMap,q,parametricSourceLogIncrement] using he.symm

/-- The straight source segment lies in the product whenever the
source domain is convex and contains the anchor. -/
theorem exp_parametricSourceLogIncrement_mul
    (M : ℂ × A → ℂ) (U : Set ℂ) (V : Set A) (b : A)
    (hcV : Convex ℝ V) (hb : b ∈ V)
    (hM : AnalyticOnNhd ℂ M (U ×ˢ V)) (hne : ∀ t ∈ U ×ˢ V, M t ≠ 0)
    (t : ℂ × A) (ht : t ∈ U ×ˢ V) :
    exp (parametricSourceLogIncrement M b t)*M (t.1,b) = M t :=
  exp_parametricSourceLogIncrement_mul_of_segment M (U ×ˢ V) b hM hne t
    (sourceSegmentMap_mem U V b hcV hb t ht)

end NLS.ComplexAnalysis
