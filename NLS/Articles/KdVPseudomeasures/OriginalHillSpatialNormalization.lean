import NLS.Articles.KdVPseudomeasures.OriginalHillSpatialCharacter
import NLS.KdV.HillNativeSpatialLinearization
import NLS.ComplexAnalysis.PeriodicCharacterAveraging
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Normalization of the ACTUAL spatial character by its genuine free
Fourier derivative. Local parameter rigidity of period-one characters and
real-analytic uniqueness extend the phase relation before differentiating
at zero. No global native injectivity or fiber connectedness is assumed. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

/-- Near any open coordinate, its actual spatial character is independent
of the source parameter, for ALL real displacements simultaneously. -/
theorem exists_open_hillRealSpatial_phase (n : ℕ+) (a : HillRealMeanZeroSource)
    (ha : hillRealPositiveCoordinate n a ≠ 0) :
    ∃ U : Set HillRealMeanZeroSource, IsOpen U ∧ a ∈ U ∧ ∀ q ∈ U, ∀ s : ℝ,
      hillRealPositiveCoordinate n (hillRealSpatialTranslation s q)=
        hillRealSpatialCoordinateRatio n s a*hillRealPositiveCoordinate n q := by
  let D : Set HillRealMeanZeroSource := {q | hillRealPositiveCoordinate n q ≠ 0}
  have hcCoord : Continuous (hillRealPositiveCoordinate n) := continuous_iff_continuousAt.mpr
    (fun q => (analyticAt_hillRealPositiveCoordinate n q).continuousAt)
  have hD : IsOpen D := isClosed_singleton.isOpen_compl.preimage hcCoord
  let F : D → ℝ → ℂ := fun q s => hillRealSpatialCoordinateRatio n s q.val
  have hraw (q : D) : hillHminusNativeCoordinate (n:ℤ) (hillRealMeanZeroInclusion q.val) ≠ 0 := by
    rw [← hillRealPositiveCoordinate_eq_native]
    exact q.property
  have hinput : Continuous (fun x : D × ℝ => (x.2,(x.1:HillRealMeanZeroSource))) :=
    continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)
  have htranslate := continuous_hillRealSpatialTranslation.comp hinput
  have hnum := (continuous_hillRealNativeCoordinate (n:ℤ)).comp htranslate
  have hden := (continuous_hillRealNativeCoordinate (n:ℤ)).comp
    (continuous_subtype_val.comp (continuous_fst : Continuous (fun x : D × ℝ => x.1)))
  have hcF : Continuous F.uncurry := by
    convert hnum.div hden (fun x => hraw x.1) using 1
    rfl
  obtain ⟨V,hV,haV,hphase⟩ := NLS.ComplexAnalysis.exists_open_eq_periodic_character_family F hcF
    (fun q s t => hillRealSpatialCoordinateRatio_add n q.val (hraw q) s t)
    (fun q => hillRealSpatialCoordinateRatio_periodic n q.val)
    (fun q t => norm_hillRealSpatialCoordinateRatio n t q.val (hraw q)) (⟨a,ha⟩ : D)
  refine ⟨Subtype.val '' V,hD.isOpenMap_subtype_val V hV,⟨⟨a,ha⟩,haV,rfl⟩,?_⟩
  rintro q ⟨p,hp,rfl⟩ s
  have he := congrFun (hphase p hp) s
  change hillRealSpatialCoordinateRatio n s p.val=hillRealSpatialCoordinateRatio n s a at he
  unfold hillRealSpatialCoordinateRatio at he
  rw [← hillRealPositiveCoordinate_eq_native,← hillRealPositiveCoordinate_eq_native] at he
  exact (div_eq_iff p.property).mp he

/-- Real-analytic uniqueness extends the local character relation to EVERY
actual source, including sources with this coordinate collapsed. -/
theorem hillRealPositiveCoordinate_spatialTranslation_eq_character (n : ℕ+)
    (a : HillRealMeanZeroSource) (ha : hillRealPositiveCoordinate n a ≠ 0) (s : ℝ)
    (q : HillRealMeanZeroSource) :
    hillRealPositiveCoordinate n (hillRealSpatialTranslation s q)=
      hillRealSpatialCoordinateRatio n s a*hillRealPositiveCoordinate n q := by
  have hf : AnalyticOnNhd ℝ (fun p => hillRealPositiveCoordinate n (hillRealSpatialTranslation s p)) univ := by
    intro p _
    have hL : AnalyticAt ℝ (hillRealSpatialTranslation s) p :=
      _root_.ContinuousLinearMap.analyticAt _ _
    exact (analyticAt_hillRealPositiveCoordinate n _).comp (f:=hillRealSpatialTranslation s) hL
  have hg : AnalyticOnNhd ℝ (fun p => hillRealSpatialCoordinateRatio n s a*hillRealPositiveCoordinate n p) univ := by
    intro p _
    exact analyticAt_const.mul (analyticAt_hillRealPositiveCoordinate n p)
  obtain ⟨U,hU,haU,hphase⟩ := exists_open_hillRealSpatial_phase n a ha
  have he : (fun p => hillRealPositiveCoordinate n (hillRealSpatialTranslation s p)) =ᶠ[𝓝 a]
      (fun p => hillRealSpatialCoordinateRatio n s a*hillRealPositiveCoordinate n p) := by
    filter_upwards [hU.mem_nhds haU] with p hp
    exact hphase p hp s
  exact congrFun (hf.eq_of_eventuallyEq hg he) q

/-- The genuine free derivative fixes the character to the EXACT original
positive2*pi*n frequency. Its value is not inferred from periodicity alone. -/
theorem hillRealSpatialCoordinateRatio_eq_exp (n : ℕ+) (a : HillRealMeanZeroSource)
    (ha : hillRealPositiveCoordinate n a ≠ 0) (s : ℝ) :
    hillRealSpatialCoordinateRatio n s a=exp ((s*(2*Real.pi*(n:ℕ)):ℝ)*I) := by
  have he : (fun q => hillRealPositiveCoordinate n (hillRealSpatialTranslation s q))=
      (fun q => hillRealSpatialCoordinateRatio n s a*hillRealPositiveCoordinate n q) :=
    funext (hillRealPositiveCoordinate_spatialTranslation_eq_character n a ha s)
  let h := WeightedCoeff.realCosineDirection (p:=2) (Weight.sobolev (-1)) (Weight.sobolev_neg (-1)) n
  have hd := congrArg (fun f : HillRealMeanZeroSource → ℂ => (fderiv ℝ f 0) h) he
  have hconst := @NLS.FunctionalAnalysis.fderiv_comp_clm_apply ℝ HillRealMeanZeroSource ℂ ℂ
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (hillRealPositiveCoordinate n) (ContinuousLinearMap.mul ℝ ℂ (hillRealSpatialCoordinateRatio n s a)) 0 h
    (analyticAt_hillRealPositiveCoordinate n 0).differentiableAt
  change (fderiv ℝ (fun q => hillRealSpatialCoordinateRatio n s a*hillRealPositiveCoordinate n q) 0) h=
    hillRealSpatialCoordinateRatio n s a*(fderiv ℝ (hillRealPositiveCoordinate n) 0) h at hconst
  rw [fderiv_hillRealPositiveCoordinate_spatialTranslation_zero,hconst] at hd
  change exp ((s*(2*Real.pi*(n:ℕ)):ℝ)*I)*(fderiv ℝ (hillRealPositiveCoordinate n) 0) h=
    hillRealSpatialCoordinateRatio n s a*(fderiv ℝ (hillRealPositiveCoordinate n) 0) h at hd
  exact (mul_right_cancel₀ (fderiv_hillRealPositiveCoordinate_cosine_ne_zero n) hd).symm

/-- Exact spatial covariance of the ACTUAL positive native coordinate at
EVERY original physical real mean-zero Hminus-one input, including closed
modes. No global inverse, properness or connected-isoset premise occurs. -/
theorem hillRealPositiveCoordinate_spatialTranslation (n : ℕ+) (s : ℝ)
    (q : HillRealMeanZeroSource) :
    hillRealPositiveCoordinate n (hillRealSpatialTranslation s q)=
      exp ((s*(2*Real.pi*(n:ℕ)):ℝ)*I)*hillRealPositiveCoordinate n q := by
  obtain ⟨a,ha⟩ := exists_hillRealPositiveCoordinate_ne_zero n
  rw [hillRealPositiveCoordinate_spatialTranslation_eq_character n a ha s q,
    hillRealSpatialCoordinateRatio_eq_exp n a ha s]


/-- The exact original spatial phase on EVERY signed native coordinate,
including negative and zero modes and arbitrary collapsed positive gaps. -/
theorem hillRealSignedMap_spatialTranslation_apply (q : HillRealMeanZeroSource) (s : ℝ) (k : ℤ) :
    (hillRealSignedMap (hillRealSpatialTranslation s q)).val.val.val k=
      exp ((s*(2*Real.pi*k):ℝ)*I)*(hillRealSignedMap q).val.val.val k := by
  have hpos (n : ℕ+) :
      (hillRealSignedMap (hillRealSpatialTranslation s q)).val.val.val (n:ℤ)=
        exp ((s*(2*Real.pi*(n:ℕ)):ℝ)*I)*(hillRealSignedMap q).val.val.val (n:ℤ) :=
    hillRealPositiveCoordinate_spatialTranslation n s q
  by_cases hk : k=0
  · subst k
    rw [show (hillRealSignedMap (hillRealSpatialTranslation s q)).val.val.val 0=0 from
      (hillRealSignedMap (hillRealSpatialTranslation s q)).val.property,
      show (hillRealSignedMap q).val.val.val 0=0 from (hillRealSignedMap q).val.property,mul_zero]
  · by_cases hkp : 0<k
    · let n : ℕ+ := ⟨k.toNat,by omega⟩
      have hn : (n:ℤ)=k := Int.toNat_of_nonneg hkp.le
      rw [← hn]
      simpa only [Int.cast_natCast] using hpos n
    · let n : ℕ+ := ⟨(-k).toNat,by omega⟩
      have hn : -(n:ℤ)=k := by
        have he : (n:ℤ)= -k := Int.toNat_of_nonneg (by omega)
        omega
      rw [← hn,(hillRealSignedMap (hillRealSpatialTranslation s q)).property,
        (hillRealSignedMap q).property,hpos,map_mul,← Complex.exp_conj]
      congr 1
      congr 1
      simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,Int.cast_neg,Int.cast_natCast]
      push_cast
      ring

/-- The ACTUAL entire native output commutes with the literal spatial
translation in the full native signed target Banach space. -/
theorem hillRealSignedMap_spatialTranslation (q : HillRealMeanZeroSource) (s : ℝ) :
    (hillRealSignedMap (hillRealSpatialTranslation s q)).val.val=
      WeightedCoeff.spatialTranslation (Weight.signedSobolev (-1/2)) (2*Real.pi) s
        (hillRealSignedMap q).val.val := by
  apply Subtype.ext
  funext k
  rw [WeightedCoeff.spatialTranslation_apply]
  exact hillRealSignedMap_spatialTranslation_apply q s k

/-- Spatial covariance on the ENTIRE original physical distribution source,
with the SAME original potential and EXACT original2*pi*k frequency. -/
theorem original_Hill_native_spatialTranslation (q : OriginalHminusOnePotential) (s : ℝ) (k : ℤ) :
    hillHminusNativeCoordinate k (originalPeriodOneCoefficients (originalHillSpatialTranslation s q))=
      exp ((s*(2*Real.pi*k):ℝ)*I)*hillHminusNativeCoordinate k (originalPeriodOneCoefficients q) := by
  have h := hillRealSignedMap_spatialTranslation_apply (originalHillRealMeanZeroSource q) s k
  rw [hillRealSignedMap_coordinate,hillRealSignedMap_coordinate] at h
  rw [← originalHillRealMeanZeroSource_spatialTranslation] at h
  simpa only [originalHillRealMeanZeroSource_inclusion] using h

end NLS.Articles.KdVPseudomeasures
