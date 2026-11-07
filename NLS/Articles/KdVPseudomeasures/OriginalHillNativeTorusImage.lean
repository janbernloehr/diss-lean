import NLS.Articles.KdVPseudomeasures.OriginalHillActionRotation
import NLS.Articles.KdVPseudomeasures.OriginalCanonicalActions
import NLS.Topology.CompactCoordinateMatching
import NLS.ComplexAnalysis.EqualNormRotation

/-! Every actual isospectral set maps ONTO its entire native action torus.
The proof uses complete actual action flows and compact actual discriminant
fibers, with no global inverse or injectivity premise. -/
noncomputable section
open Set Complex NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

/-- Literal physical real native output coefficients. -/
theorem hillRealSignedMap_coordinate (q : HillRealMeanZeroSource) (k : ℤ) :
    (hillRealSignedMap q).val.val.val k=hillHminusNativeCoordinate k (hillRealMeanZeroInclusion q) := by
  rw [hillRealSignedMap_coe,hillMeanZeroComplexMap_coe]
  rfl

theorem continuous_hillRealNativeCoordinate (k : ℤ) :
    Continuous (fun q : HillRealMeanZeroSource => hillHminusNativeCoordinate k (hillRealMeanZeroInclusion q)) := by
  have hc : Continuous hillRealSignedMap := continuous_iff_continuousAt.mpr
    (fun q => (analyticAt_hillRealSignedMap q).continuousAt)
  simpa only [Function.comp_def,WeightedCoeff.fourierRealZeroEvalCLM_apply,
    hillRealSignedMap_coordinate] using
    (WeightedCoeff.fourierRealZeroEvalCLM (Weight.signedSobolev (-1/2)) 2 k).continuous.comp hc

/-- The exact real gap integral makes every canonical action isospectral. -/
theorem hillRealCanonicalAction_eq_of_discriminant_eq (p q : HillRealMeanZeroSource)
    (hd : hillRealDiscriminantData p=hillRealDiscriminantData q) (n : ℕ+) :
    hillHminusCanonicalAction n (hillRealMeanZeroInclusion p)=
      hillHminusCanonicalAction n (hillRealMeanZeroInclusion q) := by
  let P := originalHillPotentialOfRealSource p
  let Q := originalHillPotentialOfRealSource q
  have hi : P ∈ originalIsospectralSet Q := by
    apply (mem_originalIsospectralSet_iff_discriminant_eq Q P).mpr
    simpa only [P,Q,← hillRealDiscriminantData_original,originalHillRealMeanZeroSource_ofRealSource] using hd
  have hl := (mem_originalIsospectralSet_iff_originalHillLabels Q P).mp hi
  have ha : originalCanonicalHillAction n P=originalCanonicalHillAction n Q := by
    rw [originalCanonicalHillAction_eq_real_gapIntegral,originalCanonicalHillAction_eq_real_gapIntegral,
      hl,originalHillDiscriminant_eq_of_isospectral Q P hi]
  simpa only [originalCanonicalHillAction,P,Q,originalHillPotentialOfRealSource_coefficients] using ha

/-- The actual signed physical action torus; no inverse-map data enter its definition. -/
def hillRealNativeActionTorus (q : HillRealMeanZeroSource) : Set HillRealSignedTarget :=
  {z | ∀ n : ℕ+, z.val.val.val (n:ℤ)*z.val.val.val (-(n:ℤ))=
    hillHminusCanonicalAction n (hillRealMeanZeroInclusion q)}

theorem hillRealSignedMap_mem_actionTorus_of_discriminant_eq (p q : HillRealMeanZeroSource)
    (hd : hillRealDiscriminantData p=hillRealDiscriminantData q) :
    hillRealSignedMap p ∈ hillRealNativeActionTorus q := by
  intro n
  rw [hillRealSignedMap_coordinate,hillRealSignedMap_coordinate]
  exact (hillHminusNativeComplexMap_action_identity _
    (real_mem_hillHminusActionAngleNativeDomain _ p.property) n).trans
      (hillRealCanonicalAction_eq_of_discriminant_eq p q hd n)

/-- Every point of the entire actual native action torus has an actual
isospectral preimage in the original Hminus-one norm-compact fiber. -/
theorem exists_hillReal_isospectral_preimage_of_mem_actionTorus (q : HillRealMeanZeroSource)
    (z : HillRealSignedTarget) (hz : z ∈ hillRealNativeActionTorus q) :
    ∃ p : HillRealMeanZeroSource, hillRealDiscriminantData p=hillRealDiscriminantData q ∧
      hillRealSignedMap p=z := by
  let K := {p : HillRealMeanZeroSource | hillRealDiscriminantData p=hillRealDiscriminantData q}
  let f : HillRealMeanZeroSource → ℕ+ → ℂ := fun p n =>
    hillHminusNativeCoordinate (n:ℤ) (hillRealMeanZeroInclusion p)
  obtain ⟨p,hp,hcoords⟩ := NLS.Topology.exists_compact_coordinate_match K
    (isCompact_hillRealDiscriminant_fiber q) ⟨q,rfl⟩ f
    (fun n => continuous_hillRealNativeCoordinate (n:ℤ)) (fun n => z.val.val.val (n:ℤ)) (by
      intro n x hx
      have hxn := hillRealSignedMap_mem_actionTorus_of_discriminant_eq x q hx n
      rw [(hillRealSignedMap x).property (n:ℤ),hillRealSignedMap_coordinate] at hxn
      have hzn := hz n
      rw [z.property (n:ℤ)] at hzn
      have he : f x n*(starRingEnd ℂ) (f x n)=z.val.val.val (n:ℤ)*(starRingEnd ℂ) (z.val.val.val (n:ℤ)) :=
        hxn.trans hzn.symm
      have hnorm : ‖f x n‖=‖z.val.val.val (n:ℤ)‖ := by
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        have h := congrArg Complex.re he
        simpa only [mul_conj,ofReal_re,normSq_eq_norm_sq] using h
      obtain ⟨t,ht⟩ := NLS.ComplexAnalysis.exists_exp_I_mul_eq_of_norm_eq (f x n) (z.val.val.val (n:ℤ)) hnorm
      refine ⟨originalHillNativeActionFlow n x t,
        (originalHillNativeActionFlow_conserved n x t).trans hx,?_,?_⟩
      · change hillHminusNativeCoordinate (n:ℤ) _= _
        rw [originalHillNativeActionFlow_coordinate]
        simpa only [hillActionRotationRate,ite_true] using ht
      · intro j hj
        change hillHminusNativeCoordinate (j:ℤ) _= _
        rw [originalHillNativeActionFlow_coordinate]
        have hjn : (j:ℤ) ≠ (n:ℤ) := by intro h; exact hj (PNat.coe_injective (Int.ofNat_inj.mp h))
        have hjneg : (j:ℤ) ≠ -(n:ℤ) := by
          have hjp : (0:ℤ)<j := by exact_mod_cast j.pos
          have hnp : (0:ℤ)<n := by exact_mod_cast n.pos
          omega
        simp only [hillActionRotationRate,if_neg hjn,if_neg hjneg,zero_mul,exp_zero,one_mul]
        rfl)
  refine ⟨p,hp,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  by_cases hk : k=0
  · subst k
    exact (hillRealSignedMap p).val.property.trans z.val.property.symm
  · by_cases hkp : 0<k
    · let n : ℕ+ := ⟨k.toNat,by omega⟩
      have hn : (n:ℤ)=k := Int.toNat_of_nonneg hkp.le
      rw [← hn,hillRealSignedMap_coordinate]
      exact hcoords n
    · let n : ℕ+ := ⟨(-k).toNat,by omega⟩
      have hn : -(n:ℤ)=k := by
        have h : (n:ℤ)= -k := Int.toNat_of_nonneg (by omega)
        omega
      rw [← hn,(hillRealSignedMap p).property,z.property,hillRealSignedMap_coordinate]
      exact congrArg (starRingEnd ℂ) (hcoords n)

/-- Full native isospectral torus SURJECTIVITY, without global injectivity. -/
theorem image_hillRealDiscriminant_fiber_eq_actionTorus (q : HillRealMeanZeroSource) :
    hillRealSignedMap '' {p : HillRealMeanZeroSource | hillRealDiscriminantData p=hillRealDiscriminantData q}=
      hillRealNativeActionTorus q := by
  ext z
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact hillRealSignedMap_mem_actionTorus_of_discriminant_eq p q hp
  · intro hz
    obtain ⟨p,hp,hpz⟩ := exists_hillReal_isospectral_preimage_of_mem_actionTorus q z hz
    exact ⟨p,hp,hpz⟩

/-- The full action torus is compact in the ORIGINAL native signed target norm. -/
theorem isCompact_hillRealNativeActionTorus (q : HillRealMeanZeroSource) :
    IsCompact (hillRealNativeActionTorus q) := by
  rw [← image_hillRealDiscriminant_fiber_eq_actionTorus]
  exact (isCompact_hillRealDiscriminant_fiber q).image
    (continuous_iff_continuousAt.mpr (fun p => (analyticAt_hillRealSignedMap p).continuousAt))

/-- Exact original physical potential notation for the isospectral preimage. -/
theorem original_Hill_native_isospectral_preimage (q : OriginalHminusOnePotential)
    (z : HillRealSignedTarget) (hz : z ∈ hillRealNativeActionTorus (originalHillRealMeanZeroSource q)) :
    ∃ p ∈ originalIsospectralSet q, hillRealSignedMap (originalHillRealMeanZeroSource p)=z := by
  obtain ⟨p,hp,hpz⟩ := exists_hillReal_isospectral_preimage_of_mem_actionTorus
    (originalHillRealMeanZeroSource q) z hz
  refine ⟨originalHillPotentialOfRealSource p,?_,?_⟩
  · apply (mem_originalIsospectralSet_iff_discriminant_eq _ _).mpr
    simpa only [← hillRealDiscriminantData_original,originalHillRealMeanZeroSource_ofRealSource] using hp
  · rw [originalHillRealMeanZeroSource_ofRealSource]
    exact hpz

end NLS.Articles.KdVPseudomeasures
