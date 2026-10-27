import NLS.ZakharovShabat.SourceBoundarySeries
import NLS.ZakharovShabat.AKNSCoordinates
import NLS.Fourier.SobolevSynthesis

/-! # The sine/cosine Fourier calculation in the proof of Lemma 4.2

The modes are the actual trigonometric functions. Their full signed series
converge in the uniform norm for every finite Banach exponent with one
Fourier derivative. At p=2 the sums have actual periodic H1 regularity.
The even cosine and odd sine amplitudes give the literal normalized AKNS
coordinate isomorphism onto the full original Dirichlet boundary space.
The Neumann version includes its phases. Composing with the established
physical restriction equivalences identifies both entire classical domains,
including both endpoint values. These are continuous equivalences; no
isometry between the product amplitude norm and source pair norm is asserted.
-/

noncomputable section
open scoped ENNReal
open NLS.Fourier
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The cosine wave, normalized as the average of the two signed Fourier modes. -/
def sourceCosineMode (n : ℤ) : C(AddCircle (2 : ℝ), ℂ) :=
  (1/2 : ℂ) • (fourier n + fourier (-n))
/-- The sine wave, with the exact factor 1/(2i). -/
def sourceSineMode (n : ℤ) : C(AddCircle (2 : ℝ), ℂ) :=
  (-Complex.I/2 : ℂ) • (fourier n - fourier (-n))

/-- The mode is literally cos(n*pi*x). -/
theorem sourceCosineMode_apply (n : ℤ) (x : ℝ) :
    sourceCosineMode n (x : AddCircle (2 : ℝ)) = (Real.cos (Real.pi*n*x) : ℂ) := by
  simp only [sourceCosineMode, ContinuousMap.smul_apply, ContinuousMap.add_apply,
    smul_eq_mul, fourier_two_eq_wave, wave]
  rw [show ((Real.pi : ℂ)*Complex.I*n)*x = (Real.pi*n*x : ℝ)*Complex.I by push_cast; ring]
  rw [show ((Real.pi : ℂ)*Complex.I*(-n : ℤ))*x = -(Real.pi*n*x : ℝ)*Complex.I by push_cast; ring]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos]
  ring

/-- The mode is literally sin(n*pi*x), including negative n. -/
theorem sourceSineMode_apply (n : ℤ) (x : ℝ) :
    sourceSineMode n (x : AddCircle (2 : ℝ)) = (Real.sin (Real.pi*n*x) : ℂ) := by
  simp only [sourceSineMode, ContinuousMap.smul_apply, ContinuousMap.sub_apply,
    smul_eq_mul, fourier_two_eq_wave, wave]
  rw [show ((Real.pi : ℂ)*Complex.I*n)*x = (Real.pi*n*x : ℝ)*Complex.I by push_cast; ring]
  rw [show ((Real.pi : ℂ)*Complex.I*(-n : ℤ))*x = -(Real.pi*n*x : ℝ)*Complex.I by push_cast; ring]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [Complex.cos_neg, Complex.sin_neg, Complex.ofReal_sin]
  ring_nf
  simp [Complex.I_sq]

/-- The continuous cosine series formed by symmetrizing the full Fourier data. -/
def sourceCosineSynthesis (hp : p ≠ ⊤) (a : WeightedCoeff (Weight.sobolev 1) p) :
    C(AddCircle (2 : ℝ), ℂ) :=
  (1/2 : ℂ) • (sobolevSynthesis hp a + sobolevSynthesis hp (WeightedCoeff.reflection 1 a))
/-- The continuous sine series formed by antisymmetrizing the full Fourier data. -/
def sourceSineSynthesis (hp : p ≠ ⊤) (a : WeightedCoeff (Weight.sobolev 1) p) :
    C(AddCircle (2 : ℝ), ℂ) :=
  (-Complex.I/2 : ℂ) • (sobolevSynthesis hp a - sobolevSynthesis hp (WeightedCoeff.reflection 1 a))

private theorem hasSum_reflected_modes (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev 1) p) :
    HasSum (fun n : ℤ => a.val n • fourier (-n))
      (sobolevSynthesis hp (WeightedCoeff.reflection 1 a)) := by
  simpa only [Function.comp_def, Equiv.neg_apply, WeightedCoeff.reflection_apply, neg_neg] using (Equiv.neg ℤ).hasSum_iff.mpr
    (hasSum_sobolevSynthesis hp (WeightedCoeff.reflection 1 a))

/-- The full cosine series converges unconditionally in the uniform norm. -/
theorem hasSum_sourceCosineSynthesis (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev 1) p) :
    HasSum (fun n : ℤ => a.val n • sourceCosineMode n) (sourceCosineSynthesis hp a) := by
  have h := ((hasSum_sobolevSynthesis hp a).add (hasSum_reflected_modes hp a)).const_smul (1/2 : ℂ)
  exact h.congr (fun n => by
    simp only [sourceCosineMode, smul_add, smul_smul, mul_comm])

/-- The full sine series converges unconditionally in the uniform norm. -/
theorem hasSum_sourceSineSynthesis (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev 1) p) :
    HasSum (fun n : ℤ => a.val n • sourceSineMode n) (sourceSineSynthesis hp a) := by
  have h := ((hasSum_sobolevSynthesis hp a).sub (hasSum_reflected_modes hp a)).const_smul (-Complex.I/2 : ℂ)
  exact h.congr (fun n => by
    simp only [sourceSineMode, smul_sub, smul_smul, mul_comm])


/-- Even amplitudes retain their original Fourier coefficients. -/
theorem sourceCosineSynthesis_of_even (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev 1) p) (ha : WeightedCoeff.reflection 1 a = a) :
    sourceCosineSynthesis hp a = sobolevSynthesis hp a := by
  rw [sourceCosineSynthesis, ha]
  module

/-- Odd sine amplitudes have Fourier coefficients -i times those amplitudes. -/
theorem sourceSineSynthesis_of_odd (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev 1) p) (ha : WeightedCoeff.reflection 1 a = -a) :
    sourceSineSynthesis hp a = -Complex.I • sobolevSynthesis hp a := by
  rw [sourceSineSynthesis, ha, map_neg]
  module

/-- The cosine and sine amplitude conditions in the printed proof. -/
def sourceCosineAmplitudeSpace : Submodule ℂ (WeightedCoeff (Weight.sobolev 1) p) :=
  LinearMap.ker ((WeightedCoeff.reflection 1).toLinearEquiv.toLinearMap - LinearMap.id)
def sourceSineAmplitudeSpace : Submodule ℂ (WeightedCoeff (Weight.sobolev 1) p) :=
  LinearMap.ker ((WeightedCoeff.reflection 1).toLinearEquiv.toLinearMap + LinearMap.id)

theorem mem_sourceCosineAmplitudeSpace (a : WeightedCoeff (Weight.sobolev 1) p) :
    a ∈ sourceCosineAmplitudeSpace ↔ WeightedCoeff.reflection 1 a = a := by
  change WeightedCoeff.reflection 1 a - a = 0 ↔ _
  exact sub_eq_zero

theorem mem_sourceSineAmplitudeSpace (a : WeightedCoeff (Weight.sobolev 1) p) :
    a ∈ sourceSineAmplitudeSpace ↔ WeightedCoeff.reflection 1 a = -a := by
  change WeightedCoeff.reflection 1 a + a = 0 ↔ _
  exact eq_neg_iff_add_eq_zero.symm

/-- The exact inverse cosine amplitude, with the printed normalization. -/
def sourceBoundaryCosineAmplitude (a : WeightedCoeff (Weight.sobolev 1) p) :
    sourceCosineAmplitudeSpace (p := p) :=
  ⟨aknsScale • (a + WeightedCoeff.reflection 1 a), by
    rw [mem_sourceCosineAmplitudeSpace]
    simp only [map_smul, map_add, WeightedCoeff.reflection_reflection]
    congr 1
    exact add_comm _ _⟩

/-- The exact inverse sine amplitude, including the minus sign at the original index. -/
def sourceBoundarySineAmplitude (a : WeightedCoeff (Weight.sobolev 1) p) :
    sourceSineAmplitudeSpace (p := p) :=
  ⟨aknsScale • (WeightedCoeff.reflection 1 a - a), by
    rw [mem_sourceSineAmplitudeSpace]
    simp only [map_smul, map_sub, WeightedCoeff.reflection_reflection]
    module⟩

/-- The two printed amplitude formulas are continuous and invert each other. -/
def sourceBoundaryTrigEquiv : WeightedCoeff (Weight.sobolev 1) p ≃L[ℂ]
    sourceCosineAmplitudeSpace (p := p) × sourceSineAmplitudeSpace (p := p) where
  toFun a := (sourceBoundaryCosineAmplitude a, sourceBoundarySineAmplitude a)
  invFun v := aknsScale • (v.1.val - v.2.val)
  left_inv a := by
    apply Subtype.ext
    funext n
    simp only [sourceBoundaryCosineAmplitude, sourceBoundarySineAmplitude,
      WeightedCoeff.smul_val, WeightedCoeff.sub_val, WeightedCoeff.add_val]
    ring_nf
    rw [aknsScale_sq]
    ring
  right_inv v := by
    have hc := (mem_sourceCosineAmplitudeSpace v.1.val).mp v.1.property
    have hs := (mem_sourceSineAmplitudeSpace v.2.val).mp v.2.property
    apply Prod.ext <;> apply Subtype.ext
    · change aknsScale • (aknsScale • (v.1.val-v.2.val) +
        WeightedCoeff.reflection 1 (aknsScale • (v.1.val-v.2.val))) = v.1.val
      rw [map_smul, map_sub, hc, hs]
      apply Subtype.ext
      funext n
      simp only [WeightedCoeff.smul_val, WeightedCoeff.sub_val, WeightedCoeff.add_val,
        WeightedCoeff.neg_val]
      ring_nf
      rw [aknsScale_sq]
      ring
    · change aknsScale • (WeightedCoeff.reflection 1 (aknsScale • (v.1.val-v.2.val)) -
        aknsScale • (v.1.val-v.2.val)) = v.2.val
      rw [map_smul, map_sub, hc, hs]
      apply Subtype.ext
      funext n
      simp only [WeightedCoeff.smul_val, WeightedCoeff.sub_val,
        WeightedCoeff.neg_val]
      ring_nf
      rw [aknsScale_sq]
      ring
  map_add' a b := by
    apply Prod.ext <;> apply Subtype.ext <;>
      dsimp [sourceBoundaryCosineAmplitude, sourceBoundarySineAmplitude]
    · rw [map_add]; module
    · rw [map_add]; module
  map_smul' c a := by
    apply Prod.ext <;> apply Subtype.ext <;>
      dsimp [sourceBoundaryCosineAmplitude, sourceBoundarySineAmplitude]
    · rw [map_smul]; module
    · rw [map_smul]; module
  continuous_toFun := by
    apply Continuous.prodMk <;> apply Continuous.subtype_mk
    · exact (continuous_id.add (WeightedCoeff.reflection 1).continuous).const_smul aknsScale
    · exact ((WeightedCoeff.reflection 1).continuous.sub continuous_id).const_smul aknsScale
  continuous_invFun := by fun_prop

/-- The literal Fourier coordinate isomorphism onto the entire original boundary space. -/
def sourceBoundaryTrigSourceEquiv :
    (sourceCosineAmplitudeSpace (p := p) × sourceSineAmplitudeSpace (p := p)) ≃L[ℂ]
      sourceWeightedBoundarySubspace (p := p) .dirichlet 1 :=
  sourceBoundaryTrigEquiv.symm.trans (sourceWeightedBoundaryAmplitudeEquiv .dirichlet 1)

theorem sourceBoundaryTrigSourceEquiv_apply
    (b : sourceCosineAmplitudeSpace (p := p)) (a : sourceSineAmplitudeSpace (p := p)) :
    sourceBoundaryTrigSourceEquiv (b,a) =
      sourceWeightedBoundaryAmplitudeEquiv .dirichlet 1 (aknsScale • (b.val-a.val)) := rfl

/-- The normalized vector transform sends the actual cosine/sine sums to the printed boundary sum. -/
theorem sourceBoundaryTrig_forward (hp : p ≠ ⊤)
    (b : sourceCosineAmplitudeSpace (p := p)) (a : sourceSineAmplitudeSpace (p := p))
    (x : AddCircle (2 : ℝ)) :
    aknsToZS (sourceCosineSynthesis hp b.val x, sourceSineSynthesis hp a.val x) =
      (sobolevSynthesis hp (sourceBoundaryTrigSourceEquiv (b,a)).val.fst x,
       sobolevSynthesis hp (sourceBoundaryTrigSourceEquiv (b,a)).val.snd x) := by
  have hb := (mem_sourceCosineAmplitudeSpace b.val).mp b.property
  have ha := (mem_sourceSineAmplitudeSpace a.val).mp a.property
  rw [sourceCosineSynthesis_of_even hp b.val hb, sourceSineSynthesis_of_odd hp a.val ha,
    sourceBoundaryTrigSourceEquiv_apply, sourceWeightedBoundaryAmplitudeEquiv_apply]
  simp only [BoundaryCondition.extensionSign, one_smul, WithLp.toLp_fst, WithLp.toLp_snd,
    map_smul, map_sub, hb, ha, map_neg, ContinuousMap.smul_apply,
    ContinuousMap.sub_apply, ContinuousMap.neg_apply, smul_eq_mul, aknsToZS]
  ext <;> dsimp <;> ring_nf <;> simp [Complex.I_sq, sub_eq_add_neg]

/-- The source's inverse T formula as an equality of the actual continuous representatives. -/
theorem sourceBoundaryTrig_inverse (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev 1) p) (x : AddCircle (2 : ℝ)) :
    zsToAKNS
      (sobolevSynthesis hp (sourceWeightedBoundaryAmplitudeEquiv .dirichlet 1 a).val.fst x,
       sobolevSynthesis hp (sourceWeightedBoundaryAmplitudeEquiv .dirichlet 1 a).val.snd x) =
      (sourceCosineSynthesis hp (sourceBoundaryCosineAmplitude a).val x,
       sourceSineSynthesis hp (sourceBoundarySineAmplitude a).val x) := by
  have h := sourceBoundaryTrig_forward hp (sourceBoundaryCosineAmplitude a)
    (sourceBoundarySineAmplitude a) x
  have he : sourceBoundaryTrigSourceEquiv
      (sourceBoundaryCosineAmplitude a, sourceBoundarySineAmplitude a) =
      sourceWeightedBoundaryAmplitudeEquiv .dirichlet 1 a :=
    congrArg (sourceWeightedBoundaryAmplitudeEquiv .dirichlet 1)
      (sourceBoundaryTrigEquiv.symm_apply_apply a)
  rw [he] at h
  exact (congrArg zsToAKNS h).symm.trans (zsToAKNS_aknsToZS _)


/-- The sine and cosine sums are the actual Sobolev representatives of their Fourier data. -/
theorem sourceCosineSynthesis_eq_sobolev (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev 1) p) :
    sourceCosineSynthesis hp a =
      sobolevSynthesis hp ((1/2 : ℂ) • (a + WeightedCoeff.reflection 1 a)) := by
  simp only [sourceCosineSynthesis, map_smul, map_add]

theorem sourceSineSynthesis_eq_sobolev (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev 1) p) :
    sourceSineSynthesis hp a =
      sobolevSynthesis hp ((-Complex.I/2 : ℂ) • (a - WeightedCoeff.reflection 1 a)) := by
  simp only [sourceSineSynthesis, map_smul, map_sub]

/-- The H-cos and H-sin representatives used in Lemma 4.2 have actual periodic H1 regularity. -/
theorem sourceTrigSynthesis_periodicH1 (a : WeightedCoeff (Weight.sobolev 1) 2) :
    HasPeriodicH1Regularity (sourceCosineSynthesis (by simp) a) ∧
      HasPeriodicH1Regularity (sourceSineSynthesis (by simp) a) := by
  rw [sourceCosineSynthesis_eq_sobolev, sourceSineSynthesis_eq_sobolev]
  exact ⟨hasPeriodicH1Regularity_sobolevSynthesis _,
    hasPeriodicH1Regularity_sobolevSynthesis _⟩

/-- Odd sine amplitudes give both zero endpoint traces required in the proof. -/
theorem sourceSineSynthesis_endpoints (hp : p ≠ ⊤)
    (a : sourceSineAmplitudeSpace (p := p)) :
    sourceSineSynthesis hp a.val (0 : AddCircle (2 : ℝ)) = 0 ∧
      sourceSineSynthesis hp a.val ((1 : ℝ) : AddCircle (2 : ℝ)) = 0 := by
  have ha := (mem_sourceSineAmplitudeSpace a.val).mp a.property
  have ht := sobolevTrace_eq_zero_of_odd hp a.val ha
  rw [sourceSineSynthesis_of_odd hp a.val ha]
  simpa using And.intro (congrArg (fun z : ℂ => -Complex.I*z) ht.1)
    (congrArg (fun z : ℂ => -Complex.I*z) ht.2)


/-- The displayed inverse cosine coefficient at each signed frequency. -/
theorem sourceBoundaryCosineAmplitude_apply (a : WeightedCoeff (Weight.sobolev 1) p) (n : ℤ) :
    (sourceBoundaryCosineAmplitude a).val.val n = aknsScale * (a.val n + a.val (-n)) := by
  simp only [sourceBoundaryCosineAmplitude, WeightedCoeff.smul_val, WeightedCoeff.add_val,
    WeightedCoeff.reflection_apply]

/-- The displayed inverse sine coefficient at each signed frequency. -/
theorem sourceBoundarySineAmplitude_apply (a : WeightedCoeff (Weight.sobolev 1) p) (n : ℤ) :
    (sourceBoundarySineAmplitude a).val.val n = aknsScale * (-a.val n + a.val (-n)) := by
  simp only [sourceBoundarySineAmplitude, WeightedCoeff.smul_val, WeightedCoeff.sub_val,
    WeightedCoeff.reflection_apply]
  ring

/-- Composing the literal trig map with actual physical restriction gives the full classical domain. -/
def sourceBoundaryTrigClassicalEquiv :
    (sourceCosineAmplitudeSpace (p := 2) × sourceSineAmplitudeSpace (p := 2)) ≃L[ℂ]
      BoundaryCondition.ClassicalIntervalDomain .dirichlet :=
  sourceBoundaryTrigSourceEquiv.trans (sourceClassicalBoundaryEquiv .dirichlet).symm

/-- The equivalence acts by the printed vector transform on the entire closed interval. -/
theorem sourceBoundaryTrigClassicalEquiv_apply
    (b : sourceCosineAmplitudeSpace (p := 2)) (a : sourceSineAmplitudeSpace (p := 2))
    (x : Set.Icc (0 : ℝ) 1) :
    (sourceBoundaryTrigClassicalEquiv (b,a)).val x =
      aknsToZS (sourceCosineSynthesis (by simp) b.val (x.val : AddCircle (2 : ℝ)),
        sourceSineSynthesis (by simp) a.val (x.val : AddCircle (2 : ℝ))) := by
  change ((sourceClassicalBoundaryEquiv .dirichlet).symm
    (sourceBoundaryTrigSourceEquiv (b,a))).val x = _
  rw [sourceClassicalBoundaryEquiv_symm_apply]
  exact (sourceBoundaryTrig_forward (by simp) b a (x.val : AddCircle (2 : ℝ))).symm


/-- The analogous coefficient isomorphism onto the entire Neumann boundary space. -/
def sourceBoundaryTrigNeumannSourceEquiv :
    (sourceCosineAmplitudeSpace (p := p) × sourceSineAmplitudeSpace (p := p)) ≃L[ℂ]
      sourceWeightedBoundarySubspace (p := p) .neumann 1 :=
  sourceBoundaryTrigEquiv.symm.trans (sourceWeightedBoundaryAmplitudeEquiv .neumann 1)

/-- For Neumann data the sine/cosine roles are interchanged, with their exact phases. -/
theorem sourceBoundaryTrig_neumann_forward (hp : p ≠ ⊤)
    (b : sourceCosineAmplitudeSpace (p := p)) (a : sourceSineAmplitudeSpace (p := p))
    (x : AddCircle (2 : ℝ)) :
    aknsToZS (-Complex.I * sourceSineSynthesis hp a.val x,
      Complex.I * sourceCosineSynthesis hp b.val x) =
      (sobolevSynthesis hp (sourceBoundaryTrigNeumannSourceEquiv (b,a)).val.fst x,
       sobolevSynthesis hp (sourceBoundaryTrigNeumannSourceEquiv (b,a)).val.snd x) := by
  have hb := (mem_sourceCosineAmplitudeSpace b.val).mp b.property
  have ha := (mem_sourceSineAmplitudeSpace a.val).mp a.property
  have he : sourceBoundaryTrigNeumannSourceEquiv (b,a) =
      sourceWeightedBoundaryAmplitudeEquiv .neumann 1 (aknsScale • (b.val-a.val)) := rfl
  rw [sourceCosineSynthesis_of_even hp b.val hb, sourceSineSynthesis_of_odd hp a.val ha,
    he, sourceWeightedBoundaryAmplitudeEquiv_apply]
  simp only [BoundaryCondition.extensionSign, neg_one_smul, WithLp.toLp_fst, WithLp.toLp_snd,
    map_smul, map_sub, hb, ha, map_neg, ContinuousMap.smul_apply,
    ContinuousMap.sub_apply, ContinuousMap.neg_apply, smul_eq_mul, aknsToZS]
  ext <;> dsimp <;> ring_nf <;> simp [Complex.I_sq, sub_eq_add_neg]

/-- The analogous full-domain isomorphism for Neumann data. -/
def sourceBoundaryTrigNeumannClassicalEquiv :
    (sourceCosineAmplitudeSpace (p := 2) × sourceSineAmplitudeSpace (p := 2)) ≃L[ℂ]
      BoundaryCondition.ClassicalIntervalDomain .neumann :=
  sourceBoundaryTrigNeumannSourceEquiv.trans (sourceClassicalBoundaryEquiv .neumann).symm

/-- Both endpoint values and all interior values agree with the actual Neumann representative. -/
theorem sourceBoundaryTrigNeumannClassicalEquiv_apply
    (b : sourceCosineAmplitudeSpace (p := 2)) (a : sourceSineAmplitudeSpace (p := 2))
    (x : Set.Icc (0 : ℝ) 1) :
    (sourceBoundaryTrigNeumannClassicalEquiv (b,a)).val x =
      aknsToZS (-Complex.I * sourceSineSynthesis (by simp) a.val (x.val : AddCircle (2 : ℝ)),
        Complex.I * sourceCosineSynthesis (by simp) b.val (x.val : AddCircle (2 : ℝ))) := by
  change ((sourceClassicalBoundaryEquiv .neumann).symm
    (sourceBoundaryTrigNeumannSourceEquiv (b,a))).val x = _
  rw [sourceClassicalBoundaryEquiv_symm_apply]
  exact (sourceBoundaryTrig_neumann_forward (by simp) b a (x.val : AddCircle (2 : ℝ))).symm

end NLS.ZakharovShabat
