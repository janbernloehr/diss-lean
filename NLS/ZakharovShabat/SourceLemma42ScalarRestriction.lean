import NLS.ZakharovShabat.SourceScalarIntervalH1
import NLS.ZakharovShabat.SourceLemma42FourierProof

/-! # Scalar restriction in the Fourier coordinates of Lemma 4.2

Even cosine and odd sine amplitudes restrict continuously and bijectively
to the full physical H1 and zero-trace H1 interval spaces. Both inverses
are continuous. The product identity is pointwise on the closed interval,
and the amplitude norm has explicit bounds by the actual periodic H1 energy.
The function-space versions of R_cos and R_sin, with physical norms on
both sides, are constructed in SourceLemma42PhysicalRestriction.
-/

noncomputable section
open Set NLS.Fourier
namespace NLS.ZakharovShabat
def sourceBoundaryTrigAKNSEquiv :
    (sourceCosineAmplitudeSpace (p := 2) × sourceSineAmplitudeSpace (p := 2)) ≃L[ℂ]
      AKNSIntervalDomain .dirichlet :=
  sourceBoundaryTrigClassicalEquiv.trans (aknsDomainEquiv .dirichlet).symm.toContinuousLinearEquiv

theorem sourceBoundaryTrigAKNSEquiv_apply
    (b : sourceCosineAmplitudeSpace (p := 2)) (a : sourceSineAmplitudeSpace (p := 2))
    (x : Icc (0 : ℝ) 1) :
    (sourceBoundaryTrigAKNSEquiv (b,a)).val x =
      (sourceCosineSynthesis (by simp) b.val (x.val : AddCircle (2 : ℝ)),
       sourceSineSynthesis (by simp) a.val (x.val : AddCircle (2 : ℝ))) := by
  change zsToAKNS ((sourceBoundaryTrigClassicalEquiv (b,a)).val x) = _
  rw [sourceBoundaryTrigClassicalEquiv_apply, zsToAKNS_aknsToZS]

private theorem scalarCosine_embedding (b : sourceCosineAmplitudeSpace (p := 2)) :
    sourceScalarIntervalEmbedding false
        (fun x => ((sourceBoundaryTrigAKNSEquiv (b,0)).val x).1) =
      (sourceBoundaryTrigAKNSEquiv (b,0)).val := by
  funext x
  change (((sourceBoundaryTrigAKNSEquiv (b,0)).val x).1,0) =
    (sourceBoundaryTrigAKNSEquiv (b,0)).val x
  rw [sourceBoundaryTrigAKNSEquiv_apply]
  simp [sourceSineSynthesis]

def sourceCosineRestrictionLinear :
    sourceCosineAmplitudeSpace (p := 2) →ₗ[ℂ] SourceScalarIntervalH1 false where
  toFun b := ⟨fun x => ((sourceBoundaryTrigAKNSEquiv (b,0)).val x).1, by
    change sourceScalarIntervalEmbedding false _ ∈ aknsIntervalSubmodule .dirichlet
    rw [scalarCosine_embedding]
    exact (sourceBoundaryTrigAKNSEquiv (b,0)).property⟩
  map_add' b c := by
    apply Subtype.ext
    funext x
    change ((sourceBoundaryTrigAKNSEquiv (b+c,0)).val x).1 =
      ((sourceBoundaryTrigAKNSEquiv (b,0)).val x).1 +
        ((sourceBoundaryTrigAKNSEquiv (c,0)).val x).1
    have h := sourceBoundaryTrigAKNSEquiv.map_add (b,0) (c,0)
    have hx := congrArg (fun u : AKNSIntervalDomain .dirichlet => (u.val x).1) h
    change ((sourceBoundaryTrigAKNSEquiv (b+c,0+0)).val x).1 = _ + _ at hx
    simpa only [add_zero] using hx
  map_smul' c b := by
    apply Subtype.ext
    funext x
    change ((sourceBoundaryTrigAKNSEquiv (c • b,0)).val x).1 =
      c • ((sourceBoundaryTrigAKNSEquiv (b,0)).val x).1
    have h := sourceBoundaryTrigAKNSEquiv.map_smul c (b,0)
    have hx := congrArg (fun u : AKNSIntervalDomain .dirichlet => (u.val x).1) h
    change ((sourceBoundaryTrigAKNSEquiv (c • b,c • 0)).val x).1 = c • _ at hx
    simpa only [smul_zero] using hx

theorem sourceScalarDomainEmbedding_cosine (b : sourceCosineAmplitudeSpace (p := 2)) :
    sourceScalarDomainEmbedding false (sourceCosineRestrictionLinear b) =
      sourceBoundaryTrigAKNSEquiv (b,0) := by
  apply Subtype.ext
  exact scalarCosine_embedding b

def sourceCosineRestrictionCLM :
    sourceCosineAmplitudeSpace (p := 2) →L[ℂ] SourceScalarIntervalH1 false :=
  sourceCosineRestrictionLinear.mkContinuous ‖sourceBoundaryTrigAKNSEquiv.toContinuousLinearMap‖
    (fun b => by
      change ‖sourceScalarDomainEmbedding false (sourceCosineRestrictionLinear b)‖ ≤ _
      rw [sourceScalarDomainEmbedding_cosine]
      simpa using sourceBoundaryTrigAKNSEquiv.toContinuousLinearMap.le_opNorm (b,0))

def sourceCosineExtensionCLM :
    SourceScalarIntervalH1 false →L[ℂ] sourceCosineAmplitudeSpace (p := 2) :=
  (ContinuousLinearMap.fst ℂ _ _).comp
    (sourceBoundaryTrigAKNSEquiv.symm.toContinuousLinearMap.comp
      (sourceScalarDomainIsometry false).toContinuousLinearMap)

def sourceCosineRestrictionEquiv :
    sourceCosineAmplitudeSpace (p := 2) ≃L[ℂ] SourceScalarIntervalH1 false where
  toFun := sourceCosineRestrictionCLM
  invFun := sourceCosineExtensionCLM
  map_add' := sourceCosineRestrictionCLM.map_add
  map_smul' := sourceCosineRestrictionCLM.map_smul
  left_inv b := by
    change (sourceBoundaryTrigAKNSEquiv.symm
      (sourceScalarDomainEmbedding false (sourceCosineRestrictionLinear b))).1 = b
    rw [sourceScalarDomainEmbedding_cosine, sourceBoundaryTrigAKNSEquiv.symm_apply_apply]
  right_inv f := by
    apply Subtype.ext
    funext x
    have h := congrArg (fun u : AKNSIntervalDomain .dirichlet => (u.val x).1)
      (sourceBoundaryTrigAKNSEquiv.apply_symm_apply (sourceScalarDomainEmbedding false f))
    rw [sourceBoundaryTrigAKNSEquiv_apply] at h
    change ((sourceBoundaryTrigAKNSEquiv
      ((sourceBoundaryTrigAKNSEquiv.symm (sourceScalarDomainEmbedding false f)).1,0)).val x).1 = f.val x
    rw [sourceBoundaryTrigAKNSEquiv_apply]
    exact h
  continuous_toFun := sourceCosineRestrictionCLM.continuous
  continuous_invFun := sourceCosineExtensionCLM.continuous

theorem sourceCosineRestrictionEquiv_apply (b : sourceCosineAmplitudeSpace (p := 2))
    (x : Icc (0 : ℝ) 1) :
    (sourceCosineRestrictionEquiv b).val x =
      sourceCosineSynthesis (by simp) b.val (x.val : AddCircle (2 : ℝ)) := by
  exact congrArg Prod.fst (sourceBoundaryTrigAKNSEquiv_apply b 0 x)

private theorem scalarSine_embedding (b : sourceSineAmplitudeSpace (p := 2)) :
    sourceScalarIntervalEmbedding true
        (fun x => ((sourceBoundaryTrigAKNSEquiv (0,b)).val x).2) =
      (sourceBoundaryTrigAKNSEquiv (0,b)).val := by
  funext x
  change (0,((sourceBoundaryTrigAKNSEquiv (0,b)).val x).2) =
    (sourceBoundaryTrigAKNSEquiv (0,b)).val x
  rw [sourceBoundaryTrigAKNSEquiv_apply]
  simp [sourceCosineSynthesis]

def sourceSineRestrictionLinear :
    sourceSineAmplitudeSpace (p := 2) →ₗ[ℂ] SourceScalarIntervalH1 true where
  toFun b := ⟨fun x => ((sourceBoundaryTrigAKNSEquiv (0,b)).val x).2, by
    change sourceScalarIntervalEmbedding true _ ∈ aknsIntervalSubmodule .dirichlet
    rw [scalarSine_embedding]
    exact (sourceBoundaryTrigAKNSEquiv (0,b)).property⟩
  map_add' b c := by
    apply Subtype.ext
    funext x
    change ((sourceBoundaryTrigAKNSEquiv (0,b+c)).val x).2 =
      ((sourceBoundaryTrigAKNSEquiv (0,b)).val x).2 +
        ((sourceBoundaryTrigAKNSEquiv (0,c)).val x).2
    have h := sourceBoundaryTrigAKNSEquiv.map_add (0,b) (0,c)
    have hx := congrArg (fun u : AKNSIntervalDomain .dirichlet => (u.val x).2) h
    change ((sourceBoundaryTrigAKNSEquiv (0+0,b+c)).val x).2 = _ + _ at hx
    simpa only [add_zero] using hx
  map_smul' c b := by
    apply Subtype.ext
    funext x
    change ((sourceBoundaryTrigAKNSEquiv (0,c • b)).val x).2 =
      c • ((sourceBoundaryTrigAKNSEquiv (0,b)).val x).2
    have h := sourceBoundaryTrigAKNSEquiv.map_smul c (0,b)
    have hx := congrArg (fun u : AKNSIntervalDomain .dirichlet => (u.val x).2) h
    change ((sourceBoundaryTrigAKNSEquiv (c • 0,c • b)).val x).2 = c • _ at hx
    simpa only [smul_zero] using hx

theorem sourceScalarDomainEmbedding_sine (b : sourceSineAmplitudeSpace (p := 2)) :
    sourceScalarDomainEmbedding true (sourceSineRestrictionLinear b) =
      sourceBoundaryTrigAKNSEquiv (0,b) := by
  apply Subtype.ext
  exact scalarSine_embedding b

def sourceSineRestrictionCLM :
    sourceSineAmplitudeSpace (p := 2) →L[ℂ] SourceScalarIntervalH1 true :=
  sourceSineRestrictionLinear.mkContinuous ‖sourceBoundaryTrigAKNSEquiv.toContinuousLinearMap‖
    (fun b => by
      change ‖sourceScalarDomainEmbedding true (sourceSineRestrictionLinear b)‖ ≤ _
      rw [sourceScalarDomainEmbedding_sine]
      simpa using sourceBoundaryTrigAKNSEquiv.toContinuousLinearMap.le_opNorm (0,b))

def sourceSineExtensionCLM :
    SourceScalarIntervalH1 true →L[ℂ] sourceSineAmplitudeSpace (p := 2) :=
  (ContinuousLinearMap.snd ℂ _ _).comp
    (sourceBoundaryTrigAKNSEquiv.symm.toContinuousLinearMap.comp
      (sourceScalarDomainIsometry true).toContinuousLinearMap)

def sourceSineRestrictionEquiv :
    sourceSineAmplitudeSpace (p := 2) ≃L[ℂ] SourceScalarIntervalH1 true where
  toFun := sourceSineRestrictionCLM
  invFun := sourceSineExtensionCLM
  map_add' := sourceSineRestrictionCLM.map_add
  map_smul' := sourceSineRestrictionCLM.map_smul
  left_inv b := by
    change (sourceBoundaryTrigAKNSEquiv.symm
      (sourceScalarDomainEmbedding true (sourceSineRestrictionLinear b))).2 = b
    rw [sourceScalarDomainEmbedding_sine, sourceBoundaryTrigAKNSEquiv.symm_apply_apply]
  right_inv f := by
    apply Subtype.ext
    funext x
    have h := congrArg (fun u : AKNSIntervalDomain .dirichlet => (u.val x).2)
      (sourceBoundaryTrigAKNSEquiv.apply_symm_apply (sourceScalarDomainEmbedding true f))
    rw [sourceBoundaryTrigAKNSEquiv_apply] at h
    change ((sourceBoundaryTrigAKNSEquiv
      (0,(sourceBoundaryTrigAKNSEquiv.symm (sourceScalarDomainEmbedding true f)).2)).val x).2 = f.val x
    rw [sourceBoundaryTrigAKNSEquiv_apply]
    exact h
  continuous_toFun := sourceSineRestrictionCLM.continuous
  continuous_invFun := sourceSineExtensionCLM.continuous

theorem sourceSineRestrictionEquiv_apply (b : sourceSineAmplitudeSpace (p := 2))
    (x : Icc (0 : ℝ) 1) :
    (sourceSineRestrictionEquiv b).val x =
      sourceSineSynthesis (by simp) b.val (x.val : AddCircle (2 : ℝ)) := by
  exact congrArg Prod.snd (sourceBoundaryTrigAKNSEquiv_apply 0 b x)

/-- The source's product identity, with no extra endpoint condition on the first factor. -/
def sourceScalarProductAKNSEquiv :
    (SourceScalarIntervalH1 false × SourceScalarIntervalH1 true) ≃L[ℂ]
      AKNSIntervalDomain .dirichlet :=
  (sourceCosineRestrictionEquiv.symm.prodCongr sourceSineRestrictionEquiv.symm).trans
    sourceBoundaryTrigAKNSEquiv

theorem sourceScalarProductAKNSEquiv_apply (f : SourceScalarIntervalH1 false)
    (g : SourceScalarIntervalH1 true) (x : Icc (0 : ℝ) 1) :
    (sourceScalarProductAKNSEquiv (f,g)).val x = (f.val x,g.val x) := by
  change (sourceBoundaryTrigAKNSEquiv
    (sourceCosineRestrictionEquiv.symm f,sourceSineRestrictionEquiv.symm g)).val x = _
  rw [sourceBoundaryTrigAKNSEquiv_apply,
    ← sourceCosineRestrictionEquiv_apply, ← sourceSineRestrictionEquiv_apply,
    sourceCosineRestrictionEquiv.apply_symm_apply,
    sourceSineRestrictionEquiv.apply_symm_apply]

/-- The literal T after the two scalar restrictions is the entire classical domain. -/
def sourceScalarProductClassicalEquiv :
    (SourceScalarIntervalH1 false × SourceScalarIntervalH1 true) ≃L[ℂ]
      BoundaryCondition.ClassicalIntervalDomain .dirichlet :=
  sourceScalarProductAKNSEquiv.trans (aknsDomainEquiv .dirichlet).toContinuousLinearEquiv

theorem sourceScalarProductClassicalEquiv_apply (f : SourceScalarIntervalH1 false)
    (g : SourceScalarIntervalH1 true) (x : Icc (0 : ℝ) 1) :
    (sourceScalarProductClassicalEquiv (f,g)).val x = aknsToZS (f.val x,g.val x) := by
  change aknsToZS ((sourceScalarProductAKNSEquiv (f,g)).val x) = _
  rw [sourceScalarProductAKNSEquiv_apply]

/-- The cosine amplitude norm gives the actual periodic H1 topology. -/
theorem sourceCosineSynthesis_energy_bounds (b : sourceCosineAmplitudeSpace (p := 2)) :
    ‖b.val‖ ^ 2 ≤ intervalH1Energy
        (fun x : ℝ => sourceCosineSynthesis (by simp) b.val (x : AddCircle (2 : ℝ))) 0 2 ∧
      intervalH1Energy
        (fun x : ℝ => sourceCosineSynthesis (by simp) b.val (x : AddCircle (2 : ℝ))) 0 2 ≤
          2 * Real.pi ^ 2 * ‖b.val‖ ^ 2 := by
  rw [sourceCosineSynthesis_of_even (by simp) b.val
    ((mem_sourceCosineAmplitudeSpace b.val).mp b.property)]
  exact intervalH1Energy_sobolevSynthesis_bounds b.val

/-- The sine amplitude norm gives the actual periodic H1 topology. -/
theorem sourceSineSynthesis_energy_bounds (a : sourceSineAmplitudeSpace (p := 2)) :
    ‖a.val‖ ^ 2 ≤ intervalH1Energy
        (fun x : ℝ => sourceSineSynthesis (by simp) a.val (x : AddCircle (2 : ℝ))) 0 2 ∧
      intervalH1Energy
        (fun x : ℝ => sourceSineSynthesis (by simp) a.val (x : AddCircle (2 : ℝ))) 0 2 ≤
          2 * Real.pi ^ 2 * ‖a.val‖ ^ 2 := by
  have he : sourceSineSynthesis (by simp) a.val =
      sobolevSynthesis (by simp) (-Complex.I • a.val) := by
    rw [sourceSineSynthesis_of_odd (by simp) a.val
      ((mem_sourceSineAmplitudeSpace a.val).mp a.property), map_smul]
  rw [he]
  simpa only [norm_smul, norm_neg, Complex.norm_I, one_mul] using
    intervalH1Energy_sobolevSynthesis_bounds (-Complex.I • a.val)

end NLS.ZakharovShabat
