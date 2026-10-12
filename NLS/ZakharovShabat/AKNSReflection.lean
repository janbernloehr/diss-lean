import NLS.ZakharovShabat.AKNSIntervalOperator

/-! # The even/odd AKNS extensions in Section 4

The normalized vector coordinates identify the printed even/odd extensions
with signed component swap. Both endpoint domains give actual periodic H¹
representatives. The potential always uses q even and p odd.
-/
noncomputable section
open MeasureTheory Set NLS.Fourier
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- Even/odd extensions for Dirichlet and odd/even for Neumann. -/
def aknsIntervalExtension (b : BoundaryCondition) (g : ℝ → ℂ × ℂ) (x : ℝ) : ℂ × ℂ :=
  (folded (extensionSign b) (fun t => (g t).1) (fun t => (g t).1) x,
    folded (-extensionSign b) (fun t => (g t).2) (fun t => (g t).2) x)

/-- The actual signed-swap extension is the coordinate transform of even/odd extension. -/
theorem aknsToZS_intervalExtension (b : BoundaryCondition) (g : ℝ → ℂ × ℂ) (x : ℝ) :
    aknsToZS (aknsIntervalExtension b g x) = intervalExtension b (fun t => aknsToZS (g t)) x := by
  by_cases hx : x ≤ 1
  · simp [aknsIntervalExtension, intervalExtension, folded, hx]
  · cases b <;> ext <;> simp [aknsToZS, aknsIntervalExtension, intervalExtension, folded, hx, extensionSign, sub_eq_add_neg] <;> ring

/-- Both boundary problems use q even and p odd in the potential. -/
theorem aknsPotential_intervalExtension (q p : ℝ → ℂ) (x : ℝ) :
    aknsPotential (folded 1 q q x) (folded (-1) p p x) =
      intervalExtension .dirichlet (fun t => aknsPotential (q t) (p t)) x := by
  by_cases hx : x ≤ 1
  · simp [aknsPotential, intervalExtension, folded, hx]
  · ext <;> simp [aknsPotential, intervalExtension, folded, hx, extensionSign, sub_eq_add_neg]

/-- Inverse coordinates give the printed signed-swap formula for every original pair. -/
theorem akns_intervalExtension_zsToAKNS (b : BoundaryCondition) (f : ℝ → ℂ × ℂ) (x : ℝ) :
    aknsToZS (aknsIntervalExtension b (fun t => zsToAKNS (f t)) x) = intervalExtension b f x := by
  rw [aknsToZS_intervalExtension]
  simp only [aknsToZS_zsToAKNS]

private theorem akns_boundary_reflection (b : BoundaryCondition) (u : ℂ × ℂ)
    (h : aknsBoundaryValue b u = 0) :
    u.1 = extensionSign b * u.1 ∧ u.2 = -extensionSign b * u.2 := by
  cases b <;> simp only [aknsBoundaryValue] at h <;> simp [extensionSign, h]

/-- The reflected AKNS components have actual periodic H¹ representatives. -/
def aknsCircleExtension (b : BoundaryCondition) (g : ℝ → ℂ × ℂ)
    (hg : HasAKNSIntervalDomain b g) : C(AddCircle (2 : ℝ), ℂ) × C(AddCircle (2 : ℝ), ℂ) :=
  (sobolevSynthesis (by simp) (foldedSobolevCoefficients (extensionSign b)
    (fun x => (g x).1) (fun x => (g x).1) hg.fst_regular hg.fst_regular
    (akns_boundary_reflection b (g 0) hg.left).1 (akns_boundary_reflection b (g 1) hg.right).1),
   sobolevSynthesis (by simp) (foldedSobolevCoefficients (-extensionSign b)
    (fun x => (g x).2) (fun x => (g x).2) hg.snd_regular hg.snd_regular
    (akns_boundary_reflection b (g 0) hg.left).2 (akns_boundary_reflection b (g 1) hg.right).2))

theorem aknsCircleExtension_regular (b : BoundaryCondition) (g : ℝ → ℂ × ℂ)
    (hg : HasAKNSIntervalDomain b g) :
    HasPeriodicH1Regularity (aknsCircleExtension b g hg).1 ∧
      HasPeriodicH1Regularity (aknsCircleExtension b g hg).2 :=
  ⟨hasPeriodicH1Regularity_sobolevSynthesis _, hasPeriodicH1Regularity_sobolevSynthesis _⟩

theorem aknsCircleExtension_reconstruct (b : BoundaryCondition) (g : ℝ → ℂ × ℂ)
    (hg : HasAKNSIntervalDomain b g) {x : ℝ} (hx : x ∈ Icc 0 2) :
    ((aknsCircleExtension b g hg).1 (x : AddCircle (2 : ℝ)),
      (aknsCircleExtension b g hg).2 (x : AddCircle (2 : ℝ))) = aknsIntervalExtension b g x := by
  apply Prod.ext <;> exact sobolevSynthesis_foldedSobolevCoefficients _ _ _ _ _ _ _ hx

/-- The AKNS equation extends using q even and p odd for either endpoint condition. -/
theorem akns_interval_equation_transfer (b : BoundaryCondition) (q p : ℝ → ℂ)
    (g : ℝ → ℂ × ℂ) (hg : HasAKNSIntervalDomain b g) (z : ℂ)
    (h : aknsPhysicalOperator q p g =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • g x)) :
    aknsPhysicalOperator (folded 1 q q) (folded (-1) p p) (aknsIntervalExtension b g)
      =ᵐ[volume.restrict (Ioc 0 2)] (fun x => z • aknsIntervalExtension b g x) := by
  have hzs := (akns_eigenEquation_iff b hg q p z).mpr h
  have ht := physical_interval_equation_transfer b (fun x => aknsPotential (q x) (p x))
    (fun x => aknsToZS (g x)) ((hasClassicalIntervalDomain_aknsToZS_iff b g).mpr hg) z hzs
  have he : intervalExtension b (fun x => aknsToZS (g x)) =
      (fun x => aknsToZS (aknsIntervalExtension b g x)) := funext (fun x => (aknsToZS_intervalExtension b g x).symm)
  have hp : intervalExtension .dirichlet (fun x => aknsPotential (q x) (p x)) =
      (fun x => aknsPotential (folded 1 q q x) (folded (-1) p p x)) :=
    funext (fun x => (aknsPotential_intervalExtension q p x).symm)
  rw [he,hp] at ht
  have h₁ := absolutelyContinuous_folded (extensionSign b) hg.fst_regular hg.fst_regular
    (akns_boundary_reflection b (g 1) hg.right).1
  have h₂ := absolutelyContinuous_folded (-extensionSign b) hg.snd_regular hg.snd_regular
    (akns_boundary_reflection b (g 1) hg.right).2
  have hd₁ : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 2),
      DifferentiableAt ℝ (fun t => (aknsIntervalExtension b g t).1) x := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [FunctionalAnalysis.ae_differentiableAt_complex h₁] with x hx hm
    exact hx (by simpa using Ioc_subset_Icc_self hm)
  have hd₂ : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 2),
      DifferentiableAt ℝ (fun t => (aknsIntervalExtension b g t).2) x := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [FunctionalAnalysis.ae_differentiableAt_complex h₂] with x hx hm
    exact hx (by simpa using Ioc_subset_Icc_self hm)
  filter_upwards [ht,hd₁,hd₂] with x hx hx₁ hx₂
  apply aknsCoordinateEquiv.injective
  have hc : physicalOperator (fun x => aknsPotential (folded 1 q q x) (folded (-1) p p x))
      (fun x => aknsToZS (aknsIntervalExtension b g x)) x =
      aknsToZS (aknsPhysicalOperator (folded 1 q q) (folded (-1) p p) (aknsIntervalExtension b g) x) := by
    change zsAction _ _ (deriv (fun t => (aknsToZS (aknsIntervalExtension b g t)).1) x,
      deriv (fun t => (aknsToZS (aknsIntervalExtension b g t)).2) x) = _
    rw [deriv_aknsToZS hx₁ hx₂]
    exact aknsAction_intertwining _ _ _ _
  exact hc.symm.trans (hx.trans (aknsCoordinateEquiv.map_smul z (aknsIntervalExtension b g x)).symm)

/-- The even/odd potential extension is square integrable for arbitrary original L² potentials. -/
theorem memLp_aknsPotentialExtension (q p : ℝ → ℂ)
    (hq : MemLp q 2 (volume.restrict (Ioc 0 1))) (hp : MemLp p 2 (volume.restrict (Ioc 0 1))) :
    MemLp (fun x => aknsPotential (folded 1 q q x) (folded (-1) p p x))
      2 (volume.restrict (Ioc 0 2)) := by
  have hq' := memLp_folded_of_memLp 1 hq hq
  have hp' := memLp_folded_of_memLp (-1) hp hp
  exact memLp_prod_iff.mpr ⟨hq'.add (hp'.const_mul Complex.I), hq'.sub (hp'.const_mul Complex.I)⟩

end NLS.ZakharovShabat
