import NLS.ZakharovShabat.AKNSClassicalDomain

/-! # The physical Hilbert norms of the AKNS change of coordinates

The normalized matrix preserves the original component-sum L² and H¹ energies.
The L² result is a linear isometric equivalence of the actual Lebesgue spaces.
-/
noncomputable section
open MeasureTheory Set NLS.Fourier
namespace NLS.ZakharovShabat

/-- The forward vector map preserves square integrability. -/
theorem memLp_aknsToZS {f : ℝ → ℂ × ℂ} (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    MemLp (fun x => aknsToZS (f x)) 2 (volume.restrict (Ioc 0 1)) := by
  apply memLp_prod_iff.mpr
  exact ⟨(hf.fst.add (hf.snd.const_mul Complex.I)).const_mul aknsScale,
    (hf.fst.sub (hf.snd.const_mul Complex.I)).const_mul aknsScale⟩

/-- The inverse vector map preserves square integrability. -/
theorem memLp_zsToAKNS {f : ℝ → ℂ × ℂ} (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    MemLp (fun x => zsToAKNS (f x)) 2 (volume.restrict (Ioc 0 1)) := by
  apply memLp_prod_iff.mpr
  exact ⟨(hf.fst.add hf.snd).const_mul aknsScale,
    ((hf.fst.const_mul (-Complex.I)).add (hf.snd.const_mul Complex.I)).const_mul aknsScale⟩

private theorem integrable_sq {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    IntervalIntegrable (fun x => ‖f x‖ ^ 2) volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
    ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf)

/-- Exact preservation of the physical component-sum L² energy. -/
theorem integral_sq_aknsToZS {f : ℝ → ℂ × ℂ} (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    (∫ x in (0 : ℝ)..1, ‖(aknsToZS (f x)).1‖ ^ 2) +
        (∫ x in (0 : ℝ)..1, ‖(aknsToZS (f x)).2‖ ^ 2) =
      (∫ x in (0 : ℝ)..1, ‖(f x).1‖ ^ 2) + (∫ x in (0 : ℝ)..1, ‖(f x).2‖ ^ 2) := by
  rw [← intervalIntegral.integral_add (integrable_sq (memLp_aknsToZS hf).fst)
    (integrable_sq (memLp_aknsToZS hf).snd),
    ← intervalIntegral.integral_add (integrable_sq hf.fst) (integrable_sq hf.snd)]
  exact intervalIntegral.integral_congr (fun x _ => aknsToZS_norm_sq (f x))

/-- The derivative energy is also preserved for arbitrary original interval H¹ functions. -/
theorem integral_sq_deriv_aknsToZS {g : ℝ → ℂ × ℂ}
    (h₁ : HasIntervalH1Regularity (fun x => (g x).1))
    (h₂ : HasIntervalH1Regularity (fun x => (g x).2)) :
    (∫ x in (0 : ℝ)..1, ‖deriv (fun t => (aknsToZS (g t)).1) x‖ ^ 2) +
        (∫ x in (0 : ℝ)..1, ‖deriv (fun t => (aknsToZS (g t)).2) x‖ ^ 2) =
      (∫ x in (0 : ℝ)..1, ‖deriv (fun t => (g t).1) x‖ ^ 2) +
        (∫ x in (0 : ℝ)..1, ‖deriv (fun t => (g t).2) x‖ ^ 2) := by
  have he : (fun x => (deriv (fun t => (aknsToZS (g t)).1) x,
      deriv (fun t => (aknsToZS (g t)).2) x)) =ᵐ[volume.restrict (Ioc 0 1)]
      (fun x => aknsToZS (deriv (fun t => (g t).1) x, deriv (fun t => (g t).2) x)) := by
    filter_upwards [h₁.ae_differentiableAt, h₂.ae_differentiableAt] with x hx hy
    exact deriv_aknsToZS hx hy
  have he₁ := intervalIntegral.integral_congr_ae_restrict (a := (0 : ℝ)) (b := 1) (μ := volume)
    (by simpa only [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num), Function.comp_def] using
      he.fun_comp (fun u => ‖u.1‖ ^ 2))
  have he₂ := intervalIntegral.integral_congr_ae_restrict (a := (0 : ℝ)) (b := 1) (μ := volume)
    (by simpa only [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num), Function.comp_def] using
      he.fun_comp (fun u => ‖u.2‖ ^ 2))
  rw [he₁, he₂]
  exact integral_sq_aknsToZS (memLp_prod_iff.mpr ⟨h₁.2, h₂.2⟩)

/-- The original physical H¹ norm is preserved, with no endpoint hypothesis. -/
theorem classicalIntervalNorm_aknsToZS {g : ℝ → ℂ × ℂ}
    (h₁ : HasIntervalH1Regularity (fun x => (g x).1))
    (h₂ : HasIntervalH1Regularity (fun x => (g x).2)) :
    BoundaryCondition.classicalIntervalNorm (fun x => aknsToZS (g x)) =
      BoundaryCondition.classicalIntervalNorm g := by
  apply congrArg Real.sqrt
  unfold BoundaryCondition.classicalIntervalEnergy intervalH1Energy
  have hval := integral_sq_aknsToZS (memLp_prod_iff.mpr
    ⟨memLp_of_intervalH1Regularity h₁, memLp_of_intervalH1Regularity h₂⟩)
  have hder := integral_sq_deriv_aknsToZS h₁ h₂
  linarith

/-- The normalized vector map on actual physical L² classes. -/
def aknsL2Map (u : IntervalPairL2) : IntervalPairL2 :=
  intervalL2OfFunction (fun x => aknsToZS (intervalL2Representative u x))
    (memLp_aknsToZS (memLp_intervalL2Representative u))

/-- The inverse map on actual physical L² classes. -/
def aknsL2Inverse (u : IntervalPairL2) : IntervalPairL2 :=
  intervalL2OfFunction (fun x => zsToAKNS (intervalL2Representative u x))
    (memLp_zsToAKNS (memLp_intervalL2Representative u))

theorem aknsL2Map_representative (u : IntervalPairL2) :
    intervalL2Representative (aknsL2Map u) =ᵐ[volume.restrict (Ioc 0 1)]
      (fun x => aknsToZS (intervalL2Representative u x)) := intervalL2Representative_ofFunction _ _

theorem aknsL2Inverse_representative (u : IntervalPairL2) :
    intervalL2Representative (aknsL2Inverse u) =ᵐ[volume.restrict (Ioc 0 1)]
      (fun x => zsToAKNS (intervalL2Representative u x)) := intervalL2Representative_ofFunction _ _

/-- The actual unitary coordinate map for the physical component-sum L² norm. -/
def aknsL2Equiv : IntervalPairL2 ≃ₗᵢ[ℂ] IntervalPairL2 where
  toFun := aknsL2Map
  invFun := aknsL2Inverse
  left_inv u := by
    apply intervalL2Representative_injective
    filter_upwards [aknsL2Inverse_representative (aknsL2Map u), aknsL2Map_representative u] with x hx hy
    rw [hx, hy, zsToAKNS_aknsToZS]
  right_inv u := by
    apply intervalL2Representative_injective
    filter_upwards [aknsL2Map_representative (aknsL2Inverse u), aknsL2Inverse_representative u] with x hx hy
    rw [hx, hy, aknsToZS_zsToAKNS]
  map_add' u v := by
    apply intervalL2Representative_injective
    filter_upwards [aknsL2Map_representative (u+v), intervalL2Representative_add u v,
      intervalL2Representative_add (aknsL2Map u) (aknsL2Map v), aknsL2Map_representative u,
      aknsL2Map_representative v] with x hx ha hb hu hv
    rw [hx, ha, hb, hu, hv]
    exact aknsCoordinateEquiv.map_add _ _
  map_smul' c u := by
    apply intervalL2Representative_injective
    filter_upwards [aknsL2Map_representative (c • u), intervalL2Representative_smul c u,
      intervalL2Representative_smul c (aknsL2Map u), aknsL2Map_representative u] with x hx ha hb hu
    change intervalL2Representative (aknsL2Map (c • u)) x = intervalL2Representative (c • aknsL2Map u) x
    rw [hx, ha, hb, hu]
    exact aknsCoordinateEquiv.map_smul c _
  norm_map' u := by
    change ‖aknsL2Map u‖ = ‖u‖
    have he : ‖aknsL2Map u‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [aknsL2Map, norm_sq_intervalL2OfFunction, norm_sq_intervalL2Representative]
      exact integral_sq_aknsToZS (memLp_intervalL2Representative u)
    nlinarith [norm_nonneg (aknsL2Map u), norm_nonneg u]

end NLS.ZakharovShabat
