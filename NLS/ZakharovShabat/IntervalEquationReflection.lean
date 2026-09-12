import NLS.ZakharovShabat.ClassicalIntervalExtension
import NLS.ZakharovShabat.PhysicalOperator

/-!
# Signed reflection of the original differential equation

Both boundary conditions use the Dirichlet extension of the potential. The
boundary sign belongs only to the eigenfunction extension. These identities
use actual classical derivatives and almost-everywhere equations on `[0,1]`.
-/

noncomputable section
open MeasureTheory Set NLS.Fourier
namespace NLS.ZakharovShabat

/-- Equal physical domain functions and almost-everywhere equal potentials give the same operator. -/
theorem physicalOperator_congr_on_period {φ ψ f g : ℝ → ℂ × ℂ}
    (hφ : φ =ᵐ[volume.restrict (Ioc 0 2)] ψ) (hf : EqOn f g (Icc 0 2)) :
    physicalOperator φ f =ᵐ[volume.restrict (Ioc 0 2)] physicalOperator ψ g := by
  have h₁ : EqOn (fun x => (f x).1) (fun x => (g x).1) (Ioo 0 2) :=
    fun x hx => congrArg Prod.fst (hf (Ioo_subset_Icc_self hx))
  have h₂ : EqOn (fun x => (f x).2) (fun x => (g x).2) (Ioo 0 2) :=
    fun x hx => congrArg Prod.snd (hf (Ioo_subset_Icc_self hx))
  have hm : ∀ᵐ x : ℝ ∂volume.restrict (Ioc 0 2), x ∈ Ioo (0 : ℝ) 2 := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [volume.ae_ne (2 : ℝ)] with x hne hx
    exact ⟨hx.1, lt_of_le_of_ne hx.2 hne⟩
  filter_upwards [hφ, hm] with x hx hmem
  dsimp only [physicalOperator]
  rw [h₁.deriv isOpen_Ioo hmem, h₂.deriv isOpen_Ioo hmem, hx, hf (Ioo_subset_Icc_self hmem)]

namespace BoundaryCondition

/-- Equality almost everywhere on the original interval is preserved by signed reflection. -/
theorem intervalExtension_congr_ae (b : BoundaryCondition) {f g : ℝ → ℂ × ℂ}
    (h : f =ᵐ[volume.restrict (Ioc 0 1)] g) :
    intervalExtension b f =ᵐ[volume.restrict (Ioc 0 2)] intervalExtension b g := by
  have h0 : ∀ᵐ x : ℝ, x ∈ Ioc (0 : ℝ) 1 → f x = g x :=
    (ae_restrict_iff' measurableSet_Ioc).mp h
  have hr := (volume.measurePreserving_sub_left (2 : ℝ)).quasiMeasurePreserving.ae h0
  change ∀ᵐ x ∂volume.restrict (Ioc 0 2), intervalExtension b f x = intervalExtension b g x
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [h0, hr, volume.ae_ne (2 : ℝ)] with x hx hrx hne hmem
  by_cases hx1 : x ≤ 1
  · rw [intervalExtension_left b f x hx1, intervalExtension_left b g x hx1, hx ⟨hmem.1, hx1⟩]
  · have hxr : 2 - x ∈ Ioc (0 : ℝ) 1 := by
      constructor <;> linarith [hmem.2, lt_of_le_of_ne hmem.2 hne]
    rw [intervalExtension_right b f x (lt_of_not_ge hx1),
      intervalExtension_right b g x (lt_of_not_ge hx1), hrx hxr]

/-- The physical operator commutes with signed eigenfunction reflection and Dirichlet potential reflection. -/
theorem physicalOperator_intervalExtension (b : BoundaryCondition) (φ f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) :
    physicalOperator (intervalExtension .dirichlet φ) (intervalExtension b f)
      =ᵐ[volume.restrict (Ioc 0 2)] intervalExtension b (physicalOperator φ f) := by
  have hrev : (f 1).2 = extensionSign b * (f 1).1 := by
    rw [hf.right, ← mul_assoc, extensionSign_sq, one_mul]
  filter_upwards [deriv_folded_ae (extensionSign b) hf.fst_regular hf.snd_regular hf.right,
    deriv_folded_ae (extensionSign b) hf.snd_regular hf.fst_regular hrev] with x h₁ h₂
  change (Complex.I * deriv (folded (extensionSign b) (fun t => (f t).1) (fun t => (f t).2)) x +
      folded 1 (fun t => (φ t).1) (fun t => (φ t).2) x *
        folded (extensionSign b) (fun t => (f t).2) (fun t => (f t).1) x,
    -Complex.I * deriv (folded (extensionSign b) (fun t => (f t).2) (fun t => (f t).1)) x +
      folded 1 (fun t => (φ t).2) (fun t => (φ t).1) x *
        folded (extensionSign b) (fun t => (f t).1) (fun t => (f t).2) x) = _
  rw [h₁, h₂]
  by_cases hx : x ≤ 1
  · simp [intervalExtension, folded, hx, physicalOperator]
  · apply Prod.ext <;> simp [intervalExtension, folded, hx, physicalOperator] <;> ring

/-- Lemma 4.1's physical equation transfer, for either original endpoint condition. -/
theorem physical_interval_equation_transfer (b : BoundaryCondition) (φ f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) (z : ℂ)
    (h : physicalOperator φ f =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • f x)) :
    physicalOperator (intervalExtension .dirichlet φ) (intervalExtension b f)
      =ᵐ[volume.restrict (Ioc 0 2)] (fun x => z • intervalExtension b f x) := by
  have he := intervalExtension_congr_ae b h
  change intervalExtension b (physicalOperator φ f) =ᵐ[volume.restrict (Ioc 0 2)]
    intervalExtension b (z • f) at he
  rw [map_smul] at he
  exact (physicalOperator_intervalExtension b φ f hf).trans he

end BoundaryCondition
end NLS.ZakharovShabat
