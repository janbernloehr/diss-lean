import NLS.KdV.HillAllEndpointRegularCotangents
import NLS.KdV.HillFiniteNormingGradients

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- At an actual source with every Dirichlet terminal periodic, construct all
physical correction germs at once, including collapsed gaps. Every finite
sum has its actual H1 cotangent in the norming span and these cotangents
commute under the genuine Gardner derivative bracket. -/
theorem exists_hillEndpointRegularCorrection_norming_family
    (q : RealPeriodOneHillPotential)
    (hterminal : ∀ j : ℕ, hillDirichletLogMultiplier q.val q.property.1 q.property.2 (j+1) (by omega)=0) :
    ∃ C : ℕ → ℕ → Coeff 2 → ℂ, ∃ c : ℕ → ℕ → ℂ,
      (∀ n j : ℕ,
        AnalyticAt ℂ (C n j) (SpectralWeight.one.toCoeff q.val) ∧
        ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
          C n j (SpectralWeight.one.toCoeff p.val)=hillRegularAbelianCorrection
            p.val p.property.1 p.property.2 (n+1) (by omega) (j+1) (by omega)) ∧
      (∀ n : ℕ, ∀ s : Finset ℕ,
        AnalyticAt ℂ (fun p => ∑ j∈s,C n j p) (SpectralWeight.one.toCoeff q.val) ∧
        ∀ h : WeightedCoeff SpectralWeight.one.toWeight 2,
          SpectralWeight.one.toCoeff h∈Coeff.paritySubspace 0 →
          (fderiv ℂ (fun p => ∑ j∈s,C n j p) (SpectralWeight.one.toCoeff q.val)) (SpectralWeight.one.toCoeff h)=
            hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff h) (hillFiniteNormingGradient q s (c n))) ∧
      (∀ n : ℕ, ∀ s : Finset ℕ,
        AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend (hillFiniteNormingGradient q s (c n))) 0 1 ∧
        MemLp (NLS.LinearVolterra.extend (hillFiniteNormingGradient q s (c n))) 2 (volume.restrict (Ioc (0 : ℝ) 1)) ∧
        MemLp (deriv (NLS.LinearVolterra.extend (hillFiniteNormingGradient q s (c n)))) 2 (volume.restrict (Ioc (0 : ℝ) 1))) ∧
      ∀ n m : ℕ, ∀ s t : Finset ℕ,
        (∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend (hillFiniteNormingGradient q s (c n)) x*
          deriv (NLS.LinearVolterra.extend (hillFiniteNormingGradient q t (c m))) x)=0 := by
  have hex (n j : ℕ) := exists_hillRegularAbelianCorrection_endpoint_norming_cotangent h0q h0r
    q (n+1) (j+1) (by omega) (by omega) (hterminal j)
  choose C c hC hphysical hder using hex
  refine ⟨C,c,fun n j => ⟨hC n j,hphysical n j⟩,?_,
    fun n s => hillFiniteNormingGradient_H1 q s (c n),
    fun n m s t => hillFiniteNormingGradient_GardnerBracket_eq_zero q s t (c n) (c m)⟩
  intro n s
  refine ⟨Finset.analyticAt_fun_sum _ (fun j _ => hC n j),?_⟩
  intro h heven
  rw [fderiv_fun_sum (fun j _ => (hC n j).differentiableAt)]
  simp only [sum_apply,hillFiniteNormingGradient,map_sum,map_smul,smul_eq_mul]
  exact Finset.sum_congr rfl (fun j _ => hder n j h heven)

end NLS.KdV
