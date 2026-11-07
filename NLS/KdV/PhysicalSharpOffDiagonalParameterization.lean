import NLS.KdV.PhysicalFrequencyParameterization
import NLS.KdV.PhysicalOffDiagonalFrequency
import NLS.ZakharovShabat.SourceSharpOffDiagonalDecay
import NLS.SequenceSpaces.PositiveFrequencyDecayNormalization

/-! Actual sharp off-diagonal bounds for an opaque analytic source
parameter space, using the SAME exact physical chart and inclusion. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {t : ℝ} {ht : 0≤t} {J : E →L[ℂ] PeriodOneHminusOne}

theorem PhysicalFrequencyParameterization.exists_sharp_offDiagonal_decay
    (A : PhysicalFrequencyParameterization E t ht J) (ht1 : t≤2/3)
    (q : E) (hq : q∈A.domain) (hqr : IsRealPeriodOneHminusOne (J q)) :
    ∃ T : Set E, IsOpen T ∧ q∈T ∧ T⊆A.domain ∧ ∃ M : ℝ, 0≤M ∧
      (∀ a∈T, ∀ n : ℕ+, Weight.sobolev (3*t-1) (n:ℤ)*
        ‖A.physical.offDiagonalCorrection n (J a)‖≤M) ∧
      (t<2/3 → ∀ a∈T, Tendsto (fun n : ℕ => Weight.sobolev (3*t-1) ((n+1:ℕ):ℤ)*
        ‖A.physical.offDiagonalCorrection ⟨n+1,by omega⟩ (J a)‖) atTop (𝓝 0)) := by
  let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht)
  obtain ⟨Ur,_hUr,hrealUr,_hUrV,hdecay⟩ := A.physical.atlas.exists_sharp_offDiagonal_secondMoment_decay
    t ht ht1 A.estimates.angular_extension A.physical.psi.family.domain_open A.physical.psi.family.real_subset
  obtain ⟨S,hS,hηS,_hSUr,K,hK,hb,hd⟩ := hdecay (A.normalizedSource q) (hrealUr (A.real_source q hq hqr))
  obtain ⟨T,hT,hqT,hTV,hTS,_hTB⟩ := exists_open_common_pullback_domain A.domain A.domain_open q hq
    A.normalizedSource A.analytic_source.continuousOn S hS hηS
    J J.continuous A.physical.domain A.physical.domain_open (A.domain_subset hq)
  have hraw (a : E) (haT : a∈T) (n : ℕ+) :
      A.physical.offDiagonalCorrection n (J a)=(-12 : ℂ)*
        (A.physical.atlas.weightedSecondMomentSum (n : ℤ) (L (A.normalizedSource a))-(n : ℂ)*
          (A.physical.atlas.moment (n : ℤ) (n : ℤ) 2 (L (A.normalizedSource a))-A.physical.atlas.moment (n : ℤ) (-(n : ℤ)) 2 (L (A.normalizedSource a)))) := by
    change (-12 : ℂ)*(A.physical.atlas.weightedSecondMomentSum (n : ℤ) (hillMiuraDiagonal (A.physical.psi.miura.lift (J a)))-(n : ℂ)*
      (A.physical.atlas.moment (n : ℤ) (n : ℤ) 2 (hillMiuraDiagonal (A.physical.psi.miura.lift (J a)))-A.physical.atlas.moment (n : ℤ) (-(n : ℤ)) 2 (hillMiuraDiagonal (A.physical.psi.miura.lift (J a)))))=_
    rw [A.source_identity a (hTV haT)]
  refine ⟨T,hT,hqT,hTV,12*K,mul_nonneg (by norm_num) hK,?_,?_⟩
  · intro a haT n
    let d : ℤ → ℂ := fun j => A.physical.atlas.weightedSecondMomentSum j (L (A.normalizedSource a))-(j : ℂ)*
      (A.physical.atlas.moment j j 2 (L (A.normalizedSource a))-A.physical.atlas.moment j (-j) 2 (L (A.normalizedSource a)))
    have hcal (j : ℕ+) : A.physical.offDiagonalCorrection j (J a)=(-12 : ℂ)*d (j : ℤ) := by
      simpa only [d,Int.cast_natCast] using hraw a haT j
    have hb' : ∀ j : ℤ, Weight.sobolev (3*t-1) j*‖d j‖≤K := hb (A.normalizedSource a) (hTS a haT)
    have H := Coeff.scaled_positive_frequency_bound (Weight.sobolev (3*t-1)) d
      (fun j => A.physical.offDiagonalCorrection j (J a)) (-12) hcal K hb' n
    norm_num only [norm_neg,Complex.norm_ofNat] at H
    exact H
  · intro ht2 a haT
    let d : ℤ → ℂ := fun j => A.physical.atlas.weightedSecondMomentSum j (L (A.normalizedSource a))-(j : ℂ)*
      (A.physical.atlas.moment j j 2 (L (A.normalizedSource a))-A.physical.atlas.moment j (-j) 2 (L (A.normalizedSource a)))
    have hcal (j : ℕ+) : A.physical.offDiagonalCorrection j (J a)=(-12 : ℂ)*d (j : ℤ) := by
      simpa only [d,Int.cast_natCast] using hraw a haT j
    have hd' : Tendsto (fun j : ℕ => Weight.sobolev (3*t-1) (j : ℤ)*‖d (j : ℤ)‖) atTop (𝓝 0) := by
      simpa only [d,Int.cast_natCast] using hd ht2 (A.normalizedSource a) (hTS a haT)
    exact Coeff.tendsto_scaled_positive_frequency (Weight.sobolev (3*t-1)) d
      (fun j => A.physical.offDiagonalCorrection j (J a)) (-12) hcal hd'


end NLS.KdV
