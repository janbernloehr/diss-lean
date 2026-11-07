import NLS.KdV.HillEnergyFullProduct
import NLS.SequenceSpaces.EscapingCoordinateProjection

/-! One entire affine-energy product represents all literal deleted
products and their full limit. Deleted parameter pairs converge in full
Banach norm when the omitted index escapes and the zero data converge. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

def hillAffineEnergyProduct (t : ℂ × (Coeff 2 × Coeff 2)) : ℂ :=
  jointDeletedSingleSpectralProduct (p := 2) 0 (0,t.2.1+t.1 • t.2.2)

def hillFullEnergyProductParameters (d : lp (fun _ : ℕ+ => ℂ) 2) : Coeff 2 × Coeff 2 :=
  ((Real.pi:ℂ)⁻¹ • LpSequence.positiveInsert d,-(Real.pi:ℂ)⁻¹ • positiveReciprocalCoefficients)

def hillDeletedEnergyProductParameters (n : ℕ+) (d : lp (fun _ : ℕ+ => ℂ) 2) : Coeff 2 × Coeff 2 :=
  ((hillFullEnergyProductParameters d).1-Coeff.truncate {((n:ℕ):ℤ)} (hillFullEnergyProductParameters d).1,
   (hillFullEnergyProductParameters d).2-Coeff.truncate {((n:ℕ):ℤ)} (hillFullEnergyProductParameters d).2)

theorem analyticAt_hillAffineEnergyProduct (t : ℂ × (Coeff 2 × Coeff 2)) :
    AnalyticAt ℂ hillAffineEnergyProduct t :=
  (analyticOnNhd_jointDeletedSingleSpectralProduct (by norm_num) (by norm_num) 0 _ (mem_univ _)).comp
    (f := fun s : ℂ × (Coeff 2 × Coeff 2) => (0,s.2.1+s.1 • s.2.2))
    (analyticAt_const.prod (((analyticAt_fst.comp (f := Prod.snd) analyticAt_snd)).add
      (analyticAt_fst.smul (analyticAt_snd.comp (f := Prod.snd) analyticAt_snd))))

theorem analyticAt_hillFullEnergyProductParameters (d : lp (fun _ : ℕ+ => ℂ) 2) :
    AnalyticAt ℂ hillFullEnergyProductParameters d :=
  ((LpSequence.positiveInsertIsometry.toContinuousLinearMap.analyticAt d).const_smul (c := (Real.pi:ℂ)⁻¹)).prod analyticAt_const

theorem hillEnergyRawProductEmbedding_eq_affine (E : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2) :
    hillEnergyRawProductEmbedding (E,d) =
      (hillFullEnergyProductParameters d).1+E • (hillFullEnergyProductParameters d).2 := by
  ext k
  change (Real.pi:ℂ)⁻¹*LpSequence.positiveInsert d k-(E/(Real.pi:ℂ))*positiveReciprocalCoefficients k =
    (Real.pi:ℂ)⁻¹*LpSequence.positiveInsert d k+E*(-(Real.pi:ℂ)⁻¹*positiveReciprocalCoefficients k)
  ring

theorem hillEnergyProductEmbedding_eq_affine (n : ℕ+) (E : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2) :
    hillEnergyProductEmbedding n (E,d) =
      (hillDeletedEnergyProductParameters n d).1+E • (hillDeletedEnergyProductParameters n d).2 := by
  rw [hillEnergyProductEmbedding,hillEnergyRawProductEmbedding_eq_affine]
  simp only [hillDeletedEnergyProductParameters,Coeff.truncate_add,Coeff.truncate_smul]
  module

theorem hillEnergySequenceProduct_eq_affine (n : ℕ+) (E : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2) :
    hillEnergySequenceProduct n (E,d) = hillAffineEnergyProduct (E,hillDeletedEnergyProductParameters n d) := by
  unfold hillEnergySequenceProduct hillAffineEnergyProduct
  rw [hillEnergyProductEmbedding_eq_affine]

theorem hillEnergySequenceFullProduct_eq_affine (E : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2) :
    hillEnergySequenceFullProduct (E,d) = hillAffineEnergyProduct (E,hillFullEnergyProductParameters d) := by
  unfold hillEnergySequenceFullProduct hillAffineEnergyProduct
  rw [hillEnergyRawProductEmbedding_eq_affine]

theorem tendsto_hillDeletedEnergyProductParameters
    (n : ℕ → ℕ+) (hn : Tendsto (fun j => (n j:ℕ)) atTop atTop)
    (d : ℕ → lp (fun _ : ℕ+ => ℂ) 2) (d₀ : lp (fun _ : ℕ+ => ℂ) 2) (hd : Tendsto d atTop (𝓝 d₀)) :
    Tendsto (fun j => hillDeletedEnergyProductParameters (n j) (d j)) atTop (𝓝 (hillFullEnergyProductParameters d₀)) := by
  have hp := (analyticAt_hillFullEnergyProductParameters d₀).continuousAt.tendsto.comp hd
  exact (Coeff.tendsto_remove_moving_escaping_coordinate n hn _ _ ((continuous_fst.tendsto _).comp hp)).prodMk_nhds
    (Coeff.tendsto_remove_moving_escaping_coordinate n hn _ _ ((continuous_snd.tendsto _).comp hp))

theorem tendsto_hillEnergySequenceProduct_escaping
    (n : ℕ → ℕ+) (hn : Tendsto (fun j => (n j:ℕ)) atTop atTop)
    (d : ℕ → lp (fun _ : ℕ+ => ℂ) 2) (d₀ : lp (fun _ : ℕ+ => ℂ) 2) (hd : Tendsto d atTop (𝓝 d₀))
    (E : ℕ → ℂ) (E₀ : ℂ) (hE : Tendsto E atTop (𝓝 E₀)) :
    Tendsto (fun j => hillEnergySequenceProduct (n j) (E j,d j)) atTop (𝓝 (hillEnergySequenceFullProduct (E₀,d₀))) := by
  simp_rw [hillEnergySequenceProduct_eq_affine,hillEnergySequenceFullProduct_eq_affine]
  exact (analyticAt_hillAffineEnergyProduct _).continuousAt.tendsto.comp
    (hE.prodMk_nhds (tendsto_hillDeletedEnergyProductParameters n hn d d₀ hd))

end NLS.KdV
