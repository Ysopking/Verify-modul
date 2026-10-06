import YangMills.RG.NeumannPhysicalImageSeam

namespace YangMills.RG

noncomputable section

/-- Real scalar readout of the exact reflected CMP89 full-Green series. -/
def neumannActualFullGreenReflectionReal
    {L j : ℕ} [NeZero L] (mass a : ℝ)
    (m target source : Fin 4 → ℤ) : ℝ :=
  (cmp89NeumannReflectionSeries
    (cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a)
    m target source).re

/-- Cold complex lower-ghost invariance transported to the real scalar field. -/
theorem neumannActualFullGreenReflectionReal_lowerGhost
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (m target source : Fin 4 → ℤ)
    (hm : ∀ i, 0 < m i) (htarget : target mu = 0) :
    neumannActualFullGreenReflectionReal (L := L) (j := j) mass a m
      (fun i => if i = mu then -1 else target i) source =
    neumannActualFullGreenReflectionReal (L := L) (j := j) mass a m target source := by
  unfold neumannActualFullGreenReflectionReal
  exact congrArg Complex.re
    (neumannActualFullGreenImage_lowerGhost
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hdenWindow hpairWindow hmass
      mu m target source hm htarget)

/-- Cold complex upper-ghost invariance transported to the real scalar field. -/
theorem neumannActualFullGreenReflectionReal_upperGhost
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (B : ℤ) (m target source : Fin 4 → ℤ)
    (hm : ∀ i, 0 < m i)
    (hboundary : m mu = ((L ^ j : ℕ) : ℤ) * B)
    (htarget : target mu = m mu - 1) :
    neumannActualFullGreenReflectionReal (L := L) (j := j) mass a m
      (fun i => if i = mu then m mu else target i) source =
    neumannActualFullGreenReflectionReal (L := L) (j := j) mass a m target source := by
  unfold neumannActualFullGreenReflectionReal
  exact congrArg Complex.re
    (neumannActualFullGreenImage_upperGhost
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hdenWindow hpairWindow hmass
      mu B m target source hm hboundary htarget)

end

end YangMills.RG
