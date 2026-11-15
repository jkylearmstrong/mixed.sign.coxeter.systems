/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Order.IntermediateValue
import MixedSignCoxeter.SpectralRadius

/-!
# Alternating Square $C_4(+, -, +, -)$: Questions 2.59 & 3.35

Formalizes the 4-vertex alternating square $C_4(+, -, +, -)$:
* **Question 2.59 (Non-conjugacy beyond trees)**: `alternatingSquare_principal_not_conjugate`
  proves that the bipartite principal element `w_bp = s₀ s₂ s₁ s₃` (trace `-8`) and the
  cyclic principal element `w_circ = s₀ s₁ s₂ s₃` (trace `-7`) are not conjugate in
  `GL₄(ℝ)` (and hence not conjugate in `W(C_4(+,-,+,-))`).
* **Question 3.35 (Smallest bipartite failure)**: `alternatingSquare_bipartite_not_min`
  proves that `w_bp` has a real eigenvalue `λ_bp ∈ (-6, -5)` (`|λ_bp| > 5`), whereas every
  real eigenvalue of `w_circ` satisfies `|λ| < 4`—giving a 4-vertex counterexample (smaller
  than Example 3.33's 6-vertex graph).
-/

open Matrix

namespace MixedSignCoxeter

section AlternatingSquare

/-- Generating reflection `s₀` of the alternating square `C_4(+, -, +, -)`. -/
def s0_altSq : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-1,  1,  0,  1;
      0,  1,  0,  0;
      0,  0,  1,  0;
      0,  0,  0,  1]

/-- Generating reflection `s₁` of the alternating square `C_4(+, -, +, -)`. -/
def s1_altSq : Matrix (Fin 4) (Fin 4) ℝ :=
  !![ 1,  0,  0,  0;
     -1, -1, -1,  0;
      0,  0,  1,  0;
      0,  0,  0,  1]

/-- Generating reflection `s₂` of the alternating square `C_4(+, -, +, -)`. -/
def s2_altSq : Matrix (Fin 4) (Fin 4) ℝ :=
  !![ 1,  0,  0,  0;
      0,  1,  0,  0;
      0,  1, -1,  1;
      0,  0,  0,  1]

/-- Generating reflection `s₃` of the alternating square `C_4(+, -, +, -)`. -/
def s3_altSq : Matrix (Fin 4) (Fin 4) ℝ :=
  !![ 1,  0,  0,  0;
      0,  1,  0,  0;
      0,  0,  1,  0;
     -1,  0, -1, -1]

/-- Bipartite principal element `w_bp = s₀ s₂ s₁ s₃` on `C_4(+, -, +, -)`. -/
def w_altSq_bp : Matrix (Fin 4) (Fin 4) ℝ :=
  s0_altSq * s2_altSq * s1_altSq * s3_altSq

/-- Cyclic principal element `w_circ = s₀ s₁ s₂ s₃` on `C_4(+, -, +, -)`. -/
def w_altSq_circ : Matrix (Fin 4) (Fin 4) ℝ :=
  s0_altSq * s1_altSq * s2_altSq * s3_altSq

theorem w_altSq_bp_eq :
    w_altSq_bp =
      !![-3, -1, -2, -1;
         -1, -1, -1,  0;
         -2, -1, -3, -1;
         -1,  0, -1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [w_altSq_bp, s0_altSq, s1_altSq, s2_altSq, s3_altSq,
      Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

theorem w_altSq_circ_eq :
    w_altSq_circ =
      !![-2, -2,  1,  0;
          0, -2,  2,  1;
         -1,  1, -2, -1;
         -1,  0, -1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [w_altSq_circ, s0_altSq, s1_altSq, s2_altSq, s3_altSq,
      Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

theorem trace_w_altSq_bp : Matrix.trace w_altSq_bp = -8 := by
  rw [w_altSq_bp_eq]
  simp [Matrix.trace, Fin.sum_univ_four]
  norm_num

theorem trace_w_altSq_circ : Matrix.trace w_altSq_circ = -7 := by
  rw [w_altSq_circ_eq]
  simp [Matrix.trace, Fin.sum_univ_four]
  norm_num

/-- **Question 2.59 (4-vertex non-conjugacy)**: The bipartite principal element `w_bp` and
the cyclic principal element `w_circ` of `C_4(+, -, +, -)` are not conjugate in `M₄(ℝ)`
(since they have distinct traces `-8 ≠ -7`). -/
theorem alternatingSquare_principal_not_conjugate :
    ∀ g : (Matrix (Fin 4) (Fin 4) ℝ)ˣ,
      (g : Matrix (Fin 4) (Fin 4) ℝ) * w_altSq_bp * (g⁻¹ : Matrix (Fin 4) (Fin 4) ℝ) ≠
        w_altSq_circ := by
  intro g h
  have htr := congrArg Matrix.trace h
  rw [Matrix.trace_mul_cycle] at htr
  simp only [trace_w_altSq_circ] at htr
  rw [trace_w_altSq_bp] at htr
  norm_num at htr

/-- Characteristic polynomial of `w_altSq_bp`: `(x + 1)^2 (x^2 + 6x + 1)`. -/
noncomputable def p_altSq_bp (x : ℝ) : ℝ :=
  (x + 1) ^ 2 * (x ^ 2 + 6 * x + 1)

/-- Characteristic polynomial of `w_altSq_circ`: `x^4 + 7x^3 + 16x^2 + 7x + 1`. -/
noncomputable def p_altSq_circ (x : ℝ) : ℝ :=
  x ^ 4 + 7 * x ^ 3 + 16 * x ^ 2 + 7 * x + 1

theorem w_altSq_bp_annihilated :
    (w_altSq_bp + 1) ^ 2 * (w_altSq_bp ^ 2 + 6 • w_altSq_bp + 1) = 0 := by
  rw [w_altSq_bp_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

private theorem w_altSq_circ_sq_eq :
    w_altSq_circ ^ 2 =
      !![ 3,  9, -8, -3;
         -3,  6, -9, -5;
          5, -2,  6,  4;
          4,  1,  2,  2] := by
  rw [w_altSq_circ_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

theorem w_altSq_circ_annihilated :
    w_altSq_circ ^ 4 + 7 • w_altSq_circ ^ 3 + 16 • w_altSq_circ ^ 2 + 7 • w_altSq_circ + 1 = 0 := by
  have h3 : w_altSq_circ ^ 3 = w_altSq_circ ^ 2 * w_altSq_circ := by rw [pow_succ]
  have h4 : w_altSq_circ ^ 4 = w_altSq_circ ^ 2 * w_altSq_circ ^ 2 := by rw [← pow_add]
  rw [h4, h3, w_altSq_circ_sq_eq, w_altSq_circ_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp <;> norm_num

/-- Every real root of `p_altSq_circ` satisfies `|x| < 4`. -/
theorem p_altSq_circ_abs_lt_four {x : ℝ} (hx : p_altSq_circ x = 0) : |x| < 4 := by
  unfold p_altSq_circ at hx
  by_contra h
  rw [not_lt, le_abs] at h
  rcases h with hge | hle
  · nlinarith [sq_nonneg x]
  · set y := -x
    have hy : y ≥ 4 := by linarith
    have hpoly : y ^ 4 - 7 * y ^ 3 + 16 * y ^ 2 - 7 * y + 1 = 0 := by
      dsimp [y]; linarith
    have h1 : 0 ≤ y ^ 2 * ((y - 4) * (y - 3)) :=
      mul_nonneg (sq_nonneg y) (mul_nonneg (by linarith) (by linarith))
    have h2 : 0 ≤ y * (4 * y - 7) := by nlinarith
    linarith [show y ^ 4 - 7 * y ^ 3 + 16 * y ^ 2 - 7 * y + 1 =
      y ^ 2 * ((y - 4) * (y - 3)) + y * (4 * y - 7) + 1 by ring]

/-- `p_altSq_bp` has a real root `λ_bp ∈ (-6, -5)` (so `|λ_bp| > 5`). -/
theorem p_altSq_bp_has_root_lt_neg_five :
    ∃ lam ∈ Set.Icc (-6 : ℝ) (-5), p_altSq_bp lam = 0 := by
  have hcont : ContinuousOn p_altSq_bp (Set.Icc (-6) (-5)) := by
    unfold p_altSq_bp
    fun_prop
  have hneg6 : p_altSq_bp (-6) = 25 := by unfold p_altSq_bp; norm_num
  have hneg5 : p_altSq_bp (-5) = -64 := by unfold p_altSq_bp; norm_num
  have hzero : (0 : ℝ) ∈ Set.Icc (p_altSq_bp (-5)) (p_altSq_bp (-6)) := by
    rw [hneg5, hneg6]; constructor <;> norm_num
  obtain ⟨lam, hmem, hlam⟩ :=
    intermediate_value_Icc' (show (-6 : ℝ) ≤ -5 by norm_num) hcont hzero
  exact ⟨lam, hmem, hlam⟩

/-- **Question 3.35 (4-vertex bipartite failure)**: On `C_4(+, -, +, -)`, every real root of
`p_altSq_circ` satisfies `|λ| < 4`, while `p_altSq_bp` has a real root `λ_bp` with
`|λ_bp| ≥ 5 > 4`. -/
theorem alternatingSquare_bipartite_not_min :
    (∃ lam : ℝ, p_altSq_bp lam = 0 ∧ 5 ≤ |lam|) ∧
      (∀ lam : ℝ, p_altSq_circ lam = 0 → |lam| < 4) := by
  obtain ⟨lam, hmem, hlam⟩ := p_altSq_bp_has_root_lt_neg_five
  refine ⟨⟨lam, hlam, ?_⟩, fun x hx => p_altSq_circ_abs_lt_four hx⟩
  rw [abs_of_neg (by linarith [hmem.2])]
  linarith [hmem.2]

end AlternatingSquare

end MixedSignCoxeter
