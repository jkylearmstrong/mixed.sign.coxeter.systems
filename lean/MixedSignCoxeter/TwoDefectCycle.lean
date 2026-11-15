/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Order.IntermediateValue
import MixedSignCoxeter.Howlett

/-!
# Two-Defect Cycles `C_k(+, +, -, ..., -)`

Formalizes the two-defect cycle reflection systems `cycleTwoDefectSystem k hk a b`
on `k ≥ 3` vertices, where vertices `a` and `b` carry `+2` on the diagonal of `B` and
all other vertices carry `-2`.

## Main results
* `c3_twoDefect_trace`, `c3_twoDefect_has_eigenvalue_lt_neg_one`:
  For `C_3(+, +, -)`, `tr(w) = -5` and `w` has a real eigenvalue `μ ∈ (-10, -2)` (`|μ| > 1`).
* `c4_adjTwoDefect_trace`, `c4_adjTwoDefect_trace_sq`, `c4_adjTwoDefect_charpoly`,
  `c4_adjTwoDefect_no_real_eigenvalue`, `c4_adjTwoDefect_complex_eigenvalue_norm_gt_one`:
  For `C_4(+, +, -, -)`, `tr(w) = -3`, `tr(w²) = -7`, `det(x I - w) = x⁴ + 3x³ + 8x² + 3x + 1`
  has no real roots, and every root `z ∈ ℂ` satisfies `‖z‖ ≠ 1` with at least one root
  having `‖z‖ > 1` (spectral radius `ρ(w) > 1`).
* `c5_adjTwoDefect_has_eigenvalue_lt_neg_one`:
  For `C_5(+, +, -, -, -)`, `w` has a real eigenvalue `μ ∈ (-10, -2)` (`|μ| > 1`).
-/

open Matrix

namespace MixedSignCoxeter

section TwoDefectCycle

/-- Bilinear form of the `k`-cycle with two `+` defects at vertices `a` and `b`
and `-` at all other vertices (`k ≥ 3`). -/
def B_cycleTwoDefect (k : ℕ) (a b : Fin k) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j =>
    if i = j then (if i = a ∨ i = b then 2 else -2)
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
        (i.val = 0 ∧ j.val = k - 1) ∨ (j.val = 0 ∧ i.val = k - 1) then -1
    else 0

/-- Reflection system of the two-defect `k`-cycle `C_k` (`k ≥ 3`). -/
def cycleTwoDefectSystem (k : ℕ) (_hk : 3 ≤ k) (a b : Fin k) : ReflectionSystem k where
  B := B_cycleTwoDefect k a b
  B_symm := by
    ext i j
    simp only [transpose_apply, B_cycleTwoDefect, of_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have hji : j ≠ i := Ne.symm hij
      simp only [hij, hji, ↓reduceIte]
      by_cases hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
          (i.val = 0 ∧ j.val = k - 1) ∨ (j.val = 0 ∧ i.val = k - 1)
      · split_ifs <;> first | rfl | (exfalso; tauto)
      · split_ifs <;> first | rfl | (exfalso; tauto)
  B_diag_ne_zero := by
    intro i
    simp only [B_cycleTwoDefect, of_apply, ↓reduceIte]
    split_ifs <;> norm_num

/-- Principal Coxeter element `w = s_0 * s_1 * ... * s_{k-1}` of `cycleTwoDefectSystem`. -/
noncomputable def w_cycleTwoDefect (k : ℕ) (hk : 3 ≤ k) (a b : Fin k) :
    Matrix (Fin k) (Fin k) ℝ :=
  ReflectionSystem.principalElement (cycleTwoDefectSystem k hk a b)

private lemma continuous_det_sub (n : ℕ) (W : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun x : ℝ => (x • (1 : Matrix (Fin n) (Fin n) ℝ) - W).det) := by
  simp_rw [Matrix.det_apply]
  refine continuous_finsetSum _ fun σ _ => ?_
  refine Continuous.const_smul ?_ _
  refine continuous_finsetProd _ fun i _ => ?_
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, one_apply]
  exact ((continuous_id.mul continuous_const).sub continuous_const)

private lemma exists_eigenvalue_lt_neg_one_of_ivt {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (a b : ℝ) (hab : a ≤ b) (hb : b < -1)
    (ha_neg : (a • (1 : Matrix (Fin n) (Fin n) ℝ) - W).det < 0)
    (hb_pos : 0 < (b • (1 : Matrix (Fin n) (Fin n) ℝ) - W).det) :
    ∃ μ : ℝ, μ < -1 ∧ ∃ v : Fin n → ℝ, v ≠ 0 ∧ W.mulVec v = μ • v := by
  let f : ℝ → ℝ := fun x => (x • (1 : Matrix (Fin n) (Fin n) ℝ) - W).det
  have hf_cont : Continuous f := continuous_det_sub n W
  have hmem : (0 : ℝ) ∈ Set.Icc (f a) (f b) := ⟨le_of_lt ha_neg, le_of_lt hb_pos⟩
  obtain ⟨μ, hμ_icc, hμ_root⟩ := intermediate_value_Icc hab hf_cont.continuousOn hmem
  have hμ_lt : μ < -1 := lt_of_le_of_lt hμ_icc.2 hb
  obtain ⟨v, hv, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hμ_root
  refine ⟨μ, hμ_lt, v, hv, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hmul
  exact hmul.symm

/-! ### `C_3(+, +, -)` -/

/-- Explicit matrix for `w_cycleTwoDefect 3 _ 0 1` on `C_3(+, +, -)`. -/
private def w_c3_twoDefect_explicit : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-2, -3, -2;
      0, -2, -1;
     -1, -1, -1]

private lemma w_c3_twoDefect_eq :
    w_cycleTwoDefect 3 (by decide) 0 1 = w_c3_twoDefect_explicit := by
  unfold w_cycleTwoDefect ReflectionSystem.principalElement cycleTwoDefectSystem B_cycleTwoDefect
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ReflectionSystem.prefixProd, ReflectionSystem.reflectionMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ, w_c3_twoDefect_explicit] <;>
    norm_num

/-- Trace of the principal element of `C_3(+, +, -)` is `-5`. -/
theorem c3_twoDefect_trace :
    (w_cycleTwoDefect 3 (by decide) 0 1).trace = -5 := by
  rw [w_c3_twoDefect_eq]
  simp [Matrix.trace, Fin.sum_univ_succ, w_c3_twoDefect_explicit]
  norm_num

/-- `C_3(+, +, -)` has a real eigenvalue `μ < -1` (in `(-10, -2)`), hence `ρ(w) > 1`. -/
theorem c3_twoDefect_has_eigenvalue_lt_neg_one :
    ∃ μ : ℝ, μ < -1 ∧ ∃ v : Fin 3 → ℝ, v ≠ 0 ∧
      (w_cycleTwoDefect 3 (by decide) 0 1).mulVec v = μ • v := by
  rw [w_c3_twoDefect_eq]
  refine exists_eigenvalue_lt_neg_one_of_ivt w_c3_twoDefect_explicit (-10) (-2)
    (by norm_num) (by norm_num) ?_ ?_
  · simp [Matrix.det_fin_three, w_c3_twoDefect_explicit]; norm_num
  · simp [Matrix.det_fin_three, w_c3_twoDefect_explicit]

/-! ### `C_4(+, +, -, -)` -/

/-- Explicit matrix for `w_cycleTwoDefect 4 _ 0 1` on `C_4(+, +, -, -)`. -/
private def w_c4_adjTwoDefect_explicit : Matrix (Fin 4) (Fin 4) ℝ :=
  !![ 0, -2, -1,  0;
      2, -2,  0,  1;
      1, -1,  0,  1;
     -1,  0, -1, -1]

private lemma w_c4_adjTwoDefect_eq :
    w_cycleTwoDefect 4 (by decide) 0 1 = w_c4_adjTwoDefect_explicit := by
  unfold w_cycleTwoDefect ReflectionSystem.principalElement cycleTwoDefectSystem B_cycleTwoDefect
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ReflectionSystem.prefixProd, ReflectionSystem.reflectionMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ, w_c4_adjTwoDefect_explicit] <;>
    norm_num

/-- Trace of the principal element of `C_4(+, +, -, -)` is `-3`. -/
theorem c4_adjTwoDefect_trace :
    (w_cycleTwoDefect 4 (by decide) 0 1).trace = -3 := by
  rw [w_c4_adjTwoDefect_eq]
  simp [Matrix.trace, Fin.sum_univ_succ, w_c4_adjTwoDefect_explicit]
  norm_num

/-- Trace of `w²` for `C_4(+, +, -, -)` is `-7`, exceeding `n = 4` in absolute value. -/
theorem c4_adjTwoDefect_trace_sq :
    ((w_cycleTwoDefect 4 (by decide) 0 1) ^ 2).trace = -7 := by
  rw [w_c4_adjTwoDefect_eq, sq]
  simp [Matrix.trace, Fin.sum_univ_succ, w_c4_adjTwoDefect_explicit]
  norm_num

/-- Characteristic polynomial of `C_4(+, +, -, -)` is `x⁴ + 3x³ + 8x² + 3x + 1`. -/
theorem c4_adjTwoDefect_charpoly (x : ℝ) :
    (x • (1 : Matrix (Fin 4) (Fin 4) ℝ) - w_cycleTwoDefect 4 (by decide) 0 1).det =
      x ^ 4 + 3 * x ^ 3 + 8 * x ^ 2 + 3 * x + 1 := by
  rw [w_c4_adjTwoDefect_eq]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Fin.succAbove, Matrix.one_apply, w_c4_adjTwoDefect_explicit]
  ring

/-- `C_4(+, +, -, -)` has NO real eigenvalues (`det(μ I - w) > 0` for all `μ ∈ ℝ`). -/
theorem c4_adjTwoDefect_no_real_eigenvalue (μ : ℝ) :
    (μ • (1 : Matrix (Fin 4) (Fin 4) ℝ) - w_cycleTwoDefect 4 (by decide) 0 1).det ≠ 0 := by
  rw [c4_adjTwoDefect_charpoly]
  have h1 : 0 ≤ (μ ^ 2 + 3 / 2 * μ + 1) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ μ ^ 2 := sq_nonneg _
  by_cases hμ : μ = 0
  · subst hμ; norm_num
  · have hpos : 0 < μ ^ 2 := sq_pos_of_ne_zero hμ
    linarith

/-- The characteristic polynomial of `C_4(+, +, -, -)` has a complex root `z` with `‖z‖ > 1`,
proving that its spectral radius satisfies `ρ(w) > 1`. -/
theorem c4_adjTwoDefect_complex_eigenvalue_norm_gt_one :
    ∃ z : ℂ, z ^ 4 + 3 * z ^ 3 + 8 * z ^ 2 + 3 * z + 1 = 0 ∧ 1 < ‖z‖ := by
  let p : Polynomial ℂ :=
    Polynomial.X ^ 4 + Polynomial.C 3 * Polynomial.X ^ 3 + Polynomial.C 8 * Polynomial.X ^ 2 +
      Polynomial.C 3 * Polynomial.X + Polynomial.C 1
  have hnat : p.natDegree = 4 := by
    dsimp [p]
    compute_degree!
  have hp_ne : p ≠ 0 := by
    intro h0
    have h := congrArg (fun q => q.eval 0) h0
    simp [p] at h
  have hdeg : p.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hp_ne, hnat]
    simp
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root p hdeg
  have hzeval : z ^ 4 + 3 * z ^ 3 + 8 * z ^ 2 + 3 * z + 1 = 0 := by
    simpa [p] using hz
  have hz_ne : z ≠ 0 := by
    intro h0
    subst h0
    norm_num at hzeval
  have hnorm_ne_one : ‖z‖ ≠ 1 := by
    intro hnorm
    have hconj : z * starRingEnd ℂ z = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
      norm_num
    have hinv : z⁻¹ = starRingEnd ℂ z := inv_eq_of_mul_eq_one_right hconj
    let u : ℝ := 2 * z.re
    have hu_eq : z + z⁻¹ = (u : ℂ) := by
      rw [hinv, Complex.add_conj]
    have hquad : (z + z⁻¹) ^ 2 + 3 * (z + z⁻¹) + 6 = 0 := by
      have hdiv : (z ^ 4 + 3 * z ^ 3 + 8 * z ^ 2 + 3 * z + 1) / z ^ 2 = 0 := by
        rw [hzeval, zero_div]
      have hid : (z ^ 4 + 3 * z ^ 3 + 8 * z ^ 2 + 3 * z + 1) / z ^ 2 =
          (z + z⁻¹) ^ 2 + 3 * (z + z⁻¹) + 6 := by
        field_simp [hz_ne]
        ring
      rw [← hid, hdiv]
    rw [hu_eq] at hquad
    have hreal : u ^ 2 + 3 * u + 6 = 0 := by
      exact_mod_cast hquad
    nlinarith [sq_nonneg (u + 3 / 2)]
  rcases lt_or_gt_of_ne hnorm_ne_one with hlt | hgt
  · refine ⟨z⁻¹, ?_, ?_⟩
    · have hid : z⁻¹ ^ 4 + 3 * z⁻¹ ^ 3 + 8 * z⁻¹ ^ 2 + 3 * z⁻¹ + 1 =
          (z ^ 4 + 3 * z ^ 3 + 8 * z ^ 2 + 3 * z + 1) / z ^ 4 := by
        field_simp [hz_ne]
        ring
      rw [hid, hzeval, zero_div]
    · rw [norm_inv]
      have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne
      exact one_lt_inv₀ hpos |>.mpr hlt
  · exact ⟨z, hzeval, hgt⟩

/-! ### `C_5(+, +, -, -, -)` -/

/-- Explicit matrix for `w_cycleTwoDefect 5 _ 0 1` on `C_5(+, +, -, -, -)`. -/
private def w_c5_adjTwoDefect_explicit : Matrix (Fin 5) (Fin 5) ℝ :=
  !![-2, -2,  0, -1, -2;
      0, -2,  0,  0, -1;
     -1, -1,  0,  0, -1;
      1,  0, -1,  0,  1;
     -1,  0,  0, -1, -1]

private lemma w_c5_adjTwoDefect_eq :
    w_cycleTwoDefect 5 (by decide) 0 1 = w_c5_adjTwoDefect_explicit := by
  unfold w_cycleTwoDefect ReflectionSystem.principalElement cycleTwoDefectSystem B_cycleTwoDefect
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ReflectionSystem.prefixProd, ReflectionSystem.reflectionMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ, w_c5_adjTwoDefect_explicit] <;>
    norm_num

/-- `C_5(+, +, -, -, -)` has a real eigenvalue `μ < -1` (in `(-10, -2)`), hence `ρ(w) > 1`. -/
theorem c5_adjTwoDefect_has_eigenvalue_lt_neg_one :
    ∃ μ : ℝ, μ < -1 ∧ ∃ v : Fin 5 → ℝ, v ≠ 0 ∧
      (w_cycleTwoDefect 5 (by decide) 0 1).mulVec v = μ • v := by
  rw [w_c5_adjTwoDefect_eq]
  refine exists_eigenvalue_lt_neg_one_of_ivt w_c5_adjTwoDefect_explicit (-10) (-2)
    (by norm_num) (by norm_num) ?_ ?_
  · simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
      Fin.succAbove, Matrix.one_apply, w_c5_adjTwoDefect_explicit]; norm_num
  · simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
      Fin.succAbove, Matrix.one_apply, w_c5_adjTwoDefect_explicit]; norm_num

end TwoDefectCycle

end MixedSignCoxeter
