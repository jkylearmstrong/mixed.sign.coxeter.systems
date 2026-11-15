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
* `c4_nonadjTwoDefect_charpoly`, `c4_nonadjTwoDefect_complex_eigenvalue_norm_gt_one`:
  For non-adjacent `C_4(+, -, +, -)`, `det(x I - w) = x⁴ + 4x³ + 14x² + 4x + 1` has a root
  with `‖z‖ > 1`.
* `c5_nonadjTwoDefect_has_eigenvalue_lt_neg_one`:
  For non-adjacent `C_5(+, -, +, -, -)`, `w` has a real eigenvalue `μ ∈ (-10, -2)` (`|μ| > 1`).
* `oddCycleAdjTwoDefect_has_eigenvalue_lt_neg_one`:
  For every odd adjacent two-defect cycle `C_{2m+1}(+, +, -, ..., -)` (`m ≥ 1`),
  `w` has a real eigenvalue `μ ∈ (-10, -2)` (`|μ| > 1`).
* `evenCycleAdjTwoDefect_charpoly`, `evenCycleAdjTwoDefect_complex_eigenvalue_norm_gt_one`:
  For every even adjacent two-defect cycle `C_{2m}(+, +, -, ..., -)` (`m ≥ 2`),
  `det(x I - w) = x^{2m} + 3 x^{2m-1} + 8 ∑_{k=2}^{2m-2} x^k + 3 x + 1` and has a
  complex root `z ∈ ℂ` with `‖z‖ > 1` (spectral radius `ρ(w) > 1`).
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

/-! ### Non-Adjacent Two-Defect Cycles `C_4(+, -, +, -)` and `C_5(+, -, +, -, -)` -/

/-- Explicit matrix for `w_cycleTwoDefect 4 _ 0 2` on `C_4(+, -, +, -)`. -/
private def w_c4_nonadjTwoDefect_explicit : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-2, -2,  1,  0;
      0, -2,  2,  1;
     -1,  1, -2, -1;
     -1,  0, -1, -1]

private lemma w_c4_nonadjTwoDefect_eq :
    w_cycleTwoDefect 4 (by decide) 0 2 = w_c4_nonadjTwoDefect_explicit := by
  unfold w_cycleTwoDefect ReflectionSystem.principalElement cycleTwoDefectSystem B_cycleTwoDefect
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ReflectionSystem.prefixProd, ReflectionSystem.reflectionMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ, w_c4_nonadjTwoDefect_explicit] <;>
    norm_num

/-- Trace of the principal element of `C_4(+, -, +, -)` is `-7`. -/
theorem c4_nonadjTwoDefect_trace :
    (w_cycleTwoDefect 4 (by decide) 0 2).trace = -7 := by
  rw [w_c4_nonadjTwoDefect_eq]
  simp [Matrix.trace, Fin.sum_univ_succ, w_c4_nonadjTwoDefect_explicit]
  norm_num

/-- Characteristic polynomial of `C_4(+, -, +, -)` is `x⁴ + 7x³ + 16x² + 7x + 1`. -/
theorem c4_nonadjTwoDefect_charpoly (x : ℝ) :
    (x • (1 : Matrix (Fin 4) (Fin 4) ℝ) - w_cycleTwoDefect 4 (by decide) 0 2).det =
      x ^ 4 + 7 * x ^ 3 + 16 * x ^ 2 + 7 * x + 1 := by
  rw [w_c4_nonadjTwoDefect_eq]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Fin.succAbove, Matrix.one_apply, w_c4_nonadjTwoDefect_explicit]
  ring

/-- `C_4(+, -, +, -)` has a complex root `z` of `x⁴ + 7x³ + 16x² + 7x + 1` with `‖z‖ > 1`,
proving that its spectral radius satisfies `ρ(w) > 1`. -/
theorem c4_nonadjTwoDefect_complex_eigenvalue_norm_gt_one :
    ∃ z : ℂ, z ^ 4 + 7 * z ^ 3 + 16 * z ^ 2 + 7 * z + 1 = 0 ∧ 1 < ‖z‖ := by
  let p : Polynomial ℂ :=
    Polynomial.X ^ 4 + Polynomial.C 7 * Polynomial.X ^ 3 + Polynomial.C 16 * Polynomial.X ^ 2 +
      Polynomial.C 7 * Polynomial.X + Polynomial.C 1
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
  have hzeval : z ^ 4 + 7 * z ^ 3 + 16 * z ^ 2 + 7 * z + 1 = 0 := by
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
    have hquad : (z + z⁻¹) ^ 2 + 7 * (z + z⁻¹) + 14 = 0 := by
      have hdiv : (z ^ 4 + 7 * z ^ 3 + 16 * z ^ 2 + 7 * z + 1) / z ^ 2 = 0 := by
        rw [hzeval, zero_div]
      have hid : (z ^ 4 + 7 * z ^ 3 + 16 * z ^ 2 + 7 * z + 1) / z ^ 2 =
          (z + z⁻¹) ^ 2 + 7 * (z + z⁻¹) + 14 := by
        field_simp [hz_ne]
        ring
      rw [← hid, hdiv]
    rw [hu_eq] at hquad
    have hreal : u ^ 2 + 7 * u + 14 = 0 := by
      exact_mod_cast hquad
    nlinarith [sq_nonneg (u + 7 / 2)]
  rcases lt_or_gt_of_ne hnorm_ne_one with hlt | hgt
  · refine ⟨z⁻¹, ?_, ?_⟩
    · have hid : z⁻¹ ^ 4 + 7 * z⁻¹ ^ 3 + 16 * z⁻¹ ^ 2 + 7 * z⁻¹ + 1 =
          (z ^ 4 + 7 * z ^ 3 + 16 * z ^ 2 + 7 * z + 1) / z ^ 4 := by
        field_simp [hz_ne]
        ring
      rw [hid, hzeval, zero_div]
    · rw [norm_inv]
      have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne
      exact one_lt_inv₀ hpos |>.mpr hlt
  · exact ⟨z, hzeval, hgt⟩

/-- Explicit matrix for `w_cycleTwoDefect 5 _ 0 2` on `C_5(+, -, +, -, -)`. -/
private def w_c5_nonadjTwoDefect_explicit : Matrix (Fin 5) (Fin 5) ℝ :=
  !![-4, -2,  2, -1, -2;
     -2, -2,  2,  0, -1;
      1,  1, -2,  0,  1;
      1,  0, -1,  0,  1;
     -1,  0,  0, -1, -1]

private lemma w_c5_nonadjTwoDefect_eq :
    w_cycleTwoDefect 5 (by decide) 0 2 = w_c5_nonadjTwoDefect_explicit := by
  unfold w_cycleTwoDefect ReflectionSystem.principalElement cycleTwoDefectSystem B_cycleTwoDefect
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ReflectionSystem.prefixProd, ReflectionSystem.reflectionMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ, w_c5_nonadjTwoDefect_explicit] <;>
    norm_num

/-- `C_5(+, -, +, -, -)` has a real eigenvalue `μ < -1` (in `(-10, -2)`), hence `ρ(w) > 1`. -/
theorem c5_nonadjTwoDefect_has_eigenvalue_lt_neg_one :
    ∃ μ : ℝ, μ < -1 ∧ ∃ v : Fin 5 → ℝ, v ≠ 0 ∧
      (w_cycleTwoDefect 5 (by decide) 0 2).mulVec v = μ • v := by
  rw [w_c5_nonadjTwoDefect_eq]
  refine exists_eigenvalue_lt_neg_one_of_ivt w_c5_nonadjTwoDefect_explicit (-10) (-2)
    (by norm_num) (by norm_num) ?_ ?_
  · simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
      Fin.succAbove, Matrix.one_apply, w_c5_nonadjTwoDefect_explicit]; norm_num
  · simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
      Fin.succAbove, Matrix.one_apply, w_c5_nonadjTwoDefect_explicit]; norm_num

/-! ### General Infinite Family `C_{2m+1}(+, +, -, ..., -)` (`m ≥ 1`) -/

/-- `n × n` tridiagonal matrix with diagonal `d`, superdiagonal `u`, and subdiagonal `-1`. -/
private def tridiagDU (d u : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if i = j then d
    else if i.val + 1 = j.val then u
    else if j.val + 1 = i.val then -1
    else 0

private lemma det_eq_single_row_zero' {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (k : Fin (n + 1)) (hk : ∀ j : Fin (n + 1), j ≠ k → M 0 j = 0) :
    M.det = (-1 : ℝ) ^ (k : ℕ) * M 0 k * (M.submatrix Fin.succ k.succAbove).det := by
  rw [Matrix.det_succ_row_zero]
  refine Finset.sum_eq_single k (fun j _ hjk => ?_) (fun hkmem => absurd (Finset.mem_univ k) hkmem)
  simp [hk j hjk]

private lemma det_eq_single_col_zero' {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (k : Fin (n + 1)) (hk : ∀ i : Fin (n + 1), i ≠ k → M i 0 = 0) :
    M.det = (-1 : ℝ) ^ (k : ℕ) * M k 0 * (M.submatrix k.succAbove Fin.succ).det := by
  rw [← Matrix.det_transpose, det_eq_single_row_zero' Mᵀ k (fun j hj => hk j hj)]
  simp only [transpose_apply]
  have hsub : (Mᵀ.submatrix Fin.succ k.succAbove) = (M.submatrix k.succAbove Fin.succ)ᵀ := by
    ext i j; simp
  rw [hsub, Matrix.det_transpose]

private lemma det_tridiagDU_zero (d u : ℝ) : (tridiagDU d u 0).det = 1 := by simp

private lemma det_tridiagDU_one (d u : ℝ) : (tridiagDU d u 1).det = d := by
  simp [Matrix.det_unique, tridiagDU]

private lemma det_tridiagDU_succ_succ (d u : ℝ) (n : ℕ) :
    (tridiagDU d u (n + 2)).det =
      d * (tridiagDU d u (n + 1)).det + u * (tridiagDU d u n).det := by
  let M := tridiagDU d u (n + 2)
  rw [Matrix.det_succ_row_zero]
  have hsum : ∑ j : Fin (n + 2), (-1 : ℝ) ^ (j : ℕ) * M 0 j *
      (M.submatrix Fin.succ j.succAbove).det =
      M 0 0 * (M.submatrix Fin.succ (0 : Fin (n + 2)).succAbove).det -
      M 0 1 * (M.submatrix Fin.succ (1 : Fin (n + 2)).succAbove).det := by
    have h01 : (0 : Fin (n + 2)) ≠ 1 := by simp
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (n + 2)))]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ (1 : Fin (n + 2))⟩)]
    have hrest : ∑ j ∈ (Finset.univ.erase (0 : Fin (n + 2))).erase (1 : Fin (n + 2)),
        (-1 : ℝ) ^ (j : ℕ) * M 0 j * (M.submatrix Fin.succ j.succAbove).det = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj0 : j ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
      have hj1 : j ≠ 1 := (Finset.mem_erase.mp hj).1
      have hM0j : M 0 j = 0 := by
        simp only [M, tridiagDU, of_apply, Fin.val_zero, zero_add]
        have hv0 : (0 : Fin (n + 2)) ≠ j := hj0.symm
        have hv1 : (1 : ℕ) ≠ j.val := fun h => hj1 (Fin.ext h.symm)
        simp [hv0, hv1]
      simp [hM0j]
    rw [hrest, add_zero]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_one, pow_one]
    ring
  have hM00 : M 0 0 = d := by simp [M, tridiagDU]
  have hM01 : M 0 1 = u := by
    simp only [M, tridiagDU, of_apply]
    have hne : (0 : Fin (n + 2)) ≠ 1 := by simp
    simp [hne]
  have hsub0 : M.submatrix Fin.succ (0 : Fin (n + 2)).succAbove = tridiagDU d u (n + 1) := by
    ext i j
    simp only [M, submatrix_apply, Fin.succAbove_zero, tridiagDU, of_apply, Fin.val_succ,
      Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  let N := M.submatrix Fin.succ (1 : Fin (n + 2)).succAbove
  have hcol0 : ∀ i : Fin (n + 1), i ≠ 0 → N i 0 = 0 := by
    intro i hi
    have hsucc0 : Fin.succAbove (1 : Fin (n + 2)) (0 : Fin (n + 1)) = 0 := by
      ext; simp [Fin.succAbove]
    have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
    simp only [N, submatrix_apply, hsucc0, M, tridiagDU, of_apply, Fin.ext_iff, Fin.val_succ]
    split_ifs <;> first | rfl | (have := i.isLt; simp only [Fin.ext_iff, Fin.val_zero] at *; omega)
  have hN_det := det_eq_single_col_zero' N 0 hcol0
  have hN00 : N 0 0 = -1 := by
    have hsucc0 : Fin.succAbove (1 : Fin (n + 2)) (0 : Fin (n + 1)) = 0 := by
      ext; simp [Fin.succAbove]
    simp only [N, submatrix_apply, Fin.succ_zero_eq_one, hsucc0, M, tridiagDU, of_apply]
    have hne : (1 : Fin (n + 2)) ≠ 0 := by simp
    simp [hne]
  have hNsub : N.submatrix (0 : Fin (n + 1)).succAbove Fin.succ = tridiagDU d u n := by
    ext i j
    simp only [N, submatrix_apply, Fin.succAbove_zero, tridiagDU, of_apply, M]
    have hsucc : (Fin.succAbove (1 : Fin (n + 2)) j.succ).val = j.val + 2 := by
      simp only [Fin.succAbove]
      split_ifs with h
      · exfalso; simp [Fin.lt_def] at h
      · simp
    simp only [Fin.ext_iff, Fin.val_succ, hsucc]
    split_ifs <;> first | rfl | omega
  rw [hN00, Fin.val_zero, pow_zero, one_mul, hNsub] at hN_det
  rw [hsum, hM00, hM01, hsub0, hN_det]
  ring

private lemma det_tridiagDU_one_two (n : ℕ) :
    3 * (tridiagDU 1 2 n).det = 2 ^ (n + 1) - (-1 : ℝ) ^ (n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | k
    · rw [det_tridiagDU_zero]; norm_num
    · rw [det_tridiagDU_one]; norm_num
    · rw [det_tridiagDU_succ_succ]
      have h1 := ih (k + 1) (by omega)
      have h2 := ih k (by omega)
      linear_combination h1 + 2 * h2

private lemma det_tridiagDU_nine_ten (n : ℕ) :
    11 * (tridiagDU 9 10 n).det = 10 ^ (n + 1) - (-1 : ℝ) ^ (n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | k
    · rw [det_tridiagDU_zero]; norm_num
    · rw [det_tridiagDU_one]; norm_num
    · rw [det_tridiagDU_succ_succ]
      have h1 := ih (k + 1) (by omega)
      have h2 := ih k (by omega)
      linear_combination 9 * h1 + 10 * h2

private lemma howlettU_oddCycleTwoDefect_det (m : ℕ) (hm : 1 ≤ m) :
    (ReflectionSystem.howlettU (cycleTwoDefectSystem (2 * m + 1) (by omega) 0 1).B).det = -1 := by
  rw [ReflectionSystem.howlettU_det]
  have hprod : (∏ i : Fin (2 * m + 1),
      (cycleTwoDefectSystem (2 * m + 1) (by omega) 0 1).B i i / 2) =
      ∏ i : Fin (2 * m + 1), if i = 0 ∨ i = 1 then (1 : ℝ) else (-1 : ℝ) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [cycleTwoDefectSystem, B_cycleTwoDefect, of_apply, ↓reduceIte]
    split_ifs <;> norm_num
  rw [hprod]
  have h01 : (0 : Fin (2 * m + 1)) ≠ 1 := by simp [Fin.ext_iff]; omega
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (0 : Fin (2 * m + 1)))]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ (1 : Fin (2 * m + 1))⟩)]
  simp only [↓reduceIte, true_or, or_true, one_mul]
  have hrest : ∀ i ∈ (Finset.univ.erase (0 : Fin (2 * m + 1))).erase 1,
      (if i = 0 ∨ i = 1 then (1 : ℝ) else (-1 : ℝ)) = -1 := by
    intro i hi
    have hi1 : i ≠ 1 := (Finset.mem_erase.mp hi).1
    have hi0 : i ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    simp [hi0, hi1]
  rw [Finset.prod_congr rfl hrest, Finset.prod_const]
  have hcard : ((Finset.univ.erase (0 : Fin (2 * m + 1))).erase 1).card = 2 * m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ 1⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
    omega
  rw [hcard]
  have hsplit : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
  rw [hsplit, pow_add, pow_mul]
  norm_num

/-- General Howlett matrix `x • U + Uᵀ` for `C_{2m+1}(+, +, -, ..., -)` with `d = -(x + 1)`
and `u = -x`. -/
private def cycleTwoDefectM (m : ℕ) (d u : ℝ) :
    Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ :=
  Matrix.of fun i j =>
    if i = j then (if i = 0 ∨ i = 1 then -d else d)
    else if i.val + 1 = j.val ∨ (i.val = 0 ∧ j.val = 2 * m) then u
    else if j.val + 1 = i.val ∨ (j.val = 0 ∧ i.val = 2 * m) then -1
    else 0

private lemma howlett_oddTwoDefect_eq (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    x • ReflectionSystem.howlettU (cycleTwoDefectSystem (2 * m + 1) (by omega) 0 1).B +
      (ReflectionSystem.howlettU (cycleTwoDefectSystem (2 * m + 1) (by omega) 0 1).B)ᵀ =
      cycleTwoDefectM m (-(x + 1)) (-x) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, transpose_apply,
    ReflectionSystem.howlettU_apply, cycleTwoDefectSystem, B_cycleTwoDefect, of_apply,
    cycleTwoDefectM]
  by_cases hij : i = j
  · subst hij
    simp only [lt_self_iff_false, ↓reduceIte]
    split_ifs <;> ring
  · rcases lt_trichotomy i j with hlt | heq | hgt
    · have hgt' : ¬(j < i) := not_lt_of_gt hlt
      have hji : j ≠ i := Ne.symm hij
      have hi_lt : i.val < j.val := hlt
      have hno2 : ¬(j.val + 1 = i.val ∨ (j = 0 ∧ i.val = 2 * m)) := by
        simp only [Fin.ext_iff, Fin.val_zero]; omega
      simp only [hlt, hgt', hij, hji, ↓reduceIte]
      by_cases hadj : i.val + 1 = j.val ∨ (i = 0 ∧ j.val = 2 * m)
      · have hadj' : i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
            (i = 0 ∧ j.val = 2 * m) ∨ (j = 0 ∧ i.val = 2 * m) := by tauto
        simp [hadj, hadj', hno2]; try tauto
      · have hadj' : ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
            (i = 0 ∧ j.val = 2 * m) ∨ (j = 0 ∧ i.val = 2 * m)) := by tauto
        simp [hadj, hadj', hno2]; try tauto
    · exact absurd heq hij
    · have hlt' : ¬(i < j) := not_lt_of_gt hgt
      have hji : j ≠ i := Ne.symm hij
      have hj_lt : j.val < i.val := hgt
      have hno1 : ¬(i.val + 1 = j.val ∨ (i = 0 ∧ j.val = 2 * m)) := by
        simp only [Fin.ext_iff, Fin.val_zero]; omega
      simp only [hlt', hgt, hij, hji, ↓reduceIte, hno1]
      by_cases hadj : j.val + 1 = i.val ∨ (j = 0 ∧ i.val = 2 * m)
      · have hadj' : i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
            (i = 0 ∧ j.val = 2 * m) ∨ (j = 0 ∧ i.val = 2 * m) := by tauto
        simp [hadj, hadj', hno1]; try tauto
      · have hadj' : ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
            (i = 0 ∧ j.val = 2 * m) ∨ (j = 0 ∧ i.val = 2 * m)) := by tauto
        simp [hadj, hadj', hno1]; try tauto

/-- Tridiagonal matrix with `(-d, d, ..., d)` on the diagonal (`n + 1` × `n + 1`). -/
private def tridiagFlipHead (d u : ℝ) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j =>
    if i = j then (if i = 0 then -d else d)
    else if i.val + 1 = j.val then u
    else if j.val + 1 = i.val then -1
    else 0

private lemma det_tridiagFlipHead (d u : ℝ) (n : ℕ) :
    (tridiagFlipHead d u n).det =
      -d * (tridiagDU d u n).det + u * (if n = 0 then 0 else (tridiagDU d u (n - 1)).det) := by
  rcases n with _ | k
  · simp [Matrix.det_unique, tridiagFlipHead, det_tridiagDU_zero]
  · let M := tridiagFlipHead d u (k + 1)
    rw [Matrix.det_succ_row_zero]
    have hsum : ∑ j : Fin (k + 2), (-1 : ℝ) ^ (j : ℕ) * M 0 j *
        (M.submatrix Fin.succ j.succAbove).det =
        M 0 0 * (M.submatrix Fin.succ (0 : Fin (k + 2)).succAbove).det -
        M 0 1 * (M.submatrix Fin.succ (1 : Fin (k + 2)).succAbove).det := by
      have h01 : (0 : Fin (k + 2)) ≠ 1 := by simp [Fin.ext_iff]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (k + 2)))]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ (1 : Fin (k + 2))⟩)]
      have hrest : ∑ j ∈ (Finset.univ.erase (0 : Fin (k + 2))).erase (1 : Fin (k + 2)),
          (-1 : ℝ) ^ (j : ℕ) * M 0 j * (M.submatrix Fin.succ j.succAbove).det = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hj0 : j ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
        have hj1 : j ≠ 1 := (Finset.mem_erase.mp hj).1
        have hM0j : M 0 j = 0 := by
          simp only [M, tridiagFlipHead, of_apply, Fin.val_zero, zero_add]
          have hv0 : (0 : Fin (k + 2)) ≠ j := hj0.symm
          have hv1 : (1 : ℕ) ≠ j.val := fun h => hj1 (Fin.ext h.symm)
          have hv2 : ¬(j.val + 1 = 0) := by omega
          simp [hv0, hv1, hv2]
        simp [hM0j]
      rw [hrest, add_zero]
      simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_one,
        Nat.mod_eq_of_lt (by omega : 1 < k + 2), pow_one]
      ring
    have hM00 : M 0 0 = -d := by simp [M, tridiagFlipHead]
    have hM01 : M 0 1 = u := by
      simp only [M, tridiagFlipHead, of_apply]
      have hne : (0 : Fin (k + 2)) ≠ 1 := by simp [Fin.ext_iff]
      simp [hne]
    have hsub0 : M.submatrix Fin.succ (0 : Fin (k + 2)).succAbove = tridiagDU d u (k + 1) := by
      ext i j
      simp only [M, submatrix_apply, Fin.succAbove_zero, tridiagFlipHead, tridiagDU, of_apply,
        Fin.val_succ, Fin.ext_iff, Fin.val_zero]
      split_ifs <;> first | rfl | contradiction | (have := i.isLt; have := j.isLt; omega)
    let N := M.submatrix Fin.succ (1 : Fin (k + 2)).succAbove
    have hcol0 : ∀ i : Fin (k + 1), i ≠ 0 → N i 0 = 0 := by
      intro i hi
      have hsucc0 : Fin.succAbove (1 : Fin (k + 2)) (0 : Fin (k + 1)) = 0 := by
        ext; simp [Fin.succAbove]
      have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
      have h0val : (0 : Fin (k + 2)).val = 0 := rfl
      have hc1 : i.val + 1 ≠ 0 := by omega
      have hc2 : i.val + 1 + 1 ≠ 0 := by omega
      have hc3 : 0 + 1 ≠ i.val + 1 := by omega
      simp only [N, submatrix_apply, hsucc0, M, tridiagFlipHead, of_apply, Fin.ext_iff,
        Fin.val_succ, h0val, hc1, hc2, hc3, ↓reduceIte]
    have hN_det := det_eq_single_col_zero' N 0 hcol0
    have hN00 : N 0 0 = -1 := by
      have hsucc0 : Fin.succAbove (1 : Fin (k + 2)) (0 : Fin (k + 1)) = 0 := by
        ext; simp [Fin.succAbove]
      simp only [N, submatrix_apply, Fin.succ_zero_eq_one, hsucc0, M, tridiagFlipHead, of_apply]
      have hne : (1 : Fin (k + 2)) ≠ 0 := by simp [Fin.ext_iff]
      simp [hne]
    have hNsub : N.submatrix (0 : Fin (k + 1)).succAbove Fin.succ = tridiagDU d u k := by
      ext i j
      simp only [N, submatrix_apply, Fin.succAbove_zero, tridiagFlipHead, tridiagDU, of_apply, M]
      have hsucc : (Fin.succAbove (1 : Fin (k + 2)) j.succ).val = j.val + 2 := by
        simp only [Fin.succAbove]
        split_ifs with h
        · exfalso; simp [Fin.lt_def] at h
        · simp
      simp only [Fin.ext_iff, Fin.val_succ, Fin.val_zero, hsucc]
      split_ifs <;> first | rfl | contradiction | (have := i.isLt; have := j.isLt; omega)
    rw [hN00, Fin.val_zero, pow_zero, one_mul, hNsub] at hN_det
    rw [hsum, hM00, hM01, hsub0, hN_det]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    have hsub1 : k + 1 - 1 = k := by omega
    rw [hsub1]
    ring

private lemma det_cycleTwoDefectM (m : ℕ) (hm : 2 ≤ m) (d u : ℝ) :
    (cycleTwoDefectM m d u).det =
      (d ^ 2 + u) * (tridiagDU d u (2 * m - 1)).det -
        d * u * (tridiagDU d u (2 * m - 2)).det +
        u - u ^ (2 * m) +
        u * (-d * (tridiagDU d u (2 * m - 2)).det + u * (tridiagDU d u (2 * m - 3)).det) := by
  have : NeZero (2 * m) := ⟨by omega⟩
  let M := cycleTwoDefectM m d u
  let last : Fin (2 * m + 1) := ⟨2 * m, by omega⟩
  -- Split row 0 into (M without (0, 2m)) and (only u at (0, 2m))
  let r0_noCorner : Fin (2 * m + 1) → ℝ := fun j => if j = last then 0 else M 0 j
  let r0_corner : Fin (2 * m + 1) → ℝ := fun j => if j = last then u else 0
  have hr0_eq : M 0 = r0_noCorner + r0_corner := by
    ext j
    simp only [Pi.add_apply, r0_noCorner, r0_corner, M, cycleTwoDefectM, of_apply]
    by_cases hj : j = last
    · subst hj
      have h0ne : (0 : Fin (2 * m + 1)) ≠ ⟨2 * m, by omega⟩ := by simp [Fin.ext_iff]; omega
      simp [h0ne, last]
    · simp [hj]
  have hM_upd : M = M.updateRow 0 (r0_noCorner + r0_corner) := by
    ext i j
    simp only [Matrix.updateRow_apply]
    by_cases hi : i = 0
    · subst hi; exact congrFun hr0_eq j
    · simp [hi]
  have hsplit_row : M.det = (M.updateRow 0 r0_noCorner).det + (M.updateRow 0 r0_corner).det := by
    conv_lhs => rw [hM_upd]
    exact Matrix.det_updateRow_add M 0 r0_noCorner r0_corner
  -- Split col 0 of any matrix with A last 0 = -1 into (no (2m, 0)) and (only -1 at (2m, 0))
  let c0_noCorner (A : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ) :
      Fin (2 * m + 1) → ℝ := fun i => if i = last then 0 else A i 0
  let c0_corner : Fin (2 * m + 1) → ℝ := fun i => if i = last then -1 else 0
  have hsplit_col : ∀ A : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ, A last 0 = -1 →
      A.det = (A.updateCol 0 (c0_noCorner A)).det + (A.updateCol 0 c0_corner).det := by
    intro A hAlast
    have hcol_eq : (fun i => A i 0) = c0_noCorner A + c0_corner := by
      ext i
      simp only [Pi.add_apply, c0_noCorner, c0_corner]
      by_cases hi : i = last <;> simp [hi, hAlast]
    have hA_upd : A = A.updateCol 0 (c0_noCorner A + c0_corner) := by
      ext i j
      simp only [Matrix.updateCol_apply]
      by_cases hj : j = 0
      · subst hj; exact congrFun hcol_eq i
      · simp [hj]
    conv_lhs => rw [hA_upd]
    exact Matrix.det_updateCol_add A 0 (c0_noCorner A) c0_corner
  let A1 := M.updateRow 0 r0_noCorner
  let A2 := M.updateRow 0 r0_corner
  have hA1_last : A1 last 0 = -1 := by
    have hlast0 : last ≠ 0 := by simp [last, Fin.ext_iff]; omega
    simp [A1, Matrix.updateRow_apply, hlast0, M, cycleTwoDefectM, last]
  have hA2_last : A2 last 0 = -1 := by
    have hlast0 : last ≠ 0 := by simp [last, Fin.ext_iff]; omega
    simp [A2, Matrix.updateRow_apply, hlast0, M, cycleTwoDefectM, last]
  rw [hsplit_row, hsplit_col A1 hA1_last, hsplit_col A2 hA2_last]
  -- Piece 1: M1 = A1.updateCol 0 (c0_noCorner A1)
  let M1 := A1.updateCol 0 (c0_noCorner A1)
  have hM1_det : M1.det =
      (d ^ 2 + u) * (tridiagDU d u (2 * m - 1)).det -
        d * u * (tridiagDU d u (2 * m - 2)).det := by
    rw [Matrix.det_succ_row_zero]
    have hsum : ∑ j : Fin (2 * m + 1), (-1 : ℝ) ^ (j : ℕ) * M1 0 j *
        (M1.submatrix Fin.succ j.succAbove).det =
        M1 0 0 * (M1.submatrix Fin.succ (0 : Fin (2 * m + 1)).succAbove).det -
        M1 0 1 * (M1.submatrix Fin.succ (1 : Fin (2 * m + 1)).succAbove).det := by
      have h01 : (0 : Fin (2 * m + 1)) ≠ 1 := by simp [Fin.ext_iff]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (2 * m + 1)))]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ (1 : Fin (2 * m + 1))⟩)]
      have hrest : ∑ j ∈ (Finset.univ.erase (0 : Fin (2 * m + 1))).erase (1 : Fin (2 * m + 1)),
          (-1 : ℝ) ^ (j : ℕ) * M1 0 j * (M1.submatrix Fin.succ j.succAbove).det = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hj0 : j ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
        have hj1 : j ≠ 1 := (Finset.mem_erase.mp hj).1
        have hM1_0j : M1 0 j = 0 := by
          simp only [M1, Matrix.updateCol_apply, hj0, ↓reduceIte, A1, Matrix.updateRow_apply,
            r0_noCorner, M, cycleTwoDefectM, of_apply, Fin.val_zero, zero_add]
          by_cases hjlast : j = last
          · simp [hjlast]
          · simp only [hjlast, ↓reduceIte]
            have hv0 : (0 : Fin (2 * m + 1)) ≠ j := hj0.symm
            have h1val : (1 : Fin (2 * m + 1)).val = 1 :=
              Nat.mod_eq_of_lt (by omega : (1 : ℕ) < 2 * m + 1)
            have hv1 : (1 : ℕ) ≠ j.val := by
              intro h; apply hj1; ext; exact h.symm.trans h1val.symm
            have hv2 : j.val ≠ 2 * m := fun h => hjlast (Fin.ext h)
            have hv3 : ¬(j.val + 1 = 0) := by omega
            have h0val : (0 : Fin (2 * m + 1)).val = 0 := rfl
            have hc1 : (0 : ℕ) ≠ j.val := by
              intro h; apply hj0; ext; exact h.symm.trans h0val.symm
            have hc2 : ¬((1 : ℕ) = j.val ∨ j.val = 2 * m) := by omega
            have hc3 : ¬(j.val + 1 = 0 ∨ (j.val = 0 ∧ 0 = 2 * m)) := by
              intro h; rcases h with h | ⟨h, _⟩
              · omega
              · exact hc1 h.symm
            simp only [Fin.ext_iff, h0val, hc1, hc2, hc3, true_and, ↓reduceIte]
        simp [hM1_0j]
      rw [hrest, add_zero]
      have h1val : (1 : Fin (2 * m + 1)).val = 1 :=
        Nat.mod_eq_of_lt (by omega : (1 : ℕ) < 2 * m + 1)
      simp only [Fin.val_zero, pow_zero, one_mul, h1val, pow_one]
      ring
    have hM1_00 : M1 0 0 = -d := by
      have h0last : (0 : Fin (2 * m + 1)) ≠ last := by simp [last, Fin.ext_iff]; omega
      simp [M1, Matrix.updateCol_apply, c0_noCorner, A1, Matrix.updateRow_apply, r0_noCorner,
        h0last, M, cycleTwoDefectM]
    have hM1_01 : M1 0 1 = u := by
      have h10 : (1 : Fin (2 * m + 1)) ≠ 0 := by
        intro h; have := congrArg Fin.val h; simp [Nat.mod_eq_of_lt (by omega : 1 < 2 * m + 1)] at this
      have h1last : (1 : Fin (2 * m + 1)) ≠ last := by
        intro h; have := congrArg Fin.val h; simp [last, Nat.mod_eq_of_lt (by omega : 1 < 2 * m + 1)] at this; omega
      simp [M1, Matrix.updateCol_apply, h10, A1, Matrix.updateRow_apply, r0_noCorner, h1last,
        M, cycleTwoDefectM, Nat.mod_eq_of_lt (by omega : 1 < 2 * m + 1)]
    have h2m : 2 * m = (2 * m - 1) + 1 := by omega
    have hsub0_det : (M1.submatrix Fin.succ (0 : Fin (2 * m + 1)).succAbove).det =
        (tridiagFlipHead d u (2 * m - 1)).det := by
      rw [← Matrix.det_reindex_self (finCongr h2m)]
      congr 1
      ext i j
      have h0val : (0 : Fin (2 * m + 1)).val = 0 := rfl
      have h1val : (1 : Fin (2 * m + 1)).val = 1 :=
        Nat.mod_eq_of_lt (by omega : (1 : ℕ) < 2 * m + 1)
      have h0val' : (0 : Fin ((2 * m - 1) + 1)).val = 0 := rfl
      have hsymm : ∀ x : Fin ((2 * m - 1) + 1), ((finCongr h2m).symm x).val = x.val := fun _ => rfl
      simp only [Matrix.reindex_apply, finCongr_apply, M1, submatrix_apply,
        Fin.succAbove_zero, Matrix.updateCol_apply, Fin.succ_ne_zero, ↓reduceIte, A1,
        Matrix.updateRow_apply, r0_noCorner, M, cycleTwoDefectM, of_apply, tridiagFlipHead,
        Fin.ext_iff, Fin.val_cast, Fin.val_succ, h0val, h1val, h0val', hsymm, last, Fin.val_mk]
      have hni0 : i.val + 1 ≠ 0 := by omega
      have hnj0 : j.val + 1 ≠ 0 := by omega
      simp only [hni0, hnj0, false_and, or_false, false_or]
      split_ifs <;> first | rfl | contradiction | omega
    let N := M1.submatrix Fin.succ (1 : Fin (2 * m + 1)).succAbove
    have hN_col0 : ∀ i : Fin (2 * m), i ≠ 0 → N i 0 = 0 := by
      intro i hi
      have hsucc0 : Fin.succAbove (1 : Fin (2 * m + 1)) (0 : Fin (2 * m)) = 0 := by
        ext; simp [Fin.succAbove]
      have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
      by_cases hil : i.succ = last
      · simp [N, submatrix_apply, hsucc0, M1, Matrix.updateCol_apply, c0_noCorner, hil]
      · have hil' : i.val + 1 ≠ 2 * m := by
          intro h; apply hil; ext; dsimp [last]; exact h
        have h0val : (0 : Fin (2 * m + 1)).val = 0 := rfl
        have hc1 : i.val + 1 ≠ 0 := by omega
        have hc2 : i.val + 1 + 1 ≠ 0 := by omega
        have hc3 : ¬(0 + 1 = i.val + 1 ∨ i.val + 1 = 2 * m) := by omega
        simp only [N, submatrix_apply, hsucc0, M1, Matrix.updateCol_apply, c0_noCorner, hil,
          ↓reduceIte, A1, Matrix.updateRow_apply, Fin.succ_ne_zero]
        simp only [M, cycleTwoDefectM, of_apply, Fin.ext_iff, Fin.val_succ, Fin.val_zero,
          h0val, hc1, hc2, false_and, true_and, or_false, false_or, hc3, ↓reduceIte]
    have hN00 : N 0 0 = -1 := by
      have hsucc0 : Fin.succAbove (1 : Fin (2 * m + 1)) (0 : Fin (2 * m)) = 0 := by
        ext; simp [Fin.succAbove]
      have h1val : (1 : Fin (2 * m + 1)).val = 1 :=
        Nat.mod_eq_of_lt (by omega : (1 : ℕ) < 2 * m + 1)
      have h1last : (1 : Fin (2 * m + 1)) ≠ last :=
        Fin.ne_of_val_ne (by dsimp [last]; rw [Nat.mod_eq_of_lt (by omega : 1 < 2 * m + 1)]; omega)
      have h1_eq : Fin.succ (0 : Fin (2 * m)) = (1 : Fin (2 * m + 1)) := by
        ext; rw [Fin.val_succ, Fin.val_zero, h1val]
      have h0val : (0 : Fin (2 * m + 1)).val = 0 := rfl
      have hc1 : (1 : ℕ) ≠ 0 := by omega
      have hc2 : (1 : ℕ) + 1 ≠ 0 := by omega
      have hc3 : (0 : ℕ) + 1 = 1 ∨ 1 = 2 * m := Or.inl rfl
      simp only [N, submatrix_apply, hsucc0, M1, Matrix.updateCol_apply, c0_noCorner,
        Fin.succ_ne_zero, h1_eq, h1last, ↓reduceIte, A1, Matrix.updateRow_apply]
      simp only [M, cycleTwoDefectM, of_apply, Fin.ext_iff, Fin.val_zero,
        h0val, h1val, hc1, hc2, false_and, true_and, or_false, false_or, hc3, true_or, ↓reduceIte]
    let N' : Matrix (Fin ((2 * m - 1) + 1)) (Fin ((2 * m - 1) + 1)) ℝ :=
      N.reindex (finCongr h2m) (finCongr h2m)
    have hN'_col0 : ∀ i : Fin ((2 * m - 1) + 1), i ≠ 0 → N' i 0 = 0 := by
      intro i hi
      have h0eq : (finCongr h2m).symm 0 = (0 : Fin (2 * m)) := by ext; rfl
      simp only [N', Matrix.reindex_apply, h0eq]
      apply hN_col0 ((finCongr h2m).symm i)
      intro h; apply hi; ext; simpa using congrArg Fin.val h
    have hN_det : N.det = (-1 : ℝ) ^ (0 : ℕ) * N' 0 0 *
        (N'.submatrix (0 : Fin ((2 * m - 1) + 1)).succAbove Fin.succ).det := by
      rw [← Matrix.det_reindex_self (finCongr h2m) N]
      exact det_eq_single_col_zero' N' 0 hN'_col0
    have hN00' : N' 0 0 = -1 := by
      have h0eq : (finCongr h2m).symm 0 = (0 : Fin (2 * m)) := by ext; simp
      simpa [N', Matrix.reindex_apply, h0eq] using hN00
    have hNsub : (N'.submatrix (0 : Fin ((2 * m - 1) + 1)).succAbove Fin.succ).det =
        (tridiagDU d u (2 * m - 1)).det := by
      congr 1
      ext i j
      have hsymm : ∀ x : Fin ((2 * m - 1) + 1), ((finCongr h2m).symm x).val = x.val := fun _ => rfl
      have h1val : (1 : Fin (2 * m + 1)).val = 1 :=
        Nat.mod_eq_of_lt (by omega : (1 : ℕ) < 2 * m + 1)
      have hsucc : (Fin.succAbove (1 : Fin (2 * m + 1))
          ((finCongr h2m).symm j.succ)).val = j.val + 2 := by
        simp only [Fin.succAbove]
        split_ifs with h
        · exfalso; simp only [Fin.lt_def, Fin.val_castSucc, hsymm, Fin.val_succ, h1val] at h
          omega
        · simp [hsymm]
      have h0val : (0 : Fin (2 * m + 1)).val = 0 := rfl
      have hne0 : Fin.succAbove (1 : Fin (2 * m + 1)) ((finCongr h2m).symm j.succ) ≠ 0 := by
        intro h; have := congrArg Fin.val h; rw [hsucc, Fin.val_zero] at this; omega
      have hi2 : i.val + 2 ≠ 0 := by omega
      have hj2 : j.val + 2 ≠ 0 := by omega
      simp only [N', Matrix.reindex_apply, submatrix_apply, Fin.succAbove_zero,
        finCongr_apply, Fin.val_cast, Fin.val_succ, N, Matrix.updateCol_apply,
        hne0, ↓reduceIte, M1, A1, Matrix.updateRow_apply, Fin.succ_ne_zero]
      simp only [M, cycleTwoDefectM, of_apply, tridiagDU, Fin.ext_iff, Fin.val_zero,
        h0val, h1val, hsucc, hsymm, hi2, hj2, false_and, or_false, false_or,
        add_assoc, Nat.add_right_cancel_iff]
      by_cases hij : i = j
      · subst hij; simp
      · have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
        by_cases hij1 : i.val + 1 = j.val
        · have hji1 : j.val + 1 ≠ i.val := by omega
          simp [hij', hij1, hji1]
        · by_cases hji1 : j.val + 1 = i.val
          · have hij1' : i.val + 1 ≠ j.val := by omega
            have hii : i.val + 1 + 1 ≠ i.val := by omega
            simp [hij', hij1, hij1', hji1, hii]
          · simp [hij', hij1, hji1]
    rw [hN00', pow_zero, one_mul, hNsub] at hN_det
    rw [hsum, hM1_00, hM1_01, hsub0_det, hN_det, det_tridiagFlipHead]
    have h2m1_ne : 2 * m - 1 ≠ 0 := by omega
    simp only [h2m1_ne, ↓reduceIte]
    have h2m2 : 2 * m - 1 - 1 = 2 * m - 2 := by omega
    rw [h2m2]
    ring
  -- Piece 2: M2 = A2.updateCol 0 (c0_noCorner A2)
  let M2 := A2.updateCol 0 (c0_noCorner A2)
  have hM2_det : M2.det = u := by
    have hrow0 : ∀ j : Fin (2 * m + 1), j ≠ last → M2 0 j = 0 := by
      intro j hj
      by_cases hj0 : j = 0
      · subst hj0
        have h0last : (0 : Fin (2 * m + 1)) ≠ last := by simp [last, Fin.ext_iff]; omega
        simp [M2, Matrix.updateCol_apply, c0_noCorner, h0last, A2, Matrix.updateRow_apply,
          r0_corner]
      · simp [M2, Matrix.updateCol_apply, hj0, A2, Matrix.updateRow_apply, r0_corner, hj]
    have h1 := det_eq_single_row_zero' M2 last hrow0
    have hM2_0last : M2 0 last = u := by
      have hlast0 : last ≠ 0 := by simp [last, Fin.ext_iff]; omega
      simp [M2, Matrix.updateCol_apply, hlast0, A2, Matrix.updateRow_apply, r0_corner]
    have hpow : (-1 : ℝ) ^ (last : ℕ) = 1 := by
      simp only [last, pow_mul]; norm_num
    let S2 := M2.submatrix Fin.succ last.succAbove
    have hS2_upper : S2.BlockTriangular id := by
      intro i j hij
      change j < i at hij
      have hsucc : (last.succAbove j).val = j.val := by
        simp only [Fin.succAbove]
        split_ifs with h
        · rfl
        · exfalso; apply h; simp only [Fin.lt_def, Fin.val_castSucc, last, Fin.val_mk]
          have := j.isLt; omega
      by_cases hj0 : j = 0
      · subst hj0
        have h0_eq : last.succAbove 0 = 0 := by ext; exact hsucc
        by_cases hilast : i.succ = last
        · simp [S2, submatrix_apply, h0_eq, M2, Matrix.updateCol_apply, c0_noCorner, hilast]
        · have hi0 : i.val ≠ 0 := by
            have hlt : (0 : Fin (2 * m)).val < i.val := hij
            rw [Fin.val_zero] at hlt; omega
          have hne : i.succ ≠ 0 := Fin.succ_ne_zero i
          have h0val : (0 : Fin (2 * m + 1)).val = 0 := rfl
          have hc1 : i.val + 1 ≠ 0 := by omega
          have hc2 : i.val + 1 + 1 ≠ 0 := by omega
          have hc3 : ¬(0 + 1 = i.val + 1 ∨ i.val + 1 = 2 * m) := by
            have hil' : i.val + 1 ≠ 2 * m := by
              intro h; apply hilast; ext; dsimp [last]; exact h
            omega
          simp only [S2, submatrix_apply, h0_eq, M2, Matrix.updateCol_apply, c0_noCorner, hilast,
            ↓reduceIte, A2, Matrix.updateRow_apply, hne]
          simp only [M, cycleTwoDefectM, of_apply, Fin.ext_iff, Fin.val_succ, Fin.val_zero,
            h0val, hc1, hc2, false_and, true_and, or_false, false_or, hc3, ↓reduceIte]
      · have hj0_val : j.val ≠ 0 := by
          intro h; apply hj0; ext; simpa using h
        have hne0 : last.succAbove j ≠ 0 := by
          intro h; apply hj0_val; have := congrArg Fin.val h; simpa [hsucc] using this
        have hc1 : i.val + 1 ≠ j.val := by omega
        have hc2 : ¬(i.val + 1 + 1 = j.val ∨ (i.val + 1 = 0 ∧ j.val = 2 * m)) := by omega
        have hc3 : ¬(j.val + 1 = i.val + 1 ∨ (j.val = 0 ∧ i.val + 1 = 2 * m)) := by omega
        simp only [S2, submatrix_apply, M2, Matrix.updateCol_apply, hne0, ↓reduceIte, A2,
          Matrix.updateRow_apply, Fin.succ_ne_zero]
        simp only [M, cycleTwoDefectM, of_apply, Fin.ext_iff, Fin.val_succ, hsucc,
          hc1, hc2, hc3, ↓reduceIte]
    have hS2_det : S2.det = 1 := by
      rw [Matrix.det_of_isUpperTriangular hS2_upper]
      have hdiag : ∀ i : Fin (2 * m), S2 i i = -1 := by
        intro i
        have hsucc : (last.succAbove i).val = i.val := by
          simp only [Fin.succAbove]
          split_ifs with h
          · rfl
          · exfalso; apply h; simp only [Fin.lt_def, Fin.val_castSucc, last, Fin.val_mk]
            have := i.isLt; omega
        by_cases hi0 : i = 0
        · subst hi0
          have h0_eq : last.succAbove 0 = 0 := by ext; exact hsucc
          have h1val : (1 : Fin (2 * m + 1)).val = 1 :=
            Nat.mod_eq_of_lt (by omega : (1 : ℕ) < 2 * m + 1)
          have h1last : (1 : Fin (2 * m + 1)) ≠ last :=
            Fin.ne_of_val_ne (by dsimp [last]; rw [Nat.mod_eq_of_lt (by omega : 1 < 2 * m + 1)]; omega)
          have h1_eq : Fin.succ (0 : Fin (2 * m)) = (1 : Fin (2 * m + 1)) := by
            ext; rw [Fin.val_succ, Fin.val_zero, h1val]
          have h0val : (0 : Fin (2 * m + 1)).val = 0 := rfl
          have hc1 : (1 : ℕ) ≠ 0 := by omega
          have hc2 : (1 : ℕ) + 1 ≠ 0 := by omega
          have hc3 : (0 : ℕ) + 1 = 1 ∨ 1 = 2 * m := Or.inl rfl
          simp only [S2, submatrix_apply, h0_eq, M2, Matrix.updateCol_apply, c0_noCorner,
            Fin.succ_ne_zero, h1_eq, h1last, ↓reduceIte, A2, Matrix.updateRow_apply]
          simp only [M, cycleTwoDefectM, of_apply, Fin.ext_iff, Fin.val_zero,
            h0val, h1val, hc1, hc2, false_and, true_and, or_false, false_or, hc3, true_or, ↓reduceIte]
        · have hi0_val : i.val ≠ 0 := by
            intro h; apply hi0; ext; simpa using h
          have hne0 : last.succAbove i ≠ 0 := by
            intro h; apply hi0_val; have := congrArg Fin.val h; simpa [hsucc] using this
          have hc1 : i.val + 1 ≠ i.val := by omega
          have hc2 : ¬(i.val + 1 + 1 = i.val ∨ (i.val + 1 = 0 ∧ i.val = 2 * m)) := by omega
          have hc3 : i.val + 1 = i.val + 1 ∨ (i.val = 0 ∧ i.val + 1 = 2 * m) := Or.inl rfl
          simp only [S2, submatrix_apply, M2, Matrix.updateCol_apply, hne0, ↓reduceIte, A2,
            Matrix.updateRow_apply, Fin.succ_ne_zero]
          simp only [M, cycleTwoDefectM, of_apply, Fin.ext_iff, Fin.val_succ, hsucc,
            hc1, hc2, hc3, true_or, ↓reduceIte]
      simp [hdiag, pow_mul]
    rw [hM2_0last, hpow, one_mul, hS2_det, mul_one] at h1
    exact h1
  -- Piece 3: M3 = A1.updateCol 0 c0_corner
  let M3 := A1.updateCol 0 c0_corner
  have hM3_det : M3.det = -(u ^ (2 * m)) := by
    have hcol0 : ∀ i : Fin (2 * m + 1), i ≠ last → M3 i 0 = 0 := by
      intro i hi
      simp [M3, Matrix.updateCol_apply, c0_corner, hi]
    have h1 := det_eq_single_col_zero' M3 last hcol0
    have hM3_last0 : M3 last 0 = -1 := by
      simp [M3, Matrix.updateCol_apply, c0_corner]
    have hpow : (-1 : ℝ) ^ (last : ℕ) = 1 := by
      simp only [last, pow_mul]; norm_num
    let S3 := M3.submatrix last.succAbove Fin.succ
    have hS3_lower : S3.BlockTriangular OrderDual.toDual := by
      intro i j hij
      change i < j at hij
      have hsucc : (last.succAbove i).val = i.val := by
        simp only [Fin.succAbove]
        split_ifs with h
        · rfl
        · exfalso; apply h; simp only [Fin.lt_def, Fin.val_castSucc, last, Fin.val_mk]
          have := i.isLt; omega
      by_cases hi0 : i = 0
      · subst hi0
        have h0_eq : last.succAbove 0 = 0 := by ext; exact hsucc
        by_cases hjlast : j.succ = last
        · have hlast0 : last ≠ 0 := by
            intro h; have h1 := congrArg Fin.val h; change 2 * m = 0 at h1; omega
          simp [S3, submatrix_apply, h0_eq, M3, Matrix.updateCol_apply, Fin.succ_ne_zero,
            A1, Matrix.updateRow_apply, r0_noCorner, hjlast, hlast0]
        · have hjl' : j.val + 1 ≠ 2 * m := by
            intro h; apply hjlast; ext; dsimp [last]; exact h
          have h0val : (0 : Fin (2 * m + 1)).val = 0 := rfl
          have hjpos : 0 < j.val := by
            have hlt : (0 : Fin (2 * m)).val < j.val := hij
            rw [Fin.val_zero] at hlt; exact hlt
          have hc1 : (0 : ℕ) ≠ j.val + 1 := by omega
          have hc2 : ¬(0 + 1 = j.val + 1 ∨ j.val + 1 = 2 * m) := by omega
          have hc3 : j.val + 1 + 1 ≠ 0 := by omega
          have hc4 : j.val + 1 ≠ 0 := by omega
          simp only [S3, submatrix_apply, h0_eq, M3, Matrix.updateCol_apply, Fin.succ_ne_zero,
            ↓reduceIte, A1, Matrix.updateRow_apply, r0_noCorner, hjlast]
          simp only [M, cycleTwoDefectM, of_apply, Fin.ext_iff, Fin.val_zero, h0val, Fin.val_succ,
            hc1, hc3, hc4, false_and, true_and, or_false, false_or, hc2, ↓reduceIte]
      · have hi0_val : i.val ≠ 0 := by
          intro h; apply hi0; ext; simpa using h
        have hne0 : last.succAbove i ≠ 0 := by
          intro h; apply hi0_val; have := congrArg Fin.val h; simpa [hsucc] using this
        have hc1 : i.val ≠ j.val + 1 := by omega
        have hc2 : ¬(i.val + 1 = j.val + 1 ∨ (i.val = 0 ∧ j.val + 1 = 2 * m)) := by omega
        have hc3 : ¬(j.val + 1 + 1 = i.val ∨ (j.val + 1 = 0 ∧ i.val = 2 * m)) := by omega
        simp only [S3, submatrix_apply, M3, Matrix.updateCol_apply, Fin.succ_ne_zero,
          ↓reduceIte, A1, Matrix.updateRow_apply, hne0]
        simp only [M, cycleTwoDefectM, of_apply, Fin.ext_iff, Fin.val_succ, hsucc,
          hc1, hc2, hc3, ↓reduceIte]
    have hS3_det : S3.det = u ^ (2 * m) := by
      rw [← Matrix.det_transpose, Matrix.det_of_isUpperTriangular (fun i j hij => by
        simp only [transpose_apply]; exact hS3_lower hij)]
      have hdiag : ∀ i : Fin (2 * m), S3ᵀ i i = u := by
        intro i
        simp only [transpose_apply]
        have hsucc : (last.succAbove i).val = i.val := by
          simp only [Fin.succAbove]
          split_ifs with h
          · rfl
          · exfalso; apply h; simp only [Fin.lt_def, Fin.val_castSucc, last, Fin.val_mk]
            have := i.isLt; omega
        by_cases hi0 : i = 0
        · subst hi0
          have h0_eq : last.succAbove 0 = 0 := by ext; exact hsucc
          have h1val : (1 : Fin (2 * m + 1)).val = 1 :=
            Nat.mod_eq_of_lt (by omega : (1 : ℕ) < 2 * m + 1)
          have h1last : (1 : Fin (2 * m + 1)) ≠ last :=
            Fin.ne_of_val_ne (by dsimp [last]; rw [Nat.mod_eq_of_lt (by omega : 1 < 2 * m + 1)]; omega)
          have h1_eq : Fin.succ (0 : Fin (2 * m)) = (1 : Fin (2 * m + 1)) := by
            ext; rw [Fin.val_succ, Fin.val_zero, h1val]
          have h1ne0 : (1 : Fin (2 * m + 1)) ≠ 0 :=
            Fin.ne_of_val_ne (by rw [h1val, Fin.val_zero]; omega)
          have h0val : (0 : Fin (2 * m + 1)).val = 0 := rfl
          have hc1 : (0 : ℕ) ≠ 1 := by omega
          have hc2 : (0 : ℕ) + 1 = 1 ∨ 1 = 2 * m := Or.inl rfl
          simp only [S3, submatrix_apply, h0_eq, M3, Matrix.updateCol_apply, Fin.succ_ne_zero,
            h1_eq, h1ne0, ↓reduceIte, A1, Matrix.updateRow_apply, r0_noCorner, h1last]
          simp only [M, cycleTwoDefectM, of_apply, Fin.ext_iff, Fin.val_zero,
            h0val, h1val, hc1, false_and, true_and, or_false, false_or, hc2, true_or, ↓reduceIte]
        · have hi0_val : i.val ≠ 0 := by
            intro h; apply hi0; ext; simpa using h
          have hne0 : last.succAbove i ≠ 0 := by
            intro h; apply hi0_val; have := congrArg Fin.val h; simpa [hsucc] using this
          have hc1 : i.val ≠ i.val + 1 := by omega
          have hc2 : i.val + 1 = i.val + 1 ∨ (i.val = 0 ∧ i.val + 1 = 2 * m) := Or.inl rfl
          simp only [S3, submatrix_apply, M3, Matrix.updateCol_apply, Fin.succ_ne_zero,
            ↓reduceIte, A1, Matrix.updateRow_apply, hne0]
          simp only [M, cycleTwoDefectM, of_apply, Fin.ext_iff, Fin.val_succ, hsucc,
            hc1, hc2, true_or, ↓reduceIte]
      simp only [hdiag, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hM3_last0, hpow, one_mul, hS3_det] at h1
    linarith
  -- Piece 4: M4 = A2.updateCol 0 c0_corner
  let M4 := A2.updateCol 0 c0_corner
  have hM4_det : M4.det =
      u * (-d * (tridiagDU d u (2 * m - 2)).det + u * (tridiagDU d u (2 * m - 3)).det) := by
    have hrow0 : ∀ j : Fin (2 * m + 1), j ≠ last → M4 0 j = 0 := by
      intro j hj
      by_cases hj0 : j = 0
      · subst hj0
        have h0last : (0 : Fin (2 * m + 1)) ≠ last := by simp [last, Fin.ext_iff]; omega
        simp [M4, Matrix.updateCol_apply, c0_corner, h0last]
      · simp [M4, Matrix.updateCol_apply, hj0, A2, Matrix.updateRow_apply, r0_corner, hj]
    have h1 := det_eq_single_row_zero' M4 last hrow0
    have hM4_0last : M4 0 last = u := by
      have hlast0 : last ≠ 0 := by simp [last, Fin.ext_iff]; omega
      simp [M4, Matrix.updateCol_apply, hlast0, A2, Matrix.updateRow_apply, r0_corner]
    have hpow1 : (-1 : ℝ) ^ (last : ℕ) = 1 := by
      simp only [last, pow_mul]; norm_num
    let S4 := M4.submatrix Fin.succ last.succAbove
    let last' : Fin (2 * m) := ⟨2 * m - 1, by omega⟩
    have hS4_col0 : ∀ i : Fin (2 * m), i ≠ last' → S4 i 0 = 0 := by
      intro i hi
      have h0_eq : last.succAbove 0 = 0 := by
        ext; simp only [Fin.succAbove]; split_ifs with h
        · rfl
        · exfalso; apply h; simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_zero, last]; omega
      have hilast : i.succ ≠ last := by
        intro heq; apply hi; ext
        have := congrArg Fin.val heq
        simp only [Fin.val_succ, last] at this
        simp only [last']; omega
      simp [S4, submatrix_apply, h0_eq, M4, Matrix.updateCol_apply, c0_corner, hilast]
    have h2m : 2 * m = (2 * m - 1) + 1 := by omega
    let S4' : Matrix (Fin ((2 * m - 1) + 1)) (Fin ((2 * m - 1) + 1)) ℝ :=
      S4.reindex (finCongr h2m) (finCongr h2m)
    let last'' : Fin ((2 * m - 1) + 1) := finCongr h2m last'
    have hS4'_col0 : ∀ i : Fin ((2 * m - 1) + 1), i ≠ last'' → S4' i 0 = 0 := by
      intro i hi
      apply hS4_col0 ((finCongr h2m).symm i)
      intro h; apply hi; exact (finCongr h2m).symm_apply_eq.mp (by simpa [last''] using h)
    have h2 : S4.det = (-1 : ℝ) ^ (last'' : ℕ) * S4' last'' 0 *
        (S4'.submatrix last''.succAbove Fin.succ).det := by
      rw [← Matrix.det_reindex_self (finCongr h2m) S4]
      exact det_eq_single_col_zero' S4' last'' hS4'_col0
    have hS4_last0 : S4' last'' 0 = -1 := by
      have h0_eq : last.succAbove 0 = 0 := by
        ext; simp only [Fin.succAbove]; split_ifs with h
        · rfl
        · exfalso; apply h; simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_zero, last]; omega
      have hlast'_eq : last'.succ = last := by ext; simp [last, last']; omega
      have h0eq : (finCongr h2m).symm 0 = (0 : Fin (2 * m)) := by ext; simp
      simp [S4', Matrix.reindex_apply, last'', h0eq, S4, submatrix_apply, h0_eq, hlast'_eq,
        M4, Matrix.updateCol_apply, c0_corner]
    have hpow2 : (-1 : ℝ) ^ (last'' : ℕ) = -1 := by
      have hsplit : (last'' : ℕ) = 2 * (m - 1) + 1 := by simp [last'', last']; omega
      rw [hsplit, pow_add, pow_mul]; norm_num
    have hS4_sub : (S4'.submatrix last''.succAbove Fin.succ).det =
        (tridiagFlipHead d u (2 * m - 2)).det := by
      have h2m1 : 2 * m - 1 = (2 * m - 2) + 1 := by omega
      rw [← Matrix.det_reindex_self (finCongr h2m1)]
      congr 1
      ext i j
      have hsymm : ∀ x : Fin ((2 * m - 1) + 1), ((finCongr h2m).symm x).val = x.val := fun _ => rfl
      have hsymm1 : ∀ x : Fin ((2 * m - 2) + 1), ((finCongr h2m1).symm x).val = x.val := fun _ => rfl
      have hi_lt : ((finCongr h2m).symm (last''.succAbove ((finCongr h2m1).symm i))).val = i.val := by
        rw [hsymm]
        simp only [Fin.succAbove]
        split_ifs with h
        · simp [hsymm1]
        · exfalso; apply h; simp only [Fin.lt_def, Fin.val_castSucc, hsymm1, last'', finCongr_apply,
            Fin.val_cast, last', Fin.val_mk]
          have := i.isLt; omega
      have hj_lt : (last.succAbove ((finCongr h2m).symm ((finCongr h2m1).symm j).succ)).val = j.val + 1 := by
        simp only [Fin.succAbove]
        split_ifs with h
        · simp [hsymm, hsymm1]
        · exfalso; apply h; simp only [Fin.lt_def, Fin.val_castSucc, hsymm, Fin.val_succ, hsymm1,
            last, Fin.val_mk]
          have := j.isLt; omega
      have h0val : (0 : Fin (2 * m + 1)).val = 0 := rfl
      have hj_ne0 : last.succAbove ((finCongr h2m).symm ((finCongr h2m1).symm j).succ) ≠ 0 := by
        intro h; have := congrArg Fin.val h; rw [hj_lt, h0val] at this; omega
      have h1val : (1 : Fin (2 * m + 1)).val = 1 :=
        Nat.mod_eq_of_lt (by omega : (1 : ℕ) < 2 * m + 1)
      have h0val' : (0 : Fin ((2 * m - 2) + 1)).val = 0 := rfl
      have hM4_eq : M4 (((finCongr h2m).symm (last''.succAbove ((finCongr h2m1).symm i))).succ)
          (last.succAbove ((finCongr h2m).symm ((finCongr h2m1).symm j).succ)) =
          M (((finCongr h2m).symm (last''.succAbove ((finCongr h2m1).symm i))).succ)
          (last.succAbove ((finCongr h2m).symm ((finCongr h2m1).symm j).succ)) := by
        simp only [M4, Matrix.updateCol_apply, hj_ne0, ↓reduceIte, A2, Matrix.updateRow_apply,
          Fin.succ_ne_zero]
      dsimp only [S4', S4]
      rw [Matrix.reindex_apply, submatrix_apply, Matrix.reindex_apply, submatrix_apply,
        submatrix_apply, submatrix_apply, hM4_eq]
      simp only [M, cycleTwoDefectM, tridiagFlipHead, of_apply, Fin.ext_iff, Fin.val_succ,
        h0val, h1val, h0val', hi_lt, hj_lt]
      have hi_lt' := i.isLt
      have hj_lt' := j.isLt
      have hni0 : i.val + 1 ≠ 0 := by omega
      have hni2m : i.val + 1 ≠ 2 * m := by omega
      have hnj2m : j.val + 1 ≠ 2 * m := by omega
      have hni1 : (i.val + 1 = 1) = (i.val = 0) := propext ⟨fun h => by omega, fun h => by omega⟩
      simp only [hni0, hni2m, hnj2m, hni1, Nat.add_right_cancel_iff, and_false, or_false,
        false_or]
    rw [hS4_last0, hpow2, hS4_sub, det_tridiagFlipHead] at h2
    have h2m2_ne : 2 * m - 2 ≠ 0 := by omega
    simp only [h2m2_ne, ↓reduceIte] at h2
    have h2m3 : 2 * m - 2 - 1 = 2 * m - 3 := by omega
    rw [h2m3] at h2
    rw [hM4_0last, hpow1, one_mul, h2] at h1
    rw [h1]; ring
  rw [hM1_det, hM2_det, hM3_det, hM4_det]
  ring

/-- **General Odd Two-Defect Cycle Hyperbolicity**: For every `m ≥ 1`, the principal element
`w_cycleTwoDefect (2 * m + 1) _ 0 1` of `C_{2m+1}(+, +, -, ..., -)` has a real eigenvalue
`μ < -1` (in `(-10, -2)`), hence spectral radius `ρ(w) > 1`. -/
theorem oddCycleAdjTwoDefect_has_eigenvalue_lt_neg_one (m : ℕ) (hm : 1 ≤ m) :
    ∃ μ : ℝ, μ < -1 ∧ ∃ v : Fin (2 * m + 1) → ℝ, v ≠ 0 ∧
      (w_cycleTwoDefect (2 * m + 1) (by omega) 0 1).mulVec v = μ • v := by
  by_cases hm1 : m = 1
  · subst hm1
    simpa using c3_twoDefect_has_eigenvalue_lt_neg_one
  · have hm2 : 2 ≤ m := by omega
    refine exists_eigenvalue_lt_neg_one_of_ivt
      (w_cycleTwoDefect (2 * m + 1) (by omega) 0 1) (-10) (-2) (by norm_num) (by norm_num) ?_ ?_
    · unfold w_cycleTwoDefect
      rw [ReflectionSystem.principal_charpoly_eq, howlettU_oddCycleTwoDefect_det m hm,
        howlett_oddTwoDefect_eq m hm (-10)]
      have hM := det_cycleTwoDefectM m hm2 9 10
      have h1 := det_tridiagDU_nine_ten (2 * m - 1)
      have h2 := det_tridiagDU_nine_ten (2 * m - 2)
      have h3 := det_tridiagDU_nine_ten (2 * m - 3)
      have hp1 : (2 * m - 1) + 1 = 2 * m := by omega
      have hp2 : (2 * m - 2) + 1 = 2 * m - 1 := by omega
      have hp3 : (2 * m - 3) + 1 = 2 * m - 2 := by omega
      rw [hp1] at h1; rw [hp2] at h2; rw [hp3] at h3
      have heven : (-1 : ℝ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
      have hodd : (-1 : ℝ) ^ (2 * m - 1) = -1 := by
        have hs : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
        rw [hs, pow_add, pow_mul]; norm_num
      have heven2 : (-1 : ℝ) ^ (2 * m - 2) = 1 := by
        have hs : 2 * m - 2 = 2 * (m - 1) := by omega
        rw [hs, pow_mul]; norm_num
      rw [heven] at h1; rw [hodd] at h2; rw [heven2] at h3
      have hpow10 : (10 : ℝ) ^ (2 * m) = 100 * (10 : ℝ) ^ (2 * m - 2) := by
        have hs : 2 * m = (2 * m - 2) + 2 := by omega
        rw [hs, pow_add]; norm_num; rw [mul_comm]
      have hpow10' : (10 : ℝ) ^ (2 * m - 1) = 10 * (10 : ℝ) ^ (2 * m - 2) := by
        have hs : 2 * m - 1 = (2 * m - 2) + 1 := by omega
        rw [hs, pow_add]; norm_num; rw [mul_comm]
      have hge1 : (100 : ℝ) ≤ (10 : ℝ) ^ (2 * m - 2) := by
        have hexp : 2 ≤ 2 * m - 2 := by omega
        calc (100 : ℝ) = (10 : ℝ) ^ 2 := by norm_num
          _ ≤ (10 : ℝ) ^ (2 * m - 2) := pow_le_pow_right₀ (by norm_num) hexp
      nlinarith
    · unfold w_cycleTwoDefect
      rw [ReflectionSystem.principal_charpoly_eq, howlettU_oddCycleTwoDefect_det m hm,
        howlett_oddTwoDefect_eq m hm (-2)]
      have hM := det_cycleTwoDefectM m hm2 1 2
      have h1 := det_tridiagDU_one_two (2 * m - 1)
      have h2 := det_tridiagDU_one_two (2 * m - 2)
      have h3 := det_tridiagDU_one_two (2 * m - 3)
      have hp1 : (2 * m - 1) + 1 = 2 * m := by omega
      have hp2 : (2 * m - 2) + 1 = 2 * m - 1 := by omega
      have hp3 : (2 * m - 3) + 1 = 2 * m - 2 := by omega
      rw [hp1] at h1; rw [hp2] at h2; rw [hp3] at h3
      have heven : (-1 : ℝ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
      have hodd : (-1 : ℝ) ^ (2 * m - 1) = -1 := by
        have hs : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
        rw [hs, pow_add, pow_mul]; norm_num
      have heven2 : (-1 : ℝ) ^ (2 * m - 2) = 1 := by
        have hs : 2 * m - 2 = 2 * (m - 1) := by omega
        rw [hs, pow_mul]; norm_num
      rw [heven] at h1; rw [hodd] at h2; rw [heven2] at h3
      have hpow2 : (2 : ℝ) ^ (2 * m) = 4 * (2 : ℝ) ^ (2 * m - 2) := by
        have hs : 2 * m = (2 * m - 2) + 2 := by omega
        rw [hs, pow_add]; norm_num; rw [mul_comm]
      have hpow2' : (2 : ℝ) ^ (2 * m - 1) = 2 * (2 : ℝ) ^ (2 * m - 2) := by
        have hs : 2 * m - 1 = (2 * m - 2) + 1 := by omega
        rw [hs, pow_add]; norm_num; rw [mul_comm]
      have hpos2 : (0 : ℝ) < (2 : ℝ) ^ (2 * m - 2) := by positivity
      nlinarith

/-! ### General Infinite Family `C_{2m}(+, +, -, ..., -)` (`m ≥ 2`) -/

private lemma howlettU_evenCycleTwoDefect_det (m : ℕ) (hm : 2 ≤ m) :
    (ReflectionSystem.howlettU
      (cycleTwoDefectSystem (2 * m) (by omega) ⟨0, by omega⟩ ⟨1, by omega⟩).B).det = 1 := by
  have : NeZero (2 * m) := ⟨by omega⟩
  have h0 : (⟨0, by omega⟩ : Fin (2 * m)) = 0 := Fin.ext rfl
  have h1 : (⟨1, by omega⟩ : Fin (2 * m)) = 1 := by
    ext; simp [Nat.mod_eq_of_lt (by omega : 1 < 2 * m)]
  rw [h0, h1]
  rw [ReflectionSystem.howlettU_det]
  have hprod : (∏ i : Fin (2 * m),
      (cycleTwoDefectSystem (2 * m) (by omega) 0 1).B i i / 2) =
      ∏ i : Fin (2 * m), if i = 0 ∨ i = 1 then (1 : ℝ) else (-1 : ℝ) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [cycleTwoDefectSystem, B_cycleTwoDefect, of_apply, ↓reduceIte]
    split_ifs <;> norm_num
  rw [hprod]
  have h01 : (0 : Fin (2 * m)) ≠ 1 := by
    intro h; have := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 1 < 2 * m)] at this
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (0 : Fin (2 * m)))]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ (1 : Fin (2 * m))⟩)]
  simp only [↓reduceIte, true_or, or_true, one_mul]
  have hrest : ∀ i ∈ (Finset.univ.erase (0 : Fin (2 * m))).erase 1,
      (if i = 0 ∨ i = 1 then (1 : ℝ) else (-1 : ℝ)) = -1 := by
    intro i hi
    have hi1 : i ≠ 1 := (Finset.mem_erase.mp hi).1
    have hi0 : i ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    simp [hi0, hi1]
  rw [Finset.prod_congr rfl hrest, Finset.prod_const]
  have hcard : ((Finset.univ.erase (0 : Fin (2 * m))).erase 1).card = 2 * m - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ 1⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
    omega
  rw [hcard]
  have hsplit : 2 * m - 2 = 2 * (m - 1) := by omega
  rw [hsplit, pow_mul]
  norm_num

private def evenCycleTwoDefectM (m : ℕ) (d u : ℝ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  Matrix.of fun i j =>
    if i = j then (if i.val = 0 ∨ i.val = 1 then -d else d)
    else if i.val + 1 = j.val ∨ (i.val = 0 ∧ j.val = 2 * m - 1) then u
    else if j.val + 1 = i.val ∨ (j.val = 0 ∧ i.val = 2 * m - 1) then -1
    else 0

private lemma howlett_evenTwoDefect_eq (m : ℕ) (hm : 2 ≤ m) (x : ℝ) :
    x • ReflectionSystem.howlettU
        (cycleTwoDefectSystem (2 * m) (by omega) ⟨0, by omega⟩ ⟨1, by omega⟩).B +
      (ReflectionSystem.howlettU
        (cycleTwoDefectSystem (2 * m) (by omega) ⟨0, by omega⟩ ⟨1, by omega⟩).B)ᵀ =
      evenCycleTwoDefectM m (-(x + 1)) (-x) := by
  have : NeZero (2 * m) := ⟨by omega⟩
  have h0 : (⟨0, by omega⟩ : Fin (2 * m)) = 0 := Fin.ext rfl
  have h1 : (⟨1, by omega⟩ : Fin (2 * m)) = 1 := by
    ext; simp [Nat.mod_eq_of_lt (by omega : 1 < 2 * m)]
  rw [h0, h1]
  have h1val : (1 : Fin (2 * m)).val = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, transpose_apply, smul_eq_mul,
    ReflectionSystem.howlettU, cycleTwoDefectSystem, B_cycleTwoDefect,
    evenCycleTwoDefectM, of_apply, Fin.ext_iff, Fin.val_zero, h1val]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte, lt_self_iff_false, gt_iff_lt]
    split_ifs <;> ring
  · have hji : j ≠ i := Ne.symm hij
    have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hji' : j.val ≠ i.val := Ne.symm hij'
    simp only [hij', hji', ↓reduceIte]
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have hgt' : ¬(j < i) := not_lt_of_gt hlt
      have hlt' : i < j := hlt
      simp only [hlt', hgt', ↓reduceIte]
      by_cases hadj : i.val + 1 = j.val ∨ (i.val = 0 ∧ j.val = 2 * m - 1)
      · have hadjB : i.val + 1 = j.val ∨ j.val + 1 = i.val ∨ (i.val = 0 ∧ j.val = 2 * m - 1) ∨
            (j.val = 0 ∧ i.val = 2 * m - 1) := by
          rcases hadj with h | h <;> [exact Or.inl h; exact Or.inr (Or.inr (Or.inl h))]
        simp only [hadj, hadjB, ↓reduceIte]
        ring
      · have hadjB : ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val ∨ (i.val = 0 ∧ j.val = 2 * m - 1) ∨
            (j.val = 0 ∧ i.val = 2 * m - 1)) := by
          have : i.val < j.val := hlt; omega
        have hadj2 : ¬(j.val + 1 = i.val ∨ (j.val = 0 ∧ i.val = 2 * m - 1)) := by
          have : i.val < j.val := hlt; omega
        simp only [hadj, hadjB, hadj2, ↓reduceIte]
        ring
    · exact absurd heq hij
    · have hlt' : ¬(i < j) := not_lt_of_gt hgt
      simp only [hlt', hgt, ↓reduceIte]
      by_cases hadj : j.val + 1 = i.val ∨ (j.val = 0 ∧ i.val = 2 * m - 1)
      · have hadjB' : j.val + 1 = i.val ∨ i.val + 1 = j.val ∨ (j.val = 0 ∧ i.val = 2 * m - 1) ∨
            (i.val = 0 ∧ j.val = 2 * m - 1) := by
          rcases hadj with h | h <;> [exact Or.inl h; exact Or.inr (Or.inr (Or.inl h))]
        have hadj1 : ¬(i.val + 1 = j.val ∨ (i.val = 0 ∧ j.val = 2 * m - 1)) := by
          have : j.val < i.val := hgt; omega
        simp only [hadj, hadjB', hadj1, ↓reduceIte]
        ring
      · have hadjB' : ¬(j.val + 1 = i.val ∨ i.val + 1 = j.val ∨ (j.val = 0 ∧ i.val = 2 * m - 1) ∨
            (i.val = 0 ∧ j.val = 2 * m - 1)) := by
          have : j.val < i.val := hgt; omega
        have hadj1 : ¬(i.val + 1 = j.val ∨ (i.val = 0 ∧ j.val = 2 * m - 1)) := by
          have : j.val < i.val := hgt; omega
        simp only [hadj, hadjB', hadj1, ↓reduceIte]
        ring

private lemma det_tridiagDU_charpoly (x : ℝ) (k : ℕ) :
    (tridiagDU (-(x + 1)) (-x) k).det = (-1 : ℝ) ^ k * ∑ j ∈ Finset.range (k + 1), x ^ j := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 =>
      rw [det_tridiagDU_zero]
      simp
    | 1 =>
      rw [det_tridiagDU_one]
      simp [Finset.sum_range_succ]
      ring
    | k + 2 =>
      rw [det_tridiagDU_succ_succ]
      have h1 := ih (k + 1) (by omega)
      have h2 := ih k (by omega)
      rw [h1, h2]
      have hsum : ∑ j ∈ Finset.range (k + 3), x ^ j =
          x ^ (k + 2) + ∑ j ∈ Finset.range (k + 2), x ^ j := by
        rw [Finset.sum_range_succ]; ring
      have hsum' : ∑ j ∈ Finset.range (k + 2), x ^ j =
          x ^ (k + 1) + ∑ j ∈ Finset.range (k + 1), x ^ j := by
        rw [Finset.sum_range_succ]; ring
      rw [hsum, hsum']
      have hp1 : (-1 : ℝ) ^ (k + 1) = -((-1 : ℝ) ^ k) := by rw [pow_succ]; ring
      have hp2 : (-1 : ℝ) ^ (k + 2) = (-1 : ℝ) ^ k := by rw [pow_succ, pow_succ]; ring
      rw [hp1, hp2]
      ring

private lemma det_evenCycleTwoDefectM (m : ℕ) (hm : 2 ≤ m) (d u : ℝ) :
    (evenCycleTwoDefectM m d u).det =
      (d ^ 2 + u) * (tridiagDU d u (2 * m - 2)).det -
        d * u * (tridiagDU d u (2 * m - 3)).det +
        u + u ^ (2 * m - 1) +
        u * (-d * (tridiagDU d u (2 * m - 3)).det + u * (tridiagDU d u (2 * m - 4)).det) := by
  have h2m : 2 * m = (2 * m - 1) + 1 := by omega
  let M : Matrix (Fin ((2 * m - 1) + 1)) (Fin ((2 * m - 1) + 1)) ℝ :=
    (evenCycleTwoDefectM m d u).reindex (finCongr h2m) (finCongr h2m)
  have hM_det : (evenCycleTwoDefectM m d u).det = M.det := by
    rw [← Matrix.det_reindex_self (finCongr h2m) (evenCycleTwoDefectM m d u)]
  rw [hM_det]
  haveI : NeZero (2 * m - 1) := ⟨by omega⟩
  haveI : NeZero (2 * m - 2) := ⟨by omega⟩
  let last : Fin ((2 * m - 1) + 1) := ⟨2 * m - 1, by omega⟩
  have hM_apply : ∀ i j : Fin ((2 * m - 1) + 1), M i j =
      if i.val = j.val then (if i.val = 0 ∨ i.val = 1 then -d else d)
      else if i.val + 1 = j.val ∨ (i.val = 0 ∧ j.val = 2 * m - 1) then u
      else if j.val + 1 = i.val ∨ (j.val = 0 ∧ i.val = 2 * m - 1) then -1
      else 0 := by
    intro i j
    have hsymm : ∀ x : Fin ((2 * m - 1) + 1), ((finCongr h2m).symm x).val = x.val := fun _ => rfl
    simp only [M, Matrix.reindex_apply, Matrix.submatrix_apply, evenCycleTwoDefectM, of_apply,
      hsymm, Fin.ext_iff]
  let r0_noCorner : Fin ((2 * m - 1) + 1) → ℝ := fun j => if j = last then 0 else M 0 j
  let r0_corner : Fin ((2 * m - 1) + 1) → ℝ := fun j => if j = last then u else 0
  have hr0_eq : M 0 = r0_noCorner + r0_corner := by
    ext j; simp only [Pi.add_apply, r0_noCorner, r0_corner]
    split_ifs with h
    · subst h; rw [hM_apply]; have h0last' : (0 : ℕ) ≠ 2 * m - 1 := by omega
      simp [last, h0last']
    · ring
  have hM_upd : M = M.updateRow 0 (r0_noCorner + r0_corner) := by
    rw [← hr0_eq, Matrix.updateRow_eq_self]
  let A1 := M.updateRow 0 r0_noCorner
  let A2 := M.updateRow 0 r0_corner
  have hdet_split1 : M.det = A1.det + A2.det := by
    conv_lhs => rw [hM_upd]
    exact Matrix.det_updateRow_add M 0 r0_noCorner r0_corner
  let c0_noCorner (A : Matrix (Fin ((2 * m - 1) + 1)) (Fin ((2 * m - 1) + 1)) ℝ) :
      Fin ((2 * m - 1) + 1) → ℝ := fun i => if i = last then 0 else A i 0
  let c0_corner : Fin ((2 * m - 1) + 1) → ℝ := fun i => if i = last then -1 else 0
  have hlast0 : last ≠ 0 := Fin.ne_of_val_ne (by dsimp [last]; omega)
  have hM_last0 : M last 0 = -1 := by
    rw [hM_apply]
    have h1 : (2 * m - 1 : ℕ) ≠ 0 := by omega
    have h2 : ¬((2 * m - 1 : ℕ) + 1 = 0 ∨ (2 * m - 1 = 0 ∧ 0 = 2 * m - 1)) := by omega
    have h3 : (0 : ℕ) + 1 = 2 * m - 1 ∨ (0 = 0 ∧ 2 * m - 1 = 2 * m - 1) := Or.inr ⟨rfl, rfl⟩
    simp [last, h1, h2, h3]
  have hA1_last0 : A1 last 0 = -1 := by simp [A1, Matrix.updateRow_apply, hlast0, hM_last0]
  have hA2_last0 : A2 last 0 = -1 := by simp [A2, Matrix.updateRow_apply, hlast0, hM_last0]
  have hdet_splitA1 : A1.det =
      (A1.updateCol 0 (c0_noCorner A1)).det + (A1.updateCol 0 c0_corner).det := by
    have hcol : (fun i => A1 i 0) = c0_noCorner A1 + c0_corner := by
      ext i; simp only [Pi.add_apply, c0_noCorner, c0_corner]
      split_ifs with h
      · subst h; rw [hA1_last0, zero_add]
      · ring
    conv_lhs => rw [← Matrix.updateCol_eq_self A1 0, hcol]
    exact Matrix.det_updateCol_add A1 0 (c0_noCorner A1) c0_corner
  have hdet_splitA2 : A2.det =
      (A2.updateCol 0 (c0_noCorner A2)).det + (A2.updateCol 0 c0_corner).det := by
    have hcol : (fun i => A2 i 0) = c0_noCorner A2 + c0_corner := by
      ext i; simp only [Pi.add_apply, c0_noCorner, c0_corner]
      split_ifs with h
      · subst h; rw [hA2_last0, zero_add]
      · ring
    conv_lhs => rw [← Matrix.updateCol_eq_self A2 0, hcol]
    exact Matrix.det_updateCol_add A2 0 (c0_noCorner A2) c0_corner
  rw [hdet_split1, hdet_splitA1, hdet_splitA2]
  -- Piece 1: M1 = A1.updateCol 0 (c0_noCorner A1)
  let M1 := A1.updateCol 0 (c0_noCorner A1)
  have hM1_det : M1.det =
      (d ^ 2 + u) * (tridiagDU d u (2 * m - 2)).det -
        d * u * (tridiagDU d u (2 * m - 3)).det := by
    rw [Matrix.det_succ_row_zero]
    have h1val : (1 : Fin ((2 * m - 1) + 1)).val = 1 :=
      Nat.mod_eq_of_lt (by omega : (1 : ℕ) < (2 * m - 1) + 1)
    have h01 : (0 : Fin ((2 * m - 1) + 1)) ≠ 1 :=
      Fin.ne_of_val_ne (by rw [Fin.val_zero, h1val]; omega)
    have h0last : (0 : Fin ((2 * m - 1) + 1)) ≠ last := hlast0.symm
    have h1last : (1 : Fin ((2 * m - 1) + 1)) ≠ last :=
      Fin.ne_of_val_ne (by dsimp [last]; simp [Nat.mod_eq_of_lt (by omega : 1 < (2 * m - 1) + 1)]; omega)
    have hsum : ∑ j : Fin ((2 * m - 1) + 1), (-1 : ℝ) ^ (j : ℕ) * M1 0 j *
        (M1.submatrix Fin.succ j.succAbove).det =
        M1 0 0 * (M1.submatrix Fin.succ (0 : Fin ((2 * m - 1) + 1)).succAbove).det -
        M1 0 1 * (M1.submatrix Fin.succ (1 : Fin ((2 * m - 1) + 1)).succAbove).det := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin ((2 * m - 1) + 1)))]
      rw [← Finset.add_sum_erase _ _
        (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ (1 : Fin ((2 * m - 1) + 1))⟩)]
      have hrest : ∑ j ∈ (Finset.univ.erase (0 : Fin ((2 * m - 1) + 1))).erase 1,
          (-1 : ℝ) ^ (j : ℕ) * M1 0 j * (M1.submatrix Fin.succ j.succAbove).det = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hj0 : j ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
        have hj1 : j ≠ 1 := (Finset.mem_erase.mp hj).1
        have hM1_0j : M1 0 j = 0 := by
          by_cases hjlast : j = last
          · simp [M1, Matrix.updateCol_apply, hj0, A1, Matrix.updateRow_apply, r0_noCorner, hjlast, hlast0]
          · have hj0' : (0 : ℕ) ≠ j.val := fun h => hj0 (Fin.ext h.symm)
            have hj1' : (0 : ℕ) + 1 ≠ j.val := by
              intro h; apply hj1; ext; rw [h1val]; exact h.symm
            have hjlast' : j.val ≠ 2 * m - 1 := by
              intro h; apply hjlast; ext; exact h
            simp only [M1, Matrix.updateCol_apply, hj0, ↓reduceIte, A1, Matrix.updateRow_apply,
              r0_noCorner, hjlast]
            rw [hM_apply]
            have h0val : (0 : Fin ((2 * m - 1) + 1)).val = 0 := rfl
            rw [h0val, if_neg hj0', if_neg (by omega), if_neg (by omega)]
        simp [hM1_0j]
      rw [hrest, add_zero]
      simp only [Fin.val_zero, pow_zero, one_mul, h1val, pow_one]
      ring
    have hM1_00 : M1 0 0 = -d := by
      simp only [M1, Matrix.updateCol_apply, ↓reduceIte, c0_noCorner, h0last, A1,
        Matrix.updateRow_apply, r0_noCorner]
      rw [hM_apply]; simp
    have hM1_01 : M1 0 1 = u := by
      simp only [M1, Matrix.updateCol_apply, h01.symm, ↓reduceIte, A1, Matrix.updateRow_apply,
        r0_noCorner, h1last]
      rw [hM_apply]
      have h0val : (0 : Fin ((2 * m - 1) + 1)).val = 0 := rfl
      rw [h0val, h1val, if_neg (by omega), if_pos (Or.inl rfl)]
    have hsub0_det : (M1.submatrix Fin.succ (0 : Fin ((2 * m - 1) + 1)).succAbove).det =
        -d * (tridiagDU d u (2 * m - 2)).det + u * (tridiagDU d u (2 * m - 3)).det := by
      have h2m1 : 2 * m - 1 = (2 * m - 2) + 1 := by omega
      let S0 := (M1.submatrix Fin.succ (0 : Fin ((2 * m - 1) + 1)).succAbove).reindex
        (finCongr h2m1) (finCongr h2m1)
      have hS0_det : (M1.submatrix Fin.succ (0 : Fin ((2 * m - 1) + 1)).succAbove).det = S0.det := by
        rw [← Matrix.det_reindex_self (finCongr h2m1) _]
      rw [hS0_det]
      have hS0_eq : S0 = tridiagFlipHead d u (2 * m - 2) := by
        ext i j
        have hi_val : ((finCongr h2m1).symm i).val = i.val := rfl
        have hj_val : ((finCongr h2m1).symm j).val = j.val := rfl
        have hj0 : ((finCongr h2m1).symm j).succ ≠ 0 := Fin.succ_ne_zero _
        have hi0 : ((finCongr h2m1).symm i).succ ≠ 0 := Fin.succ_ne_zero _
        simp only [S0, Matrix.reindex_apply, submatrix_apply, Fin.succAbove_zero,
          M1, Matrix.updateCol_apply, hj0, ↓reduceIte, A1, Matrix.updateRow_apply, hi0,
          tridiagFlipHead, of_apply]
        rw [hM_apply]
        simp only [Fin.val_succ, hi_val, hj_val]
        have hi_ne0 : i.val + 1 ≠ 0 := by omega
        have hj_ne0 : j.val + 1 ≠ 0 := by omega
        have hc1 : (i.val + 1 = 0 ∨ i.val + 1 = 1) ↔ i.val = 0 := by omega
        have hc2 : (i.val + 1 + 1 = j.val + 1 ∨ (i.val + 1 = 0 ∧ j.val + 1 = 2 * m - 1)) ↔
            i.val + 1 = j.val := by omega
        have hc3 : (j.val + 1 + 1 = i.val + 1 ∨ (j.val + 1 = 0 ∧ i.val + 1 = 2 * m - 1)) ↔
            j.val + 1 = i.val := by omega
        have hc4 : (i.val + 1 = j.val + 1) ↔ i = j := by
          simp [Fin.ext_iff]
        simp only [hc1, hc2, hc3, hc4, Fin.val_zero]
        by_cases hij : i = j
        · subst hij; by_cases hi0' : i = 0 <;> simp [hi0', Fin.ext_iff]
        · have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
          simp [hij, hij']
      rw [hS0_eq, det_tridiagFlipHead]
      have h2m2_ne : 2 * m - 2 ≠ 0 := by omega
      simp only [h2m2_ne, ↓reduceIte]
      have h2m3 : 2 * m - 2 - 1 = 2 * m - 3 := by omega
      rw [h2m3]
    let N := M1.submatrix Fin.succ (1 : Fin ((2 * m - 1) + 1)).succAbove
    have hN_col0 : ∀ i : Fin (2 * m - 1), i ≠ 0 → N i 0 = 0 := by
      intro i hi
      have hsucc0 : Fin.succAbove (1 : Fin ((2 * m - 1) + 1)) (0 : Fin (2 * m - 1)) = 0 := by
        ext; simp [Fin.succAbove]
      have hi_ne0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
      by_cases hil : i.succ = last
      · simp [N, submatrix_apply, hsucc0, M1, Matrix.updateCol_apply, c0_noCorner, hil]
      · have hil' : i.val + 1 ≠ 2 * m - 1 := by
          intro h; apply hil; ext; exact h
        simp only [N, submatrix_apply, hsucc0, M1, Matrix.updateCol_apply, c0_noCorner, hil,
          ↓reduceIte, A1, Matrix.updateRow_apply, Fin.succ_ne_zero]
        rw [hM_apply]
        have h0val : (0 : Fin ((2 * m - 1) + 1)).val = 0 := rfl
        rw [Fin.val_succ, h0val, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hN00 : N 0 0 = -1 := by
      have hsucc0 : Fin.succAbove (1 : Fin ((2 * m - 1) + 1)) (0 : Fin (2 * m - 1)) = 0 := by
        ext; simp [Fin.succAbove]
      have h1_eq : Fin.succ (0 : Fin (2 * m - 1)) = (1 : Fin ((2 * m - 1) + 1)) := by
        ext; rw [Fin.val_succ, Fin.val_zero, h1val]
      simp only [N, submatrix_apply, hsucc0, M1, Matrix.updateCol_apply, c0_noCorner,
        h01.symm, Fin.succ_ne_zero, h1_eq, h1last, ↓reduceIte, A1, Matrix.updateRow_apply]
      rw [hM_apply]
      have h0val : (0 : Fin ((2 * m - 1) + 1)).val = 0 := rfl
      rw [h0val, h1val, if_neg (by omega), if_neg (by omega), if_pos (Or.inl rfl)]
    have h2m1 : 2 * m - 1 = (2 * m - 2) + 1 := by omega
    let N' := N.reindex (finCongr h2m1) (finCongr h2m1)
    have hN'_col0 : ∀ i : Fin ((2 * m - 2) + 1), i ≠ 0 → N' i 0 = 0 := by
      intro i hi
      have h0eq : (finCongr h2m1).symm 0 = (0 : Fin (2 * m - 1)) := by ext; rfl
      simp only [N', Matrix.reindex_apply, h0eq]
      apply hN_col0 ((finCongr h2m1).symm i)
      intro h; apply hi; ext; simpa using congrArg Fin.val h
    have hN_det : N.det = (-1 : ℝ) ^ (0 : ℕ) * N' 0 0 *
        (N'.submatrix (0 : Fin ((2 * m - 2) + 1)).succAbove Fin.succ).det := by
      rw [← Matrix.det_reindex_self (finCongr h2m1) N]
      exact det_eq_single_col_zero' N' 0 hN'_col0
    have hN00' : N' 0 0 = -1 := by
      have h0eq : (finCongr h2m1).symm 0 = (0 : Fin (2 * m - 1)) := by ext; rfl
      simpa [N', Matrix.reindex_apply, h0eq] using hN00
    have hNsub : (N'.submatrix (0 : Fin ((2 * m - 2) + 1)).succAbove Fin.succ).det =
        (tridiagDU d u (2 * m - 2)).det := by
      congr 1; ext i j
      have hsymm : ∀ x : Fin ((2 * m - 2) + 1), ((finCongr h2m1).symm x).val = x.val := fun _ => rfl
      have hsucc : (Fin.succAbove (1 : Fin ((2 * m - 1) + 1))
          ((finCongr h2m1).symm j.succ)).val = j.val + 2 := by
        simp only [Fin.succAbove]
        split_ifs with h
        · exfalso; simp only [Fin.lt_def, Fin.val_castSucc, hsymm, Fin.val_succ, h1val] at h
          omega
        · simp [hsymm]
      have hne0 : Fin.succAbove (1 : Fin ((2 * m - 1) + 1)) ((finCongr h2m1).symm j.succ) ≠ 0 := by
        intro h; have := congrArg Fin.val h; rw [hsucc, Fin.val_zero] at this; omega
      simp only [N', Matrix.reindex_apply, submatrix_apply, Fin.succAbove_zero,
        N, Matrix.updateCol_apply, hne0, ↓reduceIte, M1, A1, Matrix.updateRow_apply,
        Fin.succ_ne_zero, tridiagDU, of_apply]
      rw [hM_apply]
      simp only [Fin.val_succ, hsymm, hsucc]
      have hi2 : ¬(i.val + 2 = 0 ∨ i.val + 2 = 1) := by omega
      have h1' : ¬(i.val + 2 = 0 ∧ j.val + 2 = 2 * m - 1) := by omega
      have h2' : ¬(j.val + 2 = 0 ∧ i.val + 2 = 2 * m - 1) := by omega
      simp only [hi2, h1', h2', or_false, Nat.add_right_cancel_iff]
      by_cases hij : i = j
      · subst hij; simp
      · have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
        by_cases hij1 : i.val + 1 = j.val
        · have hji1 : j.val + 1 ≠ i.val := by omega
          simp [hij, hij', hij1, hji1]
        · by_cases hji1 : j.val + 1 = i.val
          · have hii : i.val + 1 + 1 ≠ i.val := by omega
            simp [hij, hij', hij1, hji1, hii]
          · simp [hij, hij', hij1, hji1]
    rw [hN00', pow_zero, one_mul, hNsub] at hN_det
    rw [hsum, hM1_00, hM1_01, hsub0_det, hN_det]
    ring
  -- Piece 2: M2 = A2.updateCol 0 (c0_noCorner A2)
  let M2 := A2.updateCol 0 (c0_noCorner A2)
  have hM2_det : M2.det = u := by
    have hrow0 : ∀ j : Fin ((2 * m - 1) + 1), j ≠ last → M2 0 j = 0 := by
      intro j hj
      by_cases hj0 : j = 0
      · subst hj0; simp [M2, c0_noCorner, hlast0.symm, A2, Matrix.updateRow_apply, r0_corner]
      · simp [M2, hj0, A2, Matrix.updateRow_apply, r0_corner, hj]
    have h1 := det_eq_single_row_zero' M2 last hrow0
    have hM2_0last : M2 0 last = u := by
      simp [M2, hlast0, A2, Matrix.updateRow_apply, r0_corner]
    have hpow : (-1 : ℝ) ^ (last : ℕ) = -1 := by
      have hs : (last : ℕ) = 2 * (m - 1) + 1 := by dsimp [last]; omega
      rw [hs, pow_add, pow_mul]; norm_num
    let S2 := M2.submatrix Fin.succ last.succAbove
    have hS2_upper : S2.BlockTriangular id := by
      intro i j hij
      change j < i at hij
      have hsucc : (last.succAbove j).val = j.val := by
        simp only [Fin.succAbove]
        split_ifs with h
        · rfl
        · exfalso; apply h; simp only [Fin.lt_def, Fin.val_castSucc, last]
          have := j.isLt; omega
      by_cases hj0 : j = 0
      · subst hj0
        have h0_eq : last.succAbove 0 = 0 := by ext; exact hsucc
        by_cases hilast : i.succ = last
        · simp [S2, submatrix_apply, h0_eq, M2, c0_noCorner, hilast]
        · have hi0 : i.val ≠ 0 := by
            have hlt : (0 : Fin (2 * m - 1)).val < i.val := hij
            rw [Fin.val_zero] at hlt; omega
          have hil' : i.val + 1 ≠ 2 * m - 1 := by
            intro h; apply hilast; ext; exact h
          simp only [S2, submatrix_apply, h0_eq, M2, Matrix.updateCol_apply, c0_noCorner, hilast,
            ↓reduceIte, A2, Matrix.updateRow_apply, Fin.succ_ne_zero]
          rw [hM_apply]
          have hc1 : i.val + 1 ≠ 0 := by omega
          have hc2 : ¬(i.val + 1 + 1 = 0 ∨ (i.val + 1 = 0 ∧ (0 : ℕ) = 2 * m - 1)) := by omega
          have hc3 : ¬((0 : ℕ) + 1 = i.val + 1 ∨ ((0 : ℕ) = 0 ∧ i.val + 1 = 2 * m - 1)) := by omega
          simp [Fin.val_succ, Fin.val_zero, hc1, hc2, hc3, hi0, hil']
      · have hj0_val : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
        have hne0 : last.succAbove j ≠ 0 := by
          intro h; apply hj0_val; have := congrArg Fin.val h; simpa [hsucc] using this
        simp only [S2, submatrix_apply, M2, Matrix.updateCol_apply, hne0, ↓reduceIte, A2,
          Matrix.updateRow_apply, Fin.succ_ne_zero]
        rw [hM_apply]
        have hj0_val : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
        have hc1 : i.val + 1 ≠ j.val := by omega
        have hc2 : ¬(i.val + 1 + 1 = j.val ∨ (i.val + 1 = 0 ∧ j.val = 2 * m - 1)) := by omega
        have hc3 : ¬(j.val + 1 = i.val + 1 ∨ (j.val = 0 ∧ i.val + 1 = 2 * m - 1)) := by omega
        simp only [Fin.val_succ, hsucc, hc1, ↓reduceIte, hc2, hc3]
    have hS2_det : S2.det = -1 := by
      rw [Matrix.det_of_isUpperTriangular hS2_upper]
      have hdiag : ∀ i : Fin (2 * m - 1), S2 i i = -1 := by
        intro i
        have hsucc : (last.succAbove i).val = i.val := by
          simp only [Fin.succAbove]
          split_ifs with h
          · rfl
          · exfalso; apply h; simp only [Fin.lt_def, Fin.val_castSucc, last]
            have := i.isLt; omega
        by_cases hi0 : i = 0
        · subst hi0
          have h0_eq : last.succAbove 0 = 0 := by ext; exact hsucc
          have h1val : (1 : Fin ((2 * m - 1) + 1)).val = 1 := by
            rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
          have h1last : (1 : Fin ((2 * m - 1) + 1)) ≠ last := by
            intro h; have := congrArg Fin.val h; dsimp [last] at this
            rw [Nat.mod_eq_of_lt (by omega : 1 < (2 * m - 1) + 1)] at this; omega
          have h1_eq : Fin.succ (0 : Fin (2 * m - 1)) = (1 : Fin ((2 * m - 1) + 1)) := by
            ext; rw [Fin.val_succ, Fin.val_zero, h1val]
          simp only [S2, submatrix_apply, h0_eq, M2, Matrix.updateCol_apply, c0_noCorner,
            Fin.succ_ne_zero, h1_eq, h1last, ↓reduceIte, A2, Matrix.updateRow_apply]
          rw [hM_apply]
          have h0val : (0 : Fin ((2 * m - 1) + 1)).val = 0 := rfl
          rw [h1val, h0val]; norm_num
        · have hi0_val : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
          have hne0 : last.succAbove i ≠ 0 := by
            intro h; apply hi0_val; have := congrArg Fin.val h; simpa [hsucc] using this
          simp only [S2, submatrix_apply, M2, Matrix.updateCol_apply, hne0, ↓reduceIte, A2,
            Matrix.updateRow_apply, Fin.succ_ne_zero]
          rw [hM_apply]
          rw [Fin.val_succ, hsucc, if_neg (by omega), if_neg (by omega), if_pos (Or.inl rfl)]
      simp only [hdiag, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hs : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
      rw [hs, pow_add, pow_mul]; norm_num
    rw [hM2_0last, hpow, hS2_det] at h1
    linarith
  -- Piece 3: M3 = A1.updateCol 0 c0_corner
  let M3 := A1.updateCol 0 c0_corner
  have hM3_det : M3.det = u ^ (2 * m - 1) := by
    have hcol0 : ∀ i : Fin ((2 * m - 1) + 1), i ≠ last → M3 i 0 = 0 := by
      intro i hi; simp [M3, c0_corner, hi]
    have h1 := det_eq_single_col_zero' M3 last hcol0
    have hM3_last0 : M3 last 0 = -1 := by simp [M3, c0_corner]
    have hpow : (-1 : ℝ) ^ (last : ℕ) = -1 := by
      have hs : (last : ℕ) = 2 * (m - 1) + 1 := by dsimp [last]; omega
      rw [hs, pow_add, pow_mul]; norm_num
    let S3 := M3.submatrix last.succAbove Fin.succ
    have hS3_lower : S3.BlockTriangular OrderDual.toDual := by
      intro i j hij
      change i < j at hij
      have hsucc : (last.succAbove i).val = i.val := by
        simp only [Fin.succAbove]
        split_ifs with h
        · rfl
        · exfalso; apply h; simp only [Fin.lt_def, Fin.val_castSucc, last]
          have := i.isLt; omega
      by_cases hi0 : i = 0
      · subst hi0
        have h0_eq : last.succAbove 0 = 0 := by ext; exact hsucc
        by_cases hjlast : j.succ = last
        · simp [S3, submatrix_apply, h0_eq, M3, Matrix.updateCol_apply, Fin.succ_ne_zero,
            A1, Matrix.updateRow_apply, r0_noCorner, hjlast, hlast0]
        · have hjpos : 0 < j.val := by
            have hlt : (0 : Fin (2 * m - 1)).val < j.val := hij
            rw [Fin.val_zero] at hlt; exact hlt
          have hjl' : j.val + 1 ≠ 2 * m - 1 := by
            intro h; apply hjlast; ext; exact h
          simp only [S3, submatrix_apply, h0_eq, M3, Matrix.updateCol_apply, Fin.succ_ne_zero,
            ↓reduceIte, A1, Matrix.updateRow_apply, r0_noCorner, hjlast]
          rw [hM_apply]
          have h0val : (0 : Fin ((2 * m - 1) + 1)).val = 0 := rfl
          rw [h0val, Fin.val_succ, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      · have hi0_val : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
        have hne0 : last.succAbove i ≠ 0 := by
          intro h; apply hi0_val; have := congrArg Fin.val h; simpa [hsucc] using this
        simp only [S3, submatrix_apply, M3, Matrix.updateCol_apply, Fin.succ_ne_zero,
          ↓reduceIte, A1, Matrix.updateRow_apply, hne0]
        rw [hM_apply]
        rw [hsucc, Fin.val_succ, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hS3_det : S3.det = u ^ (2 * m - 1) := by
      rw [← Matrix.det_transpose, Matrix.det_of_isUpperTriangular (fun i j hij => by
        simp only [transpose_apply]; exact hS3_lower hij)]
      have hdiag : ∀ i : Fin (2 * m - 1), S3ᵀ i i = u := by
        intro i
        simp only [transpose_apply]
        have hsucc : (last.succAbove i).val = i.val := by
          simp only [Fin.succAbove]
          split_ifs with h
          · rfl
          · exfalso; apply h; simp only [Fin.lt_def, Fin.val_castSucc, last]
            have := i.isLt; omega
        by_cases hi0 : i = 0
        · subst hi0
          have h0_eq : last.succAbove 0 = 0 := by ext; exact hsucc
          have h1val : (1 : Fin ((2 * m - 1) + 1)).val = 1 := by
            rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
          have h1last : (1 : Fin ((2 * m - 1) + 1)) ≠ last := by
            intro h; have := congrArg Fin.val h; dsimp [last] at this
            rw [Nat.mod_eq_of_lt (by omega : 1 < (2 * m - 1) + 1)] at this; omega
          have h1_eq : Fin.succ (0 : Fin (2 * m - 1)) = (1 : Fin ((2 * m - 1) + 1)) := by
            ext; rw [Fin.val_succ, Fin.val_zero, h1val]
          simp only [S3, submatrix_apply, h0_eq, M3, Matrix.updateCol_apply, Fin.succ_ne_zero,
            h1_eq, ↓reduceIte, A1, Matrix.updateRow_apply, r0_noCorner, h1last]
          rw [hM_apply]
          have h0val : (0 : Fin ((2 * m - 1) + 1)).val = 0 := rfl
          rw [h0val, h1val]; norm_num
        · have hi0_val : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
          have hne0 : last.succAbove i ≠ 0 := by
            intro h; apply hi0_val; have := congrArg Fin.val h; simpa [hsucc] using this
          simp only [S3, submatrix_apply, M3, Matrix.updateCol_apply, Fin.succ_ne_zero,
            ↓reduceIte, A1, Matrix.updateRow_apply, hne0]
          rw [hM_apply]
          rw [hsucc, Fin.val_succ, if_neg (by omega), if_pos (Or.inl rfl)]
      simp only [hdiag, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hM3_last0, hpow, hS3_det] at h1
    rw [h1]; ring
  -- Piece 4: M4 = A2.updateCol 0 c0_corner
  let M4 := A2.updateCol 0 c0_corner
  have hM4_det : M4.det =
      u * (-d * (tridiagDU d u (2 * m - 3)).det + u * (tridiagDU d u (2 * m - 4)).det) := by
    have hrow0 : ∀ j : Fin ((2 * m - 1) + 1), j ≠ last → M4 0 j = 0 := by
      intro j hj
      by_cases hj0 : j = 0
      · subst hj0; simp [M4, c0_corner, hlast0.symm]
      · simp [M4, hj0, A2, Matrix.updateRow_apply, r0_corner, hj]
    have h1 := det_eq_single_row_zero' M4 last hrow0
    have hM4_0last : M4 0 last = u := by
      simp [M4, hlast0, A2, Matrix.updateRow_apply, r0_corner]
    have hpow1 : (-1 : ℝ) ^ (last : ℕ) = -1 := by
      have hs : (last : ℕ) = 2 * (m - 1) + 1 := by dsimp [last]; omega
      rw [hs, pow_add, pow_mul]; norm_num
    let S4 := M4.submatrix Fin.succ last.succAbove
    have h2m1 : 2 * m - 1 = (2 * m - 2) + 1 := by omega
    let S4' := S4.reindex (finCongr h2m1) (finCongr h2m1)
    have hS4_det : S4.det = S4'.det := by
      rw [← Matrix.det_reindex_self (finCongr h2m1) S4]
    let last' : Fin (2 * m - 1) := ⟨2 * m - 2, by omega⟩
    let last'' : Fin ((2 * m - 2) + 1) := finCongr h2m1 last'
    have hcol0 : ∀ i : Fin ((2 * m - 2) + 1), i ≠ last'' → S4' i 0 = 0 := by
      intro i hi
      have h0_eq : last.succAbove ((finCongr h2m1).symm 0) = 0 := by
        simp only [Fin.succAbove]
        split_ifs with h
        · rfl
        · exfalso; apply h; simp only [Fin.lt_def, Fin.val_castSucc, finCongr_apply, Fin.val_cast,
            Fin.val_zero, last]; omega
      have h0_eq' : last.succAbove 0 = 0 := by simpa using h0_eq
      have hilast : ((finCongr h2m1).symm i).succ ≠ last := by
        intro h; apply hi; ext
        have hval := congrArg Fin.val h
        have hsymm_val : ((finCongr h2m1).symm i).val = i.val := rfl
        rw [Fin.val_succ, hsymm_val] at hval
        dsimp [last] at hval
        change i.val = 2 * m - 2
        omega
      simpa [S4', Matrix.reindex_apply, S4, submatrix_apply, h0_eq', M4, c0_corner,
        finCongr] using hilast
    have h2 := det_eq_single_col_zero' S4' last'' hcol0
    rw [hS4_det] at h1
    have hS4_last0 : S4' last'' 0 = -1 := by
      have h0_eq : last.succAbove ((finCongr h2m1).symm 0) = 0 := by
        simp only [Fin.succAbove]
        split_ifs with h
        · rfl
        · exfalso; apply h; simp only [Fin.lt_def, Fin.val_castSucc, finCongr_apply, Fin.val_cast,
            Fin.val_zero, last]; omega
      have hlast'_eq : last'.succ = last := by
        ext; dsimp [last', last]; omega
      simp only [S4', Matrix.reindex_apply, last'', Equiv.symm_apply_apply, S4, submatrix_apply,
        h0_eq, hlast'_eq, M4, Matrix.updateCol_apply, ↓reduceIte, c0_corner]
    have hpow2 : (-1 : ℝ) ^ (last'' : ℕ) = 1 := by
      have hval : (last'' : ℕ) = 2 * m - 2 := rfl
      have hs : 2 * m - 2 = 2 * (m - 1) := by omega
      rw [hval, hs, pow_mul]; norm_num
    have h2m2 : 2 * m - 2 = (2 * m - 3) + 1 := by omega
    have hS4_sub : (S4'.submatrix last''.succAbove Fin.succ).reindex
        (finCongr h2m2) (finCongr h2m2) = tridiagFlipHead d u (2 * m - 3) := by
      have hlast''_val : last''.val = 2 * m - 2 := rfl
      ext i j
      have hsymm : ∀ x : Fin (2 * m - 2), ((finCongr h2m1).symm (last''.succAbove x)).val = x.val := by
        intro x
        simp only [finCongr_apply, Fin.val_cast, Fin.succAbove]
        split_ifs with h
        · rfl
        · exfalso; apply h; simp only [Fin.lt_def, Fin.val_castSucc, hlast''_val]
          have := x.isLt; omega
      have hsucc1 : (last.succAbove ((finCongr h2m1).symm ((finCongr h2m2).symm j).succ)).val =
          j.val + 1 := by
        simp only [Fin.succAbove]
        split_ifs with h
        · rfl
        · exfalso; apply h; simp only [Fin.lt_def, Fin.val_castSucc, finCongr_apply, Fin.val_cast,
            Fin.val_succ, last]
          have := j.isLt; omega
      have hne0 : last.succAbove ((finCongr h2m1).symm ((finCongr h2m2).symm j).succ) ≠ 0 := by
        intro h; have := congrArg Fin.val h; rw [hsucc1, Fin.val_zero] at this; omega
      have hi_ne0 : ((finCongr h2m1).symm (last''.succAbove ((finCongr h2m2).symm i))).succ ≠ 0 :=
        Fin.succ_ne_zero _
      simp only [Matrix.reindex_apply, S4', submatrix_apply, S4, M4, Matrix.updateCol_apply,
        hne0, ↓reduceIte, A2, Matrix.updateRow_apply, hi_ne0, tridiagFlipHead, of_apply]
      rw [hM_apply]
      have hsymm2 : ∀ x : Fin ((2 * m - 3) + 1), ((finCongr h2m2).symm x).val = x.val :=
        fun _ => rfl
      simp only [Fin.val_succ, hsymm, hsucc1, hsymm2]
      by_cases hij : i = j
      · subst hij; by_cases hi0' : i = 0
        · subst hi0'; simp
        · have hi0_val : i.val ≠ 0 := fun h => hi0' (Fin.ext h)
          simp only [hi0', ↓reduceIte]
          rw [ite_eq_right (fun h => by omega)]
      · have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
        simp only [hij, ↓reduceIte]
        rw [ite_eq_right (fun h => by omega)]
        by_cases hij1 : i.val + 1 = j.val
        · rw [ite_eq_left hij1, ite_eq_left (Or.inl (by omega))]
        · rw [ite_eq_right hij1]
          by_cases hji1 : j.val + 1 = i.val
          · rw [ite_eq_left hji1, ite_eq_right (fun h => by omega),
              ite_eq_left (Or.inl (by omega))]
          · rw [ite_eq_right hji1, ite_eq_right (fun h => by omega),
              ite_eq_right (fun h => by omega)]
    have hS4_sub_det : (S4'.submatrix last''.succAbove Fin.succ).det =
        (tridiagFlipHead d u (2 * m - 3)).det := by
      rw [← Matrix.det_reindex_self (finCongr h2m2) (S4'.submatrix last''.succAbove Fin.succ),
        hS4_sub]
    rw [hS4_last0, hpow2, hS4_sub_det, det_tridiagFlipHead] at h2
    by_cases hm2 : m = 2
    · subst hm2
      simp at h2 ⊢
      rw [hM4_0last, hpow1, h2] at h1
      rw [h1]; ring
    · have h2m3_ne : 2 * m - 3 ≠ 0 := by omega
      simp only [h2m3_ne, ↓reduceIte] at h2
      have h2m4 : 2 * m - 3 - 1 = 2 * m - 4 := by omega
      rw [h2m4] at h2
      rw [hM4_0last, hpow1, h2] at h1
      rw [h1]; ring
  rw [hM1_det, hM2_det, hM3_det, hM4_det]
  ring

/-- Characteristic polynomial of the adjacent two-defect even cycle `C_{2m}(+, +, -, ..., -)`
for `m ≥ 2`:
`det(x I - w) = x^{2m} + 3 x^{2m-1} + 8 ∑_{k=2}^{2m-2} x^k + 3 x + 1`. -/
theorem evenCycleAdjTwoDefect_charpoly (m : ℕ) (hm : 2 ≤ m) (x : ℝ) :
    (x • (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) -
      w_cycleTwoDefect (2 * m) (by omega) ⟨0, by omega⟩ ⟨1, by omega⟩).det =
      x ^ (2 * m) + 3 * x ^ (2 * m - 1) +
        8 * (∑ k ∈ Finset.Ico 2 (2 * m - 1), x ^ k) + 3 * x + 1 := by
  have : NeZero (2 * m) := ⟨by omega⟩
  unfold w_cycleTwoDefect
  rw [ReflectionSystem.principal_charpoly_eq, howlettU_evenCycleTwoDefect_det m hm, inv_one,
    one_mul, howlett_evenTwoDefect_eq m hm x, det_evenCycleTwoDefectM m hm (-(x + 1)) (-x)]
  rw [det_tridiagDU_charpoly, det_tridiagDU_charpoly, det_tridiagDU_charpoly]
  have heven2 : (-1 : ℝ) ^ (2 * m - 2) = 1 := by
    have hs : 2 * m - 2 = 2 * (m - 1) := by omega
    rw [hs, pow_mul]; norm_num
  have hodd3 : (-1 : ℝ) ^ (2 * m - 3) = -1 := by
    have hs : 2 * m - 3 = 2 * (m - 2) + 1 := by omega
    rw [hs, pow_add, pow_mul]; norm_num
  have heven4 : (-1 : ℝ) ^ (2 * m - 4) = 1 := by
    have hs : 2 * m - 4 = 2 * (m - 2) := by omega
    rw [hs, pow_mul]; norm_num
  have hodd1 : (-x) ^ (2 * m - 1) = -(x ^ (2 * m - 1)) := by
    rw [neg_pow]
    have hs : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
    rw [hs, pow_add, pow_mul]; norm_num
  rw [heven2, hodd3, heven4, hodd1]
  have hp1 : 2 * m - 2 + 1 = 2 * m - 1 := by omega
  have hp2 : 2 * m - 3 + 1 = 2 * m - 2 := by omega
  have hp3 : 2 * m - 4 + 1 = 2 * m - 3 := by omega
  rw [hp1, hp2, hp3]
  have hIco : ∑ k ∈ Finset.Ico 2 (2 * m - 1), x ^ k =
      x ^ 2 * ∑ k ∈ Finset.range (2 * m - 3), x ^ k := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    have hlen : 2 * m - 1 - 2 = 2 * m - 3 := by omega
    rw [hlen]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_add]
  by_cases hx1 : x = 1
  · subst hx1
    rw [hIco]
    simp only [one_pow, mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hcast1 : ((2 * m - 1 : ℕ) : ℝ) = 2 * (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hcast2 : ((2 * m - 2 : ℕ) : ℝ) = 2 * (m : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hcast3 : ((2 * m - 3 : ℕ) : ℝ) = 2 * (m : ℝ) - 3 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hcast1, hcast2, hcast3]
    ring
  · apply mul_left_cancel₀ (sub_ne_zero.mpr hx1)
    have hgs1 := geom_sum_mul x (2 * m - 1)
    have hgs2 := geom_sum_mul x (2 * m - 2)
    have hgs3 := geom_sum_mul x (2 * m - 3)
    have hp_2m : x ^ (2 * m) = x ^ 3 * x ^ (2 * m - 3) := by
      rw [← pow_add]; congr 1; omega
    have hp_2m1 : x ^ (2 * m - 1) = x ^ 2 * x ^ (2 * m - 3) := by
      rw [← pow_add]; congr 1; omega
    have hp_2m2 : x ^ (2 * m - 2) = x * x ^ (2 * m - 3) := by
      have hs : 2 * m - 2 = (2 * m - 3) + 1 := by omega
      conv_lhs => rw [hs, pow_succ']
    rw [hIco, hp_2m]
    rw [hp_2m1] at hgs1 ⊢
    rw [hp_2m2] at hgs2
    linear_combination
      ((-(x + 1)) ^ 2 + -x) * hgs1 +
        (2 * x * (x + 1)) * hgs2 +
        (x ^ 2 - 8 * x ^ 2) * hgs3

private lemma exists_root_norm_gt_one_of_eval_lt {n : ℕ} (p : Polynomial ℂ) (hp : p.Monic)
    (hn : p.natDegree = n) (z : ℂ) (hz1 : 1 < ‖z‖) (hlt : ‖p.eval z‖ < (‖z‖ - 1) ^ n) :
    ∃ r : ℂ, p.IsRoot r ∧ 1 < ‖r‖ := by
  by_contra hno
  push Not at hno
  have hsplits : p.Splits := IsAlgClosed.splits p
  have hcard : p.roots.card = n := by
    rw [← hn]
    exact hsplits.natDegree_eq_card_roots.symm
  have hprod : p = (p.roots.map (fun r => Polynomial.X - Polynomial.C r)).prod :=
    hsplits.eq_prod_roots_of_monic hp
  have heval : p.eval z = (p.roots.map (fun r => z - r)).prod := by
    conv_lhs => rw [hprod]
    simp [Polynomial.eval_multiset_prod, Multiset.map_map]
  have hnorm : ‖p.eval z‖ = (p.roots.map (fun r => ‖z - r‖)).prod := by
    rw [heval, Multiset.norm_prod, Multiset.map_map]
    rfl
  have hmult : ∀ s : Multiset ℝ, (∀ y ∈ s, ‖z‖ - 1 ≤ y) → (‖z‖ - 1) ^ s.card ≤ s.prod := by
    intro s hs
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons a s ih =>
      simp only [Multiset.card_cons, pow_succ', Multiset.prod_cons]
      have ha : ‖z‖ - 1 ≤ a := hs a (Multiset.mem_cons_self a s)
      have hs' : ∀ y ∈ s, ‖z‖ - 1 ≤ y := fun y hy => hs y (Multiset.mem_cons_of_mem hy)
      exact mul_le_mul ha (ih hs') (pow_nonneg (by linarith) _) (by linarith)
  have hle := hmult (p.roots.map (fun r => ‖z - r‖)) (fun y hy => by
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hy
    have hroot : p.IsRoot a := Polynomial.isRoot_of_mem_roots ha
    have ha1 : ‖a‖ ≤ 1 := hno a hroot
    have hrev := norm_sub_norm_le z a
    linarith)
  rw [Multiset.card_map, hcard, ← hnorm] at hle
  linarith

/-- **General Even Two-Defect Cycle Hyperbolicity**: For every `m ≥ 2`, the characteristic
polynomial of `w_cycleTwoDefect (2 * m) _ 0 1` on `C_{2m}(+, +, -, ..., -)` has a complex
root `z` with `‖z‖ > 1`, hence spectral radius `ρ(w) > 1`. -/
theorem evenCycleAdjTwoDefect_complex_eigenvalue_norm_gt_one (m : ℕ) (hm : 2 ≤ m) :
    ∃ z : ℂ,
      Polynomial.IsRoot
        ((w_cycleTwoDefect (2 * m) (by omega) ⟨0, by omega⟩ ⟨1, by omega⟩).charpoly.map
          (Complex.ofRealHom)) z ∧
      1 < ‖z‖ := by
  have : NeZero (2 * m) := ⟨by omega⟩
  have h0 : (⟨0, by omega⟩ : Fin (2 * m)) = 0 := Fin.ext rfl
  have h1 : (⟨1, by omega⟩ : Fin (2 * m)) = 1 := by
    ext; simp [Nat.mod_eq_of_lt (by omega : 1 < 2 * m)]
  rw [h0, h1]
  let restR : Polynomial ℝ :=
    Polynomial.C 3 * Polynomial.X ^ (2 * m - 1) +
      Polynomial.C 8 * ∑ k ∈ Finset.Ico 2 (2 * m - 1), Polynomial.X ^ k +
      Polynomial.C 3 * Polynomial.X + Polynomial.C 1
  let pR : Polynomial ℝ := Polynomial.X ^ (2 * m) + restR
  have hcharR : (w_cycleTwoDefect (2 * m) (by omega) 0 1).charpoly = pR := by
    apply Polynomial.funext
    intro x
    rw [Matrix.eval_charpoly]
    have hsc : Matrix.scalar (Fin (2 * m)) x = x • (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) := by
      ext i j; simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
    have hch := evenCycleAdjTwoDefect_charpoly m hm x
    rw [h0, h1] at hch
    rw [hsc, hch]
    simp [pR, restR, Polynomial.eval_finsetSum]
    ring
  let rest : Polynomial ℂ :=
    Polynomial.C 3 * Polynomial.X ^ (2 * m - 1) +
      Polynomial.C 8 * ∑ k ∈ Finset.Ico 2 (2 * m - 1), Polynomial.X ^ k +
      Polynomial.C 3 * Polynomial.X + Polynomial.C 1
  let p : Polynomial ℂ := Polynomial.X ^ (2 * m) + rest
  have hchar : (w_cycleTwoDefect (2 * m) (by omega) 0 1).charpoly.map Complex.ofRealHom = p := by
    rw [hcharR]
    simp [pR, restR, p, rest, Polynomial.map_sum]
  rw [hchar]
  have hlt_rest : rest.natDegree < 2 * m := by
    have h1 : (Polynomial.C (3 : ℂ) * Polynomial.X ^ (2 * m - 1)).natDegree ≤ 2 * m - 1 := by
      calc (Polynomial.C (3 : ℂ) * Polynomial.X ^ (2 * m - 1)).natDegree
          ≤ (Polynomial.C (3 : ℂ)).natDegree + (Polynomial.X ^ (2 * m - 1)).natDegree :=
            Polynomial.natDegree_mul_le
        _ ≤ 0 + (2 * m - 1) := by simp
        _ = 2 * m - 1 := zero_add _
    have h2 : (Polynomial.C (8 : ℂ) * ∑ k ∈ Finset.Ico 2 (2 * m - 1), Polynomial.X ^ k).natDegree ≤
        2 * m - 2 := by
      calc (Polynomial.C (8 : ℂ) * ∑ k ∈ Finset.Ico 2 (2 * m - 1), Polynomial.X ^ k).natDegree
          ≤ (Polynomial.C (8 : ℂ)).natDegree +
            (∑ k ∈ Finset.Ico 2 (2 * m - 1), Polynomial.X ^ k).natDegree := Polynomial.natDegree_mul_le
        _ ≤ 0 + (2 * m - 2) := by
          simp only [Polynomial.natDegree_C, zero_add]
          refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
          rw [Finset.mem_Ico] at hk
          simp only [Polynomial.natDegree_X_pow]
          omega
        _ = 2 * m - 2 := zero_add _
    have h3 : (Polynomial.C (3 : ℂ) * Polynomial.X).natDegree ≤ 1 := by
      calc (Polynomial.C (3 : ℂ) * Polynomial.X).natDegree
          ≤ (Polynomial.C (3 : ℂ)).natDegree + Polynomial.X.natDegree := Polynomial.natDegree_mul_le
        _ ≤ 0 + 1 := by simp
        _ = 1 := zero_add _
    have h4 : (Polynomial.C (1 : ℂ)).natDegree ≤ 0 := by simp
    have h12 := (Polynomial.natDegree_add_le _ _).trans (max_le h1 (h2.trans (by omega)))
    have h123 := (Polynomial.natDegree_add_le _ _).trans (max_le h12 (h3.trans (by omega)))
    have h1234 := (Polynomial.natDegree_add_le _ _).trans (max_le h123 (h4.trans (by omega)))
    dsimp [rest]
    omega
  have hdeg_lt : rest.degree < (Polynomial.X ^ (2 * m) : Polynomial ℂ).degree := by
    rw [Polynomial.degree_X_pow]
    by_cases h0 : rest = 0
    · rw [h0, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
    · rw [Polynomial.degree_eq_natDegree h0]
      exact WithBot.coe_lt_coe.mpr hlt_rest
  have hp_monic : p.Monic := (Polynomial.monic_X_pow (2 * m)).add_of_left hdeg_lt
  have hp_deg : p.natDegree = 2 * m := by
    dsimp [p]
    rw [Polynomial.natDegree_add_eq_left_of_degree_lt hdeg_lt, Polynomial.natDegree_X_pow]
  by_cases hm2 : m = 2
  · subst hm2
    obtain ⟨z, hz, hgt⟩ := c4_adjTwoDefect_complex_eigenvalue_norm_gt_one
    refine ⟨z, ?_, hgt⟩
    have hIco2 : ∑ k ∈ Finset.Ico 2 3, z ^ k = z ^ 2 := by
      rw [Finset.sum_Ico_eq_sum_range]; simp
    change p.eval z = 0
    have hpz : p.eval z = z ^ 4 + 3 * z ^ 3 + 8 * z ^ 2 + 3 * z + 1 := by
      simp [p, rest]; ring
    rw [hpz]
    simpa [Polynomial.IsRoot] using hz
  · by_cases hm3 : m = 3
    · subst hm3
      let z : ℂ := -1 + (19 / 10 : ℝ) * Complex.I
      have hnorm_sq : ‖z‖ ^ 2 = 461 / 100 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp [z]; norm_num
      have hz_gt : (214 / 100 : ℝ) < ‖z‖ :=
        lt_of_pow_lt_pow_left₀ 2 (norm_nonneg z) (by rw [hnorm_sq]; norm_num)
      have hz1 : 1 < ‖z‖ := by linarith
      have hIco3 : ∑ k ∈ Finset.Ico 2 5, z ^ k = z ^ 4 + z ^ 3 + z ^ 2 := by
        rw [Finset.sum_Ico_eq_sum_range]; simp [Finset.sum_range_succ]; ring
      have hpeval : p.eval z =
          (((((z + 3) * z + 8) * z + 8) * z + 8) * z + 3) * z + 1 := by
        simp [p, rest, Polynomial.eval_finsetSum, hIco3]; ring
      have hs1 : z + 3 = (2 : ℝ) + ((19 / 10 : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> (simp [z]; try norm_num)
      have hs2 : (z + 3) * z + 8 = ((239 / 100 : ℝ) : ℂ) + ((19 / 10 : ℝ) : ℂ) * Complex.I := by
        rw [hs1]; apply Complex.ext <;> simp [z] <;> norm_num
      have hs3 : ((z + 3) * z + 8) * z + 8 = (2 : ℝ) + ((2641 / 1000 : ℝ) : ℂ) * Complex.I := by
        rw [hs2]; apply Complex.ext <;> simp [z] <;> norm_num
      have hs4 : (((z + 3) * z + 8) * z + 8) * z + 8 =
          ((9821 / 10000 : ℝ) : ℂ) + ((1159 / 1000 : ℝ) : ℂ) * Complex.I := by
        rw [hs3]; apply Complex.ext <;> simp [z] <;> norm_num
      have hs5 : ((((z + 3) * z + 8) * z + 8) * z + 8) * z + 3 =
          ((-921 / 5000 : ℝ) : ℂ) + ((70699 / 100000 : ℝ) : ℂ) * Complex.I := by
        rw [hs4]; apply Complex.ext <;> simp [z] <;> norm_num
      have hs6 : (((((z + 3) * z + 8) * z + 8) * z + 8) * z + 3) * z + 1 =
          ((-159081 / 1000000 : ℝ) : ℂ) + ((-105697 / 100000 : ℝ) : ℂ) * Complex.I := by
        rw [hs5]; apply Complex.ext <;> simp [z] <;> norm_num
      have hpenorm_sq : ‖p.eval z‖ ^ 2 < (5 / 4 : ℝ) ^ 2 := by
        rw [hpeval, hs6, Complex.sq_norm, Complex.normSq_apply]
        simp; norm_num
      have hpenorm : ‖p.eval z‖ < 5 / 4 :=
        lt_of_pow_lt_pow_left₀ 2 (by norm_num) hpenorm_sq
      have hrhs : (5 / 4 : ℝ) < (‖z‖ - 1) ^ 6 := by
        have h1 : (114 / 100 : ℝ) < ‖z‖ - 1 := by linarith
        calc (5 / 4 : ℝ) < (114 / 100 : ℝ) ^ 6 := by norm_num
          _ < (‖z‖ - 1) ^ 6 := by gcongr
      exact exists_root_norm_gt_one_of_eval_lt p hp_monic hp_deg z hz1 (lt_trans hpenorm hrhs)
    · by_cases hm4 : m = 4
      · subst hm4
        let z : ℂ := (-197 / 200 : ℝ) + (403 / 200 : ℝ) * Complex.I
        have hnorm_sq : ‖z‖ ^ 2 = 100609 / 20000 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp [z]; norm_num
        have hz_gt : (224 / 100 : ℝ) < ‖z‖ :=
          lt_of_pow_lt_pow_left₀ 2 (norm_nonneg z) (by rw [hnorm_sq]; norm_num)
        have hz1 : 1 < ‖z‖ := by linarith
        have hIco4 : ∑ k ∈ Finset.Ico 2 7, z ^ k =
            z ^ 6 + z ^ 5 + z ^ 4 + z ^ 3 + z ^ 2 := by
          rw [Finset.sum_Ico_eq_sum_range]; simp [Finset.sum_range_succ]; ring
        have hpeval : p.eval z =
            (((((((z + 3) * z + 8) * z + 8) * z + 8) * z + 8) * z + 8) * z + 3) * z + 1 := by
          simp [p, rest, Polynomial.eval_finsetSum, hIco4]; ring
        have hs1 : z + 3 = ((403 / 200 : ℝ) : ℂ) + ((403 / 200 : ℝ) : ℂ) * Complex.I := by
          apply Complex.ext <;> (simp [z]; try norm_num)
        have hs2 : (z + 3) * z + 8 = ((391 / 200 : ℝ) : ℂ) + ((41509 / 20000 : ℝ) : ℂ) * Complex.I := by
          rw [hs1]; apply Complex.ext <;> simp [z] <;> norm_num
        have hs3 : ((z + 3) * z + 8) * z + 8 =
            ((7569173 / 4000000 : ℝ) : ℂ) + ((7580027 / 4000000 : ℝ) : ℂ) * Complex.I := by
          rw [hs2]; apply Complex.ext <;> simp [z] <;> norm_num
        have hs4 : (((z + 3) * z + 8) * z + 8) * z + 8 =
            ((927061019 / 400000000 : ℝ) : ℂ) + ((7785557 / 4000000 : ℝ) : ℂ) * Complex.I := by
          rw [hs3]; apply Complex.ext <;> simp [z] <;> norm_num
        have hs5 : ((((z + 3) * z + 8) * z + 8) * z + 8) * z + 8 =
            ((143611032157 / 80000000000 : ℝ) : ℂ) +
              ((220230117757 / 80000000000 : ℝ) : ℂ) * Complex.I := by
          rw [hs4]; apply Complex.ext <;> simp [z] <;> norm_num
        have hs6 : (((((z + 3) * z + 8) * z + 8) * z + 8) * z + 8) * z + 8 =
            ((10955889209 / 16000000000 : ℝ) : ℂ) +
              ((7244956380571 / 8000000000000 : ℝ) : ℂ) * Complex.I := by
          rw [hs5]; apply Complex.ext <;> simp [z] <;> norm_num
        have hs7 : ((((((z + 3) * z + 8) * z + 8) * z + 8) * z + 8) * z + 8) * z + 3 =
            ((801127491543387 / 1600000000000000 : ℝ) : ℂ) +
              ((780355268641013 / 1600000000000000 : ℝ) : ℂ) * Complex.I := by
          rw [hs6]; apply Complex.ext <;> simp [z] <;> norm_num
        have hs8 : (((((((z + 3) * z + 8) * z + 8) * z + 8) * z + 8) * z + 8) * z + 3) * z + 1 =
            ((-76152644548187739 / 160000000000000000 : ℝ) : ℂ) +
              ((845621955848527 / 1600000000000000 : ℝ) : ℂ) * Complex.I := by
          rw [hs7]; apply Complex.ext <;> simp [z] <;> norm_num
        have hpenorm_sq : ‖p.eval z‖ ^ 2 < (1 : ℝ) ^ 2 := by
          rw [hpeval, hs8, Complex.sq_norm, Complex.normSq_apply]
          simp; norm_num
        have hpenorm : ‖p.eval z‖ < 1 :=
          lt_of_pow_lt_pow_left₀ 2 (by norm_num) hpenorm_sq
        have hrhs : (1 : ℝ) < (‖z‖ - 1) ^ 8 := by
          have h1 : (124 / 100 : ℝ) < ‖z‖ - 1 := by linarith
          calc (1 : ℝ) < (124 / 100 : ℝ) ^ 8 := by norm_num
            _ < (‖z‖ - 1) ^ 8 := by gcongr
        exact exists_root_norm_gt_one_of_eval_lt p hp_monic hp_deg z hz1 (lt_trans hpenorm hrhs)
      · have hm5 : 5 ≤ m := by omega
        let z : ℂ := -1 + 2 * Complex.I
        have hz_quad : z ^ 2 + 2 * z + 5 = 0 := by
          simp [z]; ring_nf; simp [Complex.I_sq]
        have hmul : (z - 1) * p.eval z = -(5 * z ^ 2 + 2 * z + 1) := by
          have hsum : ∑ k ∈ Finset.Ico 2 (2 * m - 1), z ^ k =
              z ^ 2 * ∑ k ∈ Finset.range (2 * m - 3), z ^ k := by
            rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
            have hlen : 2 * m - 1 - 2 = 2 * m - 3 := by omega
            rw [hlen]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [pow_add]
          have hgs := geom_sum_mul z (2 * m - 3)
          have hpe : p.eval z = z ^ (2 * m) + 3 * z ^ (2 * m - 1) +
              8 * (z ^ 2 * ∑ k ∈ Finset.range (2 * m - 3), z ^ k) + 3 * z + 1 := by
            simp [p, rest, Polynomial.eval_finsetSum, hsum]; ring
          have hz2m : z ^ (2 * m) = z * z ^ (2 * m - 1) := by
            have hs : 2 * m = (2 * m - 1) + 1 := by omega
            conv_lhs => rw [hs, pow_succ']
          have hz2m_top : z ^ 2 * z ^ (2 * m - 3) = z ^ (2 * m - 1) := by
            rw [← pow_add]; congr 1; omega
          have hcalc : (z - 1) * p.eval z =
              z ^ (2 * m - 1) * (z ^ 2 + 2 * z + 5) - (5 * z ^ 2 + 2 * z + 1) := by
            rw [hpe, hz2m, ← hz2m_top]
            linear_combination 8 * z ^ 2 * hgs
          rw [hcalc, hz_quad, mul_zero, zero_sub]
        have hzm1_norm : ‖z - 1‖ ^ 2 = 8 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp [z]; norm_num
        have hrhs_norm : ‖-(5 * z ^ 2 + 2 * z + 1)‖ ^ 2 = 512 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp [z]; ring_nf; norm_num
        have hpenorm_sq : ‖p.eval z‖ ^ 2 = 64 := by
          have hmul_norm := congrArg (fun w : ℂ => ‖w‖ ^ 2) hmul
          rw [norm_mul, mul_pow, hzm1_norm, hrhs_norm] at hmul_norm
          linarith
        have hpenorm : ‖p.eval z‖ = 8 := by
          nlinarith [norm_nonneg (p.eval z)]
        have hz_norm_sq : ‖z‖ ^ 2 = 5 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp [z]; norm_num
        have hz_gt : (2236 / 1000 : ℝ) < ‖z‖ :=
          lt_of_pow_lt_pow_left₀ 2 (norm_nonneg z) (by rw [hz_norm_sq]; norm_num)
        have hz1 : 1 < ‖z‖ := by linarith
        have hrhs : 8 < (‖z‖ - 1) ^ (2 * m) := by
          have h1 : (1236 / 1000 : ℝ) < ‖z‖ - 1 := by linarith
          have h2 : (10 : ℕ) ≤ 2 * m := by omega
          calc (8 : ℝ) < (1236 / 1000 : ℝ) ^ 10 := by norm_num
            _ ≤ (1236 / 1000 : ℝ) ^ (2 * m) := pow_le_pow_right₀ (by norm_num) h2
            _ < (‖z‖ - 1) ^ (2 * m) := by gcongr
        rw [← hpenorm] at hrhs
        exact exists_root_norm_gt_one_of_eval_lt p hp_monic hp_deg z hz1 hrhs

end TwoDefectCycle

end MixedSignCoxeter
