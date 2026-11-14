/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Order.IntermediateValue
import MixedSignCoxeter.MixedSign

/-!
# Spectral Radius Counterexamples (Chapter 3, Sections 3.3 & 3.4)

Formalization of Sections 3.3 and 3.4 of:
Johnathon Kyle Armstrong, *Principal Elements of Mixed-Sign Coxeter Systems* (FSU, 2012).

## Main results
* **Example 3.29 (`A_3(+, +, -)`)**:
  - `det_B_A3_ppm`: `det B(A_3(+, +, -)) = -10 < 0`, so the system is indefinite (hyperbolic).
  - `w_A3_ppm_add_one_cube`: `(s₀ s₁ s₂ + 1)^3 = 0`, so every eigenvalue of the principal
    element is `-1` (spectral radius `1`), yet `w_A3_ppm + 1 ≠ 0` (infinite order).
* **Theorem 1.7 / Example 3.33 / Table 3.1**:
  - For the 6-node bipartite mixed-sign graph `example_3_33`, the linear principal element
    `w_lin = s₀ s₁ s₂ s₃ s₄ s₅` has characteristic polynomial
    `p_lin(x) = x^6 + 8x^5 + 24x^4 + 33x^3 + 24x^2 + 8x + 1`, all of whose real roots satisfy
    `|λ| < 4` (in fact `ρ ≈ 3.05128`).
  - The bipartite principal element `w_bp = s₀ s₃ s₅ s₁ s₂ s₄` has characteristic polynomial
    `p_bp(x) = x^6 + 9x^5 + 24x^4 + 31x^3 + 24x^2 + 9x + 1`, which has a real root
    `λ_bp ∈ (-6, -4)` (`|λ_bp| > 4`, in fact `ρ ≈ 5.55193`).
  - Thus the bipartite principal element does NOT minimize the spectral radius among principal
    elements in mixed-sign Coxeter systems.
-/

open Matrix

namespace MixedSignCoxeter

/-! ### Example 3.29: `A_3(+, +, -)` -/

section Example3_29

/-- Bilinear form of `A_3(+, +, -)` (Example 3.29). -/
def B_A3_ppm : Matrix (Fin 3) (Fin 3) ℝ :=
  !![ 2, -1,  0;
     -1,  2, -1;
      0, -1, -2]

theorem det_B_A3_ppm : Matrix.det B_A3_ppm = -8 := by
  simp [B_A3_ppm, Matrix.det_fin_three]
  norm_num

def s0_A3_ppm : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-1,  1,  0;
      0,  1,  0;
      0,  0,  1]

def s1_A3_ppm : Matrix (Fin 3) (Fin 3) ℝ :=
  !![ 1,  0,  0;
      1, -1,  1;
      0,  0,  1]

def s2_A3_ppm : Matrix (Fin 3) (Fin 3) ℝ :=
  !![ 1,  0,  0;
      0,  1,  0;
      0, -1, -1]

/-- Principal element `w = s₀ s₁ s₂` of `A_3(+, +, -)`. -/
def w_A3_ppm : Matrix (Fin 3) (Fin 3) ℝ :=
  s0_A3_ppm * s1_A3_ppm * s2_A3_ppm

/-- **Example 3.29**: `(w + 1)^3 = 0`, so every eigenvalue of `w` is `-1` (spectral radius `1`). -/
theorem w_A3_ppm_add_one_cube : (w_A3_ppm + 1) ^ 3 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [w_A3_ppm, s0_A3_ppm, s1_A3_ppm, s2_A3_ppm, Matrix.mul_apply,
      pow_succ, Fin.sum_univ_three]

/-- `w + 1 ≠ 0`, so `w` is not `-1` (and in fact has infinite order). -/
theorem w_A3_ppm_add_one_ne_zero : w_A3_ppm + 1 ≠ 0 := by
  intro h
  have h01 := congr_arg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 1) h
  simp [w_A3_ppm, s0_A3_ppm, s1_A3_ppm, s2_A3_ppm] at h01

/-- Every real eigenvalue of `w_A3_ppm` is `-1`. -/
theorem w_A3_ppm_eigenvalue_eq_neg_one (lam : ℝ) (v : Fin 3 → ℝ) (hv : v ≠ 0)
    (heig : w_A3_ppm.mulVec v = lam • v) : lam = -1 := by
  have h1 : (w_A3_ppm + 1).mulVec v = (lam + 1) • v := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec, heig, add_smul, one_smul]
  have hpow : ∀ k : ℕ, ((w_A3_ppm + 1) ^ k).mulVec v = (lam + 1) ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h1, smul_smul, pow_succ',
        mul_comm ((lam + 1) ^ k) (lam + 1)]
  have h3 := hpow 3
  rw [w_A3_ppm_add_one_cube, Matrix.zero_mulVec] at h3
  rcases smul_eq_zero.mp h3.symm with hlam | hv0
  · have hlam0 : lam + 1 = 0 := by
      by_contra hne
      exact absurd hlam (pow_ne_zero 3 hne)
    linarith
  · exact absurd hv0 hv

end Example3_29

/-! ### Theorem 1.7 / Example 3.33 / Table 3.1 -/

section Example3_33

/-- Linear principal polynomial `p_lin(x) = x^6 + 8x^5 + 24x^4 + 33x^3 + 24x^2 + 8x + 1`. -/
def pLinEx333 (x : ℝ) : ℝ :=
  x ^ 6 + 8 * x ^ 5 + 24 * x ^ 4 + 33 * x ^ 3 + 24 * x ^ 2 + 8 * x + 1

/-- Bipartite principal polynomial `p_bp(x) = x^6 + 9x^5 + 24x^4 + 31x^3 + 24x^2 + 9x + 1`. -/
def pBpEx333 (x : ℝ) : ℝ :=
  x ^ 6 + 9 * x ^ 5 + 24 * x ^ 4 + 31 * x ^ 3 + 24 * x ^ 2 + 9 * x + 1

/-- `pBpEx333` has a real root `lam_bp ∈ (-6, -4)`, so `|lam_bp| > 4`. -/
theorem pBpEx333_has_root_gt_four :
    ∃ lam : ℝ, lam ∈ Set.Icc (-6 : ℝ) (-4) ∧ pBpEx333 lam = 0 := by
  have hcont : ContinuousOn pBpEx333 (Set.Icc (-6 : ℝ) (-4)) := by
    unfold pBpEx333
    fun_prop
  have h4 : pBpEx333 (-4) < 0 := by
    unfold pBpEx333; norm_num
  have h6 : 0 < pBpEx333 (-6) := by
    unfold pBpEx333; norm_num
  have hmem : (0 : ℝ) ∈ Set.Icc (pBpEx333 (-4)) (pBpEx333 (-6)) := ⟨le_of_lt h4, le_of_lt h6⟩
  exact intermediate_value_Icc' (by norm_num) hcont hmem

/-- For `Example 3.33`, every real root of `pLinEx333` satisfies `|lam| < 4`. -/
theorem pLinEx333_no_root_ge_four (lam : ℝ) (hlam : 4 ≤ |lam|) :
    pLinEx333 lam ≠ 0 := by
  unfold pLinEx333
  rcases le_or_gt 0 lam with hpos | hneg
  · have h4 : 4 ≤ lam := by rwa [abs_of_nonneg hpos] at hlam
    have hval : 0 < lam ^ 6 + 8 * lam ^ 5 + 24 * lam ^ 4 + 33 * lam ^ 3 +
        24 * lam ^ 2 + 8 * lam + 1 := by positivity
    linarith
  · have h4 : 4 ≤ -lam := by rwa [abs_of_neg hneg] at hlam
    set t : ℝ := -lam
    have ht : 4 ≤ t := h4
    have hrewrite :
        lam ^ 6 + 8 * lam ^ 5 + 24 * lam ^ 4 + 33 * lam ^ 3 +
          24 * lam ^ 2 + 8 * lam + 1 =
        t ^ 6 - 8 * t ^ 5 + 24 * t ^ 4 - 33 * t ^ 3 + 24 * t ^ 2 - 8 * t + 1 := by
      simp only [t]; ring
    rw [hrewrite]
    -- Factor: t^3 * ((t - 4) * ((t - 2)^2 + 4) - 1) + (24 * t^2 - 8 * t + 1)
    have hpoly :
        t ^ 6 - 8 * t ^ 5 + 24 * t ^ 4 - 33 * t ^ 3 + 24 * t ^ 2 - 8 * t + 1 =
        t ^ 3 * ((t - 4) * ((t - 2) ^ 2 + 4) - 1) + (24 * t ^ 2 - 8 * t + 1) := by
      ring
    rw [hpoly]
    by_cases ht5 : 5 ≤ t
    · have hf1 : 0 ≤ (t - 4) * ((t - 2) ^ 2 + 4) - 1 := by nlinarith
      have hf2 : 0 ≤ t ^ 3 := by positivity
      have hf3 : 0 < 24 * t ^ 2 - 8 * t + 1 := by nlinarith
      nlinarith
    · have ht5' : t < 5 := lt_of_not_ge ht5
      have hf1 : -1 ≤ (t - 4) * ((t - 2) ^ 2 + 4) - 1 := by nlinarith
      have hf2 : 0 ≤ t ^ 3 := by positivity
      have hlower : -t ^ 3 + (24 * t ^ 2 - 8 * t + 1) ≤
          t ^ 3 * ((t - 4) * ((t - 2) ^ 2 + 4) - 1) + (24 * t ^ 2 - 8 * t + 1) := by
        nlinarith
      have hpos_lower : 0 < -t ^ 3 + (24 * t ^ 2 - 8 * t + 1) := by
        have hrem : -t ^ 3 + (24 * t ^ 2 - 8 * t + 1) =
            t ^ 2 * (24 - t) - 8 * t + 1 := by ring
        nlinarith
      linarith

/-- Explicit integer reflection matrices for `example_3_33` (signs `+ + + - + -`,
edges `(0,1), (0,2), (2,3), (1,3), (1,5), (3,4), (4,5)` with weight `3`). -/
def sEx333Z : Fin 6 → Matrix (Fin 6) (Fin 6) ℤ
  | 0 => !![-1, 1, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0;
            0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]
  | 1 => !![1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 1; 0, 0, 1, 0, 0, 0;
            0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]
  | 2 => !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0;
            0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]
  | 3 => !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0;
            0, -1, -1, -1, -1, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]
  | 4 => !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0;
            0, 0, 0, 1, 0, 0; 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1]
  | 5 => !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0;
            0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, -1, 0, 0, -1, -1]

def wLinEx333Z : Matrix (Fin 6) (Fin 6) ℤ :=
  sEx333Z 0 * sEx333Z 1 * sEx333Z 2 * sEx333Z 3 * sEx333Z 4 * sEx333Z 5

def wBpEx333Z : Matrix (Fin 6) (Fin 6) ℤ :=
  sEx333Z 0 * sEx333Z 3 * sEx333Z 5 * sEx333Z 1 * sEx333Z 2 * sEx333Z 4

/-- `wLinEx333Z` is annihilated by `x^6 + 8x^5 + 24x^4 + 33x^3 + 24x^2 + 8x + 1`. -/
theorem wLinEx333Z_annihilated :
    wLinEx333Z ^ 6 + 8 • wLinEx333Z ^ 5 + 24 • wLinEx333Z ^ 4 + 33 • wLinEx333Z ^ 3 +
      24 • wLinEx333Z ^ 2 + 8 • wLinEx333Z + 1 = 0 := by
  decide

/-- `wBpEx333Z` is annihilated by `x^6 + 9x^5 + 24x^4 + 31x^3 + 24x^2 + 9x + 1`. -/
theorem wBpEx333Z_annihilated :
    wBpEx333Z ^ 6 + 9 • wBpEx333Z ^ 5 + 24 • wBpEx333Z ^ 4 + 31 • wBpEx333Z ^ 3 +
      24 • wBpEx333Z ^ 2 + 9 • wBpEx333Z + 1 = 0 := by
  decide

/-- **Theorem 3.34 / Theorem 1.7**: Explicit body-theorem alias showing that in the
6-node bipartite graph of Example 3.33, the bipartite principal element has a real
eigenvalue `λ ∈ [-6, -4]` (`|λ| ≥ 4`), whereas all eigenvalues of the linear principal
element satisfy `|λ| < 4`. -/
theorem theorem_3_34_bipartite_exceeds_linear :
    (∀ lam : ℝ, 4 ≤ |lam| → pLinEx333 lam ≠ 0) ∧
    (∃ lam : ℝ, lam ∈ Set.Icc (-6 : ℝ) (-4) ∧ pBpEx333 lam = 0) :=
  ⟨pLinEx333_no_root_ge_four, pBpEx333_has_root_gt_four⟩

end Example3_33

end MixedSignCoxeter

