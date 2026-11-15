/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Complex.Basic
import MixedSignCoxeter.SpectralRadius

/-!
# Spectral classification and interlacing for bipartite Coxeter elements
(Theorems 3.27 and 3.28)

Formalization of Theorems 3.27 and 3.28 of:
Johnathon Kyle Armstrong, *Principal Elements of Mixed-Sign Coxeter Systems* (FSU, 2012),
which the dissertation quotes from [A'C76], [MS05], [McM02].

## Setting

Order the nodes of a bipartite classical Coxeter graph as `N₁ = Fin p` followed by
`N₂ = Fin q`. With the normalisation `B(e_i, e_i) = 2` of Chapter 3 the bilinear form is
`B = [[2, -A], [-Aᵀ, 2]]` (`bipForm A`), where `A : Matrix (Fin p) (Fin q) ℝ` holds the edge
entries `2 cos(π / m_{ij})` (the results below hold for every real `A`). The product of the
pairwise-commuting reflections in `N₁` is `s₊ = [[-1, A], [0, 1]]`, the product of those in
`N₂` is `s₋ = [[1, 0], [Aᵀ, -1]]`, and the bipartite Coxeter element is `w = s₊ s₋`
(`bipCoxeter A`). By Theorem 2.58 (`TreeConjugacy.lean`) every Coxeter element of a tree is
conjugate to `w`, so for trees the results apply to every Coxeter element.

## Main results
* `eigen_analysis`: every complex eigenvalue `λ ≠ -1` of `w` satisfies
  `λ² - (ν - 2) λ + 1 = 0` for some real eigenvalue `ν ≥ 0` of `A Aᵀ`.
* `theorem_3_27_classification` (**Theorem 3.27**):
  - `B` is positive definite (spherical) iff every eigenvalue of `w` has modulus `1` and `1`
    is not an eigenvalue;
  - `B` is positive semidefinite and degenerate (affine) iff every eigenvalue of `w` has
    modulus `1` and `1` is an eigenvalue;
  - `B` is indefinite (hyperbolic) iff `w` has a real eigenvalue `λ > 1`.
* `theorem_3_28_interlacing` (**Theorem 3.28**): if `Γ' ⊂ Γ` is an induced subgraph
  (`A' = A.submatrix f g` for injective `f`, `g`; deleting a single node `rᵢ` gives
  `Γ' = Γ/(rᵢ)`), then for every eigenvalue `λ'` of `w(Γ')` there is an eigenvalue `λ` of
  `w(Γ)` with `‖λ'‖ ≤ ‖λ‖`, i.e. `ρ(w(Γ')) ≤ ρ(w(Γ))`.
* `theorem_3_28_strict`: the inequality is strict, `‖λ'‖ < ‖λ‖`, when `Γ` is hyperbolic and
  `Γ'` is not. (The dissertation writes `λ(w₁) > λ(w₂)` with no hypothesis; strictness fails for
  spherical graphs, e.g. `A₂ ⊂ A₃`, whose Coxeter elements both have spectral radius `1`.)
-/

open Matrix

namespace MixedSignCoxeter

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The quadratic form `v ↦ vᵀ B v`. -/
def qf (B : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ := v ⬝ᵥ (B *ᵥ v)

/-- Spherical (positive definite), Definition 2.47. -/
def FormSpherical (B : Matrix ι ι ℝ) : Prop := ∀ v : ι → ℝ, v ≠ 0 → 0 < qf B v

/-- Affine (positive semidefinite and degenerate), Definition 2.48. -/
def FormAffine (B : Matrix ι ι ℝ) : Prop :=
  (∀ v : ι → ℝ, 0 ≤ qf B v) ∧ ∃ v : ι → ℝ, v ≠ 0 ∧ qf B v = 0

/-- Hyperbolic or higher rank (indefinite), Definitions 2.50–2.51. -/
def FormIndefinite (B : Matrix ι ι ℝ) : Prop :=
  (∃ u : ι → ℝ, 0 < qf B u) ∧ ∃ v : ι → ℝ, qf B v < 0

/-- `M` has the complex eigenvalue `λ`, acting on `ℂ^ι`. -/
def HasEigenC (M : Matrix ι ι ℝ) (lam : ℂ) : Prop :=
  ∃ v : ι → ℂ, v ≠ 0 ∧ (M.map (↑) : Matrix ι ι ℂ) *ᵥ v = lam • v

lemma dot_self_nonneg (v : ι → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

lemma dot_self_pos {v : ι → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v :=
  lt_of_le_of_ne (dot_self_nonneg v) (fun h => hv (dotProduct_self_eq_zero.mp h.symm))

lemma mulVec_map_ofReal (M : Matrix ι ι ℝ) (v : ι → ℝ) :
    (M.map (↑) : Matrix ι ι ℂ) *ᵥ (fun i => (v i : ℂ)) = fun i => ((M *ᵥ v) i : ℂ) := by
  funext i
  simp [mulVec, dotProduct]

lemma hasEigenC_of_real {M : Matrix ι ι ℝ} {lam : ℝ} {v : ι → ℝ} (hv : v ≠ 0)
    (h : M *ᵥ v = lam • v) : HasEigenC M lam := by
  refine ⟨fun i => (v i : ℂ), fun h0 => hv (funext fun i => by
    simpa using congr_fun h0 i), ?_⟩
  rw [mulVec_map_ofReal, h]
  funext i
  simp

lemma re_mulVec_map (M : Matrix ι ι ℝ) (x : ι → ℂ) (i : ι) :
    ((M.map (↑) : Matrix ι ι ℂ) *ᵥ x) i |>.re = (M *ᵥ fun j => (x j).re) i := by
  simp [mulVec, dotProduct, Complex.re_sum]

lemma im_mulVec_map (M : Matrix ι ι ℝ) (x : ι → ℂ) (i : ι) :
    ((M.map (↑) : Matrix ι ι ℂ) *ᵥ x) i |>.im = (M *ᵥ fun j => (x j).im) i := by
  simp [mulVec, dotProduct, Complex.im_sum]

/-- Real form of a complex eigen-equation `M x = ν x`. -/
lemma real_parts_of_eigen (M : Matrix ι ι ℝ) (x : ι → ℂ) (ν : ℂ)
    (h : (M.map (↑) : Matrix ι ι ℂ) *ᵥ x = ν • x) :
    M *ᵥ (fun j => (x j).re) = ν.re • (fun j => (x j).re) - ν.im • (fun j => (x j).im) ∧
    M *ᵥ (fun j => (x j).im) = ν.im • (fun j => (x j).re) + ν.re • (fun j => (x j).im) := by
  constructor
  · funext i
    rw [← re_mulVec_map, h]
    simp
  · funext i
    rw [← im_mulVec_map, h]
    simp [add_comm]

/-- A real symmetric matrix with a complex eigenvector has a real eigenvalue there: the
eigenvalue is real and the real or imaginary part is a real eigenvector. -/
lemma real_eigen_of_complex (M : Matrix ι ι ℝ) (hM : Mᵀ = M) (x : ι → ℂ) (hx : x ≠ 0)
    (ν : ℂ) (h : (M.map (↑) : Matrix ι ι ℂ) *ᵥ x = ν • x) :
    ν.im = 0 ∧ ∃ a : ι → ℝ, a ≠ 0 ∧ M *ᵥ a = ν.re • a := by
  obtain ⟨h1, h2⟩ := real_parts_of_eigen M x ν h
  set a : ι → ℝ := fun j => (x j).re
  set b : ι → ℝ := fun j => (x j).im
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hx
    funext j
    apply Complex.ext
    · simpa [a] using congr_fun hc.1 j
    · simpa [b] using congr_fun hc.2 j
  have hsym : a ⬝ᵥ (M *ᵥ b) = b ⬝ᵥ (M *ᵥ a) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hM, dotProduct_comm]
  rw [h1, h2] at hsym
  simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hsym
  have hpos : 0 < a ⬝ᵥ a + b ⬝ᵥ b := by
    rcases hab with ha | hb
    · exact add_pos_of_pos_of_nonneg (dot_self_pos ha) (dot_self_nonneg b)
    · exact add_pos_of_nonneg_of_pos (dot_self_nonneg a) (dot_self_pos hb)
  have hcomm : a ⬝ᵥ b = b ⬝ᵥ a := dotProduct_comm a b
  have him : ν.im * (a ⬝ᵥ a + b ⬝ᵥ b) = 0 := by linarith
  have him0 : ν.im = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact h
    · linarith
  refine ⟨him0, ?_⟩
  rw [him0, zero_smul, sub_zero] at h1
  rw [him0, zero_smul, zero_add] at h2
  rcases hab with ha | hb
  · exact ⟨a, ha, h1⟩
  · exact ⟨b, hb, h2⟩

/-- If `‖λ‖` solves `λ² - b λ + 1 = 0` with `b` real and `b² ≤ 4`, then `‖λ‖ = 1`. -/
lemma norm_eq_one_of_quadratic (lam : ℂ) (b : ℝ) (hb : b ^ 2 ≤ 4)
    (h : lam ^ 2 - b * lam + 1 = 0) : ‖lam‖ = 1 := by
  have hre := congr_arg Complex.re h
  have him := congr_arg Complex.im h
  simp [pow_two] at hre him
  have hsq : lam.re ^ 2 + lam.im ^ 2 = 1 := by
    by_cases hc : lam.im = 0
    · rw [hc] at hre
      have : (2 * lam.re - b) ^ 2 = b ^ 2 - 4 := by nlinarith
      have h1 : (2 * lam.re - b) ^ 2 = 0 := by nlinarith [sq_nonneg (2 * lam.re - b)]
      have h2 : 2 * lam.re = b := by nlinarith [sq_nonneg (2 * lam.re - b)]
      rw [hc]; nlinarith
    · have h2 : 2 * lam.re = b := by
        have : lam.im * (2 * lam.re - b) = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hc
        · linarith
      nlinarith
  have hn : ‖lam‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; nlinarith
  have hn0 : 0 ≤ ‖lam‖ := norm_nonneg _
  nlinarith

/-- For a Hermitian (real symmetric) `N`, if `N` is not positive definite then `N` has a
real eigenvector with eigenvalue `≤ 0`. -/
lemma exists_eigen_nonpos_of_not_posDef (N : Matrix ι ι ℝ) (hN : N.IsHermitian)
    (h : ¬ N.PosDef) : ∃ θ : ℝ, θ ≤ 0 ∧ ∃ u : ι → ℝ, u ≠ 0 ∧ N *ᵥ u = θ • u := by
  rw [hN.posDef_iff_eigenvalues_pos] at h
  push Not at h
  obtain ⟨i, hi⟩ := h
  refine ⟨hN.eigenvalues i, hi, ⇑(hN.eigenvectorBasis i), ?_, hN.mulVec_eigenvectorBasis i⟩
  intro h0
  have hne := (hN.eigenvectorBasis).orthonormal.ne_zero i
  apply hne
  ext j
  simpa using congr_fun h0 j

/-- For a Hermitian `N`, if `N` is not positive semidefinite then `N` has a real eigenvector
with eigenvalue `< 0`. -/
lemma exists_eigen_neg_of_not_posSemidef (N : Matrix ι ι ℝ) (hN : N.IsHermitian)
    (h : ¬ N.PosSemidef) : ∃ θ : ℝ, θ < 0 ∧ ∃ u : ι → ℝ, u ≠ 0 ∧ N *ᵥ u = θ • u := by
  rw [hN.posSemidef_iff_eigenvalues_nonneg] at h
  simp only [Pi.le_def, Pi.zero_apply, not_forall, not_le] at h
  obtain ⟨i, hi⟩ := h
  refine ⟨hN.eigenvalues i, hi, ⇑(hN.eigenvectorBasis i), ?_, hN.mulVec_eigenvectorBasis i⟩
  intro h0
  have hne := (hN.eigenvectorBasis).orthonormal.ne_zero i
  apply hne
  ext j
  simpa using congr_fun h0 j

lemma isHermitian_of_transpose_eq {N : Matrix ι ι ℝ} (h : Nᵀ = N) : N.IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, h]

end General

/-! ### The bipartite Coxeter element -/

variable {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ)

/-- `B = [[2, -A], [-Aᵀ, 2]]`: the bilinear form of a bipartite graph, nodes of `N₁` first. -/
def bipForm : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ :=
  fromBlocks (2 • (1 : Matrix (Fin p) (Fin p) ℝ)) (-A) (-Aᵀ) (2 • (1 : Matrix (Fin q) (Fin q) ℝ))

/-- `s₊`, the product of the reflections of the nodes in `N₁`. -/
def sPlusBip : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ := fromBlocks (-1) A 0 1

/-- `s₋`, the product of the reflections of the nodes in `N₂`. -/
def sMinusBip : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ := fromBlocks 1 0 Aᵀ (-1)

/-- The bipartite Coxeter element `w = s₊ s₋`. -/
def bipCoxeter : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ := sPlusBip A * sMinusBip A

lemma bipCoxeter_eq : bipCoxeter A = fromBlocks (A * Aᵀ - 1) (-A) Aᵀ (-1) := by
  simp only [bipCoxeter, sPlusBip, sMinusBip, fromBlocks_multiply]
  congr 1 <;> simp [sub_eq_add_neg, add_comm]

lemma AAt_transpose : (A * Aᵀ)ᵀ = A * Aᵀ := by
  rw [transpose_mul, transpose_transpose]

lemma dot_AAt (a : Fin p → ℝ) : a ⬝ᵥ ((A * Aᵀ) *ᵥ a) = (Aᵀ *ᵥ a) ⬝ᵥ (Aᵀ *ᵥ a) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]

lemma qf_bipForm (x : Fin p → ℝ) (y : Fin q → ℝ) :
    qf (bipForm A) (Sum.elim x y) =
      2 * (x ⬝ᵥ x) - 2 * ((Aᵀ *ᵥ x) ⬝ᵥ y) + 2 * (y ⬝ᵥ y) := by
  simp only [qf, bipForm, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    sumElim_dotProduct_sumElim, smul_mulVec, one_mulVec, neg_mulVec, dotProduct_add,
    dotProduct_neg, dotProduct_smul, smul_eq_mul]
  have h1 : x ⬝ᵥ (A *ᵥ y) = (Aᵀ *ᵥ x) ⬝ᵥ y := by
    rw [dotProduct_mulVec, mulVec_transpose]
  have h2 : y ⬝ᵥ (Aᵀ *ᵥ x) = (Aᵀ *ᵥ x) ⬝ᵥ y := dotProduct_comm _ _
  rw [h1, h2]
  ring

lemma qf_bipForm' (v : Fin p ⊕ Fin q → ℝ) :
    qf (bipForm A) v = 2 * ((v ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inl)) -
      2 * ((Aᵀ *ᵥ (v ∘ Sum.inl)) ⬝ᵥ (v ∘ Sum.inr)) + 2 * ((v ∘ Sum.inr) ⬝ᵥ (v ∘ Sum.inr)) := by
  conv_lhs => rw [← Sum.elim_comp_inl_inr v]
  exact qf_bipForm A _ _

lemma bipForm_transpose : (bipForm A)ᵀ = bipForm A := by
  simp [bipForm, fromBlocks_transpose]

/-- If `‖Aᵀ a‖² ≤ 4 ‖a‖²` for every `a`, then `B` is positive semidefinite. -/
lemma qf_nonneg_of_bound (hb : ∀ a : Fin p → ℝ, (Aᵀ *ᵥ a) ⬝ᵥ (Aᵀ *ᵥ a) ≤ 4 * (a ⬝ᵥ a))
    (v : Fin p ⊕ Fin q → ℝ) : 0 ≤ qf (bipForm A) v := by
  rw [qf_bipForm']
  set x := v ∘ Sum.inl
  set y := v ∘ Sum.inr
  have h0 := dot_self_nonneg (Aᵀ *ᵥ x - (2 : ℝ) • y)
  simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct,
    smul_eq_mul] at h0
  have hc : y ⬝ᵥ (Aᵀ *ᵥ x) = (Aᵀ *ᵥ x) ⬝ᵥ y := dotProduct_comm _ _
  have := hb x
  nlinarith

/-- The test vector of an eigenvector `a` of `A Aᵀ` with eigenvalue `ν = t²`, `t > 0`:
`qf B (a, Aᵀ a / t) = 2 ‖a‖² (2 - t)`. -/
lemma qf_test_vector (a : Fin p → ℝ) (t : ℝ) (ht : 0 < t)
    (ha : (A * Aᵀ) *ᵥ a = (t ^ 2) • a) :
    qf (bipForm A) (Sum.elim a (t⁻¹ • (Aᵀ *ᵥ a))) = 2 * (a ⬝ᵥ a) * (2 - t) := by
  rw [qf_bipForm]
  have hAA : (Aᵀ *ᵥ a) ⬝ᵥ (Aᵀ *ᵥ a) = t ^ 2 * (a ⬝ᵥ a) := by
    rw [← dot_AAt, ha, dotProduct_smul, smul_eq_mul]
  simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul, hAA]
  field_simp
  ring

/-- The eigenvalues of `A Aᵀ` are nonnegative. -/
lemma eigen_AAt_nonneg {a : Fin p → ℝ} (ha0 : a ≠ 0) {ν : ℝ}
    (ha : (A * Aᵀ) *ᵥ a = ν • a) : 0 ≤ ν := by
  have h := dot_AAt A a
  rw [ha, dotProduct_smul, smul_eq_mul] at h
  have h1 := dot_self_pos ha0
  have h2 := dot_self_nonneg (Aᵀ *ᵥ a)
  by_contra hν
  push Not at hν
  nlinarith

/-- Spherical forms force `ν < 4`, positive semidefinite forms force `ν ≤ 4`, for every
eigenvalue `ν` of `A Aᵀ`. -/
lemma eigen_AAt_le_four (hpsd : ∀ v, 0 ≤ qf (bipForm A) v) {a : Fin p → ℝ} (ha0 : a ≠ 0)
    {ν : ℝ} (ha : (A * Aᵀ) *ᵥ a = ν • a) : ν ≤ 4 := by
  have hν0 := eigen_AAt_nonneg A ha0 ha
  rcases eq_or_lt_of_le hν0 with h | hpos
  · rw [← h]; norm_num
  set t := Real.sqrt ν
  have ht : 0 < t := Real.sqrt_pos.mpr hpos
  have ht2 : t ^ 2 = ν := Real.sq_sqrt hν0
  have hq := qf_test_vector A a t ht (by rw [ht2]; exact ha)
  have := hpsd (Sum.elim a (t⁻¹ • (Aᵀ *ᵥ a)))
  rw [hq] at this
  have h1 := dot_self_pos ha0
  have ht' : t ≤ 2 := by
    by_contra hc; push Not at hc; nlinarith
  nlinarith

lemma eigen_AAt_lt_four (hsph : FormSpherical (bipForm A)) {a : Fin p → ℝ} (ha0 : a ≠ 0)
    {ν : ℝ} (ha : (A * Aᵀ) *ᵥ a = ν • a) : ν < 4 := by
  have hν0 := eigen_AAt_nonneg A ha0 ha
  rcases eq_or_lt_of_le hν0 with h | hpos
  · rw [← h]; norm_num
  set t := Real.sqrt ν
  have ht : 0 < t := Real.sqrt_pos.mpr hpos
  have ht2 : t ^ 2 = ν := Real.sq_sqrt hν0
  have hq := qf_test_vector A a t ht (by rw [ht2]; exact ha)
  have hne : Sum.elim a (t⁻¹ • (Aᵀ *ᵥ a)) ≠ 0 := by
    intro h0; apply ha0; funext i; simpa using congr_fun h0 (Sum.inl i)
  have := hsph _ hne
  rw [hq] at this
  have h1 := dot_self_pos ha0
  have ht' : t < 2 := by
    by_contra hc; push Not at hc; nlinarith
  nlinarith

/-- The complexification of `w`. -/
lemma bipCoxeter_map :
    ((bipCoxeter A).map (↑) : Matrix _ _ ℂ) =
      fromBlocks ((A.map (↑)) * (A.map (↑))ᵀ - 1) (-(A.map (↑))) (A.map (↑))ᵀ (-1) := by
  rw [bipCoxeter_eq]
  ext (i | i) (j | j) <;>
    simp [fromBlocks, Matrix.mul_apply, Matrix.one_apply, apply_ite]

/-- **Eigenvalue analysis.** Every complex eigenvalue `λ ≠ -1` of `w = s₊ s₋` satisfies
`λ² - (ν - 2) λ + 1 = 0` for a real eigenvalue `ν ≥ 0` of `A Aᵀ`. -/
theorem eigen_analysis {lam : ℂ} (h : HasEigenC (bipCoxeter A) lam) (hlam : lam ≠ -1) :
    ∃ ν : ℝ, 0 ≤ ν ∧ (∃ a : Fin p → ℝ, a ≠ 0 ∧ (A * Aᵀ) *ᵥ a = ν • a) ∧
      lam ^ 2 - ((ν : ℂ) - 2) * lam + 1 = 0 := by
  obtain ⟨v, hv0, hv⟩ := h
  rw [bipCoxeter_map, fromBlocks_mulVec] at hv
  set Ac : Matrix (Fin p) (Fin q) ℂ := A.map (↑)
  set x := v ∘ Sum.inl
  set y := v ∘ Sum.inr
  have E1 : (Ac * Acᵀ - 1) *ᵥ x + (-Ac) *ᵥ y = lam • x := by
    funext i; simpa using congr_fun hv (Sum.inl i)
  have E2 : Acᵀ *ᵥ x + (-1 : Matrix (Fin q) (Fin q) ℂ) *ᵥ y = lam • y := by
    funext i; simpa using congr_fun hv (Sum.inr i)
  have hl1 : lam + 1 ≠ 0 := fun h => hlam (by linear_combination h)
  have E2' : Acᵀ *ᵥ x = (lam + 1) • y := by
    rw [neg_mulVec, one_mulVec] at E2
    rw [add_smul, one_smul, ← E2]; abel
  have hx0 : x ≠ 0 := by
    intro hx
    apply hv0
    have hy : y = 0 := by
      rw [hx, mulVec_zero] at E2'
      funext j
      have := congr_fun E2' j
      simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hl1
    funext k
    cases k with
    | inl i => exact congr_fun hx i
    | inr j => exact congr_fun hy j
  -- `λ (A Aᵀ) x = (λ + 1)² x`
  have E3 : lam • ((Ac * Acᵀ) *ᵥ x) = ((lam + 1) ^ 2) • x := by
    have := congr_arg ((lam + 1) • ·) E1
    simp only [sub_mulVec, one_mulVec, neg_mulVec, smul_add, smul_sub, smul_neg] at this
    rw [← mulVec_smul, ← E2', mulVec_mulVec] at this
    funext i
    have hi := congr_fun this i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    linear_combination hi
  have hl0 : lam ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at E3
    apply hx0
    funext i
    have := congr_fun E3 i
    simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul, h0, zero_add, one_pow,
      one_mul] at this
    exact this.symm
  set ν : ℂ := (lam + 1) ^ 2 / lam
  have E4 : (Ac * Acᵀ) *ᵥ x = ν • x := by
    funext i
    have := congr_fun E3 i
    simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
    simp only [ν]
    field_simp
    linear_combination this
  have hmap : ((A * Aᵀ).map (↑) : Matrix (Fin p) (Fin p) ℂ) = Ac * Acᵀ := by
    simp [Ac, Matrix.map_mul, transpose_map]
  rw [← hmap] at E4
  obtain ⟨him, a, ha0, ha⟩ := real_eigen_of_complex (A * Aᵀ) (AAt_transpose A) x hx0 ν E4
  refine ⟨ν.re, eigen_AAt_nonneg A ha0 ha, ⟨a, ha0, ha⟩, ?_⟩
  have hνc : (ν.re : ℂ) = ν := Complex.ext (by simp) (by simp [him])
  rw [hνc]
  simp only [ν]
  field_simp
  ring

/-! ### Theorem 3.27 -/

lemma exhaustive : FormSpherical (bipForm A) ∨ FormAffine (bipForm A) ∨
    FormIndefinite (bipForm A) := by
  by_cases hpsd : ∀ v, 0 ≤ qf (bipForm A) v
  · by_cases hsph : FormSpherical (bipForm A)
    · exact Or.inl hsph
    · right; left
      refine ⟨hpsd, ?_⟩
      simp only [FormSpherical, not_forall, not_lt] at hsph
      obtain ⟨v, hv, hle⟩ := hsph
      exact ⟨v, hv, le_antisymm hle (hpsd v)⟩
  · right; right
    push Not at hpsd
    obtain ⟨v, hv⟩ := hpsd
    refine ⟨?_, v, hv⟩
    have hne : v ≠ 0 := by
      intro h0; rw [h0] at hv; simp [qf] at hv
    obtain ⟨k, _⟩ := Function.ne_iff.mp hne
    refine ⟨Pi.single k 1, ?_⟩
    simp only [qf, mulVec_single, mul_one, single_dotProduct, one_mul]
    cases k <;> simp [bipForm]

lemma forall_norm_eq_one (hpsd : ∀ v, 0 ≤ qf (bipForm A) v) (lam : ℂ)
    (h : HasEigenC (bipCoxeter A) lam) : ‖lam‖ = 1 := by
  by_cases hl : lam = -1
  · rw [hl]; simp
  obtain ⟨ν, hν0, ⟨a, ha0, ha⟩, hq⟩ := eigen_analysis A h hl
  have hν4 := eigen_AAt_le_four A hpsd ha0 ha
  refine norm_eq_one_of_quadratic lam (ν - 2) (by nlinarith) ?_
  push_cast
  exact hq

lemma not_eigen_one_of_spherical (hsph : FormSpherical (bipForm A)) :
    ¬ HasEigenC (bipCoxeter A) 1 := by
  intro h
  obtain ⟨ν, _, ⟨a, ha0, ha⟩, hq⟩ := eigen_analysis A h (by norm_num)
  have hν : (ν : ℂ) = 4 := by linear_combination -hq
  have hν' : ν = 4 := by exact_mod_cast hν
  have := eigen_AAt_lt_four A hsph ha0 ha
  linarith

lemma eigen_one_of_affine (haff : FormAffine (bipForm A)) : HasEigenC (bipCoxeter A) 1 := by
  obtain ⟨hpsd, v, hv0, hv⟩ := haff
  have hPSD : (bipForm A).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg
      (isHermitian_of_transpose_eq (bipForm_transpose A)) fun x => ?_
    simpa [qf] using hpsd x
  have hBv : bipForm A *ᵥ v = 0 :=
    (hPSD.dotProduct_mulVec_zero_iff).mp (by simpa [qf] using hv)
  rw [← Sum.elim_comp_inl_inr v] at hBv
  rw [bipForm, fromBlocks_mulVec] at hBv
  set x := v ∘ Sum.inl
  set y := v ∘ Sum.inr
  have e1 : (2 : ℝ) • x = A *ᵥ y := by
    funext i
    have := congr_fun hBv (Sum.inl i)
    simp [x, y, smul_mulVec, sub_eq_zero] at this ⊢
    linarith
  have e2 : Aᵀ *ᵥ x = (2 : ℝ) • y := by
    funext j
    have := congr_fun hBv (Sum.inr j)
    simp [x, y, smul_mulVec] at this ⊢
    linarith
  have hw : bipCoxeter A *ᵥ v = (1 : ℝ) • v := by
    rw [one_smul, bipCoxeter_eq]
    conv_lhs => rw [← Sum.elim_comp_inl_inr v]
    rw [fromBlocks_mulVec]
    conv_rhs => rw [← Sum.elim_comp_inl_inr v]
    congr 1
    · simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
      rw [sub_mulVec, ← mulVec_mulVec, e2, mulVec_smul, ← e1, neg_mulVec, ← e1, one_mulVec]
      funext i; simp; ring
    · simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
      rw [e2, neg_mulVec, one_mulVec]
      funext j; simp; ring
  have := hasEigenC_of_real hv0 hw
  simpa using this

/-- `w` has a real eigenvalue `> 1` when `B` is indefinite. -/
lemma real_eigen_gt_one_of_indefinite (hind : FormIndefinite (bipForm A)) :
    ∃ lam : ℝ, 1 < lam ∧ HasEigenC (bipCoxeter A) lam := by
  obtain ⟨_, v, hv⟩ := hind
  -- `4 - A Aᵀ` is not positive semidefinite
  set N : Matrix (Fin p) (Fin p) ℝ := (4 : ℝ) • 1 - A * Aᵀ
  have hNt : Nᵀ = N := by simp [N, transpose_sub, AAt_transpose]
  have hN := isHermitian_of_transpose_eq hNt
  have hnot : ¬ N.PosSemidef := by
    intro hpsd
    have hb : ∀ a : Fin p → ℝ, (Aᵀ *ᵥ a) ⬝ᵥ (Aᵀ *ᵥ a) ≤ 4 * (a ⬝ᵥ a) := by
      intro a
      have := hpsd.dotProduct_mulVec_nonneg a
      simp only [star_trivial, N, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul, dot_AAt] at this
      linarith
    exact absurd (qf_nonneg_of_bound A hb v) (not_le.mpr hv)
  obtain ⟨θ, hθ, u, hu0, hu⟩ := exists_eigen_neg_of_not_posSemidef N hN hnot
  set ν : ℝ := 4 - θ
  have huν : (A * Aᵀ) *ᵥ u = ν • u := by
    have : (A * Aᵀ) *ᵥ u = (4 : ℝ) • u - N *ᵥ u := by
      simp [N, sub_mulVec, smul_mulVec]
    rw [this, hu, ← sub_smul]
  have hν4 : 4 < ν := by simp only [ν]; linarith
  set μ := Real.sqrt ν
  have hμ : μ ^ 2 = ν := Real.sq_sqrt (by linarith)
  set lam : ℝ := ((ν - 2) + Real.sqrt ((ν - 2) ^ 2 - 4)) / 2
  have hdisc : 0 ≤ (ν - 2) ^ 2 - 4 := by nlinarith
  have hs := Real.sq_sqrt hdisc
  have hlam : lam ^ 2 - (μ ^ 2 - 2) * lam + 1 = 0 := by
    rw [hμ]; simp only [lam]; nlinarith
  have hgt : 1 < lam := by
    have := Real.sqrt_nonneg ((ν - 2) ^ 2 - 4)
    simp only [lam]; linarith
  have heig := theorem_3_27_bipartite_coxeter_eigenvalue A u μ lam (by rw [hμ]; exact huν) hlam
  refine ⟨lam, hgt, hasEigenC_of_real (v := Sum.elim ((lam + 1) • u) (Aᵀ *ᵥ u)) ?_ ?_⟩
  · intro h0
    apply hu0
    funext i
    have := congr_fun h0 (Sum.inl i)
    simp only [Sum.elim_inl, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    have hl1 : lam + 1 ≠ 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hl1
  · exact heig

/-- **Theorem 3.27** (A'Campo) for the bipartite Coxeter element `w = s₊ s₋` of a bipartite
Coxeter graph with form `B = [[2, -A], [-Aᵀ, 2]]`:
* `B` is spherical (positive definite) iff all eigenvalues of `w` have modulus `1` and `1` is
  not an eigenvalue;
* `B` is affine (positive semidefinite, degenerate) iff all eigenvalues of `w` have modulus `1`
  and `1` is an eigenvalue;
* `B` is hyperbolic or higher rank (indefinite) iff `w` has a real eigenvalue `λ > 1`. -/
theorem theorem_3_27_classification :
    (FormSpherical (bipForm A) ↔
      (∀ lam, HasEigenC (bipCoxeter A) lam → ‖lam‖ = 1) ∧ ¬ HasEigenC (bipCoxeter A) 1) ∧
    (FormAffine (bipForm A) ↔
      (∀ lam, HasEigenC (bipCoxeter A) lam → ‖lam‖ = 1) ∧ HasEigenC (bipCoxeter A) 1) ∧
    (FormIndefinite (bipForm A) ↔
      ∃ lam : ℝ, 1 < lam ∧ HasEigenC (bipCoxeter A) lam) := by
  have sph_psd : FormSpherical (bipForm A) → ∀ v, 0 ≤ qf (bipForm A) v := by
    intro h v
    by_cases hv : v = 0
    · rw [hv]; simp [qf]
    · exact (h v hv).le
  have real_gt_one_contra : ∀ lam : ℝ, 1 < lam → HasEigenC (bipCoxeter A) lam →
      (∀ v, 0 ≤ qf (bipForm A) v) → False := by
    intro lam hl he hpsd
    have := forall_norm_eq_one A hpsd _ he
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at this
    linarith
  refine ⟨⟨fun h => ⟨forall_norm_eq_one A (sph_psd h), not_eigen_one_of_spherical A h⟩,
    fun ⟨hn, h1⟩ => ?_⟩, ⟨fun h => ⟨forall_norm_eq_one A h.1, eigen_one_of_affine A h⟩,
    fun ⟨hn, h1⟩ => ?_⟩, ⟨real_eigen_gt_one_of_indefinite A, fun ⟨lam, hl, he⟩ => ?_⟩⟩
  · rcases exhaustive A with h | h | h
    · exact h
    · exact absurd (eigen_one_of_affine A h) h1
    · obtain ⟨lam, hl, he⟩ := real_eigen_gt_one_of_indefinite A h
      have := hn _ he
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at this
      linarith
  · rcases exhaustive A with h | h | h
    · exact absurd h1 (not_eigen_one_of_spherical A h)
    · exact h
    · obtain ⟨lam, hl, he⟩ := real_eigen_gt_one_of_indefinite A h
      have := hn _ he
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at this
      linarith
  · rcases exhaustive A with h | h | h
    · exact (real_gt_one_contra lam hl he (sph_psd h)).elim
    · exact (real_gt_one_contra lam hl he h.1).elim
    · exact h

end MixedSignCoxeter
