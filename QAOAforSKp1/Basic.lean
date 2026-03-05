import Mathlib


----------------------------------------------------------------
--------------------------Lemmas--------------------------------
----------------------------------------------------------------

/--
`2` is nonzero in `ℂ`.
Used to justify inverses such as `(2 : ℂ)⁻¹` in normalization proofs.
-/
lemma two_ne_zero_complex : (2 : ℂ) ≠ 0 := by
  norm_num


/--
In `ℂ`, squaring `√2` gives `2`.
This is the algebraic identity needed to simplify the `1 / √2` factors
when proving normalization of `|+⟩` and `|s⟩`.
-/
lemma sqrt2_sq_complex : ((Real.sqrt 2 : ℂ) ^ 2) = (2 : ℂ) := by
  have hR : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  exact_mod_cast hR



----------------------------------------------------------------
--------------------------Bra State-----------------------------
----------------------------------------------------------------
/-- Bra associated to `ψ` in any finite-dimensional computational basis. -/
noncomputable def bra {n : ℕ} (ψ : Fin n → ℂ) : (Fin n → ℂ) → ℂ :=
  fun φ => ∑ i : Fin n, star (ψ i) * φ i



----------------------------------------------------------------
--------------------------Single Qubit--------------------------
----------------------------------------------------------------

/-- A single-qubit pure state represented as amplitudes on basis indices `0,1`. -/
abbrev Qubit := Fin 2 → ℂ

/-- Computational basis state `|0⟩`. -/
def ket0 : Qubit :=
  ![1, 0]

/-- Computational basis state `|1⟩`. -/
def ket1 : Qubit :=
  ![0, 1]

/-- Hadamard gate on a single qubit. -/
noncomputable def hadamard (ψ : Qubit) : Qubit :=
  ![
    (ψ 0 + ψ 1) / Real.sqrt 2,
    (ψ 0 - ψ 1) / Real.sqrt 2
  ]

/-- `|+⟩ = H|0⟩` for a single qubit. -/
noncomputable def ketPlus : Qubit :=
  hadamard ket0


/-- Single qubit state normalization and orthogonalization. -/
theorem bra_ket0_ket0 : bra ket0 ket0 = 1 := by
  simp [bra, ket0]

theorem bra_ket1_ket1 : bra ket1 ket1 = 1 := by
  simp [bra, ket1]

theorem bra_ket0_ket1 : bra ket0 ket1 = 0 := by
  simp [bra, ket0, ket1]

theorem bra_ket1_ket0 : bra ket1 ket0 = 0 := by
  simp [bra, ket0, ket1]

/-- The `|+⟩` state is normalized: `⟨+|+⟩ = 1`. -/
theorem bra_ketPlus_ketPlus : bra ketPlus ketPlus = 1 := by
  simp [bra, ketPlus, hadamard, ket0]
  ring_nf
  simp [sqrt2_sq_complex]



----------------------------------------------------------------
--------------------------n-Qubits State------------------------
----------------------------------------------------------------

/-- Computational-basis index type for `(n+1)` qubits. -/
abbrev BasisIdx (n : ℕ) := Fin (2 ^ (n + 1))

/-- State space for `(n+1)` qubits in computational basis indexing. -/
abbrev State (n : ℕ) := BasisIdx n → ℂ

/-- Linear operators acting on `State n`. -/
abbrev Operator (n : ℕ) := State n → State n

/-- Computational basis ket `|y⟩` as a state function. -/
def basisKet (n : ℕ) (y : BasisIdx n) : State n :=
  fun x => if x = y then 1 else 0

/--
Adjoint (dagger) of an operator in the computational basis.
Defined by conjugate-transposing its matrix elements.
-/
noncomputable def dagger (n : ℕ) (U : Operator n) : Operator n :=
  fun ψ x => ∑ y : BasisIdx n, star (U (basisKet n y) x) * ψ y

/-- Density matrices on `(n+1)` qubits in the computational basis. -/
abbrev DensityMatrix (n : ℕ) := Matrix (BasisIdx n) (BasisIdx n) ℂ

/-- Pure-state density matrix `|ψ⟩⟨ψ|`. -/
noncomputable def pureDensity (n : ℕ) (ψ : State n) : DensityMatrix n :=
  fun x y => ψ x * star (ψ y)


/--
Split an index of `2^(n+1)` basis states into:
1 qubit index (`Fin 2`) and the remaining `n`-qubit index (`Fin (2^n)`).
-/
def splitQubitIndex {n : ℕ} (i : BasisIdx n) : Fin 2 × Fin (2 ^ n) :=
  ( ⟨i.1 % 2, Nat.mod_lt _ (by decide)⟩
  , ⟨i.1 / 2, by
      have hi : i.1 < 2 ^ n * 2 := by
        simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using i.2
      exact (Nat.div_lt_iff_lt_mul (by decide : 0 < (2 : ℕ))).2 <| by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hi
    ⟩ )

/--
Initial QAOA state on `n+1` qubits, defined as `|s⟩ = |+⟩^{⊗ (n+1)}`.
This encoding avoids the `n=0` scalar base case.
-/
noncomputable def s : (n : ℕ) → State n
  | 0 => ketPlus
  | n + 1 => fun i =>
      let p := splitQubitIndex (n := n + 1) i
      ketPlus p.1 * s n p.2

/-- Density matrix of the initial state `|s⟩`: `ρ_s = |s⟩⟨s|`. -/
noncomputable def rho_s (n : ℕ) : DensityMatrix n :=
  pureDensity n (s n)

/--
`⟨i|s⟩ = (√(2^(n+1)))⁻¹`
is the normalization factor for the uniform superposition on `2^(n+1)` basis states.
-/
lemma s_entry_const (n : ℕ) (i : BasisIdx n) :
    s n i = (Real.sqrt (2 ^ (n + 1) : ℝ) : ℂ)⁻¹ := by
  let c : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  have hketPlus : ∀ j : Fin 2, ketPlus j = c := by
    intro j
    fin_cases j <;> simp [ketPlus, hadamard, ket0, c]
  have hs_const : ∀ n : ℕ, ∀ j : BasisIdx n, s n j = c ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
        intro j
        fin_cases j <;> simp [s, hketPlus, c]
    | succ n ih =>
        intro j
        simp [s, hketPlus, ih, pow_succ, mul_comm]
  have hsqrt_pow : ∀ m : ℕ, Real.sqrt (2 ^ m : ℝ) = (Real.sqrt 2) ^ m := by
    intro m
    induction m with
    | zero =>
        simp
    | succ m ihm =>
        have h2nonneg : (0 : ℝ) ≤ 2 := by norm_num
        have hpow_nonneg : (0 : ℝ) ≤ (2 ^ m : ℝ) := by positivity
        calc
          Real.sqrt (2 ^ (m + 1) : ℝ)
              = Real.sqrt ((2 ^ m : ℝ) * 2) := by
                  simp [pow_succ, mul_comm]
          _ = Real.sqrt (2 ^ m : ℝ) * Real.sqrt 2 := by
                exact Real.sqrt_mul hpow_nonneg (2 : ℝ)
          _ = (Real.sqrt 2) ^ m * Real.sqrt 2 := by rw [ihm]
          _ = (Real.sqrt 2) ^ (m + 1) := by simp [pow_succ]
  have hsqrt_powC :
      (Real.sqrt (2 ^ (n + 1) : ℝ) : ℂ) = (Real.sqrt 2 : ℂ) ^ (n + 1) := by
    exact_mod_cast hsqrt_pow (n + 1)
  calc
    s n i = c ^ (n + 1) := hs_const n i
    _ = ((Real.sqrt 2 : ℂ)⁻¹) ^ (n + 1) := by simp [c]
    _ = ((Real.sqrt 2 : ℂ) ^ (n + 1))⁻¹ := by rw [inv_pow]
    _ = (Real.sqrt (2 ^ (n + 1) : ℝ) : ℂ)⁻¹ := by
          simp [hsqrt_powC]

/-- The initial state's density matrix has unit trace. -/
theorem trace_rho_s_eq_one (n : ℕ) : Matrix.trace (rho_s n) = 1 := by
  let c : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  have hketPlus : ∀ i : Fin 2, ketPlus i = c := by
    intro i
    fin_cases i <;> simp [ketPlus, hadamard, ket0, c]
  have hs_const : ∀ n : ℕ, ∀ i : BasisIdx n, s n i = c ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
        intro i
        fin_cases i <;> simp [s, hketPlus, c]
    | succ n ih =>
        intro i
        simp [s, hketPlus, ih, pow_succ, mul_comm]
  have hc2 : c * c = (2 : ℂ)⁻¹ := by
    dsimp [c]
    ring_nf
    simp [sqrt2_sq_complex]
  calc
    Matrix.trace (rho_s n)
        = ∑ i : BasisIdx n, s n i * star (s n i) := by
            unfold rho_s pureDensity
            simp [Matrix.trace]
    _ = ∑ i : BasisIdx n, star (s n i) * s n i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
    _ = ∑ _i : BasisIdx n, star (c ^ (n + 1)) * (c ^ (n + 1)) := by
          simp [hs_const]
    _ = (2 ^ (n + 1) : ℂ) * (star (c ^ (n + 1)) * c ^ (n + 1)) := by
          simp
    _ = (2 ^ (n + 1) : ℂ) * (c ^ (n + 1) * c ^ (n + 1)) := by
          simp [c]
    _ = (2 ^ (n + 1) : ℂ) * ((c * c) ^ (n + 1)) := by
          rw [← mul_pow]
    _ = (2 ^ (n + 1) : ℂ) * (((2 : ℂ)⁻¹) ^ (n + 1)) := by
          simp [hc2]
    _ = (2 : ℂ) ^ (n + 1) * ((2 : ℂ)⁻¹ ^ (n + 1)) := by
          norm_num
    _ = ((2 : ℂ) * (2 : ℂ)⁻¹) ^ (n + 1) := by
          rw [(mul_pow (2 : ℂ) ((2 : ℂ)⁻¹) (n + 1)).symm]
    _ = 1 := by
          simp



----------------------------------------------------------------
--------------------------The Mixer Operator--------------------
----------------------------------------------------------------

/-- Hamming distance between computational-basis indices (`(n+1)`-bit strings). -/
def basisHammingDist (n : ℕ) (x y : BasisIdx n) : ℕ :=
  ((Finset.range (n + 1)).filter (fun j => Nat.testBit x.1 j ≠ Nat.testBit y.1 j)).card

/-- Basic bound: a Hamming distance on `(n+1)` bits is at most `n+1`. -/
lemma basisHammingDist_le (n : ℕ) (x y : BasisIdx n) :
    basisHammingDist n x y ≤ n + 1 := by
  let p : ℕ → Prop := fun j => Nat.testBit x.1 j ≠ Nat.testBit y.1 j
  unfold basisHammingDist
  calc
    ((Finset.range (n + 1)).filter p).card ≤ (Finset.range (n + 1)).card := by
      exact Finset.card_le_card (Finset.filter_subset (s := Finset.range (n + 1)) (p := p))
    _ = n + 1 := by simp

/-- Computational-basis matrix element of `U_B(β) = exp(-i β ∑_j X_j)`:
⟨x|U_B(β)|y⟩ = cos(β)^(n+1-d) * (-i sin(β))^d where d is the Hamming distance between x and y.
-/
noncomputable def mixerKernel (n : ℕ) (β : ℝ) (x y : BasisIdx n) : ℂ :=
  let d := basisHammingDist n x y
  (Real.cos β : ℂ) ^ ((n + 1) - d) * ((-Complex.I) * (Real.sin β : ℂ)) ^ d

/-- Explicit mixer unitary action in the computational basis. -/
noncomputable def U_B (n : ℕ) (β : ℝ) : Operator n :=
  fun ψ x => ∑ y : BasisIdx n, mixerKernel n β x y * ψ y


/-- Dagger mixer operator, defined as the adjoint of `U_B`. -/
noncomputable def U_B_dagger (n : ℕ) (β : ℝ) : Operator n :=
  dagger n (U_B n β)

/--
Orthonormality of the mixer kernel:
`∑_z conj(K_{zx}) K_{zy} = δ_{xy}`.
-/
theorem MixerKernelOrthonormal (n : ℕ) (β : ℝ) :
    ∀ x y : BasisIdx n,
      (∑ z : BasisIdx n, star (mixerKernel n β z x) * mixerKernel n β z y)
        = if x = y then 1 else 0 := by
  sorry

/--
The mixer operator preserves the norm of the initial state:
`Tr((U_B†U_B) ρ_s) = 1` if the mixer kernel is orthonormal.
-/
theorem trace_U_B_dagger_mul_U_B_rho_s_eq_one
    (n : ℕ) (β : ℝ) :
    Matrix.trace
      ((let UBUB : DensityMatrix n :=
          fun x y => ∑ z : BasisIdx n, star (mixerKernel n β z x) * mixerKernel n β z y
        UBUB) * rho_s n)
      = 1 := by
  let UBUB : DensityMatrix n :=
    fun x y => ∑ z : BasisIdx n, star (mixerKernel n β z x) * mixerKernel n β z y
  have hId :
      UBUB = (1 : DensityMatrix n) := by
    ext x y
    simpa [UBUB, Matrix.one_apply] using (MixerKernelOrthonormal n β x y)
  calc
    Matrix.trace
        ((let UBUB : DensityMatrix n :=
            fun x y => ∑ z : BasisIdx n, star (mixerKernel n β z x) * mixerKernel n β z y
          UBUB) * rho_s n)
        = Matrix.trace (UBUB * rho_s n) := by simp [UBUB]
    _ = Matrix.trace ((1 : DensityMatrix n) * rho_s n) := by simp [hId]
    _ = Matrix.trace (rho_s n) := by simp
    _ = 1 := trace_rho_s_eq_one n


----------------------------------------------------------------
-------------------------SK Cost Function-----------------------
----------------------------------------------------------------

/-- SK couplings `J_{jk}` on `(n+1)` qubits. -/
abbrev SKCoupling (n : ℕ) := Fin (n + 1) → Fin (n + 1) → ℝ

/-- Spin value (`±1`) of qubit `j` in basis state `z`. -/
def spinAt (n : ℕ) (z : BasisIdx n) (j : Fin (n + 1)) : ℝ :=
  if Nat.testBit z.1 j.1 then (-1 : ℝ) else (1 : ℝ)

/-- Unordered edge set `{(j,k) | j < k}` used by the SK Hamiltonian. -/
def skEdgeSet (n : ℕ) : Finset (Fin (n + 1) × Fin (n + 1)) :=
  (Finset.univ.product Finset.univ).filter (fun jk => jk.1.1 < jk.2.1)

/-- SK normalization factor `1 / √(n+1)`. -/
noncomputable def skNormFactor (n : ℕ) : ℝ :=
  (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹

/-- SK cost value `C_J(z)` on computational basis state `z`. -/
noncomputable def skCostOnBasis (n : ℕ) (J : SKCoupling n) (z : BasisIdx n) : ℝ :=
  skNormFactor n *
    Finset.sum (skEdgeSet n) (fun jk => J jk.1 jk.2 * spinAt n z jk.1 * spinAt n z jk.2)

/-- Phase factor of the SK cost unitary `U_C(γ)` on basis state `|z⟩`. -/
noncomputable def U_C_phase (n : ℕ) (J : SKCoupling n) (γ : ℝ) (z : BasisIdx n) : ℂ :=
  Complex.exp (((-Complex.I) * (γ : ℂ)) * (skCostOnBasis n J z : ℂ))

/-- Phase factor of the adjoint cost unitary `U_C(γ)†` on basis state `|z⟩`. -/
noncomputable def U_C_dagger_phase (n : ℕ) (J : SKCoupling n) (γ : ℝ) (z : BasisIdx n) : ℂ :=
  Complex.exp (((Complex.I) * (γ : ℂ)) * (skCostOnBasis n J z : ℂ))


----------------------------------------------------------------
-----------QAOA at level p=1 state for the SK model-------------
----------------------------------------------------------------


/-- Pointwise phase cancellation: `U_C(γ)†(z) * U_C(γ)(z) = 1`. -/
lemma U_C_dagger_phase_mul_U_C_phase_eq_one
    (n : ℕ) (J : SKCoupling n) (γ : ℝ) (z : BasisIdx n) :
    U_C_dagger_phase n J γ z * U_C_phase n J γ z = 1 := by
  let a : ℂ := ((γ : ℂ) * (skCostOnBasis n J z : ℂ))
  have hsum : Complex.I * a + (-Complex.I) * a = 0 := by ring
  calc
    U_C_dagger_phase n J γ z * U_C_phase n J γ z
        = Complex.exp (Complex.I * a) * Complex.exp ((-Complex.I) * a) := by
            simp [U_C_dagger_phase, U_C_phase, a, mul_left_comm, mul_comm]
    _ = Complex.exp ((Complex.I * a) + ((-Complex.I) * a)) := by
          simpa [Complex.exp_add] using (Complex.exp_add (Complex.I * a) ((-Complex.I) * a)).symm
    _ = Complex.exp 0 := by simp
    _ = 1 := by simp
/--
Matrix entries of `U_C† U_B† U_B U_C` in computational basis.
`U_C` contributes only diagonal phase factors on the two outer sides.
-/
noncomputable def U_C_dagger_mul_U_B_dagger_mul_U_B_mul_U_C_matrix
    (n : ℕ) (J : SKCoupling n) (β γ : ℝ) : DensityMatrix n :=
  fun x y =>
    U_C_dagger_phase n J γ x *
      (∑ z : BasisIdx n, star (mixerKernel n β z x) * mixerKernel n β z y) *
      U_C_phase n J γ y

/--
`Tr((U_C† U_B† U_B U_C) ρ_s) = 1`
-/
theorem trace_U_C_dagger_mul_U_B_dagger_mul_U_B_mul_U_C_rho_s_eq_one
    (n : ℕ) (J : SKCoupling n) (β γ : ℝ) :
    Matrix.trace
      (U_C_dagger_mul_U_B_dagger_mul_U_B_mul_U_C_matrix n J β γ * rho_s n) = 1 := by
  have hIdAll :
      U_C_dagger_mul_U_B_dagger_mul_U_B_mul_U_C_matrix n J β γ = (1 : DensityMatrix n) := by
    ext x y
    calc
      U_C_dagger_mul_U_B_dagger_mul_U_B_mul_U_C_matrix n J β γ x y
          = (U_C_dagger_phase n J γ x *
              (∑ z : BasisIdx n, star (mixerKernel n β z x) * mixerKernel n β z y)) *
              U_C_phase n J γ y := by
                simp [U_C_dagger_mul_U_B_dagger_mul_U_B_mul_U_C_matrix]
      _ = (U_C_dagger_phase n J γ x * (if x = y then 1 else 0)) * U_C_phase n J γ y := by
            rw [MixerKernelOrthonormal n β x y]
      _ = if x = y then (U_C_dagger_phase n J γ x * U_C_phase n J γ y) else 0 := by
            by_cases hxy : x = y <;> simp [hxy]
      _ = if x = y then 1 else 0 := by
            by_cases hxy : x = y
            · subst hxy
              simp [U_C_dagger_phase_mul_U_C_phase_eq_one]
            · simp [hxy]
      _ = (1 : DensityMatrix n) x y := by simp [Matrix.one_apply]
  calc
    Matrix.trace (U_C_dagger_mul_U_B_dagger_mul_U_B_mul_U_C_matrix n J β γ * rho_s n)
        = Matrix.trace ((1 : DensityMatrix n) * rho_s n) := by simp [hIdAll]
    _ = Matrix.trace (rho_s n) := by simp
    _ = 1 := trace_rho_s_eq_one n


----------------------------------------------------------------
-----Expectation of the Exponentiated Cost - Definition---------
----------------------------------------------------------------

/--
Matrix entries of `U_C† U_B† exp(i λ (C/(n+1))) U_B U_C`
in the computational basis.
-/
noncomputable def QAOAGenMatrix
    (n : ℕ) (J : SKCoupling n) (β γ lam : ℝ) : DensityMatrix n :=
  fun x y =>
    U_C_dagger_phase n J γ x *
      (∑ z : BasisIdx n,
        star (mixerKernel n β z x) *
          Complex.exp
            (Complex.I * ((lam : ℂ) * ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ))) *
          mixerKernel n β z y) *
      U_C_phase n J γ y

/--
For fixed SK coupling `J`, the p=1 QAOA generating function value:
`⟨s| U_C† U_B† exp(i λ (C/(n+1))) U_B U_C |s⟩`
written as a trace with `ρ_s = |s⟩⟨s|`.
-/
noncomputable def QAOAGenVEV
    (n : ℕ) (J : SKCoupling n) (β γ lam : ℝ) : ℂ :=
  Matrix.trace
    (QAOAGenMatrix n J β γ lam * rho_s n)

/--
Ensemble expectation over SK couplings:
`E_J(⟨s| U_C† U_B† exp(i λ (C/(n+1))) U_B U_C |s⟩)`.
`μ` is the probability measure for `J`.
-/
noncomputable def ExpectedGeneratingFunction
    (n : ℕ) (μ : MeasureTheory.Measure (SKCoupling n)) (β γ lam : ℝ) : ℂ :=
  ∫ J, QAOAGenVEV n J β γ lam ∂μ


----------------------------------------------------------------
------Evaluation of the generating function - 1st step----------
----------------------------------------------------------------

/--
Insert complete computational-basis resolutions (`|x⟩, |z⟩, |y⟩`)
into the generating function expression to rewrite:
`E_J(⟨s| U_C† U_B† exp(i λ (C/(n+1))) U_B U_C |s⟩)`
`=`
`E_J( ⟨s|U_C†|x⟩ ⟨x|U_B†|z⟩ exp(i λ (C/(n+1))) ⟨z|U_B|y⟩⟨y|U_C|s⟩  )`
`=`
`E_J( ⟨s|x⟩ exp(i γ C(x))  ⟨x|U_B†|z⟩  exp(i λ (C/(n+1)))  ⟨z|U_B|y⟩ exp(-i γ C(y))  ⟨y|s⟩)`.
-/
theorem ExpectedGeneratingFunction_insert_basis_xyz
    (n : ℕ) (μ : MeasureTheory.Measure (SKCoupling n)) (β γ lam : ℝ) :
    ExpectedGeneratingFunction n μ β γ lam
      =
      ∫ J,
        ∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n,
          star (s n x) *
            U_C_dagger_phase n J γ x *
            star (mixerKernel n β z x) *
            Complex.exp
              (Complex.I * ((lam : ℂ) * ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ))) *
            mixerKernel n β z y *
            U_C_phase n J γ y *
            s n y ∂μ := by
  simp [ExpectedGeneratingFunction, QAOAGenVEV, QAOAGenMatrix, Matrix.trace, Matrix.mul_apply,
    rho_s, pureDensity, Finset.mul_sum, mul_comm, mul_left_comm]

/--
Replace the `|s⟩` amplitudes in the basis expansion by their explicit value
`(√(2^(n+1)))⁻¹`:
`⟨s|x⟩ = (√(2^(n+1)))⁻¹` and `⟨y|s⟩ = (√(2^(n+1)))⁻¹`.
-/
theorem ExpectedGeneratingFunction_replace_s_factors
    (n : ℕ) (μ : MeasureTheory.Measure (SKCoupling n)) (β γ lam : ℝ) :
    ExpectedGeneratingFunction n μ β γ lam
      =
      ∫ J,
        ∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n,
          star ((Real.sqrt (2 ^ (n + 1) : ℝ) : ℂ)⁻¹) *
            U_C_dagger_phase n J γ x *
            star (mixerKernel n β z x) *
            Complex.exp
              (Complex.I * ((lam : ℂ) * ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ))) *
            mixerKernel n β z y *
            U_C_phase n J γ y *
            ((Real.sqrt (2 ^ (n + 1) : ℝ) : ℂ)⁻¹) ∂μ := by
  simp [ExpectedGeneratingFunction_insert_basis_xyz, s_entry_const]

/--
Combine the two cost-unitary phase factors into a single
exponential phase:
`U_C†(x) U_C(y) exp(i λ C_J(z)/(n+1))]`
` = `
`exp(i γ (C_J(x)-C_J(y)) + i λ C_J(z)/(n+1))`.
-/
lemma U_C_phase_pair_times_genPhase
    (n : ℕ) (J : SKCoupling n) (γ lam : ℝ)
    (x y z : BasisIdx n) :
    U_C_dagger_phase n J γ x *
      U_C_phase n J γ y *
      Complex.exp (Complex.I * ((lam : ℂ) * ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ)))
      =
      Complex.exp
        ((Complex.I * ((γ : ℂ) * (((skCostOnBasis n J x : ℂ) - (skCostOnBasis n J y : ℂ)))) ) +
          (Complex.I * ((lam : ℂ) * ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ)))) := by
  let cx : ℂ := (skCostOnBasis n J x : ℂ)
  let cy : ℂ := (skCostOnBasis n J y : ℂ)
  let gz : ℂ := Complex.exp (Complex.I * ((lam : ℂ) * ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ)))
  have hxy :
      U_C_dagger_phase n J γ x * U_C_phase n J γ y
        = Complex.exp (Complex.I * ((γ : ℂ) * (cx - cy))) := by
    calc
      U_C_dagger_phase n J γ x * U_C_phase n J γ y
          = Complex.exp (((Complex.I) * (γ : ℂ)) * cx) *
              Complex.exp (((-Complex.I) * (γ : ℂ)) * cy) := by
                simp [U_C_dagger_phase, U_C_phase, cx, cy, mul_comm, mul_left_comm]
      _ = Complex.exp ((((Complex.I) * (γ : ℂ)) * cx) + (((-Complex.I) * (γ : ℂ)) * cy)) := by
            exact
              (Complex.exp_add (((Complex.I) * (γ : ℂ)) * cx) (((-Complex.I) * (γ : ℂ)) * cy)).symm
      _ = Complex.exp (Complex.I * ((γ : ℂ) * (cx - cy))) := by
            ring_nf
  calc
    U_C_dagger_phase n J γ x * U_C_phase n J γ y *
        Complex.exp (Complex.I * ((lam : ℂ) * ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ)))
        = (U_C_dagger_phase n J γ x * U_C_phase n J γ y) * gz := by
            simp [gz, mul_assoc]
    _ = Complex.exp (Complex.I * ((γ : ℂ) * (cx - cy))) * gz := by simp [hxy]
    _ =
        Complex.exp (Complex.I * ((γ : ℂ) *
          (((skCostOnBasis n J x : ℂ) - (skCostOnBasis n J y : ℂ)))) ) *
          Complex.exp (Complex.I * ((lam : ℂ) * ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ))) := by
            simp [cx, cy, gz]
    _ = Complex.exp
          ((Complex.I * ((γ : ℂ) * (((skCostOnBasis n J x : ℂ) - (skCostOnBasis n J y : ℂ)))) ) +
            (Complex.I * ((lam : ℂ) * ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ)))) := by
          exact
            (Complex.exp_add
              (Complex.I * ((γ : ℂ) * (((skCostOnBasis n J x : ℂ) - (skCostOnBasis n J y : ℂ)))))
              (Complex.I * ((lam : ℂ) * ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ)))).symm


/--
Merge the cost-unitary phase factors into a single exponential,
merge the two normalization factors `(√(2^(n+1)))⁻¹` into `(2^(n+1))⁻¹`
and take it out of the sum and integral,to rewrite the generating function as:
`E_J(⟨s| U_C† U_B† exp(i λ (C/(n+1))) U_B U_C |s⟩)`
`=`
`(2^(n+1))⁻¹ * E_J( ∑_{x,y,z} exp(i γ (C_J(x)-C_J(y)) + i λ C_J(z)/(n+1)) * K_{zx} * K_{zy} )`.
-/
theorem ExpectedGeneratingFunction_merge
    (n : ℕ) (μ : MeasureTheory.Measure (SKCoupling n)) (β γ lam : ℝ) :
    ExpectedGeneratingFunction n μ β γ lam
      =
      ((2 ^ (n + 1) : ℂ)⁻¹) *
        (∫ J,
          ∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n,
            Complex.exp
              ((Complex.I *
                  ((γ : ℂ) *
                    (((skCostOnBasis n J x : ℂ) - (skCostOnBasis n J y : ℂ)))) ) +
                (Complex.I *
                  ((lam : ℂ) *
                    ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ)))) *
              mixerKernel n β z y *
              star (mixerKernel n β z x) ∂μ) := by
  let c : ℂ := ((2 ^ (n + 1) : ℂ)⁻¹)
  let f : SKCoupling n → ℂ := fun J =>
    ∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n,
      U_C_dagger_phase n J γ x *
        U_C_phase n J γ y *
        mixerKernel n β z y *
        Complex.exp
          (Complex.I * ((lam : ℂ) * ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ))) *
        star (mixerKernel n β z x)
  let a : ℂ := (Real.sqrt (2 ^ (n + 1) : ℝ) : ℂ)⁻¹
  have hsqR : (Real.sqrt (2 ^ (n + 1) : ℝ)) ^ 2 = (2 ^ (n + 1) : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 ^ (n + 1) : ℝ) by positivity)]
  have hsq : ((Real.sqrt (2 ^ (n + 1) : ℝ) : ℂ) ^ 2) = (2 ^ (n + 1) : ℂ) := by
    exact_mod_cast hsqR
  have hfac : a * a = ((2 ^ (n + 1) : ℂ)⁻¹) := by
    calc
      a * a = a ^ 2 := by simp [pow_two]
      _ = ((Real.sqrt (2 ^ (n + 1) : ℝ) : ℂ) ^ 2)⁻¹ := by
            simp [a, inv_pow]
      _ = ((2 ^ (n + 1) : ℂ)⁻¹) := by simp [hsq]
  have hfac_mul (b : ℂ) : a * (a * b) = ((2 ^ (n + 1) : ℂ)⁻¹) * b := by
    calc
      a * (a * b) = (a * a) * b := by ring
      _ = ((2 ^ (n + 1) : ℂ)⁻¹) * b := by simp [hfac]
  have hinside :
      ExpectedGeneratingFunction n μ β γ lam
        = ∫ J,
            ∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n,
              c *
                (U_C_dagger_phase n J γ x *
                  (U_C_phase n J γ y *
                    (mixerKernel n β z y *
                      (Complex.exp
                        (Complex.I * ((lam : ℂ) * ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ))) *
                        star (mixerKernel n β z x)))) ) ∂μ := by
    simpa [a, c, hfac, hfac_mul, mul_assoc, mul_comm, mul_left_comm] using
      (ExpectedGeneratingFunction_replace_s_factors n μ β γ lam)
  calc
    ExpectedGeneratingFunction n μ β γ lam
        = ∫ J, c * f J ∂μ := by
            simpa [f, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using hinside
    _ = c * (∫ J, f J ∂μ) := by
          simpa using (MeasureTheory.integral_const_mul c f)
    _ = ((2 ^ (n + 1) : ℂ)⁻¹) *
          (∫ J,
            ∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n,
              U_C_dagger_phase n J γ x *
                (U_C_phase n J γ y *
                  (mixerKernel n β z y *
                    (Complex.exp
                      (Complex.I * ((lam : ℂ) * ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ))) *
                      star (mixerKernel n β z x))) ) ∂μ) := by
            simp [c, f, mul_assoc, mul_comm, mul_left_comm]
    _ = ((2 ^ (n + 1) : ℂ)⁻¹) *
          (∫ J,
            ∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n,
              Complex.exp
                ((Complex.I *
                    ((γ : ℂ) *
                      (((skCostOnBasis n J x : ℂ) - (skCostOnBasis n J y : ℂ)))) ) +
                  (Complex.I *
                    ((lam : ℂ) *
                      ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ)))) *
                mixerKernel n β z y *
                star (mixerKernel n β z x) ∂μ) := by
            apply congrArg (fun t => ((2 ^ (n + 1) : ℂ)⁻¹) * t)
            refine MeasureTheory.integral_congr_ae ?_
            refine Filter.Eventually.of_forall ?_
            intro J
            refine Finset.sum_congr rfl ?_
            intro x hx
            refine Finset.sum_congr rfl ?_
            intro y hy
            refine Finset.sum_congr rfl ?_
            intro z hz
            have hphase := U_C_phase_pair_times_genPhase n J γ lam x y z
            calc
              U_C_dagger_phase n J γ x *
                  (U_C_phase n J γ y *
                    (mixerKernel n β z y *
                      (Complex.exp
                        (Complex.I * ((lam : ℂ) * ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ))) *
                        star (mixerKernel n β z x))))
                  =
                  (U_C_dagger_phase n J γ x * U_C_phase n J γ y *
                    Complex.exp
                      (Complex.I * ((lam : ℂ) * ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ)))) *
                    mixerKernel n β z y *
                    star (mixerKernel n β z x) := by
                      ring
              _ =
                  Complex.exp
                    ((Complex.I *
                        ((γ : ℂ) *
                          (((skCostOnBasis n J x : ℂ) - (skCostOnBasis n J y : ℂ)))) ) +
                      (Complex.I *
                        ((lam : ℂ) *
                          ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ)))) *
                    mixerKernel n β z y *
                    star (mixerKernel n β z x) := by
                      simpa [mul_assoc, mul_comm, mul_left_comm] using
                        congrArg
                          (fun t =>
                            t * mixerKernel n β z y * star (mixerKernel n β z x))
                          hphase



/--
Swap the order of the finite sums (`x,y,z`) and the `J`-integral.
-/
theorem ExpectedGeneratingFunction_swap_integral_and_sum
    (n : ℕ) (μ : MeasureTheory.Measure (SKCoupling n)) (β γ lam : ℝ)
    (hInt : ∀ x y z : BasisIdx n,
      MeasureTheory.Integrable
        (fun J : SKCoupling n =>
          Complex.exp
            ((Complex.I *
                ((γ : ℂ) *
                  (((skCostOnBasis n J x : ℂ) - (skCostOnBasis n J y : ℂ)))) ) +
              (Complex.I *
                ((lam : ℂ) *
                  ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ)))) *
          mixerKernel n β z y *
          star (mixerKernel n β z x)) μ) :
    ExpectedGeneratingFunction n μ β γ lam
      =
      ((2 ^ (n + 1) : ℂ)⁻¹) *
        (∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n,
          ∫ J,
            Complex.exp
              ((Complex.I *
                  ((γ : ℂ) *
                    (((skCostOnBasis n J x : ℂ) - (skCostOnBasis n J y : ℂ)))) ) +
                (Complex.I *
                  ((lam : ℂ) *
                    ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ)))) *
            mixerKernel n β z y *
            star (mixerKernel n β z x) ∂μ) := by
  rw [ExpectedGeneratingFunction_merge]
  apply congrArg (fun t => ((2 ^ (n + 1) : ℂ)⁻¹) * t)
  let g : BasisIdx n → BasisIdx n → BasisIdx n → SKCoupling n → ℂ :=
    fun x y z J =>
      Complex.exp
        ((Complex.I *
            ((γ : ℂ) *
              (((skCostOnBasis n J x : ℂ) - (skCostOnBasis n J y : ℂ)))) ) +
          (Complex.I *
            ((lam : ℂ) *
              ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ)))) *
      mixerKernel n β z y *
      star (mixerKernel n β z x)
  calc
    ∫ J, ∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n, g x y z J ∂μ
        = ∑ x : BasisIdx n, ∫ J, ∑ y : BasisIdx n, ∑ z : BasisIdx n, g x y z J ∂μ := by
            simpa [g] using
              (MeasureTheory.integral_finset_sum
                (μ := μ)
                (s := (Finset.univ : Finset (BasisIdx n)))
                (f := fun x J => ∑ y : BasisIdx n, ∑ z : BasisIdx n, g x y z J)
                (by
                  intro x hx
                  exact MeasureTheory.integrable_finset_sum _ fun y _ =>
                    MeasureTheory.integrable_finset_sum _ fun z _ => hInt x y z))
    _ = ∑ x : BasisIdx n, ∑ y : BasisIdx n, ∫ J, ∑ z : BasisIdx n, g x y z J ∂μ := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          simpa [g] using
            (MeasureTheory.integral_finset_sum
              (μ := μ)
              (s := (Finset.univ : Finset (BasisIdx n)))
              (f := fun y J => ∑ z : BasisIdx n, g x y z J)
              (by
                intro y hy
                exact MeasureTheory.integrable_finset_sum _ fun z _ => hInt x y z))
    _ = ∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n, ∫ J, g x y z J ∂μ := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          refine Finset.sum_congr rfl ?_
          intro y hy
          simpa [g] using
            (MeasureTheory.integral_finset_sum
              (μ := μ)
              (s := (Finset.univ : Finset (BasisIdx n)))
              (f := fun z J => g x y z J)
              (by
                intro z hz
                exact hInt x y z))
    _ = ∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n,
          ∫ J,
            Complex.exp
              ((Complex.I *
                  ((γ : ℂ) *
                    (((skCostOnBasis n J x : ℂ) - (skCostOnBasis n J y : ℂ)))) ) +
                (Complex.I *
                  ((lam : ℂ) *
                    ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ)))) *
            mixerKernel n β z y *
            star (mixerKernel n β z x) ∂μ := by
          simp [g]

/--
Pull the mixer-kernel factors outside the `J`-integral.
For fixed `x,y,z`, `mixerKernel n β z y * star (mixerKernel n β z x)` does not depend on `J`,
so it is a constant multiplier with respect to the measure over SK couplings.
-/
theorem ExpectedGeneratingFunction_pull_out_kernel_factors
    (n : ℕ) (μ : MeasureTheory.Measure (SKCoupling n)) (β γ lam : ℝ)
    (hInt : ∀ x y z : BasisIdx n,
      MeasureTheory.Integrable
        (fun J : SKCoupling n =>
          Complex.exp
            ((Complex.I *
                ((γ : ℂ) *
                  (((skCostOnBasis n J x : ℂ) - (skCostOnBasis n J y : ℂ)))) ) +
              (Complex.I *
                ((lam : ℂ) *
                  ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ)))) *
          mixerKernel n β z y *
          star (mixerKernel n β z x)) μ) :
    ExpectedGeneratingFunction n μ β γ lam
      =
      ((2 ^ (n + 1) : ℂ)⁻¹) *
        (∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n,
          (mixerKernel n β z y * star (mixerKernel n β z x)) *
            (∫ J,
              Complex.exp
                ((Complex.I *
                    ((γ : ℂ) *
                      (((skCostOnBasis n J x : ℂ) - (skCostOnBasis n J y : ℂ)))) ) +
                  (Complex.I *
                    ((lam : ℂ) *
                      ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ)))) ∂μ)) := by
  rw [ExpectedGeneratingFunction_swap_integral_and_sum n μ β γ lam hInt]
  apply congrArg (fun t => ((2 ^ (n + 1) : ℂ)⁻¹) * t)
  refine Finset.sum_congr rfl ?_
  intro x hx
  refine Finset.sum_congr rfl ?_
  intro y hy
  refine Finset.sum_congr rfl ?_
  intro z hz
  let phase : SKCoupling n → ℂ := fun J =>
    Complex.exp
      ((Complex.I *
          ((γ : ℂ) *
            (((skCostOnBasis n J x : ℂ) - (skCostOnBasis n J y : ℂ)))) ) +
        (Complex.I *
          ((lam : ℂ) *
            ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ))))
  let k : ℂ := mixerKernel n β z y * star (mixerKernel n β z x)
  calc
    ∫ J,
      Complex.exp
        ((Complex.I *
            ((γ : ℂ) *
              (((skCostOnBasis n J x : ℂ) - (skCostOnBasis n J y : ℂ)))) ) +
          (Complex.I *
            ((lam : ℂ) *
              ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ)))) *
      mixerKernel n β z y *
      star (mixerKernel n β z x) ∂μ
        = ∫ J, phase J * k ∂μ := by
            simp [phase, k, mul_assoc, mul_comm, mul_left_comm]
    _
        = ∫ J, k * phase J ∂μ := by
            simp [phase, k, mul_comm, mul_left_comm]
    _ = k * ∫ J, phase J ∂μ := by
          simpa [phase, k] using (MeasureTheory.integral_const_mul k phase)
    _ = (mixerKernel n β z y * star (mixerKernel n β z x)) *
          (∫ J,
            Complex.exp
              ((Complex.I *
                  ((γ : ℂ) *
                    (((skCostOnBasis n J x : ℂ) - (skCostOnBasis n J y : ℂ)))) ) +
                (Complex.I *
                  ((lam : ℂ) *
                    ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ)))) ∂μ) := by
          simp [phase, k]
