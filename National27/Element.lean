import Mathlib

def State (n : ℕ) := Fin n → ℕ

def isTerminal {n : ℕ} (c : State n) : Prop :=
  ∃ i, c i = ∑ j, c j

abbrev isValidTransition {n : ℕ} (c : State n) (p : Fin n × Fin n) : Prop :=
  p.1 < p.2 ∧ c p.1 > 0 ∧ c p.2 > 0

def validTransitions {n : ℕ} (c : State n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (isValidTransition c)

def stateTransition {n : ℕ} (c : State n) (p : Fin n × Fin n) (add_i : Bool) : State n :=
  let (i, j) := p
  fun k =>
    if k = i then (if add_i then c i + 1 else c i - 1)
    else if k = j then (if add_i then c j - 1 else c j + 1)
    else c k

/-- Uniform distribution on a nonempty finset. -/
noncomputable def uniformPMF {α : Type*} [DecidableEq α] (s : Finset α) (h : s.Nonempty) : PMF α :=
  PMF.ofFinset (fun a => if a ∈ s then (s.card : ENNReal)⁻¹ else 0) s
    (by
      rw [Finset.sum_congr rfl (fun a ha => ite_eq_left ha), Finset.sum_const, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel (by exact_mod_cast h.card_pos.ne') ENNReal.coe_ne_top)
    (by simp)

noncomputable def subTransitedStatePMF {n : ℕ} (c : State n) (p : Fin n × Fin n) : PMF (State n) :=
  PMF.bernoulli (1 / 2 : NNReal) (by norm_num) >>= fun b =>
    PMF.pure (stateTransition c p b)

noncomputable def transitedStatePMF {n : ℕ} (c : State n) : PMF (State n) :=
  if h : (validTransitions c).Nonempty then
    uniformPMF (validTransitions c) h >>= subTransitedStatePMF c
  else
    PMF.pure c
