import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Monopoly Restriction as an Internal Governance Problem

This file is a self-contained Lean 4 / Mathlib document.  It combines
mathematical definitions, formal algebraic lemmas, and long-form explanatory
comments.  The economic problem is the following.

A textbook monopolist is usually modeled as a unitary decision-maker that
chooses the monopoly quantity costlessly.  A real monopoly, however, is a
multi-agent organization.  Divisions, plants, regional managers, sales agents,
and formerly independent firms often have local incentives that do not coincide
with the objective of the residual claimant.  The monopoly owner therefore must
make the organization behave like a unitary monopolist.  This requires an
internal enforcement apparatus.

The central claim formalized below is:

* The textbook monopoly quantity is denoted `Q_M`.
* The competitive or efficient quantity is denoted `Q_C`.
* The decentralized organizational quantity is denoted `Q_D`; this is the
  quantity toward which the organization drifts absent costly internal
  enforcement.
* The agency-constrained monopoly quantity is denoted `Q*`.

The maintained ranking is

  `Q_M < Q_D ≤ Q_C`.

The organization would like to drift toward `Q_D`, while the unitary textbook
monopoly benchmark is `Q_M`.  Enforcing output below `Q_D` requires monitoring,
quotas, audits, central sales offices, transfer-pricing rules, punishment,
compensation design, and hierarchy.  The enforcement gap is

  `x = Q_D - Q`.

The policy or allocative gap is

  `Δ = Q_C - Q`.

They differ when `Q_D < Q_C`:

  `Q_C - Q = (Q_C - Q_D) + (Q_D - Q)`.

The central theorem is that if enforcement costs are increasing in `x`, the
agency-constrained monopolist chooses

  `Q_M < Q* < Q_D ≤ Q_C`.

Therefore standard policy calculations that treat the unregulated monopolist as
producing `Q_M` overstate the output gap and the Harberger triangle whenever
the actual unregulated quantity is `Q* > Q_M`.

The document is organized as follows.

1. Core notation and gaps.
2. A linear-quadratic benchmark.
3. Local-incentive thought experiment: internal Cournot behavior.
4. Common-profit thought experiment: profit-sharing, shirking, and rent
   dissipation.
5. Central-command thought experiment: hierarchy, bounded punishments, and
   convex monitoring cost.
6. Downstream welfare and regulatory implication.
7. Literature notes.

The three thought experiments should not be read as an exhaustive taxonomy.
They are stylized organizational cases that demonstrate different ways in
which the same object, the enforcement cost of monopoly restriction, can arise.
-/

noncomputable section

open Real

namespace MonopolyInternalCartel

/-! ## 1. Core notation -/

/-- Linear inverse demand is summarized by the competitive intercept quantity
`Qc` and slope `b`.  Gross profit, ignoring fixed costs and enforcement costs,
is `G(Q) = b * Qc * Q - b * Q^2`.  This is equivalent to
`(p(Q) - c) Q` under `p(Q) = a - b Q`, constant marginal cost `c`, and
`Qc = (a - c) / b`. -/
def grossProfit (b Qc Q : ℝ) : ℝ :=
  b * Qc * Q - b * Q ^ 2

/-- The textbook monopoly quantity in the linear-demand, constant-marginal-cost
case is one half of the competitive quantity. -/
def monopolyQuantity (Qc : ℝ) : ℝ :=
  Qc / 2

/-- The governance gap is the amount of output that headquarters must suppress
relative to the organization's decentralized output. -/
def governanceGap (Qd Q : ℝ) : ℝ :=
  Qd - Q

/-- The regulatory or allocative gap is the shortfall from the competitive
quantity. -/
def regulatoryGap (Qc Q : ℝ) : ℝ :=
  Qc - Q

/-- The regulatory gap decomposes into the gap between the competitive and
organizational benchmark plus the internal governance gap. -/
theorem regulatoryGap_decomposition (Qc Qd Q : ℝ) :
    regulatoryGap Qc Q = (Qc - Qd) + governanceGap Qd Q := by
  unfold regulatoryGap governanceGap
  ring

/-!
Economic interpretation of the decomposition:

`governanceGap Qd Q = Q_D - Q` is the internal restriction that must be
enforced inside the monopoly organization.

`regulatoryGap Qc Q = Q_C - Q` is the welfare-relevant output shortfall from
the competitive or efficient benchmark.

When `Q_D = Q_C`, the governance and regulatory gaps coincide.  When
`Q_D < Q_C`, they differ.  The internal theory determines `Q*` by explaining
how costly it is to move the organization below `Q_D`; the regulatory theory
then evaluates the remaining gap `Q_C - Q*`.
-/

/-! ## 2. Linear-quadratic enforcement benchmark -/

/-- Quadratic enforcement cost.  The parameter `κ` measures the marginal
costliness of enforcing monopoly restriction. -/
def quadraticEnforcementCost (κ Qd Q : ℝ) : ℝ :=
  (κ / 2) * (Qd - Q) ^ 2

/-- The agency-constrained monopoly quantity in the linear-quadratic benchmark.
It solves

`max_Q b Qc Q - b Q^2 - (κ/2) (Qd - Q)^2`.
-/
def agencyConstrainedQuantity (b κ Qc Qd : ℝ) : ℝ :=
  (b * Qc + κ * Qd) / (2 * b + κ)

/-- The same quantity written in terms of the textbook monopoly quantity `Qm`. -/
def agencyConstrainedQuantityFromQM (b κ Qm Qd : ℝ) : ℝ :=
  (2 * b * Qm + κ * Qd) / (2 * b + κ)

/-- The two definitions coincide when `Qm = Qc / 2`. -/
theorem agencyConstrained_eq_fromQM (b κ Qc Qd : ℝ) :
    agencyConstrainedQuantity b κ Qc Qd =
      agencyConstrainedQuantityFromQM b κ (monopolyQuantity Qc) Qd := by
  unfold agencyConstrainedQuantity agencyConstrainedQuantityFromQM monopolyQuantity
  ring

/-- The closed-form solution is a convex combination of `Qm` and `Qd` when
`b > 0` and `κ > 0`.  This identity is purely algebraic. -/
theorem agencyConstrained_as_weighted_average
    (b κ Qm Qd : ℝ) (hden : 2 * b + κ ≠ 0) :
    agencyConstrainedQuantityFromQM b κ Qm Qd =
      (2 * b / (2 * b + κ)) * Qm +
      (κ / (2 * b + κ)) * Qd := by
  unfold agencyConstrainedQuantityFromQM
  field_simp [hden]

/-- The distance from the textbook monopoly quantity equals a positive weight
on the distance between `Qd` and `Qm`. -/
theorem agencyConstrained_minus_QM
    (b κ Qm Qd : ℝ) (hden : 2 * b + κ ≠ 0) :
    agencyConstrainedQuantityFromQM b κ Qm Qd - Qm =
      κ * (Qd - Qm) / (2 * b + κ) := by
  unfold agencyConstrainedQuantityFromQM
  field_simp [hden]
  ring

/-- The distance from the decentralized quantity equals a positive weight on
the distance between `Qd` and `Qm`. -/
theorem QD_minus_agencyConstrained
    (b κ Qm Qd : ℝ) (hden : 2 * b + κ ≠ 0) :
    Qd - agencyConstrainedQuantityFromQM b κ Qm Qd =
      (2 * b) * (Qd - Qm) / (2 * b + κ) := by
  unfold agencyConstrainedQuantityFromQM
  field_simp [hden]
  ring

/-- If `Qd > Qm`, the agency-constrained output exceeds the textbook monopoly
output. -/
theorem agencyConstrained_gt_QM
    (b κ Qm Qd : ℝ) (hb : 0 < b) (hκ : 0 < κ) (hQD : Qm < Qd) :
    Qm < agencyConstrainedQuantityFromQM b κ Qm Qd := by
  unfold agencyConstrainedQuantityFromQM
  have hden : 0 < 2 * b + κ := by nlinarith
  rw [lt_div_iff₀ hden]
  ring_nf
  nlinarith

/-- If `Qd > Qm`, the agency-constrained output remains below the decentralized
organizational quantity. -/
theorem agencyConstrained_lt_QD
    (b κ Qm Qd : ℝ) (hb : 0 < b) (hκ : 0 < κ) (hQD : Qm < Qd) :
    agencyConstrainedQuantityFromQM b κ Qm Qd < Qd := by
  unfold agencyConstrainedQuantityFromQM
  have hden : 0 < 2 * b + κ := by nlinarith
  rw [div_lt_iff₀ hden]
  ring_nf
  nlinarith

/-- The agency-constrained quantity is increasing in the enforcement-cost
parameter `κ`.  This captures the idea that costlier internal enforcement makes
the owner relax the restriction and produce more. -/
theorem derivative_kappa_closed_form
    (b κ Qm Qd : ℝ) (hden : 2 * b + κ ≠ 0) :
    -- This expression is the formal derivative of
    -- `(2*b*Qm + κ*Qd) / (2*b + κ)` with respect to `κ`.
    (2 * b * (Qd - Qm)) / (2 * b + κ) ^ 2 =
      ((Qd * (2 * b + κ)) - (2 * b * Qm + κ * Qd)) /
        (2 * b + κ) ^ 2 := by
  field_simp [hden]
  ring

/-!
The closed-form benchmark is the main algebraic result.

The owner solves

`max_Q G(Q) - E(Q_D - Q)`,

where

`G(Q) = b Q_C Q - b Q^2`

and

`E(Q_D - Q) = (κ/2) (Q_D - Q)^2`.

The first-order condition is

`b Q_C - 2 b Q + κ (Q_D - Q) = 0`.

Solving gives

`Q* = (b Q_C + κ Q_D) / (2 b + κ)`.

Since `Q_M = Q_C / 2`, this is also

`Q* = (2 b Q_M + κ Q_D) / (2 b + κ)`.

Therefore `Q*` is a weighted average of `Q_M` and `Q_D`.  If `Q_D > Q_M`,
then

`Q_M < Q* < Q_D`.

The value `Q_D - Q_M` is the amount of internal restraint required to implement
the textbook monopoly quantity.  Larger `Q_D - Q_M` or larger `κ` moves actual
output farther to the right of `Q_M`.
-/

/-! ## 3. Thought experiment I: local incentives and internal Cournot behavior -/

/-- Under local net-revenue incentives, `η` symmetric internal agents/divisions
behave like Cournot players inside the monopoly organization.  The decentralized
organizational quantity is `η / (η + 1)` times the competitive quantity.  The
variable `η` is represented as a positive real number to keep the algebra simple. -/
def localIncentiveQD (η Qc : ℝ) : ℝ :=
  (η / (η + 1)) * Qc

/-- With more than one internal agent and positive competitive quantity, the
local-incentive decentralized quantity exceeds the textbook monopoly quantity. -/
theorem localIncentiveQD_gt_QM
    (η Qc : ℝ) (hη : 1 < η) (hQc : 0 < Qc) :
    monopolyQuantity Qc < localIncentiveQD η Qc := by
  unfold monopolyQuantity localIncentiveQD
  have hden : 0 < η + 1 := by nlinarith
  have hratio : (1 : ℝ) / 2 < η / (η + 1) := by
    rw [lt_div_iff₀ hden]
    nlinarith
  calc
    Qc / 2 = ((1 : ℝ) / 2) * Qc := by ring
    _ < (η / (η + 1)) * Qc := mul_lt_mul_of_pos_right hratio hQc

/-- The local-incentive decentralized quantity is below the competitive quantity
for positive `η`. -/
theorem localIncentiveQD_lt_QC
    (η Qc : ℝ) (hη : 0 < η) (hQc : 0 < Qc) :
    localIncentiveQD η Qc < Qc := by
  unfold localIncentiveQD
  have hden : 0 < η + 1 := by nlinarith
  have hratio : η / (η + 1) < (1 : ℝ) := by
    rw [div_lt_iff₀ hden]
    nlinarith
  calc
    (η / (η + 1)) * Qc < (1 : ℝ) * Qc := mul_lt_mul_of_pos_right hratio hQc
    _ = Qc := by ring

/-!
Derivation of the local-incentive case.

Let inverse demand be `p(Q) = a - b Q`, with `b > 0`, and constant marginal
cost `c`.  The competitive quantity satisfies

`Q_C = (a - c) / b`.

A unitary textbook monopolist solves

`max_Q (p(Q) - c) Q`,

so

`Q_M = Q_C / 2`.

Now suppose that the monopoly organization contains `η` symmetric internal
agents or divisions.  Each local unit controls `q_i`, total output is

`Q = Σ_i q_i`,

and each unit is evaluated on local net revenue

`u_i = (p(Q) - c) q_i`.

The first-order condition of unit `i` is

`p(Q) + p'(Q) q_i - c = 0`.

Under symmetry, `q_i = Q / η`.  Hence

`p(Q) + p'(Q) Q/η - c = 0`.

For linear demand,

`a - b Q - b Q/η - c = 0`,

so

`Q_D^L = η/(η+1) Q_C`.

If `η > 1`, then

`Q_M = Q_C/2 < Q_D^L < Q_C`.

This is the internal-cartel result: each local unit internalizes the price
reduction on its own output, but not the price reduction imposed on the rest of
the organization.  The monopoly owner can try to impose `Q_M`, but the
organization naturally drifts toward `Q_D^L`.  The enforcement gap is

`x_L = Q_D^L - Q`.

With quadratic enforcement cost, the actual quantity is

`Q_L* = (2 b Q_M + κ_L Q_D^L) / (2 b + κ_L)`,

so

`Q_M < Q_L* < Q_D^L < Q_C`.
-/

/-! ## 4. Thought experiment II: common profit-sharing and shirking -/

/-- Mixed compensation quantity.  The local incentive weight is `α`; the
firm-wide profit-sharing weight is `β`; `η` is the number of symmetric internal
units represented as a positive real.  This formula follows from the symmetric
first-order condition

`α [p(Q) + p'(Q) Q/η - c] + β [p(Q) + p'(Q) Q - c] = 0`.
-/
def mixedCompensationQD (α β η Qc : ℝ) : ℝ :=
  ((α + β) / (α * (1 + 1 / η) + 2 * β)) * Qc

/-- If compensation has no firm-wide profit-sharing component, the mixed formula
reduces to the local-incentive internal Cournot quantity. -/
theorem mixedCompensation_no_common_profit
    (α η Qc : ℝ) (hα : α ≠ 0) (hη : η ≠ 0)
    (hden : α * (1 + 1 / η) ≠ 0) :
    mixedCompensationQD α 0 η Qc = localIncentiveQD η Qc := by
  have hηplus : 1 + η ≠ 0 := by
    intro h
    apply hden
    have hηeq : η = -1 := by linarith
    subst η
    norm_num
  have hαη : α + α * η ≠ 0 := by
    rw [show α + α * η = α * (1 + η) by ring]
    exact mul_ne_zero hα hηplus
  have hηplus' : η + 1 ≠ 0 := by
    simpa [add_comm] using hηplus
  unfold mixedCompensationQD localIncentiveQD
  field_simp [hα, hη, hden, hηplus, hαη]
  field_simp [hα, hηplus']
  ring

/-- If compensation has no local incentive component, the mixed formula reduces
to the textbook monopoly quantity. -/
theorem mixedCompensation_no_local_incentive
    (β η Qc : ℝ) (hβ : β ≠ 0) :
    mixedCompensationQD 0 β η Qc = monopolyQuantity Qc := by
  unfold mixedCompensationQD monopolyQuantity
  field_simp [hβ]
  ring

/-!
Derivation of the common-profit case.

Profit-sharing is a natural response to local overselling.  Instead of paying
agents for local net revenue, the owner can tie compensation to total firm
profit.  Let the payoff weight on local net revenue be `α ≥ 0`, and the payoff
weight on total firm profit be `β ≥ 0`.  A symmetric internal unit faces the
condition

`α [p(Q) + p'(Q) Q/η - c] + β [p(Q) + p'(Q) Q - c] = 0`.

For linear demand this gives

`Q(α, β) = ((α + β) / (α(1 + 1/η) + 2β)) Q_C`.

The formula nests two polar cases.

* If `β = 0`, then `Q(α,0) = η/(η+1) Q_C = Q_D^L`.
* If `α = 0`, then `Q(0,β) = Q_C/2 = Q_M`.

Thus common profit-sharing can discipline local overselling, but it does not
make the organization frictionless.  It changes the agency problem.  When an
agent receives only a share `s_i` of firm-wide surplus, the agent internalizes
only `s_i` of the benefit of costly effort.  If effort `e_i` creates firm-wide
benefit `B(e_i)` and imposes private cost `v(e_i)`, the efficient condition is

`B'(e_i) = v'(e_i)`.

The private condition under profit-sharing is

`s_i B'(e_i) = v'(e_i)`.

For `s_i < 1`, effort is below the first-best level under standard convexity
conditions.  With many equal profit-sharing agents, `s_i = 1/η`, so the
free-riding problem becomes more severe as the organization becomes larger.

In this case, the enforcement cost is not only the cost of preventing
unauthorized output.  It is the cost of protecting the monopoly rent stock from
internal dissipation: shirking, excess labor rents, departmental
empire-building, cost padding, capital-budget manipulation, managerial perks,
and internal lobbying.

The same framework applies by defining a decentralized or no-enforcement
benchmark `Q_D^S`.  In a pure rent-dissipation formulation one may set
`Q_D^S = Q_C`, because the rent-dissipation pressure disappears only when the
competitive output eliminates the monopoly rent wedge.  In a mixed-compensation
formulation `Q_D^S` may instead be `Q(α, β)`, the quantity generated by the
organization's incentive system before additional monitoring is imposed.

With quadratic enforcement cost,

`Q_S* = (2 b Q_M + κ_S Q_D^S) / (2 b + κ_S)`.

If `Q_D^S > Q_M`, then

`Q_M < Q_S* < Q_D^S ≤ Q_C`.
-/

/-! ## 5. Thought experiment III: central command and hierarchy -/

/-- Probability of detecting a deviation with monitoring intensity `m`.  The
functional form is increasing and concave: initial monitoring catches obvious
violations; additional monitoring faces diminishing returns. -/
def detectionProb (m : ℝ) : ℝ :=
  1 - exp (-m)

/-- Required monitoring intensity when the private deviation gain is `γ * x`,
the maximum effective punishment is `P`, and the deterrence condition is
`P * detectionProb(m) ≥ γ * x`.  The formula is defined on the domain
`γ * x < P`. -/
def requiredMonitoring (γ P x : ℝ) : ℝ :=
  - log (1 - γ * x / P)

/-- Central-command cost: hierarchy, audits, accounting systems, internal
approval rules, transfer pricing, inventory controls, and punishment systems. -/
def centralCommandCost (ω γ P x : ℝ) : ℝ :=
  (ω / 2) * (requiredMonitoring γ P x) ^ 2

/-!
Derivation of the central-command case.

Central command is another solution to local overselling and common-profit
shirking.  Headquarters can centralize prices, output quotas, customer
allocations, capacity approval, inventory release, sales exceptions, and
internal accounting.  The purpose is to make the organization behave like a
single monopoly owner.

Central command does not eliminate the agency problem.  It changes the margin
of conflict.  Once headquarters restricts output, it creates scarce internal
rights:

* the right to produce;
* the right to sell;
* the right to serve a customer;
* the right to grant a discount or non-price concession;
* the right to draw from inventory;
* the right to receive capacity investment;
* the right to obtain an exception from the quota rule.

The stricter the restriction, the more valuable each unit of quota becomes.
Plants, regions, and managers therefore have stronger incentives to misreport
local demand, manipulate costs, hide discounts, relabel transactions, claim
strategic exceptions, or pad capacity to obtain larger future allocations.

Let

`x_C = Q_D^C - Q`

be the amount of central restriction.  Let the private gain from evading
headquarters be

`g_C(x_C) = γ_C x_C`,

where `γ_C > 0`.  Let `m` be monitoring intensity and suppose the probability
of detection is

`ρ(m) = 1 - exp(-m)`.

Let `P` be the maximum effective punishment.  The organization cannot impose
infinite penalties; it can fire, demote, withhold bonuses, reassign, sue, or
block promotion, but all are bounded.  Deterrence requires

`P ρ(m) ≥ γ_C x_C`.

The minimum monitoring intensity solves

`P (1 - exp(-m)) = γ_C x_C`.

Hence

`m(x_C) = -log(1 - γ_C x_C / P)`.

This formula is meaningful only when

`γ_C x_C < P`.

If the restriction is so severe that `γ_C x_C ≥ P`, then even certain detection
cannot deter deviation.  The target output is not enforceable through this
central-command technology.

Differentiating the monitoring requirement gives

`m_x(x_C) = γ_C / (P - γ_C x_C) > 0`,

and

`m_xx(x_C) = γ_C^2 / (P - γ_C x_C)^2 > 0`.

Thus monitoring intensity rises convexly with the strictness of the output
restriction.  If the resource cost of central command is

`E_C(x_C) = (ω/2) m(x_C)^2`,

then

`E_C,x(x_C) = ω m(x_C) m_x(x_C) > 0`,

and

`E_C,xx(x_C) = ω [m_x(x_C)^2 + m(x_C)m_xx(x_C)] > 0`.

The owner solves

`max_Q G(Q) - E_C(Q_D^C - Q)`.

The first-order condition is

`G'(Q) + E_C,x(Q_D^C - Q) = 0`.

The plus sign is central.  Increasing `Q` reduces the restriction gap, so it
saves hierarchy cost.  At the textbook monopoly quantity `Q_M`, gross-profit
marginal value is zero, but the hierarchy-cost saving from higher output is
positive whenever `Q_D^C > Q_M`.  Therefore the owner moves to a quantity above
`Q_M`.  Under concavity, the optimum satisfies

`Q_M < Q_C* < Q_D^C`.

The same closed-form quadratic approximation is

`Q_C* = (2 b Q_M + κ_C Q_D^C) / (2 b + κ_C)`.
-/

/-! ## 6. Effective marginal cost -/

/-!
Let ordinary production marginal cost be constant at `c`.  Total cost is

`TC(Q) = c Q + E(Q_D - Q)`.

The derivative with respect to output is

`MC_eff(Q) = c - E_x(Q_D - Q)`.

The minus sign appears because increasing output reduces the enforcement gap.
Thus at low output the effective marginal cost can be below ordinary production
marginal cost: producing one more unit costs `c`, but saves internal
monitoring cost.  If `E_xx ≥ 0`, then

`d MC_eff(Q) / dQ = E_xx(Q_D - Q) ≥ 0`.

Consequently, effective marginal cost can rise with output even when ordinary
technological marginal cost is constant or falling.  This is the mechanism
through which internal governance costs push the actual monopolist to produce
more than the textbook monopoly quantity.
-/

/-! ## 7. Downstream welfare and regulation -/

/-- Harberger triangle for the linear-demand, constant-marginal-cost case. -/
def linearDWL (b Qc Q : ℝ) : ℝ :=
  (b / 2) * (Qc - Q) ^ 2

/-- If actual output exceeds the textbook monopoly output, the regulatory gap is
smaller than the textbook gap. -/
theorem regulatoryGap_smaller_when_actual_output_higher
    (Qc Qm Qstar : ℝ) (h : Qm < Qstar) :
    regulatoryGap Qc Qstar < regulatoryGap Qc Qm := by
  unfold regulatoryGap
  linarith

/-- Closed-form output when the decentralized organizational benchmark is a
fraction `α` of the competitive benchmark. -/
def agencyConstrainedQuantityAlpha (b κ α Qc : ℝ) : ℝ :=
  Qc * ((b + κ * α) / (2 * b + κ))

/-- The formula using `α` coincides with the general formula when
`Qd = α * Qc`. -/
theorem agencyConstrained_alpha_eq
    (b κ α Qc : ℝ) :
    agencyConstrainedQuantity b κ Qc (α * Qc) =
      agencyConstrainedQuantityAlpha b κ α Qc := by
  unfold agencyConstrainedQuantity agencyConstrainedQuantityAlpha
  ring

/-- The actual regulatory gap under the alpha parameterization. -/
theorem regulatoryGap_alpha_formula
    (b κ α Qc : ℝ) (hden : 2 * b + κ ≠ 0) :
    regulatoryGap Qc (agencyConstrainedQuantityAlpha b κ α Qc) =
      Qc * ((b + κ * (1 - α)) / (2 * b + κ)) := by
  have hden' : b * 2 + κ ≠ 0 := by
    simpa [mul_comm] using hden
  unfold regulatoryGap agencyConstrainedQuantityAlpha
  field_simp [hden, hden']
  ring

/-!
Regulatory implication.

The textbook regulatory calculation treats the unregulated monopolist as
producing `Q_M`.  The textbook output gap is

`Δ_M = Q_C - Q_M`.

In the internal-governance model, the actual unregulated output is `Q*`, so the
relevant output gap is

`Δ* = Q_C - Q*`.

Because `Q* > Q_M`,

`Δ* < Δ_M`.

With linear demand, the allocative loss triangle is

`DWL(Q) = (b/2)(Q_C - Q)^2`.

Therefore, if `Q_M < Q* ≤ Q_C`, then

`DWL(Q*) < DWL(Q_M)`.

The claim is not that regulation is never beneficial.  The claim is that the
standard calculation overstates the allocative gain from intervention whenever
it evaluates the unregulated counterfactual at `Q_M` rather than at the actual
agency-constrained quantity `Q*`.  A regulator that targets `Q_R` generates an
allocative output gain measured from `Q*`:

`∫_{Q*}^{Q_R} [p(q) - c] dq`,

not from `Q_M`:

`∫_{Q_M}^{Q_R} [p(q) - c] dq`.

When regulation itself has administrative, informational, capture, or
compliance costs, the welfare comparison must be made between imperfect
organizations: the agency-constrained monopoly and the regulator-constrained
policy regime.
-/

/-! ## 8. Summary of the unified framework -/

/-!
For each stylized organizational case `j`, define:

* `Q_D^j`: the output toward which the organization drifts absent costly
  enforcement;
* `x_j = Q_D^j - Q`: the governance gap;
* `E_j(x_j)`: the enforcement, agency, or hierarchy cost;
* `Q_j*`: the actual output chosen by the owner.

The owner's problem is

`max_Q G(Q) - E_j(Q_D^j - Q)`.

If

`G'(Q_M) = 0`, `G'' < 0`, `E_j,x > 0`, `E_j,xx ≥ 0`, and `Q_D^j > Q_M`,

then the first-order condition is

`G'(Q_j*) + E_j,x(Q_D^j - Q_j*) = 0`,

and the solution satisfies

`Q_M < Q_j* < Q_D^j ≤ Q_C`.

The three thought experiments generate `E_j` in different ways.

1. Local incentives: agents overproduce because each internalizes only the price
   effect on local output.  The decentralized benchmark is an internal Cournot
   quantity.

2. Common profit-sharing: agents internalize total profit more fully, but effort
   incentives are diluted and monopoly rents are dissipated through slack,
   bargaining, and internal appropriation.  The benchmark may be the competitive
   quantity or the mixed-compensation quantity.

3. Central command: headquarters suppresses local discretion through quotas,
   audits, reporting, transfer pricing, inventory controls, and punishment.
   Bounded punishments and diminishing returns to detection make monitoring
   costs increasing and convex in the restriction gap.

The common implication is that monopoly output restriction is not merely a
choice of `Q`.  It is an organizational command that must be transmitted,
measured, allocated, and enforced across many agents.  The stricter the
restriction, the higher the private gain from evasion or rent capture, and the
more expensive the internal enforcement apparatus becomes.  The monopolist
therefore behaves less like a frictionless textbook monopolist than the unitary
model predicts.
-/

/-! ## 9. Literature notes

The formal derivations above are self-contained.  The following works are
natural academic points of contact for a paper using this framework:

* Alchian, Armen A., and Harold Demsetz. 1972. "Production, Information Costs,
  and Economic Organization." American Economic Review.
* Jensen, Michael C., and William H. Meckling. 1976. "Theory of the Firm:
  Managerial Behavior, Agency Costs and Ownership Structure." Journal of
  Financial Economics.
* Holmström, Bengt. 1982. "Moral Hazard in Teams." Bell Journal of Economics.
* Stigler, George J. 1964. "A Theory of Oligopoly." Journal of Political
  Economy.
* Harberger, Arnold C. 1954. "Monopoly and Resource Allocation." American
  Economic Review.
* Posner, Richard A. 1969. "Natural Monopoly and Its Regulation." Stanford Law
  Review.
* Porter, Robert H. 1983. "A Study of Cartel Stability: The Joint Executive
  Committee, 1880--1886." Bell Journal of Economics.
* Genesove, David, and Wallace P. Mullin. 1998. "Testing Static Oligopoly
  Models: Conduct and Cost in the Sugar Industry, 1890--1914." RAND Journal of
  Economics.
-/

end MonopolyInternalCartel
