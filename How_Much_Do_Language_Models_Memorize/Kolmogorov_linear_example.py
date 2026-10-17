import numpy as np
import matplotlib.pyplot as plt
from scipy.stats import norm

# Reproducibility
rng = np.random.default_rng(42)

# Model parameters
theta = 0.0
sigma = 0.5
delta = 0.2

# Experiment settings
n_values = np.arange(1, 1001)
n_trials = 5000

# Store results
mean_memorization_bits = np.zeros(len(n_values))
empirical_error_probability = np.zeros(len(n_values))
theoretical_error_probability = np.zeros(len(n_values))

for j, n in enumerate(n_values):

    # Sample mean under the true model
    sample_means = theta + sigma / np.sqrt(n) * rng.standard_normal(n_trials)

    # Quantized fitted model
    T_n = delta * np.round(sample_means / delta)

    # Event that the quantized estimate differs from the true quantized value
    t_theta = delta * np.round(theta / delta)
    errors = T_n != t_theta
    empirical_error_probability[j] = np.mean(errors)

    # Paper-style compression proxy:
    # log2 p(data | target) - log2 p(data | reference), clipped at zero.
    #
    # For Gaussian observations with known sigma, the log-likelihood
    # difference depends on the sample mean:
    log_likelihood_ratio = (
        n / (2 * sigma**2)
        * ((sample_means - theta)**2 - (sample_means - T_n)**2)
    )

    memorization_bits = np.maximum(log_likelihood_ratio, 0) / np.log(2)
    mean_memorization_bits[j] = np.mean(memorization_bits)

    # Exact probability of crossing a rounding boundary.
    # theta = 0 is at the center of its quantization cell.
    theoretical_error_probability[j] = (
        2 * norm.cdf(-delta * np.sqrt(n) / (2 * sigma))
    )

# Choose an illustrative C for visual comparison.
# This is fitted to the finite simulation, not a theoretical guarantee.
valid = theoretical_error_probability > 0
ratios = (
    mean_memorization_bits[valid]
    / theoretical_error_probability[valid]
)
C_empirical = np.max(ratios) if len(ratios) else 0.0

# Plot 1: paper-style compression proxy
plt.figure(figsize=(9, 5))
plt.plot(
    n_values,
    mean_memorization_bits,
    label="Mean likelihood-based compression proxy"
)
plt.xlabel("Sample size n")
plt.ylabel("Estimated unintended memorization (bits)")
plt.title("Least squares: likelihood-based compression proxy")
plt.grid(True, alpha=0.3)
plt.legend()
plt.tight_layout()
plt.show()

# Plot 2: comparison with the quantization error probability
plt.figure(figsize=(9, 5))
plt.plot(
    n_values,
    theoretical_error_probability,
    label=r"Theoretical $p_n(\theta)$"
)
plt.plot(
    n_values,
    empirical_error_probability,
    label="Empirical quantization error probability",
    alpha=0.8
)
plt.xlabel("Sample size n")
plt.ylabel("Probability")
plt.title("Probability of a quantization error")
plt.grid(True, alpha=0.3)
plt.legend()
plt.tight_layout()
plt.show()

# Plot 3: illustrative comparison with C p_n
plt.figure(figsize=(9, 5))
plt.plot(
    n_values,
    mean_memorization_bits,
    label="Mean likelihood-based compression proxy"
)
plt.plot(
    n_values,
    C_empirical * theoretical_error_probability,
    "--",
    label=rf"$C p_n(\theta)$, with fitted $C={C_empirical:.3g}$"
)
plt.xlabel("Sample size n")
plt.ylabel("Bits")
plt.title("Illustrative comparison with a scaled error probability")
plt.grid(True, alpha=0.3)
plt.legend()
plt.tight_layout()
plt.show()

print(f"Illustrative fitted constant C = {C_empirical:.6g}")
