# Double Descent, Memorization, and Generalization

In Morris et al.'s statistical framing, the entire machine learning pipeline—from the data-generating concept to the trained weights—is described by random variables connected in a three-variable Markov chain (we use $Z$ here to avoid notation clash later, but this is $X$ in the paper):

```math
\Theta \longrightarrow Z \longrightarrow \hat{\Theta}
```

$\Theta$ is a random variable capturing our knowledge of the true parameters; $Z$ is a random variable that is the observed data and $\hat{\Theta}$ is a random variable that is the parameter estimates after observing the data $Z$ (from fitting a model for example).

The joint distribution factors according to this dependency structure:

```math
p(\Theta, Z, \hat{\Theta}) = p(\Theta) \, p(Z \mid \Theta) \, p(\hat{\Theta} \mid Z)
```

## Example -- Least Squares

Suppose $\sigma > 0$, and $X \in \mathbb{R}^n$

```math
\Theta = (m, b) \sim p(\Theta)
```

Define the design matrix:

```math
A=
\begin{pmatrix}
x_1&1\\
x_2&1\\
\vdots&\vdots\\
x_n&1
\end{pmatrix}
```

and

```math
Y = A\Theta + \boldsymbol\varepsilon \qquad \boldsymbol\varepsilon \sim \mathcal{N}(0, \sigma^2 I_n)
```


then we take the least squares solution:

```math
    \hat{\Theta} = (\hat{m}, \hat{b}) = (A^TA)^{-1}A^T\mathbf Y = \Theta + (A^TA)^{-1}A^T\boldsymbol\varepsilon
```
then because $\operatorname{Cov}(C\boldsymbol\varepsilon)=C\operatorname{Cov}(\boldsymbol\varepsilon)C^T$
```math
\hat{\Theta}|\Theta \sim \mathcal{N}(\Theta, \sigma^2 (A^TA)^{-1})
```

Intuitively, $\lim_{n\to\infty}\hat{\Theta} = \Theta$ then $\mathrm{mem}_U(Y, \hat{\Theta}, \Theta) = H(X|\Theta) - H(X|\Theta, \hat{\Theta}) \to 0$

Now we reach a technical problem Morris skirts over; it's a techical issue to do with continuous distributions.  The total memorization is
```math
I(\mathbf Y;\hat\Theta)
=D_{\mathrm{KL}}\left(
P_{\mathbf Y,\hat\Theta}
\,\middle\|\,
P_{\mathbf Y}\otimes P_{\hat\Theta}
\right)
```
which is infinite since we need the Radon-Nykodym derivative in the continuous setting:
```math
D_{\mathrm{KL}}(P\|Q)
=
\begin{cases}
\displaystyle\int \log\left(\frac{dP}{dQ}\right)dP,
& P\ll Q,\\[8pt]
+\infty, & \text{otherwise}.
\end{cases}
```
and $P_{\mathbf Y,\hat\Theta} \not\ll P_{\mathbf Y}\otimes P_{\hat\Theta}$ because $\hat\Theta$ is a deterministic function of $\mathbf Y$.  The fitted parameters $\hat\Theta$ are exact real numbers that are deterministic functions of the data $\mathbf Y$: If we know $\mathbf Y$, we can calculate $\hat\Theta$ exactly. Because the parameters are continuously distributed, specifying their exact values can require arbitrarily many bits of precision.

I think these technical issues are not imagined to arise in the paper since its setting is implicitly assumed to be discrete.  Indeed, the experiments are done on computers with floating point arithmetic of course, and this is what they are building up to.

### Quantization

Let's suppose our fitted model was instead (making the dependence on $n$ explicit) $T_n = Q(\hat{\Theta}_n)$ with $\hat{\Theta}_n = f(Y^n)$, a deterministic function of the $n$ datapoints $Y^n$.  Here, $Q:\mathbb R^d\to\mathcal F$ for finite $\mathcal F$ is a quantization function where each real number in $\hat{\Theta}_n$ is quantized (e.g. IEEE 754 floating-point format).  The rounding boundary of $Q$ is the subset of $\mathbb R^d$ where $Q$ is discontinuous.  Now the unintended memorization at some $\Theta = \theta$ is

```math
\mathrm{mem}_U(Y^n, T_n, \theta) = I(Y^n; T_n|\Theta=\theta) = H(T_n|\Theta=\theta) + H(T_n|Y^n, \Theta=\theta) = H(T_n|\Theta=\theta)
```

[$H(T_n|Y^n, \Theta=\theta) = 0$ since $T_n$ is a deterministic function of $Y^n$] It can be shown that for given fixed $\Theta = \theta$, under mild conditions on the design matrix $A$, $\hat{\Theta}_n \xrightarrow{P}\theta$.  If $\theta$ isn't at a rounding boundary of $Q$ then, by the continuous mapping theorem, $T_n  =Q(\hat{\Theta}_n)\xrightarrow{P}Q(\theta)$.  By Fano's inequality:

```math
H(T_n\mid\Theta=\theta)
\le h_2(p_n(\theta))
+p_n(\theta)\log(|\mathcal F|-1)
```

where $p_n(\theta) = P(T_n\neq Q(\theta)|\Theta = \theta)$ and $h_2(p)=-p\log p-(1-p)\log(1-p)$.

Since $p_n(\theta) \to 0$ then $H(T_n|\Theta=\theta) \to 0$

### Komologorov Complexity

I think the paper skirts over subtleties around Komologorov complexity as well.  The paper sketches the theory cursorily, while its main focus is on the experimental results. It's only defined up to a constant and depends on the precise universal Turing machine encoder details.  I think the least squares toy example here seen through the Kolmogorv lens is the result that as $n \to\infty$ the excess information required to encode the fitted model over that required for the true parameters tends to zero in expectation under any encoding:

```math
\mathbb E\!\left[
\left|K(T_n\mid\theta)-K(Q(\theta)\mid\theta)\right|
\,\middle|\,\Theta=\theta
\right]\longrightarrow 0
```

if we define $\Delta_n := K(T_n\mid\theta)-K(t_\theta\mid\theta)$.  Because $T_n$ takes values in a finite set $\mathcal F$, then $|\Delta_n|\le C$ for some $C >= 0$.  On the event $T_n=t_\theta$, we have $\Delta_n=0$. Therefore,
```math
\begin{aligned}
\mathbb E[|\Delta_n|\mid\Theta=\theta]
&=\mathbb E[|\Delta_n|\mathbf 1_{\{T_n\ne t_\theta\}}\mid\Theta=\theta]\\
&\le C\,p_n(\theta)
\end{aligned}
```
Since $p_n(\theta)\to 0$, we indeed have
```math
\mathbb E[|\Delta_n|\mid\Theta=\theta]\longrightarrow 0
```

## Conclusion

These are really a fairly trivial results: they just says that - because the linear model is so rigid - as data generated stochastically from the true underlying process governed by $\theta$ becomes very large, then the model fitted to that data can't do anything else but reflect the underlying process (which it has only seen indirectly via the data) faithfully.  However, I think this is really what the paper is getting at even with the large transformer models, except the data required there is much larger, and the empirical results of the paper are non-trivial.

This paper is a contribution to the "explaining the double descent phenomenon" literature.  But it does so along an axis of this phenomenon which is actually the classical (not-so-mysterious) one: i.e. keep the model size fixed, and increase the training data size.  We end up with an unsurprising result, which is qiute classical in spirit.  The more interesting axis is why do we observe model generalization where we travel along another axis: keep the training data size fixed but increase the size of the model, or the number of input features (see Wilson "Deep Learning is not so Mysterious or Different").


## References 

**Morris et al., [“How much do language models memorize?”](https://arxiv.org/abs/2505.24832)** | Increase **training-set size** relative to a model's estimated information-storage capacity, considering models of different sizes. | Their framework separates *unintended memorization*—information retained about particular examples—from *generalization*—information about the underlying data process. On real text, near the estimated capacity, unintended memorization becomes less beneficial, generalization grows, and double descent appears. Random-data experiments estimate GPT-style model capacity at roughly 3.6 bits per parameter.

**Wilson, [“Deep Learning is Not So Mysterious or Different”](https://arxiv.org/abs/2503.02113)** | Vary **feature-space dimension** in an overparameterized linear setting, with the dataset held fixed in the comparison. | Double descent and benign overfitting are not unique to deep networks. In underdetermined linear regression, many solutions interpolate the training data; a bias such as the Moore–Penrose minimum-norm solution can favor an interpolant that generalizes well under suitable data assumptions. |
