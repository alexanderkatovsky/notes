# Double Descent, Memorization, and Generalization

Two papers discuss double descent while moving along different axes:

| Paper | Axis explored | Explanation emphasized |
| --- | --- | --- |
| **Morris et al., [“How much do language models memorize?”](https://arxiv.org/abs/2505.24832)** | Increase **training-set size** relative to a model's estimated information-storage capacity, considering models of different sizes. | Their framework separates *unintended memorization*—information retained about particular examples—from *generalization*—information about the underlying data process. On real text, near the estimated capacity, unintended memorization becomes less beneficial, generalization grows, and double descent appears. Random-data experiments estimate GPT-style model capacity at roughly 3.6 bits per parameter. |
| **Wilson, [“Deep Learning is Not So Mysterious or Different”](https://arxiv.org/abs/2503.02113)** | Vary **feature-space dimension** in an overparameterized linear setting, with the dataset held fixed in the comparison. | Double descent and benign overfitting are not unique to deep networks. In underdetermined linear regression, many solutions interpolate the training data; a bias such as the Moore–Penrose minimum-norm solution can favor an interpolant that generalizes well under suitable data assumptions. |

**Contrast:** Morris moves along the *data-size axis*: more examples eventually make sample-specific memorization insufficient relative to the dataset's information content, encouraging generalization. Wilson moves along the *feature-dimension axis*: more features create more interpolating solutions, and the learning rule's implicit bias can select one that generalizes.

Both show that fitting the training set does not by itself determine generalization, but their thresholds and mechanisms should not be conflated. Exceeding estimated memorization capacity is not automatically the same as crossing the linear-model interpolation threshold, and a larger feature space alone does not guarantee better generalization.
