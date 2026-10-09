# Partial Solution for FLT from Trigonometric Analysis

This Lean 4 project formalizes three asymptotic results for the trigonometric
equation

```text
(sin (a * t_n) / sin (b * t_n)) ^ n = tan(t_n) ^ 2.
```

The equation arises from a geometric reformulation of a hypothetical solution
of Fermat's equation

```text
x^n + y^n = z^n,  n > 2.
```

If `x`, `y`, and `z` form the associated acute triangle with opposite angles
`alpha`, `beta`, and `gamma`, the sine rule gives

```text
x / y = sin(alpha) / sin(beta).
```

The powered lengths `x^(n/2)`, `y^(n/2)`, and `z^(n/2)` form a right triangle.
For its corresponding acute angle `theta`, one obtains the necessary identity

```text
tan(theta)^2 = (x / y)^n = (sin(alpha) / sin(beta))^n.
```

## Formalized Partial Results

Both results are proved in [`RootCollapse.lean`](RootCollapse.lean).

### 1. Nonoscillatory root collapse

```lean
RootCollapse.roots_tend_to_zero
```

Under

```text
0 < a < b <= 1,
0 < t_n < pi / 2,
```

every sequence of roots satisfies

```text
t_n -> 0.
```

The proof uses strict monotonicity of sine on the first quadrant, compactness,
and uniform geometric decay of powers of a ratio strictly below one. The
strict regime `0 < a < b < 1` is therefore covered, as is the boundary case
`b = 1`.

### 2. General-frequency level-set rigidity

```lean
RootCollapse.accumulation_point_on_level_set
```

For arbitrary frequencies, suppose a sequence of positive-ratio roots
converges to an interior point `tStar`, with

```text
0 < tStar < pi / 2
sin (b * tStar) != 0.
```

Then the accumulation point must satisfy

```text
sin (a * tStar) / sin (b * tStar) = 1.
```

This theorem applies away from poles of the sine ratio. It does not claim that
every root sequence converges, or that every point on the level set is
approached by roots. Other branches may approach zero, a pole, or `pi / 2`.

### 3. Fixed-frequency collapse on the acute branch

```lean
RootCollapse.roots_tend_to_zero_of_acute_branch
```

For fixed `0 < a < b`, the global restriction `b <= 1` can be removed if every
root satisfies the Fermat acute-angle condition

```text
0 < a * t_n < b * t_n < pi / 2.
```

Then every root sequence again satisfies `t_n -> 0`. The acute condition rules
out poles and makes sine strictly increasing between `a * t_n` and `b * t_n`,
so the level-set alternative from the general-frequency theorem is impossible.

## Meaning of Partial Solution

These results give a partial analytic classification of the trigonometric
problem induced by a hypothetical Fermat triple:

- Below the unit frequency boundary, every root sequence collapses to zero.
- For general `b > a`, every positive, interior, nonsingular accumulation
  point lies on the level set where the sine ratio equals one.
- When the frequencies are fixed and `a * t_n`, `b * t_n` remain ordered acute
  angles, that level set is inaccessible and collapse to zero is the only
  possible asymptotic behavior.

This is **not a proof of Fermat's Last Theorem**. Fermat's Last Theorem concerns
each fixed integer exponent and exact positive integers. The results here are
asymptotic statements about real roots. Across hypothetical triples with
varying exponent, the normalized frequencies may also vary, so these theorems
do not provide the missing arithmetic contradiction that excludes an integer
triple.

## Building the Proofs

The project uses Lean `v4.34.0-rc2` and a local Mathlib dependency.

From this directory, check the file directly:

```bash
lake env lean RootCollapse.lean
```

Build the complete project with:

```bash
lake build
```

The formal proofs contain no `sorry` or admitted results.

## Manuscript

The accompanying Word manuscript includes the mathematical derivations,
interpretation, graphs, limitations, and Lean theorem statements:

[`Root_Collapse_Nonoscillatory_Sine_Ratios.docx`](../output/docx/Root_Collapse_Nonoscillatory_Sine_Ratios.docx)
