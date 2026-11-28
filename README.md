# Circle enumeration and a sharpness family for resonant Rossby wave triads | 共振罗斯贝波三元组的整数圆枚举与四次增长构造

**Peiwei Wu** · Shandong Medical and Pharmaceutical University (formerly Binzhou Medical University)  
**Qian Peng** · The University of Melbourne · Corresponding author

[Paper](manuscript.pdf) · [Version DOI 10.5281/zenodo.24613761](https://doi.org/10.5281/zenodo.24613761) · [LaTeX source](manuscript.tex) · [Lean theorem audit](Main.lean) · [Exact enumeration in Python](enumerate_triads.py)

**Exact Rossby wave triad enumeration.** A nonzonal square-torus output mode of squared length M has at most twice as many ordered resonant decompositions as there are signed, ordered representations of M³ by two squares. Enumerating those circles gives a deterministic box search in N² times a power of log N. A separate infinite family of primitive exact resonances satisfies (a/b⁴)² = 3 − 8/b². Along this family a/b⁴ approaches √3 from below as b grows, so any uniform polynomial upper bound requires exponent at least four. A [subsequent counterexample](https://doi.org/10.5281/zenodo.24591008) at b = 34 has a/b⁴ > 250 and disproves Kopp's proposed coefficient √3.

本文把给定输出波向量的共振分解化为整数圆上的枚举，得到近二次时间的有限盒完整搜索。另一组 Pell 方程构造说明，统一多项式上界的指数至少为四。

**Keywords · 关键词**　exact Rossby wave triads · fixed-output enumeration · integer circle · quartic growth · 罗斯贝波共振三元组 · 整数圆枚举

## Build and verify

The project uses Lean 4.19.0 and mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. From the repository root, run

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Main.lean
```

The last command prints the axiom dependencies of 16 named theorems. The PDF can be rebuilt with `tectonic manuscript.tex`.

| Mathematical statement | Lean declarations |
| --- | --- |
| Rational dispersion relation and its integer circle criterion | [RossbyCircle.lean](RossbyCircle.lean), `frequency_cross`, `resonates_iff_circle` |
| Complete inverse, unordered fibers and exact finite set of ordered inputs | [RossbyCircle.lean](RossbyCircle.lean), `quadratic_recovery`, `circle_fiber`, `mem_allPartners`, `allPartners_card` |
| Prime-power inequality underlying the aggregate bound and explicit parameter cutoff | [Counting.lean](Counting.lean), `divisor_eight_local`, `inverse_parameter_bound` |
| Pell recurrence, exact frequencies, primitivity and sharpness above any height cutoff | [PellSharp.lean](PellSharp.lean), `orbit_spec`, `primitive`, `ratio_square`, `primitive_sharpness` |

The theorem about the finite partner set is stated without any box cutoff on either input. Lean uses classical choice to select a preimage for each nonempty fiber of the circle map. The arithmetic implementation in Python uses Gaussian square roots and parity tests. The running-time analysis combines the Lean-verified reductions with Gaussian factorization, the classical two-square formula and summation of the eightfold divisor function.

## Run the enumerator

The Python program uses only the standard library. A triad is represented by the tuple `(a,b,x,y)`, where the output is `(a,b)` and the inputs are `(x,y)` and `(a-x,b-y)`. The command-line box search returns one fully nonzonal representative per symmetry class, with a positive sum of positive real components, exchange of the inputs, and reflection of the imaginary components. Primitivity means that the four integer components have greatest common divisor one.

```sh
python3 enumerate_triads.py 100
python3 enumerate_triads.py 100 --all --list
python3 enumerate_triads.py --check
```

At N = 100 the program finds 12 primitive classes, or 29 classes including dilations. The check enumerates all integer points on the first 100 norm circles independently and compares both box counts and the actual tuples with a direct four-coordinate search at N = 32.

## GitHub topics

`rossby-waves` `wave-resonance` `diophantine-equations` `gaussian-integers` `pell-equation` `enumeration-algorithms` `lean4`

[Original question, search terms, and citation](docs/discoverability.md)
