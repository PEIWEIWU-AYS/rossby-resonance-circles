# Circle enumeration and a sharpness family for resonant Rossby wave triads

**Peiwei Wu** · Shandong Medical and Pharmaceutical University (formerly Binzhou Medical University)  
**Qian Peng** · The University of Melbourne · Corresponding author

[Paper](manuscript.pdf) · [LaTeX source](manuscript.tex) · [Lean theorem audit](Main.lean) · [Exact enumeration in Python](enumerate_triads.py)

A nonzonal square-torus output mode of squared length M has at most twice as many ordered resonant decompositions as there are signed, ordered representations of M³ by two squares. Enumerating those circles gives a deterministic box search in N² times a power of log N. A separate infinite family of primitive exact resonances satisfies (a/b⁴)² = 3 − 8/b². It approaches the coefficient in Kopp's horizontal anisotropy conjecture and proves that the proposed coefficient and exponent cannot be decreased. The full upper bound for other triads remains open.

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
