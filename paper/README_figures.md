# Redrawing the figures

Keep `plot_reset_figures.py`, `reset_gain_comparison.csv`, and
`family_convergence.csv` in the same folder. With Python 3, NumPy, and
Matplotlib available, run:

```sh
python plot_reset_figures.py
```

The script reads the accompanying data and saves four files beside itself:

| Figure | Vector file | Raster file | Size |
| --- | --- | --- | --- |
| Reversal fractions at matched disturbance | `reset_gain_comparison.pdf` | `reset_gain_comparison.png` | 3.4 by 3.55 inches |
| Asymptotic convergence | `reset_convergence.pdf` | `reset_convergence.png` | 3.4 by 4.6 inches |

The PDFs contain vector curves and embedded fonts. The PNGs are exported at
300 dpi. The script uses paths relative to its own location and can be run
from any working directory. It only redraws the saved data.

## Data and numerical precision

Both data sets use the actual output disturbance, with
`actual_log_inverse_epsilon` equal to $L_\epsilon=\ln(1/\epsilon)$ and
`gain` equal to the population reversal $\Delta=\epsilon-a=-q$.

- `reset_gain_comparison.csv` contains 209 matched values of
  $L_\epsilon$ for each construction, from $3\ln 10$ to 2560 (418 rows).
  The data were evaluated with 100 decimal digits of working precision
  and saved with 80 significant digits. The internal parameter was solved
  separately for each construction to match the actual disturbance;
  the curves are not interpolated onto a common error grid.
  `gain_fraction` is $\Delta/\epsilon$.
- `family_convergence.csv` contains 85 samples for each construction
  (170 rows), using geometrically spaced internal parameters
  $\ell\in[20,2560]$. The calculations used 100 decimal digits of working
  precision. Output quantities were saved with 30 significant digits
  and `input_L` with 20 significant digits. `scaled_log` is
  $\Delta L_\epsilon/\epsilon$ and `scaled_log_squared` is
  $\Delta L_\epsilon^2/\epsilon$. The original data identifier `aligned`
  denotes the diagonal stationary state construction; only `pure` and
  `aligned` rows are included.

For the pure stationary state construction, the saved data use
$p=e^{-\ell}$, $\nu=0$,
$A=\ell+\ln\ell+1-\ln 4$, and $B=A/\ell$.
For the diagonal stationary state construction, they use
$p=0$, $\nu=e^{-\ell}$, and $B=2A/\ell$, with $A$ at the analytic
minimum of the two-exponential population response. The actual
disturbance and reversal were evaluated from these explicit
constructions. The curves do not represent finite-error global optima.

The recorded data-generation checks for the matched-disturbance data
used 150-decimal-digit, four-dimensional GKSL matrix exponentials at
$L_\epsilon=3\ln 10,\ 6\ln 10,\ 40,\ 160$ for both constructions.
The probability discrepancies divided by the reversal were below
$10^{-65}$, and the stationary-state residual norms were below
$10^{-130}$ at those points. These checks are separate from redrawing.

All supplied CSV fields and decimal strings are preserved. Plotting
converts only the logarithmic coordinate and already-scaled ordinates
to double precision, so the very small stored probabilities need not
be converted to floating-point numbers.

## Curve and panel conventions

In the comparison figure, solid curves with sparse open circles and
open squares denote the pure and diagonal stationary state
constructions, respectively. The markers distinguish the constructions
and do not encode uncertainty. Dashed curves show
$4/(eL_\epsilon)$ and $64/(e^2L_\epsilon^2)$, respectively.

In the convergence figure, panel (a) shows
$\Delta L_\epsilon/\epsilon$ for the pure stationary state construction
and the dashed limit $4/e$. Panel (b) shows
$\Delta L_\epsilon^2/\epsilon$ for the diagonal stationary state
construction and the dashed limit $64/e^2$. All logarithms are natural.
